(* Js_of_ocaml compiler
 * http://www.ocsigen.org/js_of_ocaml/
 * Copyright (C) 2010 Jérôme Vouillon
 * Laboratoire PPS - CNRS Université Paris Diderot
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, with linking exception;
 * either version 2.1 of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *)

open! Stdlib
open Code

type prop =
  { size : int
  ; optimizable : bool
  }

type closure_info =
  { cl_params : Var.t list
  ; cl_cont : int * Var.t list
  ; cl_prop : prop
  ; cl_simpl : (Var.Set.t * bool) option
  }

let block_size { branch; body; _ } =
  List.length body
  +
  match branch with
  | Cond _ -> 2
  | Switch (_, a1, a2) -> Array.length a1 + Array.length a2
  | _ -> 0

let size_threshold = 20

let simple_function blocks name params pc =
  let bound_vars =
    ref
      (List.fold_left
         ~f:(fun s x -> Var.Set.add x s)
         ~init:Var.Set.empty
         (name :: params))
  in
  let recursive = ref false in
  let size = ref 0 in
  try
    Code.preorder_traverse
      { fold = Code.fold_children }
      (fun pc () ->
        let block = Addr.Map.find pc blocks in
        size := !size + block_size block;
        if !size > size_threshold then raise Exit;
        (match block.branch with
        | Pushtrap _ -> raise Exit
        | _ -> ());
        List.iter block.body ~f:(fun i ->
            match i with
            | Let (_, Closure _) -> raise Exit
            | _ -> ());
        Freevars.iter_block_bound_vars
          (fun x -> bound_vars := Var.Set.add x !bound_vars)
          block;
        Freevars.iter_block_free_vars
          (fun x ->
            if not (Var.Set.mem x !bound_vars) then raise Exit;
            if Var.equal x name then recursive := true)
          block)
      pc
      blocks
      ();
    (*
    Format.eprintf "SMALL: %a %d %b@." Var.print name !size !recursive;
*)
    Some (!bound_vars, !recursive)
  with Exit -> None

(****)

let optimizable blocks pc _ =
  Code.traverse
    { fold = Code.fold_children }
    (fun pc { size; optimizable } ->
      let b = Addr.Map.find pc blocks in
      let this_size = block_size b in
      let optimizable =
        optimizable
        && List.for_all b.body ~f:(function
               | Let (_, Prim (Extern "caml_js_eval_string", _)) -> false
               | Let (_, Prim (Extern "debugger", _)) -> false
               | Let
                   ( _
                   , Prim
                       (Extern ("caml_js_var" | "caml_js_expr" | "caml_pure_js_expr"), _)
                   ) ->
                   (* TODO: we should be smarter here and look the generated js *)
                   (* let's consider it this opmiziable *)
                   true
               | _ -> true)
      in
      { optimizable; size = size + this_size })
    pc
    blocks
    { optimizable = true; size = 0 }

let rec follow_branch_rec seen blocks = function
  | (pc, []) as k -> (
      let seen = Addr.Set.add pc seen in
      try
        match Addr.Map.find pc blocks with
        | { body = []; branch = Branch (pc, []); _ } when not (Addr.Set.mem pc seen) ->
            follow_branch_rec seen blocks (pc, [])
        | _ -> k
      with Not_found -> k)
  | k -> k

let follow_branch = follow_branch_rec Addr.Set.empty

let get_closures { blocks; _ } =
  Addr.Map.fold
    (fun _ block closures ->
      List.fold_left block.body ~init:closures ~f:(fun closures i ->
          match i with
          | Let (x, Closure (cl_params, cl_cont)) ->
              let cont = follow_branch blocks cl_cont in
              (* we can compute this once during the pass
                 as the property won't change with inlining *)
              let cl_prop = optimizable blocks (fst cont) true in
              let cl_simpl = simple_function blocks x cl_params (fst cont) in
              Var.Map.add x { cl_params; cl_cont; cl_prop; cl_simpl } closures
          | _ -> closures))
    blocks
    Var.Map.empty

(****)

let rewrite_block pc' pc blocks =
  let block = Addr.Map.find pc blocks in
  let block =
    match block.branch, pc' with
    | Return y, Some pc' -> { block with branch = Branch (pc', [ y ]) }
    | _ -> block
  in
  Addr.Map.add pc block blocks

(* Skip try body *)
let fold_children blocks pc f accu =
  let block = Addr.Map.find pc blocks in
  match block.branch with
  | Return _ | Raise _ | Stop -> accu
  | Branch (pc', _) | Poptrap (pc', _) -> f pc' accu
  | Pushtrap (_, _, (pc1, _), pcs) -> f pc1 (Addr.Set.fold f pcs accu)
  | Cond (_, (pc1, _), (pc2, _)) ->
      let accu = f pc1 accu in
      let accu = f pc2 accu in
      accu
  | Switch (_, a1, a2) ->
      let accu = Array.fold_right a1 ~init:accu ~f:(fun (pc, _) accu -> f pc accu) in
      let accu = Array.fold_right a2 ~init:accu ~f:(fun (pc, _) accu -> f pc accu) in
      accu

let rewrite_closure blocks cont_pc clos_pc =
  Code.traverse { fold = fold_children } (rewrite_block cont_pc) clos_pc blocks blocks

(****)

let rec find_mapping mapping x =
  match mapping with
  | [] -> x
  | ([], []) :: rest -> find_mapping rest x
  | (a :: _, b :: _) :: rest when Code.Var.compare a x = 0 -> find_mapping rest b
  | (_ :: ax, _ :: bx) :: rest -> find_mapping ((ax, bx) :: rest) x
  | ([], _ | _, []) :: _ -> assert false

let simple blocks cont mapping =
  let map_var mapping x =
    let x' = find_mapping mapping x in
    if Var.equal x x' then raise Not_found else x'
  in
  let map_prim_arg mapping = function
    | Pc c -> Pc c
    | Pv x -> Pv (map_var mapping x)
  in
  let rec follow seen (pc, args) (instr : [ `Empty | `Ok of 'a ]) mapping =
    if Addr.Set.mem pc seen
    then `Fail
    else
      let b = Addr.Map.find pc blocks in
      let mapping = (b.params, args) :: mapping in
      let instr : [ `Empty | `Ok of 'a | `Fail ] =
        match b.body, instr with
        | [], _ -> (instr :> [ `Empty | `Ok of 'a | `Fail ])
        | [ Let (y, exp) ], `Empty -> `Ok (y, exp)
        | _, _ -> `Fail
      in
      match instr, b.branch with
      | `Fail, _ -> `Fail
      | `Empty, Return ret -> `Alias (map_var mapping ret)
      | `Ok (x, exp), Return ret when Code.Var.compare x (find_mapping mapping ret) = 0
        -> (
          match exp with
          | Constant (Float _ | Int64 _ | Int _ | NativeString _) -> `Exp exp
          | Apply { f; args; exact = true } ->
              `Exp
                (Apply
                   { f = map_var mapping f
                   ; args = List.map args ~f:(map_var mapping)
                   ; exact = true
                   })
          | Prim (prim, args) ->
              `Exp (Prim (prim, List.map args ~f:(map_prim_arg mapping)))
          | Block (tag, args, aon) ->
              `Exp (Block (tag, Array.map args ~f:(map_var mapping), aon))
          | Field (x, i) -> `Exp (Field (map_var mapping x, i))
          | Closure _ -> `Fail
          | Constant _ -> `Fail
          | Apply _ -> `Fail)
      | ((`Empty | `Ok _) as instr), Branch cont ->
          follow (Addr.Set.add pc seen) cont instr mapping
      | (`Empty | `Ok _), _ -> `Fail
  in
  try follow Addr.Set.empty cont `Empty mapping with Not_found -> `Fail

let rec args_equal xs ys =
  match xs, ys with
  | [], [] -> true
  | x :: xs, Pv y :: ys -> Code.Var.compare x y = 0 && args_equal xs ys
  | _ -> false

let inline live_vars closures name pc (outer, p) =
  let block = Addr.Map.find pc p.blocks in
  let body, (outer, branch, p) =
    List.fold_right
      block.body
      ~init:([], (outer, block.branch, p))
      ~f:(fun i (rem, state) ->
        match i with
        | Let (x, Apply { f; args; exact = true; _ }) when Var.Map.mem f closures -> (
            let outer, branch, p = state in
            let { cl_params = params
                ; cl_cont = clos_cont
                ; cl_prop = { size = f_size; optimizable = f_optimizable }
                ; cl_simpl
                } =
              Var.Map.find f closures
            in
            match simple p.blocks clos_cont [ params, args ] with
            | `Alias arg -> (
                match rem, branch with
                | [], Return y when Var.compare x y = 0 -> [], (outer, Return arg, p)
                | _ ->
                    let blocks =
                      Addr.Map.add
                        p.free_pc
                        { params = [ x ]; body = rem; branch }
                        p.blocks
                    in
                    ( []
                    , ( outer
                      , Branch (p.free_pc, [ arg ])
                      , { p with blocks; free_pc = p.free_pc + 1 } ) ))
            | `Exp exp -> Let (x, exp) :: rem, state
            | `Fail -> (
                if live_vars.(Var.idx f) = 1
                   && Bool.equal outer.optimizable f_optimizable
                      (* Inlining the code of an optimizable function could
                         make this code unoptimized. (wrt to Jit compilers) *)
                   && f_size < Config.Param.inlining_limit ()
                then
                  let blocks, cont_pc =
                    match rem, branch with
                    | [], Return y when Var.compare x y = 0 ->
                        (* We do not need a continuation block for tail calls *)
                        p.blocks, None
                    | _ ->
                        ( Addr.Map.add
                            p.free_pc
                            { params = [ x ]; body = rem; branch }
                            p.blocks
                        , Some p.free_pc )
                  in
                  let blocks = rewrite_closure blocks cont_pc (fst clos_cont) in
                  (* We do not really need this intermediate block.
                     It just avoids the need to find which function
                     parameters are used in the function body. *)
                  let blocks =
                    Addr.Map.add
                      (p.free_pc + 1)
                      { params; body = []; branch = Branch clos_cont }
                      blocks
                  in
                  let outer = { outer with size = outer.size + f_size } in
                  ( []
                  , ( outer
                    , Branch (p.free_pc + 1, args)
                    , { p with blocks; free_pc = p.free_pc + 2 } ) )
                else
                  match cl_simpl with
                  | Some (bound_vars, recursive)
                    when (not recursive)
                         ||
                         match name with
                         | None -> true
                         | Some f' -> not (Var.equal f f') ->
                      let p, f, params, clos_cont =
                        Duplicate.closure p ~bound_vars ~f ~params ~cont:clos_cont
                      in
                      (*
                      Format.eprintf "DUPLICATE %a ==> %d@." Var.print f (fst clos_cont);
*)
                      if recursive
                      then
                        ( Let (f, Closure (params, clos_cont))
                          :: Let (x, Apply { f; args; exact = true })
                          :: rem
                        , (outer, branch, p) )
                      else
                        let blocks, cont_pc =
                          match rem, branch with
                          | [], Return y when Var.compare x y = 0 ->
                              (* We do not need a continuation block for tail calls *)
                              p.blocks, None
                          | _ ->
                              ( Addr.Map.add
                                  p.free_pc
                                  { params = [ x ]; body = rem; branch }
                                  p.blocks
                              , Some p.free_pc )
                        in
                        let blocks = rewrite_closure blocks cont_pc (fst clos_cont) in
                        (* We do not really need this intermediate block.
                           It just avoids the need to find which function
                           parameters are used in the function body. *)
                        let blocks =
                          Addr.Map.add
                            (p.free_pc + 1)
                            { params; body = []; branch = Branch clos_cont }
                            blocks
                        in
                        let outer = { outer with size = outer.size + f_size } in
                        ( []
                        , ( outer
                          , Branch (p.free_pc + 1, args)
                          , { p with blocks; free_pc = p.free_pc + 2 } ) )
                  | _ -> i :: rem, state))
        | Let (x, Closure (l, (pc, []))) when not (Config.Flag.effects ()) -> (
            let block = Addr.Map.find pc p.blocks in
            match block with
            | { body = [ Let (y, Prim (Extern prim, args)) ]
              ; branch = Return y'
              ; params = []
              } ->
                let len = List.length l in
                if Code.Var.compare y y' = 0
                   && Primitive.has_arity prim len
                   && args_equal l args
                then Let (x, Prim (Extern "%closure", [ Pc (String prim) ])) :: rem, state
                else i :: rem, state
            | _ -> i :: rem, state)
        | _ -> i :: rem, state)
  in
  outer, { p with blocks = Addr.Map.add pc { block with body; branch } p.blocks }

(****)

let times = Debug.find "times"

let f p live_vars =
  Code.invariant p;
  let t = Timer.make () in
  let closures = get_closures p in
  let _closures, p =
    Code.fold_closures
      p
      (fun name _ (pc, _) (closures, p) ->
        let traverse outer =
          Code.traverse
            { fold = Code.fold_children }
            (inline live_vars closures name)
            pc
            p.blocks
            (outer, p)
        in
        match name with
        | None ->
            let _, p = traverse (optimizable p.blocks pc true) in
            closures, p
        | Some x ->
            let info = Var.Map.find x closures in
            let outer, p = traverse info.cl_prop in
            let closures = Var.Map.add x { info with cl_prop = outer } closures in
            closures, p)
      (closures, p)
  in
  if times () then Format.eprintf "  inlining: %a@." Timer.print t;
  Code.invariant p;
  p
