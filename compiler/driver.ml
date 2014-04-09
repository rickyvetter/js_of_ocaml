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

let debug = Option.Debug.find "main"
let times = Option.Debug.find "times"

open Util

let tailcall p =
  if debug () then Format.eprintf "Tail-call optimization...@.";
  Tailcall.f p

let deadcode' p =
  if debug () then Format.eprintf "Dead-code...@.";
  Deadcode.f p

let deadcode p =
  let r,_ = deadcode' p
  in r

let inline p =
  if Option.Optim.inline () && Option.Optim.deadcode ()
  then
    let (p,live_vars) = deadcode' p in
    if debug () then Format.eprintf "Inlining...@.";
    Inline.f p live_vars
  else p

let specialize_1 (p,info) =
  if debug () then Format.eprintf "Specialize...@.";
  Specialize.f info p

let specialize_js (p,info) =
  if debug () then Format.eprintf "Specialize js...@.";
  Specialize_js.f info p

let specialize' (p,info) =
  let p = specialize_1 (p,info)in
  let p = specialize_js (p,info) in
  p,info

let specialize p =
  fst (specialize' p)

let eval (p,info) =
  if Option.Optim.staticeval()
  then Eval.f info p
  else p

let flow p =
  if debug () then Format.eprintf "Data flow...@.";
  Flow.f p

let flow_simple p =
  if debug () then Format.eprintf "Data flow...@.";
  Flow.f ~skip_param:true p

let phi p =
  if debug () then Format.eprintf "Variable passing simplification...@.";
  Phisimpl.f p

let print p =
  if debug () then Code.print_program (fun _ _ -> "") p; p

let (>>>) x f = f x

let (>>) f g = fun x -> g (f x)

let rec loop max name round i (p : 'a) : 'a =
  let p' = round p in
  if i >= max || Code.eq p' p
  then p'
  else
    begin
      if times ()
      then Format.eprintf "Start Iteration (%s) %d...@." name i;
      loop max name round (i+1) p'
    end

let identity x = x

(* o1 *)

let o1 : 'a -> 'a=
  print >>
  tailcall >>
  flow_simple >> (* flow simple to keep information for furture tailcall opt *)
  specialize' >>
  eval >>
  inline >> (* inlining may reveal new tailcall opt *)
  deadcode >>
  tailcall >>
  phi >>
  flow >>
  specialize >>
  inline >>
  deadcode >>
  print >>
  flow >>
  specialize >>
  inline >>
  deadcode >>
  phi >>
  flow >>
  specialize >>
  identity

(* o2 *)

let o2 : 'a -> 'a =
  loop 10 "o1" o1 1 >>
  print

(* o3 *)

let round1 : 'a -> 'a =
  print >>
  tailcall >>
  inline >> (* inlining may reveal new tailcall opt *)
  deadcode >>
  (* deadcode required before flow simple -> provided by constant *)
  flow_simple >> (* flow simple to keep information for furture tailcall opt *)
  specialize' >>
  eval >>
  identity

let round2 =
  flow >>
  specialize' >>
  eval >>
  deadcode >>
  o1

let o3 =
  loop 10 "tailcall+inline" round1 1 >>
  loop 10 "flow" round2 1 >>
  print


let profile = ref o1

let generate (p,live_vars) =
  if times ()
  then Format.eprintf "Start Generation...@.";
  Generate.f p live_vars


let header formatter ~standalone js =
  if standalone then begin
    let version = match Compiler_version.git_version with
      | "" -> Compiler_version.s
      | v  -> Printf.sprintf "%s+git-%s"Compiler_version.s v in

    Pretty_print.string formatter
      ("// This program was compiled from OCaml by js_of_ocaml "
       ^ version);
    Pretty_print.newline formatter;
  end;
  js

let debug_linker = Option.Debug.find "linker"

let global_object = Option.global_object

let gen_missing js missing =
  if Option.Optim.genprim ()
  then begin
    let open Javascript in
    let miss = StringSet.fold (fun prim acc ->
        let p = S {name=prim;var=None} in
        (p,
         Some (
           ECond(EBin(NotEqEq,
                      EDot(EVar (S {name=global_object;var=None}),prim),
                      EVar(S {name="undefined";var=None})),
                 EDot(EVar (S {name=global_object;var=None}),prim),
                 EFun(None,[],[
                     Statement(
                       Expression_statement (
                         ECall(EVar (S {name="caml_failwith";var=None}),
                               [EBin(Plus,EStr(prim,`Utf8),EStr(" not implemented",`Utf8))]),
                         N))],N)
                ),
           N
         )) :: acc
      ) missing [] in
    if not (StringSet.is_empty missing)
    then begin
      Format.eprintf "There are some missing primitives@.";
      Format.eprintf "Dummy implementations (raising 'Failure' exception) ";
      Format.eprintf "will be used if they are not available at runtime.@.";
      Format.eprintf "You can prevent the generation of dummy implementations with ";
      Format.eprintf "the commandline option '-disable genprim'@.";
      Format.eprintf "Missing primitives:@.";
      StringSet.iter (fun nm -> Format.eprintf "  %s@." nm) missing
    end;
    Statement (Variable_statement miss) :: js
  end
  else
    js


let link formatter ~standalone ?linkall js =
  if standalone
  then
    begin
      let t = Util.Timer.make () in
      if times ()
      then Format.eprintf "Start Linking...@.";
      let traverse = new Js_traverse.free in
      let js = traverse#program js in
      let free = traverse#get_free_name in

      let prim = Primitive.get_external () in
      let prov = Linker.get_provided () in

      let all_external = StringSet.union prim prov in

      let used = StringSet.inter free all_external in
      let js,missing = Linker.resolve_deps ?linkall js used in
      let js = gen_missing js missing in
      if times () then Format.eprintf "  linking: %a@." Util.Timer.print t;
      js
    end
  else js


let check_js ~standalone js =
  if standalone
  then
    begin
      let t = Util.Timer.make () in
      if times ()
      then Format.eprintf "Start Checks...@.";

      let traverse = new Js_traverse.free in
      let js = traverse#program js in
      let free = traverse#get_free_name in

      let prim = Primitive.get_external () in
      let prov = Linker.get_provided () in

      let all_external = StringSet.union prim prov in

      let missing = StringSet.inter free all_external in

      let other =  StringSet.diff free missing in

      let res = VarPrinter.get_reserved() in
      let other = StringSet.diff other res in
      if not (StringSet.is_empty missing)
      then begin
        Format.eprintf "Missing primitives:@.";
        StringSet.iter (fun nm -> Format.eprintf "  %s@." nm) missing
      end;

      let probably_prov = StringSet.inter other Reserved.provided in
      let other = StringSet.diff other probably_prov in

      if not (StringSet.is_empty other) && debug_linker ()
      then
        begin
          Format.eprintf "Missing variables:@.";
          StringSet.iter (fun nm -> Format.eprintf "  %s@." nm) other
        end;

      if not (StringSet.is_empty probably_prov) && debug_linker ()
      then
        begin
          Format.eprintf "Variables provided by the browser:@.";
          StringSet.iter (fun nm -> Format.eprintf "  %s@." nm) probably_prov
        end;
      if times () then Format.eprintf "  checks: %a@." Util.Timer.print t;
      js
    end
  else js

let coloring js =
  let t = Util.Timer.make () in
  if times ()
  then Format.eprintf "Start Coloring...@.";
  let js = Js_assign.program js in
  if times () then Format.eprintf "  coloring: %a@." Util.Timer.print t;
  js

let output formatter ?source_map d js =
  let t = Util.Timer.make () in
  if times ()
  then Format.eprintf "Start Writing file...@.";
  Js_output.program formatter ?source_map d js;
  if times () then Format.eprintf "  write: %a@." Util.Timer.print t

let pack ~standalone ?(toplevel=false)?(linkall=false) js =
  let module J = Javascript in
  let t = Util.Timer.make () in
  if times ()
  then Format.eprintf "Start Optimizing js...@.";
  (* pre pack optim *)
  let js =
    if Option.Optim.share_constant ()
    then
      let t1 = Util.Timer.make () in
      let js = (new Js_traverse.share_constant)#program js in
      if times () then Format.eprintf "    share constant: %a@." Util.Timer.print t1;
      js
    else js in
  let js =
    if Option.Optim.compact_vardecl ()
    then
      let t2 = Util.Timer.make () in
      let js = (new Js_traverse.compact_vardecl)#program js in
      if times () then Format.eprintf "    compact var decl: %a@." Util.Timer.print t2;
      js
    else js in

  (* pack *)
  let use_strict js =
    if Option.Optim.strictmode ()
    then J.Statement (J.Expression_statement (J.EStr ("use strict", `Utf8), J.N)) :: js
    else js in

  let js = if standalone then
      let f =
        J.EFun (None, [J.S {J.name = global_object; var=None }], use_strict js,J.N) in
      [J.Statement (
        J.Expression_statement
          ((J.ECall (f, [J.EVar (J.S {J.name="this";var=None})])), J.N))]
    else
      let f = J.EFun (None, [J.V (Code.Var.fresh ())], js, J.N) in
      [J.Statement (J.Expression_statement (f, J.N))] in

  (* post pack optim *)
  let t3 = Util.Timer.make () in
  let js = (new Js_traverse.simpl)#program js in
  if times () then Format.eprintf "    simpl: %a@." Util.Timer.print t3;
  let t4 = Util.Timer.make () in
  let js = (new Js_traverse.clean)#program js in
  if times () then Format.eprintf "    clean: %a@." Util.Timer.print t4;
  let js =
    if (Option.Optim.shortvar ())
    then
      let t5 = Util.Timer.make () in
      let keeps =
        if toplevel
        then StringSet.add global_object (Primitive.get_external ())
        else StringSet.empty in
      let keeps = StringSet.add "caml_get_global_data" keeps in
      let js = (new Js_traverse.rename_variable keeps)#program js in
      if times () then Format.eprintf "    shortten vars: %a@." Util.Timer.print t5;
      js
    else js in
  if times () then Format.eprintf "  optimizing: %a@." Util.Timer.print t;
  js



let configure formatter p =
  let pretty = Option.Optim.pretty () in
  Pretty_print.set_compact formatter (not pretty);
  Code.Var.set_pretty pretty;
  p

let f ?(standalone=true) ?toplevel ?linkall ?source_map formatter d =
  configure formatter >>
  !profile >>
  deadcode' >>
  generate >>

  link formatter ~standalone ?linkall >>

  pack ~standalone ?linkall ?toplevel >>

  coloring >>

  check_js ~standalone >>
  header formatter ~standalone >>
  output formatter ?source_map d

let from_string prims s formatter =
  let (p,d) = Parse_bytecode.from_string prims s in
  f ~standalone:false formatter d p

let set_profile = function
  | 0 ->
    List.iter Option.Optim.enable ["pretty";"debuginfo"];
    List.iter Option.Optim.disable ["inline"];
    profile := o1
  | 1 -> profile := o1
  | 2 -> profile := o2
  | 3 -> profile := o3
  | _ -> ()
