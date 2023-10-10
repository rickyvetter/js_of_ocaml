(* Js_of_ocaml compiler
 * http://www.ocsigen.org/js_of_ocaml/
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

open! Js_of_ocaml_compiler.Stdlib
open Js_of_ocaml_compiler

let times = Debug.find "times"

let debug_mem = Debug.find "mem"

let () = Sys.catch_break true

let gen_unit_filename dir u =
  Filename.concat dir (Printf.sprintf "%s.js" (Ocaml_compiler.Cmo_format.name u))

let header formatter ~custom_header =
  match custom_header with
  | None -> ()
  | Some c -> Pretty_print.string formatter (c ^ "\n")

let jsoo_header formatter build_info =
  Pretty_print.string formatter "// Generated by js_of_ocaml\n";
  Pretty_print.string formatter (Build_info.to_string build_info)

let output_gen ~standalone ~custom_header ~build_info ~source_map output_file f =
  let f chan k =
    let fmt = Pretty_print.to_out_channel chan in
    Driver.configure fmt;
    if standalone then header ~custom_header fmt;
    if Config.Flag.header () then jsoo_header fmt build_info;
    let sm = f ~standalone ~source_map:(Option.map ~f:snd source_map) (k, fmt) in
    match source_map, sm with
    | None, _ | _, None -> ()
    | Some (output_file, _), Some sm ->
        let urlData =
          match output_file with
          | None ->
              let data = Source_map_io.to_string sm in
              "data:application/json;base64," ^ Base64.encode_exn data
          | Some output_file ->
              Source_map_io.to_file sm output_file;
              Filename.basename output_file
        in
        Pretty_print.newline fmt;
        Pretty_print.string fmt (Printf.sprintf "//# sourceMappingURL=%s\n" urlData)
  in

  match output_file with
  | `Stdout -> f stdout `Stdout
  | `Name name -> Filename.gen_file name (fun chan -> f chan `File)

let run
    { Cmd_arg.common
    ; profile
    ; source_map
    ; runtime_files
    ; no_runtime
    ; input_file
    ; output_file
    ; params
    ; static_env
    ; wrap_with_fun
    ; dynlink
    ; linkall
    ; target_env
    ; toplevel
    ; no_cmis
    ; runtime_only
    ; include_dirs
    ; fs_files
    ; fs_output
    ; fs_external
    ; export_file
    ; keep_unit_names
    } =
  let include_cmis = toplevel && not no_cmis in
  let custom_header = common.Jsoo_cmdline.Arg.custom_header in
  Jsoo_cmdline.Arg.eval common;
  (match output_file with
  | `Stdout, _ -> ()
  | `Name name, _ when debug_mem () -> Debug.start_profiling name
  | `Name _, _ -> ());
  List.iter params ~f:(fun (s, v) -> Config.Param.set s v);
  List.iter static_env ~f:(fun (s, v) -> Eval.set_static_env s v);
  let t = Timer.make () in
  let include_dirs =
    List.filter_map (include_dirs @ [ "+stdlib/" ]) ~f:(fun d -> Findlib.find [] d)
  in
  let exported_unit =
    match export_file with
    | None -> None
    | Some file ->
        if not (Sys.file_exists file)
        then failwith (Printf.sprintf "export file %S does not exists" file);
        let ic = open_in file in
        let t = Hashtbl.create 17 in
        (try
           while true do
             Hashtbl.add t (input_line ic) ()
           done;
           assert false
         with End_of_file -> ());
        close_in ic;
        Some (Hashtbl.fold (fun cmi () acc -> cmi :: acc) t [])
  in
  let runtime_files =
    if (not no_runtime) && (toplevel || dynlink)
    then
      let add_if_absent x l = if List.mem x ~set:l then l else x :: l in
      runtime_files |> add_if_absent "+toplevel.js" |> add_if_absent "+dynlink.js"
    else runtime_files
  in
  let runtime_files, builtin =
    List.partition_map runtime_files ~f:(fun name ->
        match Builtins.find name with
        | Some t -> `Snd t
        | None -> `Fst name)
  in
  let t1 = Timer.make () in
  let builtin =
    if no_runtime then builtin else Js_of_ocaml_compiler_runtime_files.runtime @ builtin
  in
  List.iter builtin ~f:(fun t ->
      let filename = Builtins.File.name t in
      let runtimes = Linker.Fragment.parse_builtin t in
      Linker.load_fragments ~target_env ~filename runtimes);
  Linker.load_files ~target_env runtime_files;
  Linker.check_deps ();
  if times () then Format.eprintf "  parsing js: %a@." Timer.print t1;
  if times () then Format.eprintf "Start parsing...@.";
  let need_debug = Option.is_some source_map || Config.Flag.debuginfo () in
  let check_debug (one : Parse_bytecode.one) =
    if (not runtime_only)
       && Option.is_some source_map
       && Parse_bytecode.Debug.is_empty one.debug
       && not (Code.is_empty one.code)
    then
      warn
        "Warning: '--source-map' is enabled but the bytecode program was compiled with \
         no debugging information.\n\
         Warning: Consider passing '-g' option to ocamlc.\n\
         %!"
  in
  let pseudo_fs_instr prim debug cmis =
    let paths =
      include_dirs @ StringSet.elements (Parse_bytecode.Debug.paths debug ~units:cmis)
    in
    Pseudo_fs.f ~prim ~cmis ~files:fs_files ~paths
  in
  let env_instr () =
    List.concat_map static_env ~f:(fun (k, v) ->
        Primitive.add_external "caml_set_static_env";
        let var_k = Code.Var.fresh () in
        let var_v = Code.Var.fresh () in
        Code.
          [ Let (var_k, Prim (Extern "caml_jsstring_of_string", [ Pc (String k) ])), noloc
          ; Let (var_v, Prim (Extern "caml_jsstring_of_string", [ Pc (String v) ])), noloc
          ; ( Let
                (Var.fresh (), Prim (Extern "caml_set_static_env", [ Pv var_k; Pv var_v ]))
            , noloc )
          ])
  in
  let output (one : Parse_bytecode.one) ~standalone ~source_map ~linkall output_file =
    check_debug one;
    let init_pseudo_fs = fs_external && standalone in
    let sm =
      match output_file with
      | `Stdout, fmt ->
          let instr =
            List.concat
              [ pseudo_fs_instr `create_file one.debug one.cmis
              ; (if init_pseudo_fs then [ Pseudo_fs.init () ] else [])
              ; env_instr ()
              ]
          in
          let code = Code.prepend one.code instr in
          Driver.f
            ~standalone
            ?profile
            ~linkall
            ~wrap_with_fun
            ?source_map
            fmt
            one.debug
            code
      | `File, fmt ->
          let fs_instr1, fs_instr2 =
            match fs_output with
            | None -> pseudo_fs_instr `create_file one.debug one.cmis, []
            | Some _ -> [], pseudo_fs_instr `create_file_extern one.debug one.cmis
          in
          let instr =
            List.concat
              [ fs_instr1
              ; (if init_pseudo_fs then [ Pseudo_fs.init () ] else [])
              ; env_instr ()
              ]
          in
          let code = Code.prepend one.code instr in
          let res =
            Driver.f
              ~standalone
              ?profile
              ~linkall
              ~wrap_with_fun
              ?source_map
              fmt
              one.debug
              code
          in
          Option.iter fs_output ~f:(fun file ->
              Filename.gen_file file (fun chan ->
                  let instr = fs_instr2 in
                  let code = Code.prepend Code.empty instr in
                  let pfs_fmt = Pretty_print.to_out_channel chan in
                  Driver.f' ~standalone ?profile ~wrap_with_fun pfs_fmt one.debug code));
          res
    in
    if times () then Format.eprintf "compilation: %a@." Timer.print t;
    sm
  in
  let output_partial
      (cmo : Cmo_format.compilation_unit)
      ~standalone
      ~source_map
      code
      ((_, fmt) as output_file) =
    assert (not standalone);
    let uinfo = Unit_info.of_cmo cmo in
    Pretty_print.string fmt "\n";
    Pretty_print.string fmt (Unit_info.to_string uinfo);
    output code ~source_map ~standalone ~linkall:false output_file
  in
  let output_runtime ~standalone ~source_map ((_, fmt) as output_file) =
    assert (not standalone);
    let uinfo = Unit_info.of_primitives [] in
    Pretty_print.string fmt "\n";
    Pretty_print.string fmt (Unit_info.to_string uinfo);
    let code =
      { Parse_bytecode.code = Code.empty
      ; cmis = StringSet.empty
      ; debug = Parse_bytecode.Debug.create ~include_cmis:false false
      }
    in
    output code ~source_map ~standalone ~linkall:true output_file
  in
  (if runtime_only
   then (
     let prims = Primitive.get_external () |> StringSet.elements in
     assert (List.length prims > 0);
     let code, uinfo = Parse_bytecode.predefined_exceptions () in
     let uinfo = { uinfo with primitives = uinfo.primitives @ prims } in
     let code : Parse_bytecode.one =
       { code
       ; cmis = StringSet.empty
       ; debug = Parse_bytecode.Debug.create ~include_cmis:false false
       }
     in
     output_gen
       ~standalone:true
       ~custom_header
       ~build_info:(Build_info.create `Runtime)
       ~source_map
       (fst output_file)
       (fun ~standalone ~source_map ((_, fmt) as output_file) ->
         Pretty_print.string fmt "\n";
         Pretty_print.string fmt (Unit_info.to_string uinfo);
         output code ~source_map ~standalone ~linkall:true output_file))
   else
     let kind, ic, close_ic, include_dirs =
       match input_file with
       | None -> Parse_bytecode.from_channel stdin, stdin, (fun () -> ()), include_dirs
       | Some fn ->
           let ch = open_in_bin fn in
           let res = Parse_bytecode.from_channel ch in
           let include_dirs = Filename.dirname fn :: include_dirs in
           res, ch, (fun () -> close_in ch), include_dirs
     in
     (match kind with
     | `Exe ->
         let t1 = Timer.make () in
         (* The OCaml compiler can generate code using the
            "caml_string_greaterthan" primitive but does not use it
            itself. This is (was at some point at least) the only primitive
            in this case.  Ideally, Js_of_ocaml should parse the .mli files
            for primitives as well as marking this primitive as potentially
            used. But the -linkall option is probably good enough. *)
         let linkall = linkall || toplevel || dynlink in
         let code =
           Parse_bytecode.from_exe
             ~includes:include_dirs
             ~include_cmis
             ~link_info:(toplevel || dynlink)
             ~linkall
             ?exported_unit
             ~debug:need_debug
             ic
         in
         if times () then Format.eprintf "  parsing: %a@." Timer.print t1;
         output_gen
           ~standalone:true
           ~custom_header
           ~build_info:(Build_info.create `Exe)
           ~source_map
           (fst output_file)
           (output code ~linkall)
     | `Cmo cmo ->
         let output_file =
           match output_file, keep_unit_names with
           | (`Stdout, false), true -> `Name (gen_unit_filename "./" cmo)
           | (`Name x, false), true -> `Name (gen_unit_filename (Filename.dirname x) cmo)
           | (`Stdout, _), false -> `Stdout
           | (`Name x, _), false -> `Name x
           | (`Name x, true), true
             when String.length x > 0 && Char.equal x.[String.length x - 1] '/' ->
               `Name (gen_unit_filename x cmo)
           | (`Name _, true), true | (`Stdout, true), true ->
               failwith "use [-o dirname/] or remove [--keep-unit-names]"
         in
         let t1 = Timer.make () in
         let code =
           Parse_bytecode.from_cmo
             ~includes:include_dirs
             ~include_cmis
             ~debug:need_debug
             cmo
             ic
         in
         let linkall = linkall || toplevel || dynlink in
         if times () then Format.eprintf "  parsing: %a@." Timer.print t1;
         output_gen
           ~standalone:false
           ~custom_header
           ~build_info:(Build_info.create `Cmo)
           ~source_map
           output_file
           (fun ~standalone ~source_map output ->
             let source_map =
               if linkall
               then output_runtime ~standalone ~source_map output
               else source_map
             in
             output_partial cmo code ~standalone ~source_map output)
     | `Cma cma when keep_unit_names ->
         List.iter cma.lib_units ~f:(fun cmo ->
             let output_file =
               match output_file with
               | `Stdout, false -> gen_unit_filename "./" cmo
               | `Name x, false -> gen_unit_filename (Filename.dirname x) cmo
               | `Name x, true
                 when String.length x > 0 && Char.equal x.[String.length x - 1] '/' ->
                   gen_unit_filename x cmo
               | `Stdout, true | `Name _, true ->
                   failwith "use [-o dirname/] or remove [--keep-unit-names]"
             in
             let t1 = Timer.make () in
             let code =
               Parse_bytecode.from_cmo
                 ~includes:include_dirs
                 ~include_cmis
                 ~debug:need_debug
                 cmo
                 ic
             in
             if times ()
             then
               Format.eprintf
                 "  parsing: %a (%s)@."
                 Timer.print
                 t1
                 (Ocaml_compiler.Cmo_format.name cmo);
             output_gen
               ~standalone:false
               ~custom_header
               ~build_info:(Build_info.create `Cma)
               ~source_map
               (`Name output_file)
               (output_partial cmo code))
     | `Cma cma ->
         let linkall = linkall || toplevel || dynlink in
         let f ~standalone ~source_map output =
           let source_map =
             if linkall then output_runtime ~standalone ~source_map output else source_map
           in
           List.fold_left cma.lib_units ~init:source_map ~f:(fun source_map cmo ->
               let t1 = Timer.make () in
               let code =
                 Parse_bytecode.from_cmo
                   ~includes:include_dirs
                   ~include_cmis
                   ~debug:need_debug
                   cmo
                   ic
               in
               if times ()
               then
                 Format.eprintf
                   "  parsing: %a (%s)@."
                   Timer.print
                   t1
                   (Ocaml_compiler.Cmo_format.name cmo);
               output_partial cmo ~standalone ~source_map code output)
         in
         output_gen
           ~standalone:false
           ~custom_header
           ~build_info:(Build_info.create `Cma)
           ~source_map
           (fst output_file)
           f);
     close_ic ());
  Debug.stop_profiling ()

let info name =
  Info.make
    ~name
    ~doc:"Js_of_ocaml compiler"
    ~description:
      "Js_of_ocaml is a compiler from OCaml bytecode to Javascript. It makes it possible \
       to run pure OCaml programs in JavaScript environments like web browsers and \
       Node.js."

let term = Cmdliner.Term.(const run $ Cmd_arg.options)

let command =
  let t = Cmdliner.Term.(const run $ Cmd_arg.options) in
  Cmdliner.Cmd.v (info "compile") t
