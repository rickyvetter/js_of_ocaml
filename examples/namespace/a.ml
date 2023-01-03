let () = print_endline "A"

exception Exn

let try_with f = try f () with Exn -> ()

let raise_ () = raise Exn

let () = Js_of_ocaml.Js.(export "tryWith" (wrap_callback try_with))

let () = Js_of_ocaml.Js.(export "raise" (wrap_callback raise_))
