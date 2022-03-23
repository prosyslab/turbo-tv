type e = string * string

exception TypeMismatch of e
exception InvalidFormat of e
exception NodeNotFound of e
exception IdNotFound of e
exception InvalidGraphLine of e
exception InvalidIndex of e
exception InvalidValue of e

let err excpt =
  (match excpt with
  | TypeMismatch (c, r) -> Printf.fprintf stderr "Type mismatch: %s\n%s\n\n" c r
  | InvalidFormat (c, r) ->
      Printf.fprintf stderr "Invalid Format: %s\n%s\n\n" c r
  | NodeNotFound (c, r) ->
      Printf.fprintf stderr "Node not found: %s\n%s\n\n" c r
  | IdNotFound (c, r) -> Printf.fprintf stderr "Id not found: %s\n%s\n\n" c r
  | InvalidGraphLine (c, r) ->
      Printf.fprintf stderr "Invalid graph line: %s\n%s\n\n" c r
  | InvalidIndex (c, r) -> Printf.fprintf stderr "Invalid index: %s\n%s\n\n" c r
  | InvalidValue (c, r) -> Printf.fprintf stderr "Invalid value: %s\n%s\n\n" c r
  | _ -> ());
  raise excpt
