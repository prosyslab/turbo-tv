open Z3utils
open ValueOperator
module Objects = Memory.Objects

type t = { map : BitVec.t; value : Seq.t }

let length t = BitVec.length_of t.value

(* initialize *)
let create value = { map = Objmap.string_map; value }

let allocate t mem =
  print_endline "In Strings.alllocate";
  let size = t.value |> Seq.length_of |> Integer.to_bv |> Value.from_bv in
  let ptr, mem = Memory.allocate (BitVec.andi size 4) mem in
  let raw_ptr = ptr |> TaggedPointer.to_raw_pointer in
  let mem =
    mem
    |> Memory.store Bool.tr raw_ptr Objmap.size Objmap.string_map
    |> Memory.store Bool.tr (TaggedPointer.movei raw_ptr Objmap.size) 0 t.value
  in
  print_endline (t.value |> Expr.to_simplified_string);
  (ptr, mem)

let load ptr mem =
  print_endline "In Strings.load";
  print_endline "In Strings.load - load map";
  let map = Memory.load (ptr |> TaggedPointer.to_raw_pointer) Objmap.size mem in
  print_endline "In Strings.load - load value";
  let value =
    Memory.load
      (TaggedPointer.movei ptr Objmap.size |> TaggedPointer.to_raw_pointer)
      0 mem
  in
  print_endline (value |> Expr.to_simplified_string);
  { map; value }

let from_string s =
  print_endline "In Strings.from_string";
  let values = s |> String.split_on_char ' ' |> List.tl |> List.hd in
  if String.equal "\"\"" values then "" |> Seq.from_string |> create
  else if String.starts_with ~prefix:"\"" values then (
    let re = Re.Pcre.regexp "[^\\\"]+" in
    let value_o = Re.exec re values in
    print_endline
      (Re.Group.get value_o 0 |> Seq.from_string |> Seq.length_of
     |> Expr.to_simplified_string);
    print_endline (Re.Group.get value_o 0);
    Re.Group.get value_o 0 |> Seq.from_string |> create)
  else if String.equal "#" values then "" |> Seq.from_string |> create
  else if String.starts_with ~prefix:"#" values then
    let re = Re.Pcre.regexp "([^#]+)" in
    let value_o = Re.exec re values in
    Re.Group.get value_o 0 |> Seq.from_string |> create
  else values |> Seq.from_string |> create

let is_string ptr mem =
  print_endline "In Stirngs.is_string";
  print_endline (ptr |> Expr.to_simplified_string);
  ptr |> Objects.is_string mem |> Expr.simplify None |> B.is_true

let get_length t =
  print_endline "In Strings.get_length";
  print_endline (t.value |> Expr.get_sort |> Z3.Sort.to_string);
  print_endline (t.value |> Expr.to_simplified_string);
  t.value |> Seq.length_of |> Integer.to_bv |> Value.from_bv

let equal lptr rptr mem =
  let lobj = load lptr mem in
  let robj = load rptr mem in
  if
    Seq.le lobj.value robj.value |> Expr.simplify None |> B.is_true
    && Seq.lt lobj.value robj.value |> Expr.simplify None |> B.is_true = false
  then Value.tr
  else Value.fl

let concat _ l r =
  let res = Seq.concat [ l.value; r.value ] in
  create res

let to_string model t =
  print_endline "In Strings.to_string";
  print_endline (t.value |> Model.eval model |> Expr.to_simplified_string);
  (* print_endline (t.value |> Model.eval model |> Seq.get_string); *)
  (* t.value |> Model.eval model |> Seq.get_string *)
  t.value |> Model.eval model |> Expr.to_simplified_string

let to_bytestring model t =
  let map_bs = t.map |> Model.eval model |> Expr.to_string in
  let value_bs = t.value |> Model.eval model |> Expr.to_string in
  String.concat " " [ map_bs; value_bs ]
