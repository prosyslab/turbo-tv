open Z3utils
open ValueOperator

type t = { map : BitVec.t; value : BitVec.t }

let length t = BitVec.length_of t.value

(* initialize *)
let create value = { map = Objmap.string_map; value }

let allocate t mem =
  let size = length t / 8 in
  let ptr, mem = Memory.allocate (Value.from_int (Objmap.size + size)) mem in
  let string_value = t.value in
  let raw_ptr = ptr |> TaggedPointer.to_raw_pointer in
  let mem =
    mem
    |> Memory.store Bool.tr raw_ptr Objmap.size Objmap.string_map
    |> Memory.store Bool.tr
         (TaggedPointer.movei raw_ptr Objmap.size)
         size string_value
  in
  (ptr, mem)

let load ptr mem =
  let map = Memory.load (ptr |> TaggedPointer.to_raw_pointer) Objmap.size mem in
  let len = Memory.size_of (TaggedPointer.bid_of ptr) mem in
  let value =
    Memory.load
      (TaggedPointer.movei ptr Objmap.size |> TaggedPointer.to_raw_pointer)
      ((len |> BitVec.to_sint |> Expr.to_simplified_string |> int_of_string)
      - Objmap.size)
      mem
  in
  { map; value }

let from_string s =
  let values = s |> String.split_on_char ' ' |> List.tl |> List.hd in
  if String.equal "\"\"" values then "" |> BitVecVal.from_string |> create
  else if String.starts_with ~prefix:"\"" values then
    let re = Re.Pcre.regexp "[^\\\"]+" in
    let value_o = Re.exec re values in
    Re.Group.get value_o 0 |> BitVecVal.from_string |> create
  else if String.equal "#" values then "" |> BitVecVal.from_string |> create
  else if String.starts_with ~prefix:"#" values then
    let re = Re.Pcre.regexp "([^#]+)" in
    let value_o = Re.exec re values in
    Re.Group.get value_o 0 |> BitVecVal.from_string |> create
  else values |> BitVecVal.from_string |> create

let get_length t = t.value |> BitVec.length_of |> Int32.of_int

let concat _ l r =
  let res = BitVec.concat l.value r.value in
  create res

let to_string model t =
  let bv = t.value |> Model.eval model in
  let len = BitVec.length_of bv in
  let rec ext i str =
    if i < 7 then str
    else
      ext (i - 8)
        (bv
        |> BitVec.extract i (i - 7)
        |> BitVec.to_sint |> Expr.to_simplified_string |> int_of_string
        |> Char.chr |> String.make 1 |> String.cat str)
  in
  ext (len - 1) ""

let to_bytestring model t =
  let map_bs = t.map |> Model.eval model |> Expr.to_string in
  let value_bs = t.value |> Model.eval model |> Expr.to_string in
  String.concat " " [ map_bs; value_bs ]
