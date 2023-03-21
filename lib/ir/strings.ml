open Z3utils
open ValueOperator
module Objects = Memory.Objects

type t = { map : BitVec.t; value : Seq.t }

(* initialize *)
let create value = { map = Objmap.string_map; value }

let allocate t mem =
  let size = t.value |> Str.length |> Integer.to_bv |> Value.from_bv in
  let ptr, mem = Memory.allocate (BitVec.addi size Objmap.size) mem in
  let raw_ptr = ptr |> TaggedPointer.to_raw_pointer in
  let mem =
    mem
    |> Memory.Bytes.store Bool.tr raw_ptr Objmap.size Objmap.string_map
    |> Memory.Strings.store Bool.tr
         (TaggedPointer.movei raw_ptr Objmap.size)
         t.value
  in
  (ptr, mem)

let load ptr mem =
  let map =
    Memory.Bytes.load (ptr |> TaggedPointer.to_raw_pointer) Objmap.size mem
  in
  let value =
    Memory.Strings.load
      (TaggedPointer.movei ptr Objmap.size |> TaggedPointer.to_raw_pointer)
      mem
  in
  { map; value }

let from_char_bv c =
  let str = Str.from_char_bv c in
  create str

let from_string s =
  let str = s |> String.split_on_char ' ' |> List.tl |> List.hd in
  if String.equal "\"\"" str || String.equal "#" str then
    "" |> Str.from_string |> create
  else if String.starts_with ~prefix:"\"" str then
    let re = Re.Pcre.regexp "[^\\\"]+" in
    let value = Re.exec re str in
    Re.Group.get value 0 |> Str.from_string |> create
  else if String.starts_with ~prefix:"#" str then
    let re = Re.Pcre.regexp "[^#]+" in
    let value = Re.exec re str in
    Re.Group.get value 0 |> Str.from_string |> create
  else str |> Str.from_string |> create

let is_string ptr mem =
  ptr |> Objects.is_string mem |> Expr.simplify None |> B.is_true

let length t = t.value |> Str.length |> Integer.to_bv |> Value.from_bv

let equal lptr rptr mem =
  let lobj = load lptr mem in
  let robj = load rptr mem in
  Bool.ite (Bool.eq lobj.value robj.value) Value.tr Value.fl

let concat l r =
  let res = Str.concat [ l.value; r.value ] in
  create res

let nth t i = Str.nth t.value (i |> BitVec.to_uint)

let to_string model t = t.value |> Model.eval model |> Str.get_string
