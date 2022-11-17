open Z3utils
open ValueOperator

type t = BitVec.t

let char_len = 8

let char_size = char_len / 8

let length t = BitVec.length_of t

let size t = length t / 8

let ordi c = Char.code c |> BitVecVal.from_int ~len:char_len

let from_string s =
  let len = String.length s in
  (* bulk initialization may optimize the performance*)
  s
  |> String.fold_left
       (fun acc c -> BitVec.concat (ordi c) acc)
       (BitVecVal.zero ~len:char_len ())
  (* truncate the trailing zero byte *)
  |> BitVec.extract ((len * char_len) + 7) 8

let promote mem t =
  let ptr, mem =
    Memory.allocate ~angelic:Bool.tr (Value.from_int (length t)) mem
  in
  ( ptr,
    mem
    |> Memory.store Bool.tr
         (ptr |> TaggedPointer.to_raw_pointer)
         Objmap.size Objmap.string_map
    |> Memory.store Bool.tr
         (TaggedPointer.movei ptr Objmap.size |> TaggedPointer.to_raw_pointer)
         (size t) t )
