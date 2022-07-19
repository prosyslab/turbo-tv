open Z3utils
module HeapNumber = Objects.HeapNumber

(* Number ::= TaggedSigned | HeapNumber | Int32 | Uint32 | Float64 *)

let is_number value mem =
  Bool.ite
    (value |> Value.has_type Type.int32)
    Bool.tr
    (Bool.ite
       (value |> Value.has_type Type.uint32)
       Bool.tr
       (Bool.ite
          (value |> Value.has_type Type.float64)
          Bool.tr
          (Bool.ite
             (value |> Value.has_type Type.tagged_signed)
             Bool.tr
             (Bool.ite
                (Bool.ands
                   [
                     value |> Value.has_type Type.tagged_pointer;
                     Objects.is_heap_number value mem;
                   ])
                Bool.tr Bool.fl))))

let are_numbers values mem =
  Bool.ands (values |> List.rev_map (fun value -> is_number value mem))

let to_float64 mem number =
  let heap_number = HeapNumber.load number mem in
  Bool.ite
    (number |> Value.has_type Type.int32)
    (number |> Value.Int32.to_float64)
    (Bool.ite
       (number |> Value.has_type Type.uint32)
       (number |> Value.Uint32.to_float64)
       (Bool.ite
          (number |> Value.has_type Type.float64)
          number
          (Bool.ite
             (number |> Value.has_type Type.tagged_signed)
             (number |> Value.TaggedSigned.to_float64)
             (heap_number |> HeapNumber.to_float64))))

let eq lnum rnum mem =
  let lnum_f64 = lnum |> to_float64 mem in
  let rnum_f64 = rnum |> to_float64 mem in
  (* https://tc39.es/ecma262/#sec-numeric-types-number-equal *)
  Bool.ite
    (* lnum = nan \/ rnum = nan -> false *)
    (Bool.ors [ Float64.is_nan lnum_f64; Float64.is_nan rnum_f64 ])
    Bool.fl
    (* lnum = rnum -> true *)
    (Bool.ite
       (Float64.eq lnum_f64 rnum_f64)
       Bool.tr
       (Bool.ite
          (* lnum = -0 /\ rnum = 0 -> true *)
          (Bool.ands
             [ Float64.is_minus_zero lnum_f64; Float64.is_zero rnum_f64 ])
          Bool.tr
          (* lnum = 0 /\ rnum = -0 -> true *)
          (Bool.ite
             (Bool.ands
                [ Float64.is_minus_zero rnum_f64; Float64.is_zero lnum ])
             Bool.tr Bool.fl)))
