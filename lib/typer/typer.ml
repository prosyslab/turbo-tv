open Z3utils
open ValueOperator
module Boundary = Types.Boundary
module HeapNumber = Objects.HeapNumber

let rec verify (value : Value.t) (ty : Types.t) mem =
  match ty with
  | MinusZero | NaN | OtherUnsigned31 | OtherUnsigned32 | OtherSigned32
  | Negative31 | Unsigned30 | Signed31 | Signed32 | Signed32OrMinusZero
  | Signed32OrMinusZeroOrNaN | Negative32 | Unsigned31 | Unsigned32
  | Unsigned32OrMinusZero | Unsigned32OrMinusZeroOrNaN | Integral32
  | Integral32OrMinusZero | Integral32OrMinusZeroOrNaN | MinusZeroOrNaN
  | PlainNumber | OrderedNumber | Number ->
      (* if there exists a boundary B of the region R that satisfy T <= B, then T <= R *)
      let region = Types.decompose ty |> List.map Boundary.from_type in
      List.fold_left
        (fun verified boundary ->
          let in_bound =
            match boundary with
            | Boundary.IntBoundary (lb, ub) ->
                Bool.ite
                  (value |> Value.has_type Type.tagged_signed)
                  (TaggedSigned.is_in_range value lb ub)
                  (Bool.ite
                     (value |> Value.has_type Type.int32)
                     (Int32.is_in_range value lb ub)
                     (Bool.ite
                        (value |> Value.has_type Type.uint32)
                        (Uint32.is_in_range value lb ub)
                        (Bool.ite
                           (value |> Value.has_type Type.int64)
                           (Int64.is_in_range value lb ub)
                           (Bool.ite
                              (value |> Value.has_type Type.uint64)
                              (Uint64.is_in_range value lb ub)
                              (Bool.ite
                                 (Bool.ands
                                    [
                                      value |> Value.has_type Type.float64;
                                      Bool.not (value |> Float64.is_nan);
                                      Bool.not (value |> Float64.is_minus_zero);
                                      Bool.not (value |> Float64.is_inf);
                                      Bool.not (value |> Float64.is_ninf);
                                    ])
                                 (* don't use is_in_range. it'll make off-by-one error  *)
                                 (Bool.ands
                                    [
                                      Float64.ge value
                                        (Float64.of_float (lb |> float_of_int));
                                      Float64.le value
                                        (Float64.of_float
                                           (ub + 1 |> float_of_int));
                                    ])
                                 (Bool.ite
                                    (value |> Value.has_type Type.int8)
                                    (Int8.is_in_range value lb ub)
                                    (Bool.ite
                                       (value |> Value.has_type Type.uint8)
                                       (Uint8.is_in_range value lb ub)
                                       Bool.fl)))))))
            | FloatBoundary (lb, ub) ->
                if lb == nan && ub == nan then value |> Float64.is_nan
                else if lb == -0.0 && ub == -0.0 then
                  value |> Float64.is_minus_zero
                else Float64.is_in_range value lb ub
            | OtherBoundary ->
                Bool.ite
                  (value |> Value.has_type Type.int64)
                  (Bool.not
                     (Int64.is_in_range value
                        (-Utils.pow 2 31)
                        (Utils.pow 2 32 - 1)))
                  (Bool.ite
                     (value |> Value.has_type Type.uint64)
                     (Bool.not
                        (Uint64.is_in_range value
                           (-Utils.pow 2 31)
                           (Utils.pow 2 32 - 1)))
                     (Bool.ite
                        (value |> Value.has_type Type.float64)
                        (Bool.not
                           (Float64.is_in_range value
                              (-.Stdlib.Float.pow 2.0 31.0)
                              (Stdlib.Float.pow 2.0 32.0 -. 1.)))
                        Bool.fl))
          in
          Bool.ors [ verified; in_bound ])
        Bool.fl region
  (* T <= (T1 \/ ... \/ Tn)  if  (T <= T1) \/ ... \/ (T <= Tn) *)
  | Union fields ->
      Bool.ors (List.rev_map (fun field_ty -> verify value field_ty mem) fields)
  (* (T1, T2, ..., Tn) <= (T1', T2', ... Tn') if T1 <= T1' /\ T2 <= T2' /\ ... Tn <= Tn' *)
  | Tuple fields ->
      let size_of_composed = value |> Composed.size_of in
      let decomposed = value |> Composed.to_list in
      if size_of_composed = List.length fields then
        Bool.ands (List.rev_map2 (fun v f -> verify v f mem) decomposed fields)
      else
        failwith
          (Format.sprintf "is: wrong number of fields %s" (ty |> Types.to_string))
  | Range (lb, ub) ->
      let s_v =
        Bool.ite
          (value |> Value.has_type Type.int32)
          (value |> Int32.to_float64)
          (Bool.ite
             (value |> Value.has_type Type.int64)
             (value |> Int64.to_float64)
             (Bool.ite
                (value |> Value.has_type Type.uint32)
                (value |> Uint32.to_float64)
                (Bool.ite
                   (value |> Value.has_type Type.uint64)
                   (value |> Uint64.to_float64)
                   (Bool.ite
                      (value |> Value.has_type Type.tagged_signed)
                      (value |> TaggedSigned.to_float64)
                      (Bool.ite
                         (value |> Value.has_type Type.int8)
                         (value |> Int8.to_float64)
                         (Bool.ite
                            (value |> Value.has_type Type.uint8)
                            (value |> Uint8.to_float64)
                            (Bool.ite
                               (value |> Value.has_type Type.float64)
                               value
                               (Bool.ite
                                  (Bool.ands
                                     [
                                       value
                                       |> Value.has_type Type.tagged_pointer;
                                       value |> Objects.is_heap_number mem;
                                     ])
                                  (value |> Number.to_float64 mem)
                                  value))))))))
      in
      (* let u_v =
           Bool.ite
             (value |> Value.has_type Type.int32)
             (value |> Uint32.to_float64)
             (Bool.ite
                (value |> Value.has_type Type.int64)
                (value |> Uint64.to_float64)
                (Bool.ite
                   (value |> Value.has_type Type.uint32)
                   (value |> Int32.to_float64)
                   (Bool.ite
                      (value |> Value.has_type Type.uint64)
                      (value |> Int64.to_float64)
                      (Bool.ite
                         (value |> Value.has_type Type.tagged_signed)
                         (value |> TaggedSigned.to_float64)
                         (Bool.ite
                            (value |> Value.has_type Type.int8)
                            (value |> Uint8.to_float64)
                            (Bool.ite
                               (value |> Value.has_type Type.uint8)
                               (value |> Int8.to_float64)
                               (Bool.ite
                                  (value |> Value.has_type Type.float64)
                                  value
                                  (Bool.ite
                                     (Bool.ands
                                        [
                                          value
                                          |> Value.has_type Type.tagged_pointer;
                                          value |> Objects.is_heap_number mem;
                                        ])
                                     (value |> Number.to_float64 mem)
                                     value))))))))
         in *)
      Bool.ors [ Float64.is_in_range s_v lb ub ]
  (* for now, handle only numeric types *)
  | _ -> Bool.tr
