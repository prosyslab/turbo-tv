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
  | Integral32OrMinusZero | Integral32OrMinusZeroOrNaN | MinusZeroOrNaN ->
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
                                      value |> Float64.is_integer;
                                    ])
                                 (Float64.is_in_range value (lb |> float_of_int)
                                    (ub |> float_of_int))
                                 (Bool.ite
                                    (value |> Value.has_type Type.int8)
                                    (Int8.is_in_range value lb ub)
                                    (Bool.ite
                                       (value |> Value.has_type Type.uint8)
                                       (Uint8.is_in_range value lb ub)
                                       Bool.fl)))))))
            | FloatBoundary (lb, ub) ->
                if ty = NaN then value |> Float64.is_nan
                else if ty = Types.MinusZero then value |> Float64.is_minus_zero
                else
                  let value_f = value |> Value.data_of |> Float.from_ieee_bv in
                  Bool.ands
                    [
                      value |> Value.is_float;
                      Float.gef value_f lb;
                      Float.lef value_f ub;
                    ]
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
      else failwith "is: wrong number of fields"
  | Range (lb, ub) ->
      let lb_f = lb |> Float64.from_numeral in
      let ub_f = ub |> Float64.from_numeral in

      (* if value is a integer *)
      let value_s =
        Bool.ite
          (value |> Value.is_32bit_integer)
          (value |> Int32.to_float64)
          (value |> Int64.to_float64)
      in
      let value_u =
        Bool.ite
          (value |> Value.is_32bit_integer)
          (value |> Uint32.to_float64)
          (value |> Uint64.to_float64)
      in

      let int_expr =
        Bool.ors
          [
            Bool.ands [ Float64.ge value_s lb_f; Float64.le value_s ub_f ];
            Bool.ands [ Float64.ge value_u lb_f; Float64.le value_u ub_f ];
          ]
      in

      (* otherwise, assume value is a number *)
      let num_f64 = value |> Number.to_float64 mem in
      let number_expr =
        Bool.ands
          [
            Float64.ge num_f64 (lb |> Float64.from_numeral);
            Float64.le num_f64 (ub |> Float64.from_numeral);
          ]
      in
      Bool.ite (value |> Value.is_integer) int_expr number_expr
  (* for now, handle only numeric types *)
  | _ -> Bool.tr
