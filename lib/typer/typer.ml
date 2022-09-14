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
            | Boundary.Int32Boundary (lb, ub) ->
                Bool.ands
                  [
                    Value.is_integer value;
                    Uint32.ge value (lb |> Value.from_int);
                    Uint32.le value (ub |> Value.from_int);
                  ]
            | FloatBoundary (lb, ub) ->
                let number = HeapNumber.load value mem in
                Bool.ands
                  [
                    value |> Objects.is_heap_number mem;
                    Float.gef (Float.from_ieee_bv number.value) lb;
                    Float.lef (Float.from_ieee_bv number.value) ub;
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

      (* if value is a integer; (assume there are only 32bit integer and 64bit integer) *)
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
