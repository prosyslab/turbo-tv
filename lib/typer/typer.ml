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
      (* if value is int32 *)
      let is_int32 = Value.has_type Type.int32 value in
      let int32_lb = Stdlib.Float.to_int lb in
      let int32_ub = Stdlib.Float.to_int ub in
      let int32_expr =
        Bool.ands
          [
            Int32.gei value (min int32_lb int32_ub);
            Int32.lei value (max int32_lb int32_ub);
          ]
      in

      (* if value is uint32 *)
      let is_uint32 = Value.has_type Type.uint32 value in
      let uint32_lb =
        match Stdlib.Int32.of_float lb |> Stdlib.Int32.unsigned_to_int with
        | Some n -> n
        | None -> Stdlib.Float.to_int lb
      in
      let uint32_ub =
        match Stdlib.Int32.of_float ub |> Stdlib.Int32.unsigned_to_int with
        | Some n -> n
        | None -> Stdlib.Float.to_int ub
      in
      let uint32_expr =
        Bool.ands
          [
            Uint32.gei value (min uint32_lb uint32_ub);
            Uint32.lei value (max uint32_lb uint32_ub);
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
      Bool.ite is_int32 int32_expr (Bool.ite is_uint32 uint32_expr number_expr)
  (* for now, handle only numeric types *)
  | _ -> Bool.tr
