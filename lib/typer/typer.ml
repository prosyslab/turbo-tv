open Z3utils
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
                    Value.ugei ~width:32 value lb;
                    Value.ulei ~width:32 value ub;
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
      let size_of_composed = value |> Value.Composed.size_of in
      let decomposed = value |> Value.Composed.to_list in
      if size_of_composed = List.length fields then
        Bool.ands (List.rev_map2 (fun v f -> verify v f mem) decomposed fields)
      else failwith "is: wrong number of fields"
  | Range (lb, ub) ->
      (* assume value is a number *)
      let num_f64 = value |> Number.to_float64 mem in
      Bool.ands
        [
          Float64.ge num_f64 (lb |> Float.from_float |> Float64.from_float);
          Float64.le num_f64 (ub |> Float.from_float |> Float64.from_float);
        ]
  (* for now, handle only numeric types *)
  | _ -> Bool.tr
