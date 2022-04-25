open Z3utils
module Region = Types.Region
module Boundary = Region.Boundary

let rec verify (value : Value.t) (ty : Types.t) =
  match ty with
  | MinusZero | NaN | OtherUnsigned31 | OtherUnsigned32 | OtherSigned32
  | Negative31 | Unsigned30 | Signed31 | Signed32 | Signed32OrMinusZero
  | Signed32OrMinusZeroOrNaN | Negative32 | Unsigned31 | Unsigned32
  | Unsigned32OrMinusZero | Unsigned32OrMinusZeroOrNaN | Integral32
  | Integral32OrMinusZero | Integral32OrMinusZeroOrNaN | MinusZeroOrNaN ->
      let region = ty |> Types.decompose |> Region.from_types in
      List.fold_left
        (fun verified boundary ->
          let lb, ub = Boundary.int_range_of boundary in
          let in_bound =
            Bool.ands [ Value.sgei value lb; Value.slei value ub ]
          in
          Bool.ors [ verified; in_bound ])
        Bool.fl region
  (* T <= (T1 \/ ... \/ Tn)  if  (T <= T1) \/ ... \/ (T <= Tn) *)
  | Union fields ->
      Bool.ors (List.rev_map (fun field_ty -> verify value field_ty) fields)
  (* (T1, T2, ..., Tn) <= (T1', T2', ... Tn') if T1 <= T1' /\ T2 <= T2' /\ ... Tn <= Tn' *)
  | Tuple fields ->
      let size_of_composed = value |> Value.Composed.size_of in
      let decomposed = value |> Value.Composed.to_list in
      if size_of_composed = List.length fields then
        Bool.ands (List.rev_map2 (fun v f -> verify v f) decomposed fields)
      else failwith "is: wrong number of fields"
  (* for now, handle only numeric types *)
  | Range (_lb, _ub) -> failwith "not implemented"
  | _ -> Bool.tr
