module Operand = Operands.Operand

exception Invalid_instruction of string * string

type t = Types.t option * Opcode.t * Operands.t

let create ty opcode operands : t = (ty, opcode, operands)

let empty : t = (None, Opcode.empty, [])

(* getter *)
let ty_of (ty, _, _) : Types.t option = ty

let opcode (_, opcode, _) : Opcode.t = opcode

let operands (_, _, operands) : Operands.t = operands

let err instr reason =
  Printf.fprintf stderr "Invalid Instruction: %s\n%s\n\n" instr reason;
  raise (Invalid_instruction (instr, reason))

let create_from instr =
  let parse_opcode instr =
    let opcode_reg = Re.Pcre.regexp "#[a-zA-Z0-9]+:([a-zA-Z0-9]+)" in
    let opcode_str =
      try Re.Group.get (Re.exec opcode_reg instr) 1
      with Not_found ->
        let reason = "Cannot match 'opcode' from the instruction." in
        err instr reason
    in

    try opcode_str |> Opcode.of_str
    with Opcode.Invalid_opcode ->
      let reason = "Unknown opcode: " ^ opcode_str in
      err instr reason
  in

  let parse_operands kind instr =
    let rec parse_operand (kinds : Opcode.kind list) instr operands =
      let b1_re = Re.Pcre.regexp "(?:\\[([^,]*)[^\\]]*\\])\\([^\\)]*\\)" in
      let b2_re =
        Re.Pcre.regexp "(?:\\[[^,]*, ([^,]*)[^\\]]*\\])\\([^\\)]*\\)"
      in
      let b4_re =
        Re.Pcre.regexp
          "(?:\\[[^,]*, [^,]*, [^,]*, ([^,]*)[^\\]]*\\])\\([^\\)]*\\)"
      in
      let p1_re = Re.Pcre.regexp "(?:\\[[^\\]]*\\]){0,1}\\(#(\\d*)[^\\)]*\\)" in
      let p2_re =
        Re.Pcre.regexp "(?:\\[[^\\]]*\\]){0,1}\\([^,]*, #(\\d*)[^\\)]*\\)"
      in
      let p3_re =
        Re.Pcre.regexp
          "(?:\\[[^\\]]*\\]){0,1}\\([^,]*, [^,]*, #(\\d*)[^\\)]*\\)"
      in

      let vargs_re = Re.Pcre.regexp "(?:\\[[^\\]]*\\]){0,1}\\((.*)[^\\)]*\\)" in
      match kinds with
      | k :: t -> (
          try
            match k with
            | B1 ->
                let b1 =
                  Re.Group.get (Re.exec b1_re instr) 1 |> Operand.of_const
                in
                parse_operand t instr (b1 :: operands)
            | B2 ->
                let b2 =
                  Re.Group.get (Re.exec b2_re instr) 1 |> Operand.of_const
                in
                parse_operand t instr (b2 :: operands)
            | B4 ->
                let b4 =
                  Re.Group.get (Re.exec b4_re instr) 1 |> Operand.of_const
                in
                parse_operand t instr (b4 :: operands)
            | P1 ->
                let p1 =
                  Re.Group.get (Re.exec p1_re instr) 1 |> Operand.of_id
                in
                parse_operand t instr (p1 :: operands)
            | P2 ->
                let p2 =
                  Re.Group.get (Re.exec p2_re instr) 1 |> Operand.of_id
                in
                parse_operand t instr (p2 :: operands)
            | P3 ->
                let p3 =
                  Re.Group.get (Re.exec p3_re instr) 1 |> Operand.of_id
                in
                parse_operand t instr (p3 :: operands)
            | VARGS ->
                let vargs =
                  Re.Group.get (Re.exec vargs_re instr) 1
                  |> String.split_on_char ','
                in
                List.fold_left
                  (fun res arg ->
                    let re = Re.Pcre.regexp "#(\\d*)" in
                    (Re.Group.get (Re.exec re arg) 1 |> Operand.of_id) :: res)
                  [] vargs
            | UNIMPL -> []
            | _ -> failwith "Unreachable"
          with Not_found ->
            let reason = "Cannot parse operands" in
            err instr reason)
      | [] -> List.rev operands
    in

    let kinds = Opcode.split_kind kind in
    [] |> parse_operand kinds instr
  in

  let ty_str_of instr =
    let type_reg = Re.Pcre.regexp "\\[Type: ([^\\]]*)\\]" in
    try Some (Re.Group.get (Re.exec type_reg instr) 1) with Not_found -> None
  in

  let rec parse_type ty_str : Types.t =
    let is_union ty_str = String.starts_with ~prefix:"Union" ty_str in
    let is_range ty_str = String.starts_with ~prefix:"Range" ty_str in
    let is_tuple ty_str = String.starts_with ~prefix:"<" ty_str in
    let is_heap_constant ty_str =
      String.starts_with ~prefix:"HeapConstant" ty_str
    in
    let is_other_number_constant ty_str =
      String.starts_with ~prefix:"OtherNumberConstant" ty_str
    in

    let parse_structural kind s_ty_str =
      let tys_reg = Re.Pcre.regexp "Union\\(([^\\)]*)\\)" in
      let elems_ty_str =
        try
          Re.Group.get (Re.exec tys_reg s_ty_str) 1 |> String.split_on_char ','
        with Not_found ->
          let reason = "Cannot parse '" ^ kind ^ "' from the " ^ s_ty_str in
          err instr reason
      in
      let elems_ty = List.map parse_type elems_ty_str in

      match kind with
      | "Union" -> Types.Union elems_ty
      | "Tuple" -> Tuple elems_ty
      | _ -> failwith "Unreachable"
    in

    let parse_constant kind c_ty_str =
      let value_reg = Re.Pcre.regexp (kind ^ "\\((0x[0-9a-f]*).*") in
      let value_str =
        try Re.Group.get (Re.exec value_reg c_ty_str) 1
        with Not_found ->
          let reason = "Cannot parse '" ^ kind ^ "' from the " ^ c_ty_str in
          err instr reason
      in
      let value = value_str |> int_of_string in
      match kind with
      | "HeapConstant" -> Types.HeapConstant value
      | "OtherNumberConstant" -> OtherNumberConstant value
      | _ -> failwith "Unreachable"
    in

    let parse_range range_ty_str =
      let limits_reg =
        Re.Pcre.regexp "Range\\((-?[\\.0-9]*),\\s*(-?[\\.0-9]*)\\)"
      in
      let limits =
        try
          let lb =
            Re.Group.get (Re.exec limits_reg range_ty_str) 1 |> float_of_string
          in
          let ub =
            Re.Group.get (Re.exec limits_reg range_ty_str) 2 |> float_of_string
          in
          (lb, ub)
        with Not_found ->
          let reason = "Cannot parse 'Range' from the " ^ range_ty_str in
          err instr reason
      in
      Types.Range limits
    in

    if ty_str |> is_union then parse_structural "Union" ty_str
    else if ty_str |> is_tuple then parse_structural "Tuple" ty_str
    else if ty_str |> is_range then parse_range ty_str
    else if ty_str |> is_heap_constant then parse_constant "HeapConstant" ty_str
    else if ty_str |> is_other_number_constant then
      parse_constant "OtherNumberConstant" ty_str
    else ty_str |> Types.of_string
  in

  let opcode = parse_opcode instr in
  let kind = opcode |> Opcode.get_kind in
  let operands = parse_operands kind instr in
  let ty =
    match ty_str_of instr with
    | Some ty_str -> Some (parse_type ty_str)
    | None -> None
  in

  create ty opcode operands
