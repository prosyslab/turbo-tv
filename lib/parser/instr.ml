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
      let c1_re =
        Re.Pcre.regexp
          "(?:\\[[^\\]]*\\]){0,1}\\([^\\)]*\\)\\([^\\)]*\\)\\(#(\\d*)[^\\)]*\\)"
      in
      let cv_re = Re.Pcre.regexp "(?:\\[[^\\]]*\\]){0,1}\\((.*)[^\\)]*\\)" in

      let e1_re =
        Re.Pcre.regexp "(?:\\[[^\\]]*\\]){0,1}\\([^\\)]*\\)\\(#(\\d*)[^\\)]*\\)"
      in

      let v1_re = Re.Pcre.regexp "(?:\\[[^\\]]*\\]){0,1}\\(#(\\d*)[^\\)]*\\)" in
      let v2_re =
        Re.Pcre.regexp "(?:\\[[^\\]]*\\]){0,1}\\([^,]*, #(\\d*)[^\\)]*\\)"
      in

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
            | C1 ->
                let c1 =
                  Re.Group.get (Re.exec c1_re instr) 1 |> Operand.of_id
                in
                parse_operand t instr (c1 :: operands)
            | E1 ->
                let e1 =
                  Re.Group.get (Re.exec e1_re instr) 1 |> Operand.of_id
                in
                parse_operand t instr (e1 :: operands)
            | V1 ->
                let v1 =
                  Re.Group.get (Re.exec v1_re instr) 1 |> Operand.of_id
                in
                parse_operand t instr (v1 :: operands)
            | V2 ->
                let v2 =
                  Re.Group.get (Re.exec v2_re instr) 1 |> Operand.of_id
                in
                parse_operand t instr (v2 :: operands)
            | CV ->
                let vargs =
                  Re.Group.get (Re.exec cv_re instr) 1
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

  let opcode = parse_opcode instr in
  let kind = opcode |> Opcode.get_kind in
  let operands = parse_operands kind instr in
  let ty =
    match ty_str_of instr with
    | Some ty_str -> Some (ty_str |> Types.of_string)
    | None -> None
  in

  create ty opcode operands
