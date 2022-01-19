exception Invalid_instruction of string * string

type t = Opcode.t * Operand.t list

let create opcode operands : t = (opcode, operands)
let empty : t = (Opcode.empty, [])

(* getter *)
let opcode (opcode, _) : Opcode.t = opcode
let operands (_, operands) : Operand.t list = operands

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
      let p1_re = Re.Pcre.regexp "(?:\\[[^\\]]*\\]){0,1}\\(#(\\d*)[^\\)]*\\)" in
      let p2_re =
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
            | UNIMPL -> parse_operand [] instr []
            | _ -> failwith "Unreachable"
          with Not_found ->
            let reason = "Cannot parse operands" in
            err instr reason)
      | [] -> List.rev operands
    in

    let kinds = Opcode.split_kind kind in
    [] |> parse_operand kinds instr
  in

  let opcode = parse_opcode instr in
  let kind = opcode |> Opcode.get_kind in
  let operands = parse_operands kind instr in

  create opcode operands
