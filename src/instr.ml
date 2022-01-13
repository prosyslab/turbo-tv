open Operand

exception Invalid_instruction of string * string

type t = Opcode.t * Operand.t list

let create opcode operands = (opcode, operands)

let err instr reason =
  Printf.fprintf stderr "Invalid Instruction: %s\n%s\n\n" instr reason;
  raise (Invalid_instruction (instr, reason))

let parse_instr instr =
  let get_id_and_opcode instr =
    let id_opcode_reg = Str.regexp "#\\([0-9]+\\):\\([a-zA-Z0-9]+\\)" in
    if Str.string_match id_opcode_reg instr 0 then
      let id = instr |> Str.matched_group 1 |> int_of_string in
      let opcode =
        try instr |> Str.matched_group 2 |> Opcode.of_str
        with Opcode.Invalid_opcode ->
          let reason = "Unknown opcode: " ^ (instr |> Str.matched_group 2) in
          err instr reason
      in
      (id, opcode)
    else err instr "Cannot match 'id' and 'opcode' from the instruction."
  in

  let id, opcode = get_id_and_opcode instr in

  (* TODO *)
  match opcode with
  | Branch | Call | ChangeInt32ToTagged | CheckedTaggedSignedToInt32
  | Checkpoint | EffectPhi | End | ExternalConstant | FrameState | HeapConstant
  | IfFalse | IfTrue | Int32Add ->
      (id, create opcode [ Int 1 ])
  | Int32Constant | Int64Constant | Load | LoadStackCheckOffset | Merge
  | Parameter | Return | StackPointerGreaterThan | Start | TypedStateValues ->
      (id, create opcode [ Int 2 ])
