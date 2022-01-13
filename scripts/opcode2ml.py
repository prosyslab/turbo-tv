opcodes = open("opcodes.txt").readlines()

t = "type t = \n"
of_str = """
let of_str str =
  match str with
"""
to_str = """
let to_str opcode =
  match opcode with
"""

for opcode in opcodes:
    opcode = opcode.strip()

    t += f"  | {opcode}\n"
    of_str += f"  | \"{opcode}\" -> {opcode}\n"
    to_str += f"  | {opcode} -> \"{opcode}\"\n"

of_str += " | _ -> raise Invalid_opcode"

print(t)
print(of_str)
print(to_str)
