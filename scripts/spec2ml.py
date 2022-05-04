#!/usr/bin/env python3
import subprocess
from functools import reduce
from pathlib import Path
from argparse import ArgumentParser
import tempfile

SRC_PATH = Path.cwd() / "lib/parser"
TMPL_PATH = Path.cwd() / "tmpl"


def read_spec(spec_p: Path):
    opcodes = {}
    specs = spec_p.read_text().split("\n")
    for op_spec in specs:
        splitted = op_spec.strip().split(",")
        opcode, operands = splitted[0], splitted[1:]
        kind = "".join(operands).upper()

        if kind == "":
            kind = "UNIMPL"

        if kind not in opcodes:
            opcodes[kind] = [opcode]
        else:
            opcodes[kind].append(opcode)

        elem_kinds = split_kind(kind)
        for ek in elem_kinds:
            if ek not in opcodes:
                opcodes[ek] = []

    return opcodes


def print_in_format(src):
    _, tmp = tempfile.mkstemp()

    with open(tmp, "w") as tmp_out:
        tmp_out.write(src)

    subprocess.run(f"ocamlformat --enable-outside-detected-project {tmp}",
                   shell=True)


def save_in_format(src, dst_p):
    with open(dst_p, "w") as out:
        out.write(src)

    subprocess.run(f"ocamlformat -i {dst_p}", shell=True)


def gen_opcode(opcodes, replace=False):
    '''Generate the `src/opcode.ml` from `spec/opcodes.spec`'''
    kind = f"type kind = \n"

    for k, opcode_group in opcodes.items():
        kind += f"  | {k}\n"
    kind += "  | Empty\n\n"

    t = "type t = \n"
    of_str = ("let of_str str = \n"
              "  match str with\n")
    to_str = ("let to_str opcode = \n"
              "  match opcode with\n")
    get_kind = ("let get_kind opcode = \n"
                "  match opcode with\n")
    split_kind = ("let split_kind kind = \n"
                  "match kind with \n")

    for k, opcode_group in opcodes.items():
        if len(opcode_group) > 0:
            t += f"  (* {k.lower()} *)\n"

        for opcode in opcode_group:
            t += f"  | {opcode}"
            of_str += f"  | \"{opcode}\" ->  {opcode}\n"
            to_str += f"  |  {opcode} -> \"{opcode}\"\n"
            get_kind += f"  | {opcode}"

        if opcode_group != []:
            get_kind += f" -> {k}\n"
        split_kind += f"| {k} -> [{k if (k == 'UNIMPL' or k == 'VARGS') else ';'.join([k[2*i:2*i+2] for i in range(len(k)//2)])}]\n"
        t += "\n"

    t += ("  | Empty\n"
          "[@@deriving equal]\n\n")
    get_kind += "  | Empty -> Empty \n\n"
    split_kind += "| Empty -> [Empty]\n"
    of_str += "  | _ -> raise Invalid_opcode\n\n"
    to_str += "  | Empty -> failwith \"Unreachable\"\n\n"
    split_kind += "\n\n"

    opcode_tmpl = open(TMPL_PATH / "opcode.mlt").read()
    opcode_gen = opcode_tmpl.format(kind=kind,
                                    t=t,
                                    get_kind=get_kind,
                                    split_kind=split_kind,
                                    of_str=of_str,
                                    to_str=to_str)

    if replace:
        save_in_format(opcode_gen, SRC_PATH / "opcode.ml")
    else:
        print_in_format(opcode_gen)


def split_kind(kind):
    return [kind] if (kind == 'UNIMPL' or kind == "VARGS") else [
        kind[2 * i:2 * i + 2] for i in range(len(kind) // 2)
    ]


def gen_re_from_kind(kind):
    if kind == "UNIMPL":
        return ""

    p_operand_re = "#(\\\\d*)"
    p_re_prefix = "\\\\("
    p_re_suffix = "[^\\\\)]*\\\\)"

    b_operand_re = "([^,]*)"
    b_re_prefix = "(?:\\\\["
    b_re_suffix = "[^\\\\]]*\\\\])"

    if kind == "CV":
        return f"let {kind.lower()}_re = Re.Pcre.regexp \"{b_re_prefix}{b_re_suffix}{{0,1}}{p_re_prefix}{p_re_suffix}{p_re_prefix}{p_re_suffix}{p_re_prefix}(.*){p_re_suffix}\" in\n"

    operand_kind = kind[0].upper()
    operand_pos = int(kind[1])
    skip_re = "[^,]*, "
    skips_re = skip_re * (operand_pos - 1)

    if operand_kind == "B":
        re = f"let {kind.lower()}_re = Re.Pcre.regexp \"{b_re_prefix}{skips_re}{b_operand_re}{b_re_suffix}{p_re_prefix}{p_re_suffix}\" in"
    elif operand_kind == "V":
        re = f"let {kind.lower()}_re = Re.Pcre.regexp \"{b_re_prefix}{b_re_suffix}{{0,1}}{p_re_prefix}{skips_re}{p_operand_re}{p_re_suffix}\" in"
    elif operand_kind == "E":
        re = f"let {kind.lower()}_re = Re.Pcre.regexp \"{b_re_prefix}{b_re_suffix}{{0,1}}{p_re_prefix}{p_re_suffix}{p_re_prefix}{skips_re}{p_operand_re}{p_re_suffix}\" in"
    elif operand_kind == "C":
        re = f"let {kind.lower()}_re = Re.Pcre.regexp \"{b_re_prefix}{b_re_suffix}{{0,1}}{p_re_prefix}{p_re_suffix}{p_re_prefix}{p_re_suffix}{p_re_prefix}{skips_re}{p_operand_re}{p_re_suffix}\" in"

    return re


def gen_match_from_kind(kind):
    if kind == "UNIMPL":
        return ""
    elif kind.endswith("V"):
        return (
            f"| {kind} ->\n"
            f"  let vargs= \n"
            f"    Re.Group.get(Re.exec {kind.lower()}_re instr) 1 |> String.split_on_char ','"
            f"  in \n"
            f"  List.fold_left\n"
            "     (fun res arg ->"
            "       let re = Re.Pcre.regexp \"#(\\\\d*)\" in"
            "       (Re.Group.get (Re.exec re arg) 1 |> Operand.of_id) :: res)"
            "     [] vargs")
    else:
        operand_type = "id" if kind.startswith("V") or kind.startswith(
            "E") or kind.startswith("C") else "const"
        return (
            f"| {kind} ->\n"
            f"  let {kind.lower()}= \n"
            f"    Re.Group.get(Re.exec {kind.lower()}_re instr) 1 |> Operand.of_{operand_type} \n"
            f"  in \n"
            f"  parse_operand t instr ({kind.lower()}::operands)")


def gen_instr(opcodes, replace=False):
    '''Generate the part of `src/instr.ml` from `specs/opcodes.spec`'''
    unique_kinds = set(
        reduce(lambda r, k: r + split_kind(k), opcodes.keys(), []))
    unique_kinds = dict({k: {} for k in unique_kinds})

    for kind in unique_kinds.keys():
        unique_kinds[kind]["re"] = gen_re_from_kind(kind)
        unique_kinds[kind]["match"] = gen_match_from_kind(kind)

    kinds_re = "\n".join([
        v["re"] if (k != "UNIMPL") else ""
        for k, v in sorted(unique_kinds.items())
    ]) + "\n"

    kinds_match = "\n".join([
        v["match"] if (k != "UNIMPL" and k[-1] != 'V') else ""
        for k, v in sorted(unique_kinds.items())
    ])
    kinds_match += f"{unique_kinds['CV']['match']}\n"
    kinds_match += ("| UNIMPL -> []\n"
                    "|_ -> failwith \"Unreachable\"\n")

    parse_operand = (
        "let rec parse_operand (kinds : Opcode.kind list) instr operands =\n"
        f"{kinds_re}"
        "match kinds with\n"
        "| k :: t -> (\n"
        "try\n"
        "match k with\n"
        f"{kinds_match}"
        "with Not_found ->\n"
        "let reason = \"Cannot parse operands\" in\n"
        "err instr reason)\n"
        "| [] -> List.rev operands\n"
        "in\n")

    instr_tmpl = open(TMPL_PATH / "instr.mlt", "r").read()
    instr_gen = instr_tmpl.format(parse_operand=parse_operand)

    if replace:
        save_in_format(instr_gen, SRC_PATH / "instr.ml")

    else:
        print_in_format(instr_gen)


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("--opcode",
                        action="store_true",
                        help="Generate opcode.ml")
    parser.add_argument("--instr",
                        action="store_true",
                        help="Generate instr.ml")
    parser.add_argument("--replace", default=False, action="store_true")

    args = parser.parse_args()

    spec_p = (Path(__file__).parent.parent / "specs" /
              "opcodes.spec").resolve()
    spec = read_spec(spec_p)

    if args.opcode:
        gen_opcode(spec, args.replace)
    elif args.instr:
        gen_instr(spec, args.replace)
    else:
        parser.print_help()
