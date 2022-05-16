#!/usr/bin/env python3
from pathlib import Path
import gspread

OPCODE_WKSHT_NAMES = [
    "common-operator", "js-operator", "simplified-operator", "machine-operator"
]
SPECS_P = Path().cwd() / "specs"


def fetch_spec(gc: gspread.Client) -> dict[str:str]:
    opcodes_sht = gc.open("Turbofan Opcodes")
    wkshts = [opcodes_sht.worksheet(name) for name in OPCODE_WKSHT_NAMES]
    spec = {}

    for sht in wkshts:
        values = sht.get_values()
        head = values[0]
        opcodes = values[1:]
        max_nargs = ["Arg" in cname for cname in head].count(True)

        for opcode in opcodes:
            name, args = opcode[0], opcode[1:max_nargs+1]

            # remove empty cell
            args = filter(lambda c: c, args)
            args = ",".join(list(args))

            spec[name] = args

    return spec


def emit_spec(spec: dict[str:str], name: str) -> None:
    spec = sorted(spec.items())
    output = "\n".join([f"{opcode},{args}" for opcode, args in spec])

    with open((SPECS_P / name).with_suffix(".spec"), "w") as spec_out:
        spec_out.write(output)


if __name__ == "__main__":
    gc = gspread.service_account()
    spec = fetch_spec(gc)
    emit_spec(spec, "opcodes")
