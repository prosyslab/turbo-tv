#!/usr/bin/env python3
import re
import subprocess

from pathlib import Path

PROJECT_ROOT = Path(__file__).absolute().parent.parent.parent
TYPES_H_PATH = PROJECT_ROOT / 'v8' / 'src' / 'compiler' / 'types.h'
TYPES_ML_PATH = PROJECT_ROOT / 'jstv' / 'lib' / 'parser' / 'types.ml'


def get_bitset_types():
    result = []

    type_parse_re = r' V\(([a-zA-Z0-9]+),'
    lines = TYPES_H_PATH.read_text().split('\n')
    for line in lines:
        m = re.search(type_parse_re, line)
        if m != None:
            result.append(m.groups()[0])

    return result


def generate_types_ml(bitset_types, non_bitset_types):
    template = '''
type bitset =
{}

type non_bitset =
{}

type t = B of bitset | NB of non_bitset

let of_str str =
  match str with
{}
  | _ -> raise Not_found

let none = B None
'''

    bitset = ''
    for t in bitset_types:
        bitset += f'  | {t}\n'

    non_bitset = ''
    for t in non_bitset_types:
        non_bitset += f'  | {t}\n'

    of_str = ''
    for t in bitset_types:
        of_str += f'  | "{t}" -> B {t}\n'
    for t in non_bitset_types:
        of_str += f'  | "{t}" -> NB {t}\n'

    TYPES_ML_PATH.write_text(template.format(bitset, non_bitset, of_str))
    subprocess.run(['ocamlformat', TYPES_ML_PATH, '--inplace'])


if __name__ == '__main__':
    bitset_types = get_bitset_types()
    non_bitset_types = [
        'HeapConstant', 'OtherNumberConstant', 'Tuple', 'Union', 'Range'
    ]
    generate_types_ml(bitset_types, non_bitset_types)
