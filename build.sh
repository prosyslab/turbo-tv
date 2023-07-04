#!/bin/bash

NCPU="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)"
OCAML_VERSION="4.13.1"
TURBO_TV_OPAM_SWITCH="turbo-tv"
opam update
opam init --compiler=$OCAML_VERSION -j $NCPU --no-setup

switch_exists=no
for installed_switch in $(opam switch list --short); do
  if [[ "$installed_switch" == "$TURBO_TV_OPAM_SWITCH" ]]; then
    switch_exists=yes
    break
  fi
done

if [ "$switch_exists" = "no" ]; then
  opam switch create $TURBO_TV_OPAM_SWITCH $OCAML_VERSION
else
  opam switch $TURBO_TV_OPAM_SWITCH
fi

eval $(SHELL=bash opam env --switch=$TURBO_TV_OPAM_SWITCH)
opam install core_unix cmdliner dune ocamlgraph z3 ocamlformat=0.22.4 oUnit

if [ "$1" = "gen" ]; then
  # generate source codes from `specs/opcodes.spec`
  scripts/fetch-spec.py
  scripts/spec2ml.py --instr --replace
  scripts/spec2ml.py --opcode --replace
fi

make
