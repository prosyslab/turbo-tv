#!/bin/bash

NCPU="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)"
OCAML_VERSION="4.13.1"
JSTV_OPAM_SWITCH="jstv-4.13.1"
opam init --compiler=$OCAML_VERSION -j $NCPU --no-setup

switch_exists=no
for installed_switch in $(opam switch list --short); do
  if [[ "$installed_switch" == "$JSTV_OPAM_SWITCH" ]]; then
    switch_exists=yes
    break
  fi
done

if [ "$switch_exists" = "no" ]; then
  opam switch create $JSTV_OPAM_SWITCH $OCAML_VERSION
else
  opam switch $JSTV_OPAM_SWITCH
fi

eval $(SHELL=bash opam env --switch=$JSTV_OPAM_SWITCH)
opam install core cmdliner dune ocamlgraph

# generage source codes from `specs/opcodes.spec`
scripts/spec2ml.py --instr --replace
scripts/spec2ml.py --opcode --replace

make
