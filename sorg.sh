#!/bin/bash
Z3DIR=$(ocamlfind query z3)

SORGDIR=$(dirname "$(realpath "$0")")
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$Z3DIR "$SORGDIR"/_build/default/main.exe "$@"
