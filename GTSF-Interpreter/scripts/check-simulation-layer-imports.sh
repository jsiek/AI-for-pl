#!/bin/sh

# Enforce the one-way dependency from constructive interpreter simulation to
# later catch-up and DGG proofs. The simulation root may use the interpreter,
# fuel metatheory, typing, and narrowing, but not any catch-up or DGG module.

set -eu

root_module=$1
shift

graph_file=$(mktemp "./gtsf-simulation-deps.XXXXXX.dot")
trap 'rm -f "$graph_file"' EXIT HUP INT TERM

"$@" --dependency-graph="$graph_file" "$root_module"

for forbidden_module in \
  DGG.DoubleInterpreter \
  DGG.DoubleInterpreterCatchUp \
  Examples.DoubleInterpreterCatchUpExamples \
  DGG.DoubleInterpreterFullCatchUp \
  DGG.InterpreterDynamicGradualGuaranteeDirect \
  DGG.InterpreterDynamicGradualGuaranteeProof \
  Core.InterpreterObservations
do
  if grep -F "label=\"$forbidden_module\"" "$graph_file" >/dev/null
  then
    echo "forbidden simulation dependency: $forbidden_module" >&2
    exit 1
  fi
done

if grep -E \
  'label="(proof\.)?[^"]*(CatchUp|DGG)[^"]*"' \
  "$graph_file" >/dev/null
then
  echo "forbidden simulation dependency: catch-up or DGG proof" >&2
  exit 1
fi
