#!/bin/sh

# Reject small-step and reduction-based DGG modules from an Agda dependency
# graph. The first argument is the root module. The Agda command and all of
# its ordinary arguments follow it.

set -eu

root_module=$1
shift

graph_file=$(mktemp "./gtsf-interpreter-deps.XXXXXX")
trap 'rm -f "$graph_file"' EXIT HUP INT TERM

"$@" --dependency-graph="$graph_file" "$root_module"

for forbidden_module in \
  NuReduction \
  Eval \
  DynamicGradualGuarantee
do
  if grep -F "label=\"$forbidden_module\"" "$graph_file" >/dev/null
  then
    echo "forbidden dependency: $forbidden_module" >&2
    exit 1
  fi
done

if grep -E 'label="proof\.NuDGG' "$graph_file" >/dev/null
then
  echo "forbidden dependency: reduction-based proof.NuDGG module" >&2
  exit 1
fi
