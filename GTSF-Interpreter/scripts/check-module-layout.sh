#!/bin/sh

# Keep public interpreter modules in their documented topic namespaces and
# reject stale module declarations after future moves.

set -eu

for file in ./*.agda
do
  case "$file" in
    ./Interpreter.agda|./InterpreterAll.agda)
      ;;
    *)
      echo "unexpected root module: $file" >&2
      exit 1
      ;;
  esac
done

for artifact in ./*.agdai
do
  [ -e "$artifact" ] || continue
  source=${artifact%.agdai}.agda
  if [ ! -f "$source" ]
  then
    echo "orphaned root interface: $artifact" >&2
    exit 1
  fi
done

for file in $(find . -type f -name '*.agda' | sort)
do
  relative=${file#./}
  expected=$(printf '%s' "${relative%.agda}" | tr '/' '.')
  actual=$(awk '
    $1 == "module" && NF >= 3 { print $2; exit }
    $1 == "module" && NF == 1 { getline; print $1; exit }
  ' "$file")
  if [ "$actual" != "$expected" ]
  then
    echo "module/path mismatch: $file" >&2
    echo "  expected: $expected" >&2
    echo "  actual:   $actual" >&2
    exit 1
  fi
done
