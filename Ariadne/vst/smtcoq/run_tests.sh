#!/bin/sh
# Runs inside the image (called by check.sh through ../run.sh).
# Prints the probe lines of each test file to out/<file>.txt.
set -u
coqc="coqc -native-compiler no -Q . SMT"
mkdir -p out
$coqc Probe.v && $coqc IntCompDec.v || exit 1
for f in smoke b1_side; do
  $coqc "$f.v" > "out/$f.log" 2>&1
  echo "$f coqc exit $?" >> out/status.txt
  grep -oE '(OK|NO) "[^"]*" "[^"]*"' "out/$f.log" | tr -d '"' > "out/$f.txt"
done
$coqc proved.v > out/proved.log 2>&1
echo "proved coqc exit $?" >> out/status.txt
