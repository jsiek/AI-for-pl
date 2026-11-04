#!/bin/sh
# Trial of the REALLMS prover tier on B1's Coq lemmas, proofs hidden
# (--blank: the model sees each goal's statement and context, not the
# session's existing proofs).  From this directory:
#   ./trial.sh <model> [results.jsonl]
# One JSON report per lemma is appended to results (default
# results/trial_<model>.jsonl); transcripts go to .work/logs/.
set -u
model=$1
out=${2:-results/trial_$model.jsonl}
dir=../bench/b1/session/interactive
mkdir -p results .work/logs
for lemma in mem_cons all_live_cons all_init_cons dll_frame dll_links; do
  python3 -I reallms_coq.py --model "$model" --blank --max-steps 30 \
    --file "$dir/lemma_$lemma.v" --log ".work/logs/${model}_$lemma.log" \
    | python3 -I -c 'import json,sys; r=json.load(sys.stdin); print(json.dumps(r))' \
    >> "$out"
  tail -1 "$out" | python3 -I -c 'import json,sys; r=json.load(sys.stdin); print(r["file"].split("/")[-1], r["status"], r["steps"], "steps", r["seconds"], "s", r["usage"])'
done
