#!/bin/sh
# Compare the coqc and petanque backends with one model on B1's Coq
# lemmas, proofs hidden.  From this directory:
#   ./eval_backends.sh [model] [results.jsonl]
# mem_cons runs 3 times per backend (variance), the others once.  Runs go
# one at a time (REALLMS rate limit).  Transcripts: .work/logs/eval_*.
set -u
model=${1:-glm-5.3-flash}
out=${2:-results/eval_backends_$model.jsonl}
dir=../bench/b1/session/interactive
mkdir -p results .work/logs
run() {  # run <backend> <lemma> <n>; stops the evaluation on a crash
  tmp=.work/eval_run.json
  python3 -I reallms_coq.py --model "$model" --backend "$1" --blank \
    --file "$dir/lemma_$2.v" \
    --log ".work/logs/eval_${model}_$1_$2_$3.log" > "$tmp" ||
    { echo "reallms_coq.py failed ($1 $2 $3)"; exit 1; }
  python3 -I -c 'import json,sys; r=json.load(sys.stdin); r["run"]=int(sys.argv[1]); print(json.dumps(r))' "$3" \
    < "$tmp" >> "$out"
  tail -1 "$out" | python3 -I -c 'import json,sys; r=json.load(sys.stdin); print(r["backend"], r["file"].split("/")[-1], r["run"], r["status"], r["steps"], "steps", r["seconds"], "s", sum(r["usage"].values()), "tokens")'
}
for lemma in mem_cons all_live_cons all_init_cons dll_frame dll_links; do
  n=1; [ "$lemma" = mem_cons ] && n=3
  i=1
  while [ "$i" -le "$n" ]; do
    for backend in coqc petanque; do run "$backend" "$lemma" "$i"; done
    i=$((i + 1))
  done
done
