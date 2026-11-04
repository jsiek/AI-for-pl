# Prover tier 1: REALLMS models on WP's Coq goals

Plan §12.2, tier 1.  `reallms_coq.py` gives a model served by IU's
REALLMS service (default `glm-5.3-flash`) one Coq goal produced by
Frama-C/WP (a `session/interactive/*.v` file written by Why3's Coq
driver) and tools to explore and check, until `coqc` accepts its proof.

```bash
cd Ariadne/prover
python3 reallms_coq.py --file ../bench/b1/session/interactive/lemma_mem_cons.v \
  [--model glm-5.3-flash] [--blank] [--hint "..."] [--max-steps 30] \
  [--log .work/logs/x.log] [--apply]
```

Only a short JSON report goes to stdout: status, steps, seconds, token
usage, tool-call counts, `coqc` runs, and the script if solved.  The
transcript (the model's reasoning and every tool call) goes to `--log`.

## How it works

The client (key lookup, streamed chat with tool calls, the tool loop
with nudging) is `scripts/reallms_client.py`, shared with the Agda worker
`scripts/reallms_agent.py`.  The key comes from `$REALLMS_API_KEY`, an
`export` line in `~/.zshrc`, or `~/.reallms_key`; it is never printed,
logged or committed.  `python3 ../../scripts/reallms_client.py` lists the
models the key can use.

Tools given to the model:

| Tool | What |
|---|---|
| `read_file(path, start?, end?)` | a file under `Ariadne/` |
| `grep(pattern, path?)` | `.v`, `.c`, `.h`, `.md` files under `Ariadne/` |
| `coq_query(command)` | one `Search` / `Check` / `Print` / `About` / `Locate` in the goal file's context |
| `show_goals(script)` | the goal state after a partial script |
| `check_proof(script)` | the whole script, spliced between the goal's `Proof.` and `Qed.`, checked by `coqc` |

`coqc` runs in the M0 image (`../env/run.sh`, about 0.7 s per run) with
`-native-compiler no` and Why3's Coq library, like WP's own check.

**Verdict.**  A script passes iff `coqc` accepts the file and the script
contains none of `admit`, `Admitted`, `Abort`, `give_up`, `Qed`,
`Defined`, `Axiom`, `Parameter`, `Hypothesis`, `Variable`, `Theorem`,
`Lemma`, `Definition`, `Require`, `Set`, `Unset`, … (so it cannot close
the goal early, open a new one, or add assumptions).  The statement and
the Why3 context are taken from the file and never from the model.
`--apply` writes the proof into the file; WP's `-wp-interactive batch`
then rechecks it as part of `../bench/b1/run.sh`.

**`--blank`** hides the proofs of the target and of every goal file next
to it, from the prompt, `read_file` and `grep` (statements stay
visible).  Without it the model can simply read the existing proof: in
the first test run, GLM read the goal file and resubmitted its proof
verbatim.  `test_tools.py` checks the tools and the hiding offline (no
model calls).

## Trial: B1's Coq lemmas, proofs hidden

`./trial.sh <model>` runs the 5 lemmas of `../bench/b1` that need Coq,
with `--blank` and 30 steps each, and appends one JSON report per lemma
to `results/trial_<model>.jsonl`.

### Round 1: first setup, all 5 lemmas (`results/round1_*.jsonl`)

Nothing solved by either model (30 steps or giving up; 150-520 s and
roughly 100k-350k prompt tokens per lemma).

### Iterating on the easiest lemma, `mem_cons`

`mem_cons` is a 20-line proof with `lia` and the Why3 list lemmas
`nth_zero`, `nth_cons`, `length_cons`, `length_pos`.  The transcripts
showed the setup, not only the models, was at fault:

| Problem seen in the transcripts | Fix |
|---|---|
| Error line numbers were off by one | script-relative lines fixed |
| A failing script returned only the error, never the goal it failed on | `show_goals` and `check_proof` add the goal state just before the failing step (one more `coqc` run) |
| GLM resent the identical `show_goals` call 20 times | a repeated identical call is answered with "same as your previous call", without running it |
| gpt-oss wrapped the script in `Proof.` … `Qed.`, then tried `Defined.` | a leading `Proof.` and a final `Qed.`/`Defined.` are dropped |
| `rewrite nth_cons` fails: Why3 lemmas have hypotheses and conjunctions | prompt: use `destruct (L args) as [H1 H2]` / `pose proof` |
| `lia` fails on `Length.length (a :: l)`, and on `<` unfolded into a `match` by `simpl`/`unfold` | prompt: rewrite with the length lemma, give lia `length_pos`, no `simpl`/`cbn`/`unfold` on Z comparisons |
| HTTP 429 from REALLMS when two runs went in parallel | `reallms_client.chat` retries with backoff (Retry-After); runs go one at a time |

The prompt additions describe the Why3 encoding in general (opaque
`nth`/`length` axiomatised by conditional lemmas), not this lemma's
proof.

| Round | GLM 5.3 Flash | gpt-oss-120b |
|---|---|---|
| 1 (first setup) | not solved: 30 steps, 223 s, 345k tokens | not solved: 30 steps, 239 s, 205k tokens |
| 2 (error state, line numbers, repeats, `Proof.`/`Qed.`) | HTTP 429 after 5 steps | gave up: 27 steps, 320 s, 242k tokens |
| 3 (+ Why3/lia guidance, backoff) | **solved: 9 steps, 105 s, 63k tokens** (5 `check_proof`, 5 `coq_query`) | gave up: 30 steps, 299 s, 355k tokens |

GLM's proof (round 3) differs from the session's (another case split,
`rewrite <- Ha. apply nth_zero`), and its one `read_file` of the goal
file returned the statement with the proof hidden.  One run per cell:
no variance estimate yet.
