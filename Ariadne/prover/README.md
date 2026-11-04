# Prover tier 1: REALLMS models on WP's Coq goals

Plan §12.2, tier 1.  `reallms_coq.py` gives a model served by IU's
REALLMS service (default `glm-5.3-flash`) one Coq goal produced by
Frama-C/WP (a `session/interactive/*.v` file written by Why3's Coq
driver) and tools to explore and check, until `coqc` accepts its proof.

```bash
cd Ariadne/prover
python3 reallms_coq.py --file ../bench/b1/session/interactive/lemma_mem_cons.v \
  [--model glm-5.3-flash] [--blank] [--hint "..."] [--max-seconds 120] \
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

**Budget: time, not turns.**  A run stops after `--max-seconds` (default
120) of working time: wall clock minus the backoffs after HTTP 429, so a
busy service does not eat the budget.  The check comes before each
reply, so a run can overrun by one reply and its tool calls; that is
deliberate, since the reply in flight may hold the proof.
`--max-steps` (default 100) is only a backstop.  `test_budget.py` tests
the budget offline.

Escalation policy: GLM gets 2 minutes, then the lemma goes to Sonnet.
From the trials below (which used a 30-turn budget), GLM finishes
`mem_cons` (87-105 s) and `all_init_cons` (57 s) within that; its other
two successes took 506 s and 666 s, where Sonnet takes 21-28 s and about
40k tokens.

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

### Backends: coqc vs Pétanque (GLM 5.3 Flash, `mem_cons`, proofs hidden)

Same prompt and 30-turn budget; Pétanque runs after the bullet fix
(bullets dropped in `run_tactics`).

| Backend | Solved | Turns | Wall clock | Tokens |
|---|---|---|---|---|
| coqc (whole script per check) | 2 / 2 | 9, 6 | 105 s, 87 s | 63k, 41k |
| Pétanque (`run_tactics`) | 2 / 3 | 8, 27, 8 (gave up) | 163 s, 173 s, 386 s | 93k, 375k, 127k |

One Pétanque success never called `run_tactics` (it used `check_proof`,
i.e. the coqc path); the other used it 22 times and took 9x the tokens
of a coqc success.  **Decision: GLM stays on the coqc backend.**  Small
sample, but nothing suggests step-wise interaction helps this model, and
it costs more turns and tokens.  The Pétanque backend stays (tested by
`test_petanque.py`) for uses where step-wise state is the point: tier-0
search with hammer/sauto in M2, and trying the Claude tiers.

### GLM 5.3 Flash on the other four lemmas (coqc, proofs hidden, 1 run each)

| Lemma | Result | Turns | Wall clock | Tokens |
|---|---|---|---|---|
| `all_live_cons` | **solved** | 18 | 506 s | 243k |
| `all_init_cons` | **solved** | 5 | 57 s | 36k |
| `dll_frame` (induction) | gave up | 11 | 405 s | 165k |
| `dll_links` (induction, 50 lines by hand) | gave up | 7 | 361 s | 122k |

With `mem_cons`, GLM proves 3 of B1's 5 Coq lemmas.  On both induction
lemmas the replies that ended the run were cut off at the 16k-token
output limit while still reasoning (about 50k characters each), so they
had no tool call and the nudges ran out: the model was never told it was
cut off.  (`results/glm_coqc_4lemmas.jsonl`)

### Sonnet 5.5 (tier 2) on the same five lemmas

Run as Claude Code subagents (no Anthropic API key here; billed to the
subscription), one per lemma, with the same tools as the REALLMS worker
through `prover_cli.py` (statement, query, goals, check; same verdict),
the proofs hidden (stripped copies of the goal files to read), and the
same budget (30 goals+check calls).  Each proof was rechecked with
`coqc`, and each transcript audited: no access to the session files,
version control, vst/ or other lemmas' directories.

| Lemma | Sonnet 5.5 | goals+check calls | Wall clock | Tokens | GLM 5.3 Flash (coqc) |
|---|---|---|---|---|---|
| `mem_cons` | solved | 3 | 22 s | 37k | solved (2/2 runs, 41k-63k) |
| `all_live_cons` | solved | 3 | 21 s | 37k | solved (243k) |
| `all_init_cons` | solved | 1 | 13 s | 36k | solved (36k) |
| `dll_frame` (induction) | solved | 2 | 28 s | 40k | gave up |
| `dll_links` (induction) | solved | 11 | 75 s | 49k | gave up |

Sonnet's proofs: `results/sonnet/`.  Token counts for Sonnet are the
subagent totals (they include Claude Code's own system prompt).

### GLM rerun of the induction lemmas (32k output limit, told when cut off)

| Lemma | Result | Turns | Wall clock | Tokens | Replies cut off |
|---|---|---|---|---|---|
| `dll_frame` | **solved** | 8 | 666 s | 138k | 1 |
| `dll_links` | not solved (30 turns) | 30 | 1519 s | 594k | 6 |

So GLM proves 4 of the 5 lemmas once cut-off replies are handled;
`dll_links` (a 50-line induction by hand) is beyond it within 30 turns,
while Sonnet proves it in 11 calls.  (`results/glm_coqc_induction_rerun.jsonl`)
