# Plan Q10: Frama-C/WP vs VST on B1a (one run per side)

The design is in `../plan.md`, Q10 ("First run: B1a, one run per side").

```bash
cd Ariadne/bench/b1a && python3 -I make_b1a.py      # the shared inputs
cd Ariadne/harness && python3 harness.py ../bench/b1a --config b1a_frozen.json \
  --annotator opus --prove-scope lemmas --tiers 0,2 --opus-usd 3 \
  --opus-turns 150 --opus-wp-calls 25 --claude-usd 1 --annotator-retries 1 \
  --max-iterations 3 --max-usd 6 --max-seconds 7200     # Frama-C side
cd Ariadne/q10 && python3 run_vst.py                # VST side (--dry-run first)
python3 check_wp.py ../runs/q10/<wp run>            # WP mutants
python3 check_vst.py ../runs/q10/<vst run>          # VST check and mutants
python3 spec_lines.py ../runs/q10/<vst run>/verif_b1a.v   # spec sizes
```

| File | What |
|---|---|
| `../bench/b1a/make_b1a.py` | writes `b1a.c` (VST), `b1a_frozen.c` (Frama-C, public spec only) and `spec/sglib_dl_list_spec.h` (the public half of the template) from B1 |
| `../bench/b1a/SPEC.md` | the English spec both sides get |
| `../harness/b1a_frozen.json` | the harness config for B1a |
| `run_vst.py` | the VST run: run directory, fence, `claude -p`, `summary.json` |
| `mutants.py` | B1's mutants as they apply to B1a |
| `check_wp.py`, `check_vst.py` | mutant rejection (and, for VST, what was proved) |
| `spec_lines.py` | public spec size on each side |

## Results (2026-11-06, one run per side)

| Side | Wall time | Tokens: input / output / cache write / cache read (total) | USD | Model calls | Proved / open | Mutants rejected | Public spec lines |
|---|---|---|---|---|---|---|---|
| Frama-C/WP pipeline (`harness.py`, Opus 5.5 annotator + Opus 5.5 prover) | 2338 s | 204 / 111,826 / 278,286 / 3,126,675 (3.52 M) | 5.09 (cap 6) | 9 `claude -p` (1 annotator, 8 prover), 139 turns | 253 / 263 goals; open: 5 function goals, 5 lemmas | 6 / 6 that apply | 135, given (human) |
| VST (`run_vst.py`, one Opus 5.5 agent) | 2373 s | 170 / 84,998 / 146,837 / 7,560,158 (7.79 M) | 4.39 (cap 15) | 1 `claude -p`, 162 turns | 6 / 6 functions + `semax_prog`, all `Qed` | 4 / 4 tried (by script breakage, see below); `noassign` has no analogue | 101, written by the agent (94 without boilerplate) |

USD and tokens are from `claude -p`'s JSON result (`modelUsage`),
API-equivalent.  The two runs ran at the same time on one 24-core
machine.

**Frama-C side** (`../runs/q10/wp-run2/report.md`).  Before any model
call, WP on the frozen spec closed 185 of 213 goals (Qed 135, SMT 50).
The annotator (Opus 5.5, one call: 39 turns, 12 of its 25 `wp` calls,
814 s, $2.55) wrote loop invariants, asserts and 14 lemmas; its patch
passed the guardrails.  The prover (tier 0, then Opus 5.5) proved 8 of
the lemmas in Coq ($0.11-0.62 each; tier 0 proved none), coqc, coqchk
and Print Assumptions accepted all 8.  Then the run cap stopped it: the
9th lemma's $1 call and the second annotator call ($3) would have passed
$6.  Final: 253 / 263 (Qed 163, SMT 82, Coq 8); open: `add`'s
`in_live_list(elem)` postcondition, 4 goals of `b1` (a loop invariant,
two asserts, a `loop assigns` part), and lemmas `iter_free`, `iter_fwd`,
`iter_start`, `list_frame`, `list_insert`.  The annotator said it gave
up on "budget", with goals left where the provers would not apply its
two-state lemmas to an existentially quantified list.

**VST side** (`../runs/q10/vst-run1/`).  `verif_b1a.v` (561 lines)
proves `semax_body` for `add`, `it_init_on_equal`, `it_init`,
`it_next`, `b1`, `main` and `prog_correct : semax_prog prog tt Vprog
Gprog`, all with `Qed`.  `check_vst.py` rechecked it against a pristine
`b1a.c` (the run's copy was also unchanged): clightgen + coqc pass, no
`Admitted`/`admit`/`Axiom`/`Parameter`/`Conjecture`, and Print
Assumptions equals the smoke test's list (VST's allocator assumptions
and the classical axioms).  Its funspecs against SPEC.md (read by hand):
`add` takes `*list` as the head of `s2` in the whole list `s1 ++ s2`
(any node, or NULL with an empty list) and returns the list `s1 ++ elem
:: s2`, which is stronger than the ACSL (the exact new list; the new
head when `s1` is empty); the iterator state is the whole list split as
`sA ++ sM ++ sB`, owning the nodes still to visit and handing each
returned node's ownership to the caller, with `subcomparator` NULL; the
returned node's fields are existential (weaker than it could be, as the
agent said).  No funspec is narrower than SPEC.md.

**Mutants.**

| Mutant | Frama-C (`check_wp.py`): first goal that fails | VST (`check_vst.py`) |
|---|---|---|
| `uaf` | the moved walk's loop invariants, `established` | rejected: `coqc` fails in `body_b1` |
| `nullchk` | `ariadne_live` and `rte_mem_access` at `l->i` | rejected: `body_b1` |
| `noinit` | the assert that every live node's payload is initialised, after the (removed) write | rejected: `body_b1` |
| `vacuity` | `assert \false` | analogue: `semax_prog` is proved (a call from `main` meets `b1`'s precondition) |
| `nowashead` | `b1`'s invariant "the_list is a head", preserved | rejected by hand: `add`'s post weakened to `EX s1', whole_list (s1' ++ elem :: s2)` (body_add skipped), `body_b1` fails at the call |
| `noassign` | `add`'s `assigns` | no analogue (frames are ownership) |
| `uaf_back`, `nullfirst`, `nulllast` | not B1a (B1b code) | not B1a |

The Frama-C result is partial, so a mutant counts as rejected only by
goals the unmutated result proves (`check_wp.py` reruns it as a
control); each failing goal above is at the mutated code.  **The VST
rejections are weak evidence**: every one fails at a tactic that no
longer matches the program's shape ("No matching clauses for match",
or a bullet error), which any change to the code would cause, not at a
refused safety obligation.  For `uaf` and `nullchk`, VST's soundness
says no proof can exist (each mutant has a stuck Clight execution); for
`noinit` and `nowashead` it does not settle the question.

## What makes the comparison unfair

*   **The VST agent wrote its own public spec.**  On the Frama-C side the
    135-line public spec is given and frozen (Q11); on the VST side the
    funspecs are the agent's, checked only by hand against SPEC.md.
    They match it and are in places stronger, but nothing forced that.
*   **Different specs and models of memory.**  The Frama-C spec goes
    through the ghost liveness model (`live`, `all_live`, `dll` with
    `\nth` and `mem`, `iter_at` with indices) and needs frame and
    two-state lemmas; VST's ownership gives framing and distinctness for
    free.  So the Frama-C side proves a harder, index-based formulation
    of the same properties.
*   **Budget shape.**  The VST agent had one $15 call and used $4.39.
    The pipeline had per-call caps ($3 annotator, $1 per prover goal)
    inside a $6 run cap, so it stopped at $5.09 with $0.91 unusable: a
    second annotator call could not fit.  With the VST side's budget
    shape, the Frama-C side might have finished; this run does not say.
*   **Guidance.**  The annotator gets WP's open goals with their text
    (`TASK.md`) and the prover one goal at a time; the VST agent gets
    Floyd's error messages from its own `coqc` runs.  Step 0 (runtime
    checking) was off for B1a (`../plan.md` Q10).
*   **Mutants.**  VST's mutant rejections come from script breakage (see
    above); `noassign` has no VST analogue and `vacuity` only a rough one.
*   **One run per side**, at the same time on one machine, so wall times
    share the CPU and nothing is known about variance.

## Isolation on the VST side

As run (`../runs/q10/vst-run1/fence.json`): cwd the run directory,
which held only `b1a.c`, `SPEC.md`, `TASK.md` and `example/` (VST's
smoke test); `--safe-mode --restricted --strict-mcp-config
--disable-slash-commands --no-session-persistence`; tools Bash, Read,
Write, Edit; allowed: Read/Write/Edit under the run directory and one
command, `vst-run1.tool`, a script outside the run directory that runs
one command in `ariadne-vst:dev` with only the run directory mounted at
`/work` and `--network none`; denied: `git`, and Read/Write/Edit of
`Ariadne/vst/b1/**` in this worktree and in the main checkout;
`--permission-mode dontAsk`; `GIT_DIR` and `GIT_CEILING_DIRECTORIES`
set.  The run had one permission denial: a `sed -i` on its own
`verif_b1a.v`.  No `--add-dir`.  The prompt told it not to read outside
the run directory except the VST/Rocq installation in the image.

## Artefacts

*   `../runs/q10/wp-run2/` (git-ignored): the Frama-C run (`report.md`,
    `report.json`, `patch1.c`, `annotator/`, `tier2/`, `q10-mutants/`).
    `../runs/q10/wp-run1/` is a first start whose WP container was killed
    (exit 137) before any model call ($0).
*   `../runs/q10/vst-run1/` (git-ignored): the VST run (`verif_b1a.v`,
    `result.json`, `summary.json`, `fence.json`, `q10-check/`).
