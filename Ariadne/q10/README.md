# Plan Q10: Frama-C/WP vs VST on B1a

The design is in `../plan.md`, Q10 ("First run: B1a, one run per side"
and "Rerun of the Frama-C side, twice").

```bash
cd Ariadne/bench/b1a && python3 -I make_b1a.py      # the shared inputs
cd Ariadne/harness && python3 harness.py ../bench/b1a --config b1a_frozen.json \
  --annotator opus --prove-scope lemmas --tiers 0,2 --opus-usd 3 \
  --opus-turns 150 --opus-wp-calls 25 --claude-usd 1 --annotator-retries 1 \
  --max-iterations 3 --max-usd 10 --max-seconds 7200    # Frama-C side
                                                    # (wp-run2: --max-usd 6)
cd Ariadne/q10 && python3 run_vst.py                # VST side (--dry-run first)
python3 check_wp.py ../runs/q10/<wp run>            # WP mutants
python3 check_vst.py ../runs/q10/<vst run>          # VST check and mutants
python3 spec_lines.py ../runs/q10/<vst run>/verif_b1a.v   # spec sizes
python3 summarize.py ../runs/q10/<run> ...          # the table rows
cd Ariadne/bench/b1a/rac && ./check.sh              # step 0 on the reference
cd Ariadne/bench/b1a && ./run_ref.sh                # WP on the reference
python3 test_mutants.py; python3 test_run_vst.py    # offline tests
```

| File | What |
|---|---|
| `../bench/b1a/make_b1a.py` | writes `b1a.c` (VST), `b1a_frozen.c` (Frama-C, public spec only) and `spec/sglib_dl_list_spec.h` (the public half of the template) from B1 |
| `../bench/b1a/SPEC.md` | the English spec both sides get |
| `../harness/b1a_frozen.json` | the harness config for B1a |
| `run_vst.py` | the VST run: run directory, fence, `claude -p`, `summary.json` |
| `mutants.py` | B1's mutants as they apply to B1a (anchors on C code, annotations allowed between its lines) |
| `../bench/b1a/rac/check.sh` | step 0 for B1a: B1's runtime-check tools with B1a's oracle, coverage, the runtime mutants |
| `../bench/b1a/b1a_ref.c`, `run_ref.sh` | the step-0 reference (B1's certified annotations on B1a's driver) and its WP check |
| `summarize.py` | one table row per run directory |
| `check_wp.py`, `check_vst.py` | mutant rejection (and, for VST, what was proved) |
| `spec_lines.py` | public spec size on each side |

## All runs (2026-11-06)

| Run | Wall time | Tokens: input / output / cache write / cache read (total) | USD | Model calls | Proved / open | Mutants rejected | Step 0 (per source checked) |
|---|---|---|---|---|---|---|---|
| `wp-run2` (Frama-C, `--max-usd 6`, no step 0) | 2338 s | 204 / 111,826 / 278,286 / 3,126,675 (3.52 M) | 5.09 | 9 (1 annotator, 8 prover), 139 turns | 253 / 263; 10 open (5 function goals, 5 lemmas); stopped by the run cap | 6 / 6 | off |
| `wp-run3` (Frama-C, `--max-usd 10`; **one annotator call lost to a step-0 tooling bug**) | 2894 s | 210 / 144,464 / 396,272 / 4,880,399 (5.42 M) | 7.04 | 9 (3 annotator, 6 prover), 150 turns | 234 / 249 (Qed 152, SMT 76, Coq 6); 15 open, all function goals | 5 / 6 (`noinit`: its goals already open) | frozen source PASS (26 clauses, all evaluated); patch 1 PASS (38, all evaluated); patch 2 FAIL on the mutant anchor (the bug); patch 3 FAIL: E-ACSL check fired (`\valid_read(&(*list)->ptr_to_previous)` in `add`); mutants 4/4 caught each time |
| `wp-run4` (Frama-C, `--max-usd 10`, all fixes) | 3043 s | 254 / 144,620 / 399,171 / 5,113,194 (5.66 M) | 7.11 | 11 (3 annotator, 8 prover), 191 turns | **certified 303 / 303** (Qed 173, SMT 122, Coq 8; 16 lemmas) | 6 / 6 | frozen source PASS (26 clauses, all evaluated); patch 1 PASS (46, all evaluated); patches 2-3 inconclusive: E-ACSL build failed (a ghost variable `gp`, which `gen_rac.py` drops); mutants 4/4 caught where run |
| `vst-run1` (VST agent) | 2373 s | 170 / 84,998 / 146,837 / 7,560,158 (7.79 M) | 4.39 | 1, 162 turns | all 6 functions + `semax_prog`, `Qed` | 4 / 4 tried, by script breakage | not applicable |

USD and tokens: `claude -p`'s JSON (`modelUsage`, API-equivalent),
summed by `summarize.py`.  Goals: the harness's WP census (Qed, SMT,
Coq).  Mutants: `check_wp.py` (WP, counting only goals the unmutated
result proves) and `check_vst.py`.  Step 0: `bench/b1a/rac/check.sh`
in the harness (ASan + UBSan, E-ACSL with the twins, coverage by
`rac/coverage.py`, the runtime mutants `vacuity`, `uaf`, `nullchk`,
`noinit`).  `wp-run3` and `wp-run4` ran one after the other on an
otherwise idle machine; `wp-run2` and `vst-run1` ran at the same time.
Rerun spending: $14.15 of the approved $20.

**wp-run4** (`../runs/q10/wp-run4/report.md`).  Three annotator calls,
all accepted ($2.18, $2.70, $0.54; 47, 54 and 12 turns): after the
first, 5 goals open; after the second, 8 (new lemmas); after the third,
0.  The Opus prover proved the 8 Coq lemmas; coqc, coqchk and Print
Assumptions accepted them, every guardrail passed.  The run did not
reach its cap.  Step 0 checked the frozen source and the first patch
fully; on the second and third patches E-ACSL could not build (a ghost
variable the runtime-check generator drops), so step 0 was inconclusive
there and only the sanitizers and the twin tests ran.

**wp-run3** (`../runs/q10/wp-run3/report.md`).  The first patch was
accepted (21 goals open after it).  The second call's patch put an
assert inside the forward walk's body; `mutants.py` needed the walk's
two lines adjacent, so step 0 failed on building the `uaf` mutant and
rejected the patch without checking it.  The anchors were fixed during
the run (`test_mutants.py`); the retry call's patch was then rejected
by a real E-ACSL check (an assert in `add` reading
`(*list)->ptr_to_previous` on a run where `*list` was NULL).  With the
one retry used, refinement ended at $7.04, 15 function goals open.

**What each fix changed.**
1.  *Report crash* (`test_report.py`): `wp-run3` and `wp-run4` each
    ended with their `verdict:` line and a complete `report.md`.
2.  *`run_vst.py` reserves first* (`test_run_vst.py`): offline only (no
    VST rerun).  The ledger is now calibrated (0.108% of the week per
    USD), so its 20% cap is a real limit.
3.  *Run cap as min(per-call cap, budget left)* (`test_budget.py`,
    `test_annotator.py`): not exercised by these runs; neither came
    within one per-call cap of $10 (every call ran at its full $3 or
    $1 cap).
4.  *Step 0 for B1a*: on in both reruns.  On the reference
    `b1a_ref.c` (WP 313 / 313 by `run_ref.sh`) it passes: 300 random
    runs under ASan + UBSan and E-ACSL, 61 clauses checked at run time
    (48 evaluated, 13 never evaluated), and catches the four runtime
    mutants (`vacuity` by its assert, `uaf` by ASan and a loop
    invariant, `nullchk` by UBSan and an RTE check, `noinit` by the
    oracle and `payload_written`).  `nowashead` and `noassign` weaken
    only `add`'s contract and run correctly, so they are WP's to reject.
    In the runs it rejected one wrong patch (wp-run3's third) and was
    inconclusive on two (wp-run4).

## First run (2026-11-06, one run per side)

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
    inside a run cap: at $6 (`wp-run2`) it stopped at $5.09 with $0.91
    unusable; at $10 one rerun certified for $7.11 and one ended at
    $7.04 with its retries used.  The VST side has one run, the Frama-C
    side three with different settings.
*   **Guidance.**  The annotator gets WP's open goals with their text
    (`TASK.md`) and the prover one goal at a time; the VST agent gets
    Floyd's error messages from its own `coqc` runs.  Step 0 was off in
    `wp-run2` and on in the reruns, where it also filters patches; the
    VST side has no runtime checking.
*   **wp-run3 is affected by a tooling change mid-run**: one annotator
    call was lost to the step-0 anchor bug, and the anchors were fixed
    while the run went on.
*   **Mutants.**  VST's mutant rejections come from script breakage (see
    above); `noassign` has no VST analogue and `vacuity` only a rough one.
*   **Few runs.**  One VST run; three Frama-C runs, of which two share
    settings (`wp-run3`, `wp-run4`) and gave certified once and 15 open
    once.  `wp-run2` and `vst-run1` shared the machine.
*   **Wall time is not like for like**: the Frama-C runs include WP,
    step 0, tier 0 (30 s per lemma) and the certification steps.

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
*   `../runs/q10/wp-run3/`, `../runs/q10/wp-run4/` (git-ignored): the
    reruns, with `q10-mutants/`; `../runs/q10/dry-wp3/` is the dry run
    of step 0 on `wp-run2`'s patch (no model call).
*   `../runs/q10/vst-run1/` (git-ignored): the VST run (`verif_b1a.v`,
    `result.json`, `summary.json`, `fence.json`, `q10-check/`).
