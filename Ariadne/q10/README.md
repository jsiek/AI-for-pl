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

**B1a's inputs are a snapshot.**  `bench/b1a/` keeps the spec its runs
(`wp-run2` to `wp-run4`, `vst-run1`, `vst-run2`) used: the iterator spec
of 2026-11-07, in `bench/b1a/spec/` (public half) and
`bench/b1a/spec_full/` (the whole template and the witness hints, for
`b1a_ref.c`, `run_ref.sh` and `rac/check.sh`).  `make_b1a.py` would now
write the 2026-11-08 spec; it is not rerun.  B1c (`bench/b1c/`) uses the
new spec.

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

## B1c: a client that reuses the list after iterating (2026-11-08)

`bench/b1c/`: B1a's four sglib functions, and a driver that builds a
list, walks it with the iterator without freeing (summing the payloads,
recording the node at position m / 2), adds a new node before that
node, then iterates from the new node freeing every node.  The frozen
iterator spec of 2026-11-07 could not verify this driver (the iterated
list was existential); the owner approved the change of plan Q12, and
B1c uses the new spec.  The driver's contract is B1a's, for an
`unsigned` result.  (`c`, the walk counter, is `unsigned` so that the
reference needs no bound on the number of steps.)

**Reference** (`b1c_ref.c`, `run_ref.sh`): WP proves 349 / 349 goals
(Qed 186, Alt-Ergo 140, CVC5 9, Z3 2, Coq 12: B1's 9 scripts and 3 new
ones: lemmas `dll_shared` (two whole lists sharing a node are the same,
by index) and `dll_shared_live`, and the establishment of the first
walk's invariant, across `it_init`'s write to the iterator).  Step 0
(`rac/check.sh`, B1's tools with B1c's oracle, the unsigned sum) passes:
300 random runs under ASan + UBSan and E-ACSL, 61 clauses checked at run
time (48 evaluated, 13 never evaluated); it catches all five runtime
mutants.  WP (`check_wp.py --bench b1c --source ../bench/b1c/b1c_ref.c`)
rejects all eight mutants of `mutants_b1c.py`:

| Mutant | Reference: first goal that fails (WP) | Step 0 (ASan+UBSan / E-ACSL) |
|---|---|---|
| `uaf` (payload read through `the_list` after the last iteration) | `ariadne_live` at the read | heap-use-after-free / - |
| `nullchk` | `ariadne_live`, `rte_mem_access` at `l->i` | null member access / RTE mem_access |
| `noinit` | `payload_written` | oracle / `payload_written` |
| `addfreed` (step 3's `add` given a freed node) | `add_pre2b` (the list holding `mid` is live) | heap-use-after-free / `add_pre2` |
| `vacuity` | `assert \false` | - / `vacuity` |
| `nowashead` | `head_after_add` (build loop) | not for step 0 |
| `noassign` | `add`'s `assigns` | not for step 0 |
| `nextpost` (it_next's postcondition of 2026-11-07) | the first walk's invariant, `preserved` (and `established`, whose Coq script no longer replays) | not for step 0 |

**Runs** (one each, one after the other):

| Run | Wall time | Tokens: input / output / cache write / cache read (total) | USD | Model calls | Proved / open | Mutants rejected | Step 0 (per source checked) |
|---|---|---|---|---|---|---|---|
| `vst-b1c` (VST agent, $15 cap) | 5679 s | 278 / 174,498 / 268,822 / 21,499,356 (21.94 M) | 9.94 | 1, 268 turns | all 6 functions + `semax_prog`, `Qed`; assumptions as the smoke test | 4 / 4 C-level, all by script breakage | not applicable |
| `wp-b1c` (Frama-C pipeline, $10 cap) | 4123 s | 262 / 203,564 / 472,113 / 7,570,971 (8.25 M) | 9.36 | 8 (4 annotator, 4 prover), 205 turns | 290 / 293 (Qed 173, SMT 113, Coq 4); open: the first walk's invariant `established`, `add`'s `in_live_list(elem)` postcondition, `it_next`'s new postcondition | 8 / 8 | frozen source and patches 1-2 PASS (25, 25, 45 clauses, all evaluated; 5/5 mutants caught); patch 3 rejected (an E-ACSL check fired in `add`); patch 4 judged by patch 3's log (a harness defect, fixed after the run) |

USD and tokens: `claude -p`'s JSON (`summarize.py`); goals: the
harness's WP census; mutants: `check_vst.py --bench b1c`, `check_wp.py
--bench b1c`; step 0: `bench/b1c/rac/check.sh` in the harness.

*wp-b1c* (`../runs/q10/wp-b1c/report.md`): annotator calls $1.03 (8
turns), $2.63 (51 turns), then $2.85 and $2.14 for iteration 3, both
patches rejected by step 0.  The third patch fired a real E-ACSL check
(an assert in `add` reading `(*list)->ptr_to_previous` when `*list` was
NULL, E-ACSL's eager `\at`).  The fourth patch's E-ACSL build failed (a
ghost variable `g_pp`, which `gen_rac.py` drops), which is
*inconclusive*, but the harness read the FAIL lines of the whole step-0
log, including the third patch's, and rejected it.  Fixed after the run
(`harness.last_run`, `test_report.py`); not rerun.  Checked without a
model (`--overlay` of that patch, `--tiers 0`): 348 / 358 goals, one
function goal and nine induction lemmas open, which the paid prover
tier would have had to take.

*vst-b1c* (`../runs/q10/vst-b1c/`): 952 lines, every function `Qed`,
`check_vst.py` against a pristine `b1c.c`.  Three permission denials:
a `sed -i` on its own file, `git status`, and an `rm` of its scratch
files.

**The VST iterator spec, read by hand.**  The iterator *borrows* the
list; it never takes ownership of it.  A whole list is `cells s ps 0
(Zlength s)` (each node owned: `data_at` + `malloc_token`); the iterator
struct is `it_rep it s b f cur`, the struct alone, holding positions `b`
and `f` of the list `s` as pointers.  `it_init` / `it_init_on_equal` take
the whole list and give it back whole, with `init_result` (start at node
`j`: `b = j - 1`, `f = j + 1`, result node `j`).  `it_next` asks only
for the nodes still to visit, `cells s ps 0 (b+1)` and `cells s ps f
(Zlength s)`, and gives them back unchanged, with `next_step` saying
exactly which step it took (backward, forward, or the end with NULL).
So a client may free each returned node (B1a) or keep the whole list
and use it again (B1c).  *Interleaving `add`:* supported in principle:
`add` needs the whole list and returns `ins j e s`; the iterator state is
only pointers, which the client can re-read as positions in the new list
(`it_rep_fold`), but the spec says nothing about where the new node falls
relative to `b`, `f`, so the client must work that out.  *A second
iteration before the first ends:* supported: the client still owns the
whole list (the first iterator holds no cells), so `it_init` on a second
iterator struct goes through, and the two only read.  Against SPEC.md
it is stronger than the frozen ACSL (`next_step` is exact; `add` gives the
exact new list) and does not state that freed nodes keep their links
(separation logic says nothing about freed memory).

**Which mutant rejections are real refused obligations.**  Frama-C: all
of them, on both the reference and `wp-b1c`'s result: each fails at a
goal at the mutated code, by WP from the same annotations, and
`check_wp.py` counts only goals the unmutated source proves (for
`nextpost`, `established` fails because its Coq script no longer
replays, but `preserved` is an SMT goal that is genuinely refused).
VST: none directly: each mutant breaks `body_b1` at a tactic that no
longer matches the program ("No matching clauses for match", "No
applicable tactic").  For `uaf`, `nullchk` and `addfreed`, VST's
soundness theorem rules out any proof (each has a stuck Clight
execution); for `noinit` it does not settle it.

## All runs (2026-11-06)

| Run | Wall time | Tokens: input / output / cache write / cache read (total) | USD | Model calls | Proved / open | Mutants rejected | Step 0 (per source checked) |
|---|---|---|---|---|---|---|---|
| `wp-run2` (Frama-C, `--max-usd 6`, no step 0) | 2338 s | 204 / 111,826 / 278,286 / 3,126,675 (3.52 M) | 5.09 | 9 (1 annotator, 8 prover), 139 turns | 253 / 263; 10 open (5 function goals, 5 lemmas); stopped by the run cap | 6 / 6 | off |
| `wp-run3` (Frama-C, `--max-usd 10`; **one annotator call lost to a step-0 tooling bug**) | 2894 s | 210 / 144,464 / 396,272 / 4,880,399 (5.42 M) | 7.04 | 9 (3 annotator, 6 prover), 150 turns | 234 / 249 (Qed 152, SMT 76, Coq 6); 15 open, all function goals | 5 / 6 (`noinit`: its goals already open) | frozen source PASS (26 clauses, all evaluated); patch 1 PASS (38, all evaluated); patch 2 FAIL on the mutant anchor (the bug); patch 3 FAIL: E-ACSL check fired (`\valid_read(&(*list)->ptr_to_previous)` in `add`); mutants 4/4 caught each time |
| `wp-run4` (Frama-C, `--max-usd 10`, all fixes) | 3043 s | 254 / 144,620 / 399,171 / 5,113,194 (5.66 M) | 7.11 | 11 (3 annotator, 8 prover), 191 turns | **certified 303 / 303** (Qed 173, SMT 122, Coq 8; 16 lemmas) | 6 / 6 | frozen source PASS (26 clauses, all evaluated); patch 1 PASS (46, all evaluated); patches 2-3 inconclusive: E-ACSL build failed (a ghost variable `gp`, which `gen_rac.py` drops); mutants 4/4 caught where run |
| `vst-run1` (VST agent) | 2373 s | 170 / 84,998 / 146,837 / 7,560,158 (7.79 M) | 4.39 | 1, 162 turns | all 6 functions + `semax_prog`, `Qed` | 4 / 4 tried, by script breakage | not applicable |
| `vst-run2` (VST agent, same inputs and settings, 2026-11-07) | 3566 s | 180 / 128,528 / 188,988 / 9,130,320 (9.45 M) | 5.91 | 1, 177 turns | all 6 functions + `semax_prog`, `Qed` | 4 / 4 tried, by script breakage | not applicable |

USD and tokens: `claude -p`'s JSON (`modelUsage`, API-equivalent),
summed by `summarize.py`.  Goals: the harness's WP census (Qed, SMT,
Coq).  Mutants: `check_wp.py` (WP, counting only goals the unmutated
result proves) and `check_vst.py`.  Step 0: `bench/b1a/rac/check.sh`
in the harness (ASan + UBSan, E-ACSL with the twins, coverage by
`rac/coverage.py`, the runtime mutants `vacuity`, `uaf`, `nullchk`,
`noinit`).  `wp-run3` and `wp-run4` ran one after the other on an
otherwise idle machine; `wp-run2` and `vst-run1` ran at the same time.
Rerun spending: $14.15 of the approved $20.

**vst-run2** (`../runs/q10/vst-run2/`, 2026-11-07), for variance: the
same run directory contents, prompt, tool script, flags and $15 cap as
`vst-run1`, with the fixed `run_vst.py` (the cap reserved in the
calibrated ledger first) and one more fence: Read/Write/Edit denied on
every other entry of `runs/q10/` (`vst-run1/`, its tool script and
logs, the Frama-C runs).  `check_vst.py`: clightgen + coqc pass on a
pristine `b1a.c` (the run's copy unchanged), no `Admitted`/`admit`/
`Axiom`, Print Assumptions as the smoke test; `verif_b1a.v` 821 lines
(vst-run1: 561).  Two permission denials, both a `sed -i` on its own
file.  The mutants break `body_b1` by tactic mismatch, as in vst-run1;
`nowashead` (add's post weakened to `EX s1', wlist P (s1' ++ elem ::
...)`, `body_add` skipped) breaks `body_b1` too.  Its public spec is 104
lines without boilerplate and proof-only definitions (vst-run1: 94).

*Its funspecs against vst-run1's* (read by hand): **the same strength
overall, stronger in one place, weaker in one**, all within SPEC.md.
*   Lists: vst-run2's `wlist P s` is a list of node addresses with a
    payload predicate `P` (`True` in the sglib specs, "is an int" in
    `b1`); vst-run1's is a list of (address, payload) pairs.  vst-run1
    keeps each payload's exact value across calls, vst-run2 only that it
    satisfies `P` (weaker there, and not needed for memory safety).
*   `add`: the same.  vst-run2 names the start node by its index `j`
    (`*list` is `nodeat s j`) and returns `sublist 0 j s ++ elem ::
    sublist j _ s`; vst-run1 splits the list as `s1 ++ s2` and returns
    `s1 ++ elem :: s2`.  Both give the new head when the old `*list` was
    NULL or the head.
*   Iterator: the same state (vst-run2: positions `b`, `f` and the
    owned segments `0..b`, `f..k-1`; vst-run1: `sA ++ sM ++ sB`).
    **vst-run2 is stronger on the returned node**: it is node `c` with
    `b < c < f`, owned with its exact links in `s`; vst-run1 gave the
    node with existential fields.
*   `b1`, `main`: the same (an int returned; `input` unchanged).
*   Neither states that freed nodes keep their links (separation logic
    says nothing about freed memory; not needed for safety).

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
*   **Few runs.**  Two VST runs (both proved everything: $4.39 and
    $5.91, 2373 s and 3566 s); three Frama-C runs, of which two share
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
*   `../runs/q10/vst-run2/` (git-ignored): the second VST run, with
    `budget_gate.json` and `q10-check/` (including the hand-made
    `nowashead`).
*   `../runs/q10/vst-run1/` (git-ignored): the VST run (`verif_b1a.v`,
    `result.json`, `summary.json`, `fence.json`, `q10-check/`).
