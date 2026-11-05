# M2 harness: the pipeline without an LLM

Plan §5 steps 0-7 on a benchmark directory, with no model calls
(milestone M2, plan §8).  B1 is the first benchmark (`b1.json`).

```bash
cd Ariadne/harness
python3 harness.py ../bench/b1                 # B1 as M1 left it
python3 harness.py ../bench/b1 --blank-coq     # without the 5 Coq proofs
python3 harness.py ../bench/b1 --overlay my_b1.c   # an edited b1.c
python3 test_guardrails.py; python3 test_tier0.py; python3 test_harness.py
```

Needs the M0 image and the plugin built (`../env/run.sh dune build` in
`../plugin`).  Exit code 0 iff the verdict is `certified`.

## What a run does

A run copies the benchmark into its own directory (default
`../runs/<name>-<time>/`, git-ignored; it must be under `Ariadne/`, which
the image mounts at `/ariadne`) and works only there.  Every benchmark file
is hashed before and after; a change fails the run (`benchmark_untouched`).

| Step | What | Code |
|---|---|---|
| pre | guardrails 7.1-7.3a on the copy against the benchmark: overlay, frozen spec, ACSL lint; a failure stops the run before any tool sees the edit | `guardrails.py` |
| 0 | runtime checking: the benchmark's `rac/check.sh` (sanitizers, E-ACSL with the twins, the mutants), pointed at the copy | config `rac` |
| 1 | `-ariadne`, RTE (`-rte-initialized @all`), `-print` into `b1.rte.c` | |
| 2 | Eva: skipped (optional in the plan) | |
| 3 | WP, one run per pass of the config (`run.sh`'s flags); `-wp-interactive update` makes WP write a Coq goal file for every goal it sends to Coq | |
| 4 | tier-0 search on each open goal; if it closes any, step 3 again (`batch`), so WP itself confirms the scripts | `tier0.py` |
| 5 | refinement: a **stub**; each open goal is recorded as a stall with its statement as the last state, and the loop ends (no annotator in M2) | |
| 6 | for every goal Coq closed: Coq lint, `coqc`, one `coqchk -o` over all modules, `Print Assumptions wp_goal`, axioms against the allow-list | |
| 7 | caps (`--max-iterations`, `--max-seconds`); verdict `certified` only if every guardrail passed and every goal is accounted for; otherwise a failure report (open goals with their last state) and the `cert/` directory is deleted | |

Output: `report.json` (census, every goal with its discharger, seconds per
step, guardrail verdicts, tier-0 attempts, stalls), `report.md` (a short
summary), `logs/`, and on success `cert/` (the Coq goal files with their
`.vo`).

## Guardrails (`guardrails.py`, plan §7)

| Check | Rule | Bad inputs tested |
|---|---|---|
| `overlay` (7.1) | annotations and ghost code stripped (textually, and again by `frama-c -no-annot`), `-print` of the edited file equals the original's | a changed statement, a dropped initialiser; an added assert and ghost code pass |
| `frozen_spec` (7.2, 7.3a) | each function contract and each `predicate`/`logic`/`inductive`/`axiomatic`/`type` is hashed (comments dropped, whitespace normalised); a changed, removed or added item fails.  Lemmas are not frozen: they are proved | weakened `requires`, dropped `ensures`, `requires \false`, a changed predicate, an added predicate; an added lemma and a changed comment pass |
| `lint_acsl` (7.3) | no more `axiom`, `axiomatic`, `admit`, `logic`, `predicate`, `inductive`, `type` in the annotations than the baseline | `axiomatic` + `axiom`, `admit`, the non-terminating `logic` of `env/smoke/bad_def.c` |
| `lint_coq` (7.3) | the script between `Proof.` and `Qed.` passes `prover/reallms_coq.py`'s `FORBIDDEN` (Admitted, admit, Axiom, Parameter, ...), nothing after `Qed.`, and the context is the one WP wrote | each of those, and an axiom added to the context |
| `allow_list_coqchk`, `allow_list_print_assumptions` (7.4) | every axiom is one of Rocq's classical axioms (fixed list), a `Why3.*` axiom, or declared in the WP-generated context of its own goal file (Why3 theories and the frozen spec as WP exports it) | an `Axiom cheat : False` in a goal file's context, which coqc accepts and coqchk lists |
| `goal_accounting` (7.5) | each pass has its expected goal count, every goal has a discharger (Qed, SMT, Coq) or is listed out of scope, and every Coq goal's script was certified in step 6 | an open goal, a shrunken selection, an uncertified Coq goal |
| `benchmark_untouched` | the benchmark directory is byte-identical after the run | |

`test_harness.py` runs the harness end to end on three bad overlays (code
change, `requires \false`, `admit`): each is rejected before step 0.

Not done: the vacuity check of 7.2 (a satisfiable precondition); the
benchmark's `vacuity` mutant covers B1's spec as a whole.  Sandboxing
(7.6) is Docker's: no network is not yet enforced.

## Tier-0 search (`tier0.py`, plan §12.2 tier 0)

For one goal file, starting from the statement (any script in the file is
ignored), try a fixed list of whole scripts through Pétanque, each with
a time cap (`--tactic-seconds`, default 60), until one finishes or the
goal's cap (`--goal-seconds`, default 300) runs out.  The list:
`sauto`, `hammer`, `firstorder`, `lia`, `intuition`; for `<->` goals
`split; intros; sauto | hammer`; `unfold` of the definitions the
statement mentions, then `sauto`, `hammer`, `firstorder`, or `sauto use:`
Why3's list lemmas (`nth_zero`, `nth_cons`, `length_cons`, `length_pos`,
`length_nil`); `induction` on each list variable and on each of the
first three premises, then `sauto` / `hammer` / `sauto use:`.  The first
script Pétanque finishes is checked by `coqc`; when `hammer` succeeded,
the tactic it reconstructs is checked first.

## Results on B1 (`results/`)

| Run | Verdict | Qed | SMT | Coq | Open | Wall clock |
|---|---|---|---|---|---|---|
| `harness.py ../bench/b1` (`results/b1-full.md`) | certified | 189 | 127 | 5 (human scripts) | 0 | 75 s |
| `--blank-coq` (`results/b1-blank.md`) | failed (5 open) | 189 | 127 | 0 | 5 | 1408 s |

Seconds per step, full run / blank run: guardrails 0.9 / 0.9, RAC 18 / 18
(7 of 7 mutants caught), normalise 0.5 / 0.5, WP 39 / 99 (the five lemmas
run into the 60 s SMT timeout), tier 0 - / 1289, close out 16 / 0.  In
the full run, step 6 compiles the 5 Coq goals, `coqchk -o` lists 545
axioms over the 5 modules and `Print Assumptions` 35, all on the
allow-list.

**How much of M1 automation alone closes: 316 of 321 goals (98.4%).**
With the human's invariants, asserts and lemma statements but none of
the human's Coq scripts, Qed and SMT close everything except the five
lemmas that M1 proved in Coq, and **tier 0 closes 0 of those 5** (per-goal
cap 300 s, 15-20 candidates each; `results/b1-blank-tier0.jsonl` lists
every attempt).  `hammer` runs all four of its ATPs (Vampire, Eprover,
Z3 via `z3_tptp`, CVC4) and returns "ATPs failed to find a proof" in
22-27 s on each;
`sauto` fails fast or runs into the 60 s cap.  The three list lemmas
need the conditional Why3 lemmas `nth_cons` / `length_cons` used with
`lia` for index arithmetic, and the two induction lemmas need induction
on the `P_dll` hypothesis with case-specific reasoning: beyond the fixed
list.  These are the goals for the prover tiers 1-2 (`../prover/`: GLM
proves 4, Sonnet 5).
