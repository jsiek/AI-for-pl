# M2 harness: the pipeline without an LLM

Plan §5 steps 0-7 on a benchmark directory, with no model calls
(milestone M2, plan §8).  B1 is the first benchmark (`b1.json`).

```bash
cd Ariadne/harness
python3 harness.py ../bench/b1                 # B1 as M1 left it
python3 harness.py ../bench/b1 --blank-coq     # without the 5 Coq proofs
python3 harness.py ../bench/b1 --overlay my_b1.c   # an edited b1.c
python3 harness.py ../bench/b1 --blank-coq --tiers 0,1,2   # with the prover tiers
python3 budget.py show                         # the Anthropic budget ledger
python3 test_guardrails.py; python3 test_tier0.py; python3 test_harness.py
python3 test_budget.py; python3 test_tiers.py  # offline, no model calls
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
| 4 | proof search on each open goal: tier 0, then tier 1 (GLM), then tier 2 (Sonnet, within the budget ledger); a proof counts once `coqc` accepts it in the real goal file; if any goal closed, step 3 again (`batch`), so WP itself confirms the scripts | `tier0.py`, `tiers.py`, `budget.py` |
| 5 | refinement: a **stub**; each open goal is recorded as a stall with its statement as the last state, and the loop ends (no annotator in M2) | |
| 6 | for every goal Coq closed: Coq lint, `coqc`, one `coqchk -o` over all modules, `Print Assumptions wp_goal`, axioms against the allow-list | |
| 7 | caps (`--max-iterations`, `--max-seconds`); verdict `certified` only if every guardrail passed and every goal is accounted for; otherwise a failure report (open goals with their last state) and the `cert/` directory is deleted | |

Output: `report.json` (census, every goal with its discharger, seconds per
step, guardrail verdicts, step 4's attempts per goal and tier with
seconds, tokens and USD, the budget, stalls), `report.md` (a short
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

## Prover tiers 1 and 2 (`tiers.py`, plan §12.2)

`--tiers` (default `0,1,2`) picks the tiers; `--goals REGEX` limits step
4 to some goals.  On each goal tier 0 leaves open, `tiers.chain` runs
the next tier until one's proof is confirmed: no forbidden command
(`reallms_coq.FORBIDDEN`) and `coqc` accepts the real goal file with it
(then it is written there and WP reruns).  Every tier gets at most the
time left under `--max-seconds`.

| Tier | How | Per-goal cap | Charged |
|---|---|---|---|
| 1 | `../prover/reallms_coq.py --blank` (GLM 5.3 Flash on REALLMS); `--hide` makes `read_file`/`grep` refuse other runs, `prover/results`, `harness/results` and every benchmark's `session/` (they hold proofs of the same goals), except the run's own copy | `--glm-seconds` 120 of working time | no: tokens logged as free |
| 2 | headless Claude Code: `claude -p --model claude-sonnet-5-5 --output-format json` in `<run>/tier2/<goal>/`, which holds only `GOAL.v` (the statement, no proof) | `--sonnet-calls` 30 `goals`/`check` calls (`prover_cli.py` refuses more), `--sonnet-turns` 60, `--sonnet-seconds` 600, `--sonnet-usd` 1 (`--max-budget-usd`) | yes, in the ledger |

Tier 2's fence: `--safe-mode` (no CLAUDE.md, skills, plugins, hooks,
MCP), `--restricted` (user and project settings ignored, file tools
confined to the working directory), `--tools Bash,Read,Write,Edit`,
`--allowedTools` with the four `python3 prover_cli.py
statement|query|goals|check GOAL.v [SCRIPT.v]` forms and Read/Write/Edit
under the work directory, `--disallowedTools "Bash(git *)"`,
`--permission-mode dontAsk` (anything else is denied, not asked).  The
git rule matters: Claude Code otherwise runs read-only git commands
unasked, and the history holds the benchmark's proofs; `GIT_DIR` and
`GIT_CEILING_DIRECTORIES` fence git a second time.  A probe with Haiku
confirmed it: the four commands and Write in the directory ran; `cat
/etc/hostname`, `ls ..`, a Read of `bench/b1/b1.c`, `git log`, `git -C
.. show` and a compound command were denied.

The JSON result's fields used: `modelUsage.<model>.{inputTokens,
outputTokens, cacheCreationInputTokens, cacheReadInputTokens, costUSD}`
(else `usage.{input_tokens, output_tokens, cache_creation_input_tokens,
cache_read_input_tokens}` and `total_cost_usd`), `subtype`, `num_turns`,
`result`, `permission_denials`.

**End to end on `mem_cons`** (`--blank-coq --no-rac --goals mem_cons`,
one run each): tier 1 alone, GLM used its 120 s (45 steps, 613k tokens,
free) without a proof; tier 2 alone, Sonnet proved it in 9.6 s (4
turns, 1 `check` call, 47.6k tokens, $0.080 API-equivalent, no
permission denials); `coqc` accepted it, the WP rerun counted the goal
as Coq-proved, and step 6 certified it (coqchk and Print Assumptions on
the allow-list).

## Budget ledger (`budget.py`, plan §11 item 3)

`../runs/budget.json` (git-ignored; `--ledger` for another) keeps the
Anthropic spending since the last weekly reset, per role (prover,
annotator) and per model: calls, the four token counts and the
API-equivalent USD.  **The unit is USD**: token totals are dominated by
cache reads, which cost about a tenth of other input, so cost tracks
the limit better.  Before each tier-2 call `reserve` takes the call's
cap (`--sonnet-usd`) and refuses if the week would pass the cap; the
refusal goes into the ledger and the report, the run stops asking
Claude (`cap_hit: budget`), and the goal stays open.  After the call
`charge` books its reported cost (or its cap, if it was killed or gave
no JSON).  GLM's tokens go under `free`, uncharged.

Percent of the weekly limit = USD x `pct_per_usd`.  Cap 20%, warning at
15% (in the report).  **Until calibrated, `pct_per_usd` is a placeholder
of 2% per USD** (the cap is then $10, about 100 goals at `mem_cons`'s
cost), and the report says so.  Calibrate with

```bash
python3 budget.py calibrate --percent P --since YYYY-MM-DD
```

where P is `/usage`'s "Current week (all models)" and the date is the
last weekly reset: it runs `npx -y ccusage@20.0.40 claude daily --since
YYYYMMDD --breakdown --json`, takes `totals.totalCost` (else the sum of
`daily[].totalCost`; these names are not yet checked against this version's output), and stores P / cost with both inputs and the
date.  ccusage covers all Claude Code use on this machine, the owner's
interactive sessions included, which is what the weekly limit counts;
it counts by day, so the reset day is counted whole.  The ledger's own
totals stay separate.

**The weekly % is readable programmatically**: `claude -p /usage
--output-format json` is a local command (`num_turns` 0, no tokens)
whose `result` text has "Current week (all models): N% used · resets
<date> (<zone>)".  `budget.weekly_usage()` parses it; the harness
records a reading before and after step 4 when tier 2 runs, and its
reset time becomes the ledger's `resets_at`; at `resets_at` the week's
totals move to `past_weeks`.  It is an integer % of all use, so it
cannot see one goal (23% before and after the `mem_cons` run).

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
