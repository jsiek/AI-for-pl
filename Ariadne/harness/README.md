# Ariadne harness: the pipeline, with the prover tiers and the annotator

Plan §5 steps 0-7 on a benchmark directory (milestones M2 and M3, plan
§8).  B1 is the first benchmark: `b1.json` runs it as M1 left it,
`b1_frozen.json` from its frozen contracts only (M3, "Annotator").

```bash
cd Ariadne/harness
python3 harness.py ../bench/b1                 # B1 as M1 left it
python3 harness.py ../bench/b1 --blank-coq     # without the 5 Coq proofs
python3 harness.py ../bench/b1 --overlay my_b1.c   # an edited b1.c
python3 harness.py ../bench/b1 --blank-coq --tiers 0,1,2   # with the prover tiers
python3 budget.py show                         # the Anthropic budget ledger
python3 test_guardrails.py; python3 test_tier0.py; python3 test_harness.py
python3 test_budget.py; python3 test_tiers.py  # offline, no model calls
python3 test_annotator.py                      # offline: fake annotator
python3 harness.py ../bench/b1 --config b1_frozen.json --annotator opus \
  --prove-scope lemmas --max-iterations 3      # M3: from frozen contracts
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
| pre | guardrails 7.1-7.3a on the copy against the benchmark: frozen spec, ACSL lint, ghost lint, then overlay; a failure stops the run before any tool sees the edit | `guardrails.py` |
| 0 | runtime checking: the benchmark's `rac/check.sh` (sanitizers, E-ACSL with the twins, the mutants), pointed at the copy | config `rac` |
| 1 | `-ariadne`, RTE (`-rte-initialized @all`), `-print` into `b1.rte.c` | |
| 2 | Eva: skipped (optional in the plan) | |
| 3 | WP, one run per pass of the config (`run.sh`'s flags); `-wp-interactive update` makes WP write a Coq goal file for every goal it sends to Coq | |
| 4 | proof search on each open goal: tier 0, then tier 1 (GLM), then tier 2 (Sonnet, within the budget ledger); a proof counts once `coqc` accepts it in the real goal file; if any goal closed, step 3 again (`batch`), so WP itself confirms the scripts | `tier0.py`, `tiers.py`, `budget.py` |
| 5 | refinement: with `--annotator opus` (or `fake:LIST.json`), the annotator gets the open goals and returns a patch; the guardrails, then step 0, check it; a rejected patch goes back with the reason (`--annotator-retries`); an accepted one replaces the copy's source, and steps 1, 3 (`update`, WP's session cache reuses unchanged goals) and 4 run again, up to `--max-iterations` patches.  Without an annotator each open goal is recorded as a stall and the loop ends | `annotator.py`, `annotator_cli.py` |
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
| `lint_ghost` (7.3) | ghost code may only declare and assign ghost variables: no more ghost loops, jumps, returns, calls, `__heap` or allocator names than the baseline.  WP does not check termination here, so `//@ ghost while (1);` would make every later goal vacuous; writing `__heap` would edit the frozen liveness model | a ghost loop, `__heap = 0`, a ghost call to `ariadne_free_dllist`, a ghost `return`; a ghost declaration and assignment pass |
| `lint_coq` (7.3) | the script between `Proof.` and `Qed.` passes `prover/reallms_coq.py`'s `FORBIDDEN` (Admitted, admit, Axiom, Parameter, ...), nothing after `Qed.`, and the context is the one WP wrote | each of those, and an axiom added to the context |
| `allow_list_coqchk`, `allow_list_print_assumptions` (7.4) | every axiom is one of Rocq's classical axioms (fixed list), a `Why3.*` axiom, or declared in the WP-generated context of its own goal file (Why3 theories and the frozen spec as WP exports it) | an `Axiom cheat : False` in a goal file's context, which coqc accepts and coqchk lists |
| `goal_accounting` (7.5) | each pass has its expected goal count (or at least `{"min": n}`, the frozen-only count, once the annotator adds goals), every goal has a discharger (Qed, SMT, Coq) or is listed out of scope, and every Coq goal's script was certified in step 6 | an open goal, a shrunken selection, an uncertified Coq goal |
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
no JSON).  The reservation is held in the ledger, under its lock, from
`reserve` until `charge` (or `release`, for a call that never ran), and
every projection counts the reservations in flight, so concurrent runs
cannot pass the cap together.  A reservation older than 6 hours belongs
to a run that died and stops counting.  GLM's tokens go under `free`, uncharged.

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
`daily[].totalCost`; checked against 20.0.40's output), and stores P / cost with both inputs and the
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

## Annotator (step 5; `annotator.py`, `annotator_cli.py`, plan §12.1)

**Starting point.**  `b1_frozen.json` runs `../bench/b1/b1_frozen.c`, B1
with the frozen spec only (decisions in `../bench/b1/README.md`,
"Frozen-only variant"): the copy leaves out `b1.c`, `b1_gen.c`, the
READMEs, `mutants.py` and the human's Coq scripts, so nothing a model
can read in the run holds the human's annotations.  Step 0 runs `rac/
check.sh` on the copy's source in quick mode (`SRC`, no mutants: their
anchors are the human's annotations).  The functions pass must have at
least the frozen-only 254 goals; `--functions` cuts the selection down
(the minimum is then the sum of `function_goals`).

**Call.**  `claude -p --model claude-opus-5-5 --output-format json` in
`<run>/annotator/call<n>/`, which holds `SOURCE.c` (the current source,
or the rejected patch to fix), `TASK.md` and `ariadne_alloc.h`.
`TASK.md` (built by `Run.task`): the rules (the guardrails, in words),
the WP flags, the iteration, then the open goals grouped by function
(whose frozen contract is in `SOURCE.c`) and line, each with step 4's
prover reports (tier, result, Sonnet's last words), WP's text of each
open goal (`-wp-status` in step 3's log, as `Goal ... Prove: ...`), the
rejection reason if any, and one line per earlier iteration.  The fence
is tier 2's: `--safe-mode --restricted`, `--tools Bash,Read,Write,Edit`,
`--allowedTools` only `python3 annotator_cli.py check SOURCE.c`, `...
wp SOURCE.c *` and Read/Write/Edit in its directory, `Bash(git *)`
denied, `--permission-mode dontAsk`, `GIT_DIR` and
`GIT_CEILING_DIRECTORIES` set.  Caps per call: `--opus-usd`
(`--max-budget-usd`, reserved in the ledger first under the
`annotator` role and released if the call never runs), `--opus-turns`,
`--opus-seconds`, `--opus-wp-calls` (`annotator_cli.py` refuses more).

**Its oracle** (`annotator_cli.py`): `check` runs the guardrails against
the frozen baseline; `wp FUNCTION|lemmas` runs them and, only if they
pass, WP with Alt-Ergo, CVC5 and Z3 (20 s each, no Coq) on that target,
and prints the census and WP's text of each open goal.

**The patch** is the `SOURCE.c` the call leaves.  The harness checks it
again (`patch_checks`: frozen spec, ACSL lint, ghost lint, then the
overlay), then runs step 0 on it; a rejection goes back with the reason
(guardrail verdicts with hints, or the failing E-ACSL check) and the
copy keeps its last accepted source.  The same `SOURCE.c` returned, or
a budget refusal, ends refinement.  Step 4 skips a goal whose goal file
is byte-identical to one it already failed on, and `--prove-scope
lemmas` keeps the prover tiers to lemma goals, so function goals go
straight to the annotator (plan §12.3 S5).

**Offline tests** (`test_annotator.py`, patches from `fake_patches.py`,
`get_first` only, no model): a good patch (the human's `get_first`
annotations and lemmas) is accepted and only the five lemmas M1 proved
in Coq stay open; a weakened frozen precondition, an added predicate
and a ghost loop are each rejected by the guardrails before Frama-C,
and a false loop invariant by step 0 (E-ACSL), each reason reaching the
next call and WP running once; an annotator adding useless asserts
stops at `--max-iterations`.  Plus the command's fence and a fake
`claude` charged to the `annotator` role.

### One function: `get_first` from its frozen contract (`results/b1-frozen-getfirst.md`)

`--functions sglib_dllist_get_first --prove-scope lemmas --tiers 0,1,2
--annotator opus`: **certified, 23/23 goals** (Qed 13, Alt-Ergo 8, Z3
1, Coq 1) in 602 s and **one iteration**.  Before the patch 6 of 16
goals were open (the loop body's accesses, `assigns`, `heads_list`).
Opus 5.5 took 152 s, 15 turns and 5 `wp` calls, **$0.46**; it wrote
(`results/b1-frozen-getfirst-patch1.c`) a loop invariant (`_dll_` and
`list` are both nodes of one live list from NULL), `loop assigns _dll_`,
and four lemmas: `dll_head`, `dll_prev_head` and `dll_inv`, proved by
SMT, and `dll_prev_nth` (node j's `ptr_to_previous` is node j-1), which
needs induction: tier 0 and GLM missed it, **Sonnet proved it for
$0.14** (`results/b1-frozen-getfirst-lemma_dll_prev_nth.v`), coqc,
WP's rerun, coqchk and Print Assumptions accepted it.  Opus's one
attempt outside its fence (a `grep` in `harness/`) was denied.

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

### Pilot: GLM then Sonnet (`--blank-coq --tiers 1,2`, `results/b1-blank-tiers.md`)

**Certified, 321/321**: Qed 189, SMT 127, Coq 5, all five Coq proofs
written by the prover tiers, rechecked by coqc and counted by WP's rerun.
Total 939 s, of which the proof step took 734 s.

| Lemma | GLM 5.3 Flash (2 min) | Sonnet 5.5 | Proved by |
|---|---|---|---|
| `mem_cons` | proved, 69 s, 8 turns, 47k tokens | - | GLM |
| `all_live_cons` | proved, 59 s, 4 turns, 37k | - | GLM |
| `all_init_cons` | stopped at 127 s, 82k | proved, 15 s, $0.10 | Sonnet |
| `dll_frame` | stopped at 160 s, 54k | proved, 27 s, $0.14 | Sonnet |
| `dll_links` | stopped at 207 s, 70k | proved, 62 s, $0.17 | Sonnet |

Sonnet's total: $0.41 API-equivalent, 409k tokens, 0.036% of the weekly
limit by the ledger's calibration (0.089% per USD: `/usage` showed 23%
against ccusage's $258.54 since the reset).  GLM's 2 minutes overrun by
up to 87 s because the reply in flight finishes.  GLM is not consistent
across runs: here it proved `all_live_cons` (506 s in the prover trial)
and missed `all_init_cons` (57 s there).
