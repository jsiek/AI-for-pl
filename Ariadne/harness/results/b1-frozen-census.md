# Ariadne M2 run: b1

**Verdict: failed.**  206 / 254 goals proved; 320.4 s; model runs: 0.

## Goal census

| Discharger | after step 3 | final |
|---|---|---|
| qed | 158 | 158 |
| smt | 48 | 48 |
| coq | 0 | 0 |
| open | 48 | 48 |
| total | 254 | 254 |

SMT by prover: Alt-Ergo 46, CVC5 2.

## Steps

| Step | Seconds | Result |
|---|---|---|
| guardrails_pre | 0.9 | ok=True |
| 0_rac | 8.6 | ok=True, pass_lines=3, mutants_as_expected=0 |
| 1_normalise | 0.5 | ok=True |
| 2_eva |  | skipped: optional (plan 5.2) |
| 3_wp | 310.4 | ok=True |
| 5_refine | 0.0 | edits=0 |
| 6_close_out | 0.0 | coq_goals=0, coqc_ok=0 |

## Guardrails

| Check | Verdict |
|---|---|
| overlay | pass |
| frozen_spec | pass |
| lint_acsl | pass |
| lint_coq | pass |
| benchmark_untouched | pass |
| goal_accounting | FAIL |

## Goals not closed by Qed or SMT

- `typed_b1_assert_rte_initialization` (line 683): open
- `typed_b1_assert_rte_initialization_2` (line 686): open
- `typed_b1_assert_ariadne_live_2` (line 688): open
- `typed_b1_assert_rte_initialization_5` (line 688): open
- `typed_b1_assert_rte_mem_access_2` (line 688): open
- `typed_b1_assert_rte_initialization_8` (line 691): open
- `typed_b1_assert_rte_initialization_9` (line 691): open
- `typed_b1_assert_ariadne_live_3` (line 692): open
- `typed_b1_assert_rte_initialization_11` (line 692): open
- `typed_b1_assert_rte_mem_access_3` (line 692): open
- `typed_b1_assert_rte_initialization_13` (line 691): open
- `typed_b1_assert_rte_mem_access_4` (line 691): open
- `typed_b1_assert_rte_initialization_14` (line 693): open
- `typed_b1_assert_rte_initialization_15` (line 693): open
- `typed_b1_assert_ariadne_live_5` (line 695): open
- `typed_b1_assert_rte_initialization_17` (line 695): open
- `typed_b1_assert_rte_mem_access_5` (line 695): open
- `typed_b1_assert_rte_initialization_19` (line 694): open
- `typed_b1_assert_rte_mem_access_6` (line 694): open
- `typed_b1_assert_rte_initialization_20` (line 696): open
- `typed_b1_assert_rte_initialization_21` (line 696): open
- `typed_b1_assert_rte_initialization_23` (line 701): open
- `typed_b1_call_sglib_dllist_add_requires` (line 689): open
- `typed_b1_call_sglib_dllist_add_requires_3` (line 689): open
- `typed_b1_call_sglib_dllist_get_first_requires` (line 691): open
- `typed_b1_call_sglib_dllist_get_last_requires` (line 693): open
- `typed_b1_call_sglib_dllist_it_init_requires` (line 696): open
- `typed_b1_call_sglib_dllist_it_init_requires_2` (line 696): open
- `typed_b1_call_ariadne_free_dllist_requires_freeable` (line 699): open
- `typed_b1_call_sglib_dllist_it_next_requires` (line 697): open
- `typed_b1_call_sglib_dllist_it_next_requires_2` (line 697): open
- `typed_b1_call_sglib_dllist_it_next_requires_3` (line 697): open
- `typed_b1_call_sglib_dllist_it_next_requires_4` (line 697): open
- `typed_sglib_dllist_add_ensures_2` (line 132): open
- `typed_sglib_dllist_get_first_ensures_heads_list` (line 422): open
- `typed_sglib_dllist_get_first_assert_ariadne_live` (line 433): open
- `typed_sglib_dllist_get_first_assert_rte_initialization_2` (line 433): open
- `typed_sglib_dllist_get_first_assert_rte_initialization_3` (line 433): open
- `typed_sglib_dllist_get_first_assert_rte_mem_access` (line 433): open
- `typed_sglib_dllist_get_first_assigns_part2` (line 427): open
- `typed_sglib_dllist_get_last_ensures_last_of_list` (line 444): open
- `typed_sglib_dllist_get_last_assert_ariadne_live` (line 455): open
- `typed_sglib_dllist_get_last_assert_rte_initialization_2` (line 455): open
- `typed_sglib_dllist_get_last_assert_rte_initialization_3` (line 455): open
- `typed_sglib_dllist_get_last_assert_rte_mem_access` (line 455): open
- `typed_sglib_dllist_get_last_assigns_part2` (line 449): open
- `typed_sglib_dllist_it_init_on_equal_call_sglib_dllist_it_next_requires_4` (line 613): open
- `typed_sglib_dllist_it_next_ensures` (line 639): open

## Failure report

Guardrails failed: goal_accounting.  Steps failed: none.  Open goals: 48 (last states in report.json).  No certificate was produced.
