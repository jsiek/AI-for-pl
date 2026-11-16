# Ariadne M2 run: b1 (Coq scripts dropped)

**Verdict: certified.**  321 / 321 goals proved; 939.2 s; model runs: 8.

## Goal census

| Discharger | after step 3 | final |
|---|---|---|
| qed | 189 | 189 |
| smt | 127 | 127 |
| coq | 0 | 5 |
| open | 5 | 0 |
| total | 321 | 321 |

SMT by prover: Alt-Ergo 112, CVC5 10, Z3 5.

## Steps

| Step | Seconds | Result |
|---|---|---|
| guardrails_pre | 0.9 | ok=True |
| 0_rac | 17.8 | ok=True, pass_lines=5, mutants_as_expected=7 |
| 1_normalise | 0.5 | ok=True |
| 2_eva |  | skipped: optional (plan 5.2) |
| 3_wp | 170.0 | ok=True, runs=2 |
| 4_prove | 733.7 | tried=5, proved=5 |
| 6_close_out | 16.1 | coq_goals=5, coqc_ok=5 |

## Guardrails

| Check | Verdict |
|---|---|
| overlay | pass |
| frozen_spec | pass |
| lint_acsl | pass |
| lint_coq | pass |
| allow_list_coqchk | pass |
| allow_list_print_assumptions | pass |
| benchmark_untouched | pass |
| goal_accounting | pass |

## Proof search (tiers [1, 2])

| Goal | Proved by | Seconds | Tokens | USD charged | Attempts (tier: result) |
|---|---|---|---|---|---|
| `typed_lemma_all_init_cons` | tier 2 (claude-sonnet-5-5) | 142.6 | 183829 | 0.10419 | 1: open 127.2 s, 81715 tok; 2: proved 14.7 s, 102114 tok |
| `typed_lemma_all_live_cons` | tier 1 (glm-5.3-flash) | 60.0 | 37453 | 0 | 1: proved 59.4 s, 37453 tok |
| `typed_lemma_dll_frame` | tier 2 (claude-sonnet-5-5) | 188.1 | 223091 | 0.136247 | 1: open 160.1 s, 54260 tok; 2: proved 27.3 s, 168831 tok |
| `typed_lemma_dll_links` | tier 2 (claude-sonnet-5-5) | 269.4 | 208887 | 0.165314 | 1: open 207.0 s, 70441 tok; 2: proved 61.8 s, 138446 tok |
| `typed_lemma_mem_cons` | tier 1 (glm-5.3-flash) | 70.0 | 47377 | 0 | 1: proved 69.4 s, 47377 tok |

## Budget

Anthropic use charged this run: $0.405751 (API-equivalent), 409391 tokens.  Ledger this week: $0.4058, 0.036% of the weekly limit (cap 20.0%, warning 15.0%), calibrated.  `/usage` weekly (all Claude Code use): 23.0% before, 23.0% after.

## Goals not closed by Qed or SMT

- `typed_lemma_all_init_cons` (line 54): coq
- `typed_lemma_all_live_cons` (line 46): coq
- `typed_lemma_dll_frame` (line 111): coq
- `typed_lemma_dll_links` (line 94): coq
- `typed_lemma_mem_cons` (line 43): coq
