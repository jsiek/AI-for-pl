# Ariadne run: b1

**Verdict: certified.**  330 / 330 goals proved; 1412.1 s; model runs: 8.

## Goal census

| Discharger | after step 3 | final |
|---|---|---|
| qed | 186 | 186 |
| smt | 140 | 140 |
| coq | 0 | 4 |
| open | 4 | 0 |
| total | 330 | 330 |

SMT by prover: Alt-Ergo 122, CVC5 15, Z3 3.

## Steps

| Step | Seconds | Result |
|---|---|---|
| guardrails_pre | 0.9 | ok=True |
| 0_rac | 10.2 | ok=True, pass_lines=3, mutants_as_expected=0 |
| 1_normalise | 0.5 | ok=True |
| 2_eva |  | skipped: optional (plan 5.2) |
| 3_wp | 120.8 | ok=True, runs=2 |
| 4_prove | 1264.6 | tried=4, proved=4 |
| 6_close_out | 15.0 | coq_goals=4, coqc_ok=4 |

## Guardrails

| Check | Verdict |
|---|---|
| frozen_spec | pass |
| lint_acsl | pass |
| lint_ghost | pass |
| overlay | pass |
| lint_coq | pass |
| allow_list_coqchk | pass |
| allow_list_print_assumptions | pass |
| benchmark_untouched | pass |
| goal_accounting | pass |

## Proof search (tiers [0, 1, 2])

| Goal | Proved by | Seconds | Tokens | USD charged | Attempts (tier: result) |
|---|---|---|---|---|---|
| `typed_lemma_dll_frame` | tier 2 (claude-sonnet-5-5) | 326.2 | 289961 | 0.166719 | 0: open 120.2 s; 1: open 160.3 s, 68944 tok; 2: proved 45.0 s, 221017 tok |
| `typed_lemma_dll_last` | tier 2 (claude-sonnet-5-5) | 301.6 | 209406 | 0.123689 | 0: open 120.2 s; 1: open 157.7 s, 69349 tok; 2: proved 23.0 s, 140057 tok |
| `typed_lemma_dll_nth_next` | tier 2 (claude-sonnet-5-5) | 319.1 | 329373 | 0.164026 | 0: open 120.2 s; 1: open 161.1 s, 68878 tok; 2: proved 37.2 s, 260495 tok |
| `typed_lemma_dll_nth_prev` | tier 2 (claude-sonnet-5-5) | 314.4 | 302141 | 0.173355 | 0: open 120.2 s; 1: open 150.2 s, 67463 tok; 2: proved 43.4 s, 234678 tok |

## Budget

Anthropic use charged this run: $0.627789 (API-equivalent), 856247 tokens.  Ledger this week: $5.5917, 0.497% of the weekly limit (cap 20.0%, warning 15.0%), calibrated.  `/usage` weekly (all Claude Code use): 26.0% before, 26.0% after.

## Goals not closed by Qed or SMT

- `typed_lemma_dll_frame` (line 103): coq
- `typed_lemma_dll_last` (line 125): coq
- `typed_lemma_dll_nth_next` (line 117): coq
- `typed_lemma_dll_nth_prev` (line 106): coq
