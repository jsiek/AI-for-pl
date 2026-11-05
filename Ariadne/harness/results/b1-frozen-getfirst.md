# Ariadne run: b1

**Verdict: certified.**  23 / 23 goals proved; 602.0 s; model runs: 3.

## Goal census

| Discharger | after step 3 | final |
|---|---|---|
| qed | 10 | 13 |
| smt | 0 | 9 |
| coq | 0 | 1 |
| open | 6 | 0 |
| total | 16 | 23 |

SMT by prover: Alt-Ergo 8, Z3 1.

## Steps

| Step | Seconds | Result |
|---|---|---|
| guardrails_pre | 0.9 | ok=True |
| 0_rac | 16.9 | ok=True, pass_lines=6, mutants_as_expected=0, runs=2 |
| 1_normalise | 1.0 | ok=True, runs=2 |
| 2_eva |  | skipped: optional (plan 5.2) |
| 3_wp | 129.7 | ok=True, runs=3 |
| 4_prove | 289.4 | tried=1, proved=1, runs=2 |
| 5_refine | 162.0 | edits=1 |
| 6_close_out | 10.6 | coq_goals=1, coqc_ok=1 |

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
| `typed_lemma_dll_prev_nth` | tier 2 (claude-sonnet-5-5) | 283.7 | 210953 | 0.142996 | 0: open 120.2 s; 1: open 131.9 s, 56157 tok; 2: proved 31.0 s, 154796 tok |

## Refinement (step 5)

| Iteration | Call | Verdict | Turns | wp calls | Seconds | USD | Open after |
|---|---|---|---|---|---|---|---|
| 1 | claude-opus-5-5 #1 | accepted | 15 | 5 | 152.4 | 0.456508 | 1 |

## Budget

Anthropic use charged this run: $0.599504 (API-equivalent), 425847 tokens.  Ledger this week: $1.0053, 0.089% of the weekly limit (cap 20.0%, warning 15.0%), calibrated.  `/usage` weekly (all Claude Code use): 23.0% before, 24.0% after.

## Goals not closed by Qed or SMT

- `typed_lemma_dll_prev_nth` (line 102): coq
