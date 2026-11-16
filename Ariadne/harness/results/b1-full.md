# Ariadne M2 run: b1

**Verdict: certified.**  321 / 321 goals proved; 74.8 s; LLM calls: 0.

## Goal census

| Discharger | after step 3 | final |
|---|---|---|
| qed | 189 | 189 |
| smt | 127 | 127 |
| coq | 5 | 5 |
| open | 0 | 0 |
| total | 321 | 321 |

SMT by prover: Alt-Ergo 112, CVC5 10, Z3 5.

## Steps

| Step | Seconds | Result |
|---|---|---|
| guardrails_pre | 0.9 | ok=True |
| 0_rac | 18.1 | ok=True, pass_lines=5 |
| 1_normalise | 0.5 | ok=True |
| 2_eva |  | skipped: optional (plan 5.2) |
| 3_wp | 39.3 | ok=True |
| 6_close_out | 16.0 | coq_goals=5, coqc_ok=5 |

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

## Goals not closed by Qed or SMT

- `typed_lemma_all_init_cons` (line 54): coq
- `typed_lemma_all_live_cons` (line 46): coq
- `typed_lemma_dll_frame` (line 111): coq
- `typed_lemma_dll_links` (line 94): coq
- `typed_lemma_mem_cons` (line 43): coq
