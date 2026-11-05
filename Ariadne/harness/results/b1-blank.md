# Ariadne M2 run: b1 (Coq scripts dropped)

**Verdict: failed.**  316 / 321 goals proved; 1396.8 s; LLM calls: 0.

## Goal census

| Discharger | after step 3 | final |
|---|---|---|
| qed | 189 | 189 |
| smt | 127 | 127 |
| coq | 0 | 0 |
| open | 5 | 5 |
| total | 321 | 321 |

SMT by prover: Alt-Ergo 112, CVC5 11, Z3 4.

## Steps

| Step | Seconds | Result |
|---|---|---|
| guardrails_pre | 0.9 | ok=True |
| 0_rac | 17.9 | ok=True, pass_lines=5, mutants_as_expected=7 |
| 1_normalise | 0.5 | ok=True |
| 2_eva |  | skipped: optional (plan 5.2) |
| 3_wp | 99.1 | ok=True |
| 4_tier0 | 1278.4 | tried=5, proved=0 |
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

## Tier-0 search

| Goal | Result | Seconds | Script |
|---|---|---|---|
| `typed_lemma_all_init_cons` | open | 260.4 |  |
| `typed_lemma_all_live_cons` | open | 300.3 |  |
| `typed_lemma_dll_frame` | open | 300.8 |  |
| `typed_lemma_dll_links` | open | 300.3 |  |
| `typed_lemma_mem_cons` | open | 116.5 |  |

## Goals not closed by Qed or SMT

- `typed_lemma_all_init_cons` (line 54): open
- `typed_lemma_all_live_cons` (line 46): open
- `typed_lemma_dll_frame` (line 111): open
- `typed_lemma_dll_links` (line 94): open
- `typed_lemma_mem_cons` (line 43): open

## Failure report

Guardrails failed: goal_accounting.  Steps failed: none.  Open goals: 5 (last states in report.json).  No certificate was produced.
