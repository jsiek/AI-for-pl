# `sim-left` Parallelization Plan (12 Workers)

This plan is for the holes in `sim-left` inside `DGGSim.agda`, using
`SimLeftLemmas.agda` as the shared helper location.

## Scope

- Main target theorem: `sim-left` in `DGGSim.agda` (line range around 111-536).
- Hole count in `sim-left` right now: 47.
- `sim-left*` at line 559 is intentionally out of scope for this sheet.

## Conflict-avoidance protocol

1. Each worker owns only the hole lines listed in the assignment table.
2. Workers do not reorder clauses, add imports, or reformat outside owned lines.
3. New helper lemmas go only in `SimLeftLemmas.agda` under that worker's slot.
4. Helper names must use prefix `sim-left-wXX-...` where `XX` is worker id.
5. Every helper should include a short comment listing the hole lines it serves.
6. Each worker should run `agda -i PolyUpDown/agda PolyUpDown/agda/extrinsic-inst/DGGSim.agda` before handing off.
7. If a worker cannot finish a hole, add a short comment directly below that
   hole (`{!!}`) explaining the blocker and naming attempted lemmas/helpers.

### Blocked-hole comment format

Use this exact shape under the hole:

`-- BLOCKED[WXX][HYY]: <one-line reason>. Tried: <lemma1>, <lemma2>.`

## Hole IDs

- H01: 134
- H02: 141
- H03: 149
- H04: 163
- H05: 172
- H06: 190
- H07: 201
- H08: 208
- H09: 215
- H10: 218
- H11: 229
- H12: 236
- H13: 243
- H14: 250
- H15: 261
- H16: 268
- H17: 275
- H18: 282
- H19: 293
- H20: 300
- H21: 307
- H22: 318
- H23: 325
- H24: 332
- H25: 365
- H26: 399
- H27: 413
- H28: 422
- H29: 465
- H30: 474
- H31: 506
- H32: 508
- H33: 510
- H34: 512
- H35: 514
- H36: 516
- H37: 518
- H38: 520
- H39: 522
- H40: 524
- H41: 526
- H42: 528
- H43: 530
- H44: 533
- H45: 534
- H46: 535
- H47: 536

These `HYY` ids are stable only for this snapshot of the file. The line numbers
will shift as holes are filled or clauses are edited.

## Worker assignment sheet

- W01: H01-H04 (lines 134, 141, 149, 163); focus on `ξ-·₁` and first `ξ-·₂` bridge.
- W02: H05-H08 (lines 172, 190, 201, 208); finish `ξ-·₂` and start `ξ-·α`.
- W03: H09-H12 (lines 215, 218, 229, 236); finish `ξ-·α`, start `ξ-up`.
- W04: H13-H16 (lines 243, 250, 261, 268); finish `ξ-up`, start `ξ-down`.
- W05: H17-H20 (lines 275, 282, 293, 300); finish `ξ-down`, start `ξ-⊕₁`.
- W06: H21-H24 (lines 307, 318, 325, 332); finish `ξ-⊕₁` and `ξ-⊕₂`.
- W07: H25-H28 (lines 365, 399, 413, 422); `β`, `β-up-∀`, `β-up-↦` simulation branches.
- W08: H29-H32 (lines 465, 474, 506, 508); `β-down-↦` and first identity cases.
- W09: H33-H36 (lines 510, 512, 514, 516); seal/tag/delta branches.
- W10: H37-H40 (lines 518, 520, 522, 524); blame propagation branches (application/type/up).
- W11: H41-H44 (lines 526, 528, 530, 533); blame branches plus `β-Λ`.
- W12: H45-H47 (lines 534, 535, 536); PolyUpDown-specific `β-down-∀`, `β-down-ν`, `β-up-ν`.

## Helper-lemma placement rules

- `SimLeftLemmas.agda` now has explicit "Worker WXX helper slot" sections.
- Workers should append helpers only in their own slot.
- If a helper is clearly cross-cutting, define it in W12 slot with prefix
  `sim-left-w12-shared-...` and mention all consuming hole IDs.

## Merge strategy

1. Merge W01-W06 first (congruence families).
2. Merge W07-W08 second (beta family catchup flows).
3. Merge W09-W12 third (identity/blame/poly-instantiation leaves).
4. Run a full `DGGSim.agda` check after each wave.

## Hole ID stability policy

- Do not reassign an existing `HYY` once workers start.
- If a hole is solved, keep its `HYY` reserved in the tracker as "done".
- If new holes appear, append new IDs (`H48+`) instead of renumbering old ones.
- Use both `(HYY, current line)` when reporting status; line is expected to drift.
