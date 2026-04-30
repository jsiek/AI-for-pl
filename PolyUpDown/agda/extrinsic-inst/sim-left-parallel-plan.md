# `sim-left` Parallelization Plan (12 Workers)

This plan is for the holes in `sim-left` inside `SimLeft.agda`, using
`SimLeftLemmas.agda` as the shared helper location.

## Scope

- Main target theorem: `sim-left` in `SimLeft.agda` (line range around 67-509).
- Hole count in `sim-left` right now: 41.

## Conflict-avoidance protocol

1. Each worker owns only the hole IDs listed in the assignment table.
2. Workers do not reorder clauses, add imports, or reformat outside owned lines.
3. New helper lemmas go only in `SimLeftLemmas.agda` under that worker's slot.
4. Helper names must use prefix `sim-left-wXX-...` where `XX` is worker id.
5. Every helper should include a short comment listing the hole IDs it serves.
6. Each worker should run
   `agda -v0 -i PolyUpDown/agda/extrinsic-inst -i PolyUpDown/agda PolyUpDown/agda/extrinsic-inst/SimLeft.agda`
   before handoff.
7. If a worker cannot finish a hole, add a blocked comment directly below that
   hole (`{!!}`) explaining the blocker and attempted helper lemmas.

### Blocked-hole comment format

Use a multi-line Agda comment in this exact shape:

`{- BLOCKED[WXX][HYY]:`
`   <full blocker reason, one or more lines>`
`-}`

## Hole IDs (current snapshot)

- H01: 118
- H02: 127
- H03: 145
- H04: 156
- H05: 163
- H06: 170
- H07: 173
- H08: 184
- H09: 191
- H10: 198
- H11: 205
- H12: 216
- H13: 223
- H14: 230
- H15: 237
- H16: 261
- H17: 268
- H18: 279
- H19: 286
- H20: 293
- H21: 326
- H22: 360
- H23: 374
- H24: 383
- H25: 442
- H26: 474
- H27: 483
- H28: 485
- H29: 487
- H30: 489
- H31: 491
- H32: 493
- H33: 495
- H34: 497
- H35: 499
- H36: 501
- H37: 503
- H38: 506
- H39: 507
- H40: 508
- H41: 509

These `HYY` ids are stable only for this snapshot of the file. The line numbers
will shift as holes are filled or clauses are edited.

## Worker assignment sheet (12 workers)

- W01: H01-H04 (118, 127, 145, 156) - `ξ-·₂` and early `ξ-·α` bridge cases.
- W02: H05-H08 (163, 170, 173, 184) - remaining `ξ-·α` plus start of `ξ-up`.
- W03: H09-H11 (191, 198, 205) - `ξ-up` continuation.
- W04: H12-H14 (216, 223, 230) - `ξ-down` core cases.
- W05: H15-H17 (237, 261, 268) - `ξ-down` tail and `ξ-⊕₁` transitions.
- W06: H18-H21 (279, 286, 293, 326) - `ξ-⊕₂` plus `β` down-right branch.
- W07: H22-H24 (360, 374, 383) - `β-up-∀` and `β-up-↦` wrapper branches.
- W08: H25-H27 (442, 474, 483) - `β-down-↦` wrapper branch and identity setup.
- W09: H28-H30 (485, 487, 489) - tag/untag and `δ-⊕` identity branches.
- W10: H31-H33 (491, 493, 495) - blame application/type-application branches.
- W11: H34-H37 (497, 499, 501, 503) - blame up/down/operator branches.
- W12: H38-H41 (506, 507, 508, 509) - PolyUpDown store-allocation/poly-instantiation (`β-Λ`, `β-down-∀`, `β-down-ν`, `β-up-ν`).

## Helper-lemma placement rules

- `SimLeftLemmas.agda` has explicit "Worker WXX helper slot" sections.
- Workers append helpers only in their own slot.
- If a helper is cross-cutting, define it in W12 slot with prefix
  `sim-left-w12-shared-...` and mention all consuming hole IDs.

## Merge strategy

1. Merge W01-W06 first (congruence family and basic `β` flow).
2. Merge W07-W09 second (`β-up-*`/`β-down-*` wrappers and identity/tag cases).
3. Merge W10-W12 third (blame family and poly/store-allocation leaves).
4. Run a full `SimLeft.agda` check after each wave.

## Hole ID stability policy

- Do not reassign an existing `HYY` once workers start.
- If a hole is solved, keep its `HYY` reserved in the tracker as "done".
- If new holes appear, append new IDs (`H42+`) instead of renumbering old ones.
- Use both `(HYY, current line)` when reporting status; line is expected to drift.
