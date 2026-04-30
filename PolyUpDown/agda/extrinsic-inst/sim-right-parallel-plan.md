# `sim-right` Parallelization Plan (12 Workers)

This plan is for `sim-right` in `SimRight.agda`, using
`SimRightLemmas.agda` as the shared helper location.

## Scope

- Main target theorem: `sim-right` in `SimRight.agda` (line range around 28-100).
- Hole count in `sim-right` right now: 28.
- Out of scope: `sim-right*` in `DGGSim.agda` (keep as integration target only).

## Conflict-avoidance protocol

1. Each worker owns only the hole lines listed in the assignment table.
2. Workers do not reorder clauses, add imports, or reformat outside owned lines.
3. New helper lemmas go only in `SimRightLemmas.agda` under that worker's slot.
4. Helper names must use prefix `sim-right-wXX-...` where `XX` is worker id.
5. Every helper should include a short comment listing the hole lines it serves.
6. Each worker should run
   `agda -v0 -i PolyUpDown/agda/extrinsic-inst -i PolyUpDown/agda PolyUpDown/agda/extrinsic-inst/SimRight.agda`
   before handoff.
7. If a worker cannot finish a hole, add a short comment directly below that
   hole (`{!!}`) explaining the blocker and naming attempted lemmas/helpers.

### Blocked-hole comment format

Use this exact shape under the hole:

`-- BLOCKED[WXX][RYY]: <one-line reason>. Tried: <lemma1>, <lemma2>.`

## Hole IDs

- R01: 45
- R02: 47
- R03: 49
- R04: 51
- R05: 53
- R06: 55
- R07: 57
- R08: 59
- R09: 61
- R10: 63
- R11: 65
- R12: 67
- R13: 69
- R14: 71
- R15: 73
- R16: 75
- R17: 77
- R18: 81
- R19: 83
- R20: 85
- R21: 87
- R22: 89
- R23: 91
- R24: 93
- R25: 95
- R26: 97
- R27: 99
- R28: 101

These `RYY` ids are stable only for this snapshot of the file. The line numbers
will shift as holes are filled or clauses are edited.

## Worker assignment sheet (12 workers)

- W01: R01-R03 (45, 47, 49) - early raw beta cases.
- W02: R04-R06 (51, 53, 55) - remaining raw cast-id cases.
- W03: R07-R09 (57, 59, 61) - seal/tag raw cases.
- W04: R10-R12 (63, 65, 67) - delta and blame application raw cases.
- W05: R13-R15 (69, 71, 73) - blame type/cast/raw cases.
- W06: R16-R18 (75, 77, 81) - end raw blame + `β-Λ`.
- W07: R19-R20 (83, 85) - `β-down-∀`, `β-down-ν`.
- W08: R21-R22 (87, 89) - `β-up-ν`, `ξ-·₁`.
- W09: R23-R24 (91, 93) - `ξ-·₂`, `ξ-·α`.
- W10: R25-R26 (95, 97) - `ξ-up`, `ξ-down`.
- W11: R27 (99) - `ξ-⊕₁`.
- W12: R28 (101) - `ξ-⊕₂` and shared helper cleanup.

## Helper-lemma placement rules

- `SimRightLemmas.agda` has explicit "Worker WXX helper slot" sections.
- Workers append helpers only in their own slot.
- If a helper is cross-cutting, define it in W12 slot with prefix
  `sim-right-w12-shared-...` and mention all consuming hole IDs.

## Merge strategy

1. Merge W01-W06 first (raw non-store-allocating cases).
2. Merge W07-W10 second (allocation and congruence core cases).
3. Merge W11-W12 third (final operator branches and shared helper cleanup).
4. Run a full `SimRight.agda` check after each wave.

## Hole ID stability policy

- Do not reassign an existing `RYY` once workers start.
- If a hole is solved, keep its `RYY` reserved in the tracker as "done".
- If new holes appear, append new IDs (`R29+`) instead of renumbering old ones.
- Use both `(RYY, current line)` when reporting status; line is expected to drift.
