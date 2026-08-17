LG-3z assembly resister: structural factories after views/fuel surface

Status: STOPPED on a live paired active-cast endpoint/factory assembly
resister, after the two requested preparatory residuals checked.

Checked LG-3z chunk, 2026-08-17:

- `proof/DGG/CastConsistencyViews.agda` now exposes function-ground tag and
  projection views, plus universal-ground tag and projection views.  The
  universal views are intentionally not exact `∀` inversions: they carry the
  `inst`/`gen` and `bot` alternatives that make plain universal inversion
  invalid in the live imprecision relation.
- `proof/DGG/Catchup/FuelKnotProof.agda` now has the private structural fuel
  surface:
  - `StructuralFuelStepSurface`;
  - `smaller-structural-extra`;
  - `smaller-inst : ... -> StructuralInstCatchupRightAt`;
  - `smaller-structural-value`.
  It also has `StructuralFuelKnot` internally and erases through
  `erase-structural-fuel-step` / `erase-structural-fuel-knot` at the public
  `FuelStepSurface` / `FuelKnot` boundary.

Gate:

```text
cd GTSFImp && AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home make check
```

Result:

```text
agda --safe -v0 All.agda
agda -v0 LegacyAll.agda
postulate-check: OK (no postulates; NON_COVERING at legacy baseline)
```

Committed as:

```text
a303d5ea LG-3 add ground-family views and structural fuel surface
```

Remaining assembly resister:

The concrete `StructuralExtraCastFactory` dispatcher cannot be completed by
only plumbing the new views into the current checked paired active rows.  The
row/factory boundary still asks the dispatcher for endpoint witnesses that are
not uniformly produced by "invert the final `q`" at the current row shapes.

The relevant checked row signatures in `ExtraCastRightAtProof.agda` are:

- `structural-paired-ground-extra-cast-right-at` requires
  `qG : C ⊑ᵂ⟨ W ⟩ G`.
- `structural-paired-project-same-extra-cast-right-at` requires
  both `qG : C ⊑ᵂ⟨ W ⟩ G` and `q : A ⊑ᵂ⟨ W ⟩ G`.
- `structural-paired-project-expand-extra-cast-right-at` requires
  `qG : C ⊑ᵂ⟨ W ⟩ G`.

For target projection expansion, `qG` is recoverable from the landed visible
tag-layer premise, not from the final post-source endpoint.  This is exactly
what the checked counterexample scratch records:

```agda
paired-expand-cell-nonempty :
  W ∣ [] ⊢²
    source-core ⟨ source-cast ⟩
    ⊑ target-star-value ⟨ target-expand-cast ⟩ ∶ qB

no-post-source-midpoint : A ⊑ᵂ⟨ W ⟩ G → ⊥
```

The same scratch also shows the multi-step landing relation that avoids the
refuted post-source midpoint:

```agda
paired-expand-end-relation :
  W ∣ [] ⊢²
    source-core ⟨ source-cast ⟩
    ⊑ target-ground-core ⟨ target-residual ⟩ ∶ qB
```

So the remaining factory step is not a stale import or a missing view
constructor.  It needs one of the following checked interfaces before the
dispatcher can be total:

1. a landed-tag premise extractor that returns the peeled core relation and
   its `C ⊑ᵂ⟨ W ⟩ G` endpoint for the paired projection rows, threaded through
   the same source-wrapper/lambda cases as `target-id-step-inversion`; and
2. a paired ground row/dispatcher split that handles source inert ground-family
   cases at the endpoint actually derivable from the final `q`, without
   requiring the refuted post-source midpoint and without changing
   `CastTermImprecision2`.

No protected relation or surface was changed.  In particular,
`GTSF/QuotientedTermImprecision.agda`, `CastTermImprecision2.agda`, and
`PLAN.md` were not edited.
