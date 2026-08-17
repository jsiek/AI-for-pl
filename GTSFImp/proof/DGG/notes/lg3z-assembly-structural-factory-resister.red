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

LG-3aa postscript, 2026-08-17:

The final assembly attempt used the required holes-first method on the
concrete `structural-extra-cast-right-at` head dispatcher, then reverted the
diagnostic worker edit to keep the live tree green.  The diagnostic reached the
approved I1/I2 boundary and did not produce a complete inhabitant inventory.

The direct paired-ground endpoint test was:

```agda
qG = target-ground-cast-witness {W = W} {G = G}
       Gᵍ Ans c p ?
```

Agda reduces the remaining premise to the pre-source midpoint
`C ⊑ᵂ⟨ W ⟩ ★`.  That is exactly the midpoint that I2 forbids using
uniformly: the row must be split by the source inert family and call a row
whose endpoint is derivable from the final `q`.

Complete residual list from this attempt:

1. I1, landed-tag premise extractor: not landed.  The paired projection rows
   still need a checked extractor that takes the whole relation
   `W ∣ γ ⊢² M ⊑ M′ ⟨ ？ c ⟩ ∶ q`, uses target typing plus `canonical-★` to
   expose `M′ = N ⟨ _! (idᵍ Gᵍ) ⟩`, and threads the peeled premise/core
   through the same `cast⊑²`, `Λ⊑²`, `Λ⊑²-smart-comma`, `reveal⊑²`, and
   `conceal⊑²` source-wrapper cases as `target-id-step-inversion`.
2. I2, paired ground row/dispatcher split: not landed.  The existing checked
   row `structural-paired-ground-extra-cast-right-at` requires
   `qG : C ⊑ᵂ⟨ W ⟩ G`; the obvious `target-ground-cast-witness` route asks for
   `C ⊑ᵂ⟨ W ⟩ ★`.  The remaining implementation must add per-source-inert
   rows/endpoints, using `⇒⊑★-inv`, `⇒⊑⇒-inv`, and the ground-family cast
   views, rather than forcing that midpoint.
3. Extra-cast head dispatcher: not landed.  After the inert/id/bot rows, the
   remaining target-head cells are active ground, source-wrapper recursion for
   active ground, projection same, projection expand, target `inst`, and target
   `gen`.  `gen` should be an inert row once `gen-safe` is threaded; `inst`
   should call the structural inst worker in the direct target-cast case, but
   still needs the paired/source-wrapper dispatch.
4. `StructuralValueCatchupRightAt`: not landed.  The row combinators for
   target casts are checked, but the derivation-primary worker over
   `TargetCastBound` is still absent.  The source-`Λ` rows must use the landed
   `SourceΛReplayStack` plumbing rather than naive child-result unlift.
5. Concrete structural factory pair: not landed.  `FuelKnotProof.agda` has the
   structural fuel surface and `build-structural-fuel-knot`, but no concrete
   `StructuralExtraCastFactory`/`StructuralValueCatchupFactory` pair because
   the two workers above are not complete.
6. Public `FuelKnot`: not landed in the requested higher-order form over the
   M5 `InstCatchup` factory.  The final public form remains blocked on the
   concrete structural factory pair; no M5 packages were chased in this
   attempt.
7. Grounding residual: unchanged.  The checked residual remains
   `grounding-preservation-knot`; no new LG-3 grounding theorem was assembled.
8. Notes cleanup: not performed.  Since assembly did not complete, the `lg3*`
   resister postscripts were not marked resolved, the ten-file notes
   regression was not run as a resolved-notes sweep, and stale scratch
   supersessions were not edited.

Stop-rule status:

- The diagnostic worker holes were reverted.
- No pragmas, postulates, protected relations, protected surfaces, or
  `PLAN.md` edits were committed.
- This postscript is the green residual record for LG-3aa.

Gate after the LG-3aa residual record:

```text
cd GTSFImp && AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home make check
```

Result:

```text
agda --safe -v0 All.agda
agda -v0 LegacyAll.agda
postulate-check: OK (no postulates; NON_COVERING at legacy baseline)
```
