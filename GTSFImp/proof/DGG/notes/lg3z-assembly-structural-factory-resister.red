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

LG-3ac fallback postscript, 2026-08-17:

The LG-3ac holes-first pass did not land the dispatcher or factory assembly.
The temporary diagnostic `StructuralExtraCastRightAt` head split was removed
before this note, so the live proof tree is again hole-free.

qG sourcing status by source result family:

1. Function ground, target `G = ★ ⇒ ★`: derivable from the final
   `q : A₁ ⇒ A₂ ⊑ᵂ⟨ W ⟩ ★` by `⇒⊑★-inv`, then
   `⇒⊑⇒` over the two component `⊑ ★` facts.
2. Base ground, target `G = ι`: derivable by the base tag/project view;
   the final `ι⊑★` witness gives the shape and the endpoint is `ι⊑ι`.
3. Name ground, target `G = ＇ X`: derivable only when the view pins the same
   embedded name, yielding `X⊑X`.  The view is a syntax view, not a name
   alignment theorem for unrelated source/target names.
4. Universal ground, target `G = `∀ ★`: the valid cases are the live
   imprecision cases, not a fake exact-∀ inversion: `∀★⊑★` maps to
   `∀⊑∀ ★⊑★`, `∀⊑★ body` maps to `∀⊑∀ body`, and `bot⊑★` maps to
   `bot-elim`.  The existing universal views correctly expose the additional
   `inst`/`gen` alternatives that any total endpoint lemma must handle.
5. Source injection is the blocking family for the current checked paired
   active-ground row.  If `cᴸ` is the inert tag layer
   `_! (idᵍ Hᵍ)`, the source result type is `★`; the final witness is
   `q : ★ ⊑ᵂ⟨ W ⟩ ★`, and the row asks the dispatcher for
   `qG : ★ ⊑ᵂ⟨ W ⟩ G`.  There is no such constructor for a non-star ground
   `G`.  No premise in the current row signature rules this case out.

This last item is the concrete residual that prevented qG sourcing from being
landed as a dispatcher-only lemma.  It is different from the older refuted
`C ⊑ᵂ⟨ W ⟩ ★` midpoint route: the obstruction is now the post-source
injection endpoint required by the checked paired row itself.

I1 surgery extractor status:

- The available checked projection rows still require an exposed tag premise
  of the form
  `W ∣ γ ⊢² M ⊑ N ⟨ _! (idᵍ Gᵍ) ⟩ ∶ p★`.
- `canonical-★` can expose a tag layer from the target value, but the extractor
  must also transport the exact tag ground through `cast⊑²`, `Λ⊑²`,
  `Λ⊑²-smart-comma`, `reveal⊑²`, and `conceal⊑²`, matching the recursive shape
  of `target-id-step-inversion`.
- That wrapper-aware extractor was not landed.  The existing
  `GeneratedProjectionReplacementProof` cells remain exposed-tag consumers,
  not whole-premise extractors.

Assembly status after LG-3ac:

- Extra-cast dispatcher: not landed.  Direct id/inert/bot rows are checked;
  active ground/projection dispatch remains blocked by the qG/injection
  endpoint and the I1 extractor.
- Both workers: not landed.  `ValueCatchupRightProof.agda` still exposes row
  combinators, not a derivation-primary `StructuralValueCatchupRightAt`.
- Concrete structural factory pair: not landed.
- Public `FuelKnot`: still only available through the higher-order factory
  adapter in `Catchup/FuelKnotProof.agda`; no concrete LG-3 instantiation was
  produced.
- Grounding residual: unchanged; `grounding-preservation-knot` remains the
  checked residual.
- RESOLVED notes: not marked resolved because assembly did not complete.
- `TagDisciplineScratch.agda:232` is stale/superseded by the live
  `SourceConcealPartnerOK`/matched-partner surfaces.  The old scratch carries
  only `SealTargetOK`; the apparent one-line constructor-argument repair is
  insufficient, so it was not fixed in this chunk.  See
  `SURGERY-PREFLIGHT.md` and `TAG-DISCIPLINE-DOSSIER.md` for the superseding
  tag-discipline record.

Commands run during LG-3ac:

```text
cd GTSFImp/proof/DGG/notes && AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home agda -i ../../.. -v0 TagDisciplineScratch.agda
```

Result:

```text
pre-existing failure at TagDisciplineScratch.agda:232; stale scratch not fixed
```
