LG-3 blocked surface: `ExtraCastRight²` / `ExtraCastRightAt`

The CatchupCast-family premises have been removed from the live statements.
The new surfaces consume:

`W ∣ γ ⊢² M ⊑ M′ ⟨ c′ ⟩ ∶ q`, `Value M`, and `Value M′`.

2026-08-16 columnless redesign update: the value-catch-up statement now also
uses `TargetCastBound fuel rel`, a derivation-indexed bound on target-side
casts.  This removes the separate column peel blocker but does not discharge
this note: `ExtraCastRightAt` and the target-cast case of value catch-up still
need the inversion below.

The old proof cannot be mechanically replayed because it used `CatchupCast`
as a hand-written proof that the target cast redex reduces to a value still
related to the same source.  For the inversion-based proof we need a live CTI
target-cast preservation/inversion surface of the following shape:

if `M′ ⟨ c′ ⟩ —→[ χ ] N′` is the target cast step selected by the dynamic
semantics and `W ∣ γ ⊢² M ⊑ M′ ⟨ c′ ⟩ ∶ q`, then the step-specific CTI
inversion must produce an extended world and
`W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶ transport⊑ᵂ ext q`.

The inert/id direct cases are straightforward.  The blocked part is the deep
wrapper-aware inversion needed when the whole CTI derivation is not headed by
`⊑cast²`/`cast⊑cast²`, especially for projection/expansion and source-wrapper
heads.  This is a genuine missing proof interface, not a stale import issue.

Postscript 2026-08-16:

Checked progress now lives in
`proof/DGG/Catchup/TargetCastStepInversionProof.agda`.

Closed cells:

- exposed `⊑cast²` / `β-id`;
- exposed `⊑cast²` / `ground`;
- exposed `⊑cast²` / `expand`;
- exposed generated-projection replacement aliases for matched projection and
  projection expansion;
- paired `cast⊑cast²` / `β-id`.

The remaining open core is no longer the generated-projection replacement
itself.  The focused paired non-identity endpoint gap is recorded in
`lg3-paired-target-cast-inversion-post-source-gap.red`.  The wrapper-aware
theorem, `ExtraCastRightAt`, and `ValueCatchupRightAt` are still blocked on
that gap plus source/target wrapper replay integration.

Postscript 2026-08-16, structural boundary factoring:

The source-wrapper replay surface mismatch is now superseded by
`proof/DGG/Catchup/StructuralCatchupRightDef.agda`.  Internal LG-3 catch-up
results carry `StructuralWorldExtendᴿ` and erase to public `WorldExtendᴿ` only
at the value-catch-up / extra-cast boundary.

The remaining open core is the structural multi-step worker recorded in
`lg3-target-cast-multistep-worker-resister.red`: it must assemble the checked
exposed cast cells, source-wrapper structural replay, target-wrapper
peel/absorption, and the paired ground/expand multi-step re-attachment
restatement into `StructuralExtraCastRightAt` and
`StructuralValueCatchupRightAt`, then erase to the public `ExtraCastRightAt`
and `ValueCatchupRightAt`.
