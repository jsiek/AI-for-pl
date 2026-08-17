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

Postscript 2026-08-16, LG-3j endpoint-partner invariant:

The source-conceal endpoint partner side condition is no longer part of this
blocked surface.  `StructuralCatchupRightResult` now carries the conditional
endpoint transformer for `SourceConcealPartnerOK`, and the checked
source-conceal row uses it to replay `CTI2.conceal⊑²` at the child endpoint.

This note remains open only for the structural multi-step target-cast worker
and the subsequent full assembly of `StructuralExtraCastRightAt`,
`StructuralValueCatchupRightAt`, and the public erased factory surfaces.

Postscript 2026-08-16, LG-3m source-row order:

The source reveal/conceal rebase-crossing demand from LG-3k/LG-3l is resolved
by reordering those rows: recurse at the premise world, pull the child
structural trace back to the outer world, then replay the source wrapper at the
outer endpoint.  The endpoint-partner field is now plan-polymorphic, so no
non-total `SourceConcealPartnerOK W -> SourceConcealPartnerOK Wᵖ`
transformer is required.

This note remains open for the target-cast multi-step worker and factory
assembly only.

Postscript 2026-08-16, LG-3o target-cast endpoint field:

The target-cast row-composition blocker recorded in
`lg3-target-cast-multistep-worker-resister.red` is resolved by the new
`StructuralCatchupRightResult.source-conceal-endpoint-partner-target-cast`
field.  The checked target-cast and paired target-cast row combinators now
derive their endpoint partners from the child and residual structural results,
with no explicit `partner-endpoint` argument.

This does not discharge the full `ExtraCastRightAt` theorem.  The remaining
open item for this note is still the structural multi-step target-cast worker
and the concrete factory assembly that consumes it.

Postscript 2026-08-17, LG-3x paired active rows:

The paired active target rows are no longer the open row-level blocker.  The
sanctioned stuttering-composite rows now check in
`proof/DGG/Catchup/ExtraCastRightAtProof.agda`:

- `structural-paired-ground-extra-cast-right-at`;
- `structural-paired-project-same-extra-cast-right-at`;
- `structural-paired-project-expand-extra-cast-right-at`.

The remaining blocker for this note is the whole-premise extractor/factory
assembly recorded in `lg3-target-cast-multistep-worker-resister.red`: the
factory must derive the re-attachment endpoint `C ⊑ᵂ⟨ W ⟩ G` and the peeled
tag-layer core for the general `CTI2.cast⊑cast² cᴸ cᴿ prem q` input before it
can call the checked rows.  This is not the refuted premise-first midpoint
route.

Postscript 2026-08-17, LG-3ad source-injection active-ground row:

The ★-source active-ground family is no longer part of this row-level blocker.
`structural-source-injection-ground-extra-cast-right-at` now checks.  It uses
`source-ground-cast-witness` to recover `H ⊑ᵂ⟨ W ⟩ G` from the premise
`H ⊑ᵂ⟨ W ⟩ B` and the active target ground consistency `B ∼ G`, recurses on
`⊑cast² cᴿ prem qHG`, then re-attaches the paired tags `H!` and `G!`.

This does not assemble `StructuralExtraCastRightAt`.  The remaining blocker is
still the general whole-premise extractor/dispatcher and the value/fuel factory
assembly recorded in `lg3-target-cast-multistep-worker-resister.red`.
