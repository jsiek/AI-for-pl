LG-3i stop note: source-conceal replay needs endpoint partner preservation

Status: open as of 2026-08-16.

The supervisor-requested structural pullbacks through `RebaseAtᴸ` and
`TagRebaseAtᴸ` are tractable and now checked.  No smart-fresh pushout
inversion was used, and no fresh target center is moved across a pivot.

The remaining source-wrapper obstruction is narrower.

For the source reveal row:

`CTI2.reveal⊑² mono rb sc c⊢ prem q`

the derivation-primary worker can recurse on `prem` at the premise world,
obtain:

`child : StructuralCatchupRightResult Wᵖ γᵖ M M′ p`

pull `child.structural-ext` back through `rb`, and replay the wrapper at the
outer endpoint.  This is checked as `structural-catchup-source-reveal`.

For the source conceal row:

`CTI2.conceal⊑² partner mono rb sc c⊢ prem q`

the same trace geometry is now available.  Recursion at the premise world gives
the endpoint target:

`child.N′`

and the pulled-back outer trace supplies:

`rb′ : CTI2.TagRebaseAtᴸ child.W′ W′ Xᴸ?
        (mapPivotChanges child.χs Xᴿ?)`

so replaying `CTI2.conceal⊑²` at the outer endpoint only lacks:

`SourceConcealPartnerOK child.W′ M c
  (mapPivotChanges child.χs Xᴿ?) child.N′`

The original row supplies:

`partner : SourceConcealPartnerOK Wᵖ M c Xᴿ? M′`

but this is indexed by the original premise target `M′`, not the reduced
endpoint `child.N′`.  The existing transport helpers preserve the predicate
across world renaming, target insertion, store movement, decay, and the local
target id-cast peel.  They do not preserve or reconstruct the `seal` branch
across an arbitrary catch-up target reduction.

For non-seal source conceal conversions the endpoint predicate is trivial:
`fun-conceal-target`, `all-conceal-target`, and `id-conceal-target` can be
rebuilt at any endpoint.  For `seal X R`, however,
`SourceConcealPartnerOK` contains `SealPartnerOK`, whose `star-rep-target`,
`plain-target`, and `name-protected-target` branches depend on the final target
shape and occupancy facts.  The current `StructuralCatchupRightResult` records
the final relation and target value, but it does not record a preservation
principle turning the original `partner` into the endpoint partner.

Required theorem shape:

`sourceConcealPartnerCatchupEndpoint :`

`  partner : SourceConcealPartnerOK W M c Xᴿ? M′`
`  child   : StructuralCatchupRightResult W γ M M′ p`
`  ------------------------------------------------`
`  SourceConcealPartnerOK child.W′ M c`
`    (mapPivotChanges child.χs Xᴿ?) child.N′`

or an equivalent worker invariant that carries this endpoint witness whenever a
source-conceal replay may need it.

This is not the refuted smart-fresh pushout inversion.  It is an endpoint
partner-preservation gap for the source-conceal side condition.  The structural
pullback lemmas, the reveal row, and the conditional conceal replay combinator
are checked; the full `StructuralValueCatchupRightAt` and
`StructuralExtraCastRightAt` factory assembly should stop here until this
endpoint partner invariant is supplied.
