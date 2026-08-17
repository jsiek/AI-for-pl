LG-3i resolved note: source-conceal replay endpoint partner preservation

Status: resolved on 2026-08-16 by LG-3j.

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

The required theorem shape was:

`sourceConcealPartnerCatchupEndpoint :`

`  partner : SourceConcealPartnerOK W M c Xᴿ? M′`
`  child   : StructuralCatchupRightResult W γ M M′ p`
`  ------------------------------------------------`
`  SourceConcealPartnerOK child.W′ M c`
`    (mapPivotChanges child.χs Xᴿ?) child.N′`

or an equivalent worker invariant that carries this endpoint witness whenever a
source-conceal replay may need it.

This was not the refuted smart-fresh pushout inversion.  It was an endpoint
partner-preservation gap for the source-conceal side condition.

Resolution postscript, 2026-08-16:

`StructuralCatchupRightResult` now carries the internal endpoint-partner
invariant directly:

`source-conceal-endpoint-partner :`
`  SourceConcealPartnerOK W P c Xᴿ? M″ →`
`  SourceConcealPartnerOK W′ P c`
`    (mapPivotChanges χs Xᴿ?) N′`

The field is source-polymorphic in `P`, so source wrappers can replay a
premise-row partner for the original source term while unrelated callers pay
only the conditional argument they actually use.

The checked `structural-catchup-source-conceal` row now takes the original
row's

`partner : SourceConcealPartnerOK Wᵖ M c Xᴿ? M′`

and replays the outer `CTI2.conceal⊑²` at the child endpoint by applying:

`StructuralCatchupRightResult.source-conceal-endpoint-partner child partner`

This closes the source-conceal replay obstruction recorded here.  No checked
row exposed a partner-violating reachable endpoint, and no change to the live
imprecision relation was made.

The remaining LG-3 factory obstruction is separate: the full
`StructuralValueCatchupRightAt`, `StructuralExtraCastRightAt`, and public fuel
factory assembly still wait on the structural multi-step target-cast worker
tracked in `lg3-target-cast-multistep-worker-resister.red`.

LG-3m update, 2026-08-16:

The endpoint-partner invariant above is now plan-polymorphic.  Its live shape
takes an explicit `StructuralWorldExtendᴿ χs W₀ W₀′`, so source reveal and
source conceal can recurse at the premise world, pull the child trace back to
the outer world, and forward the child's invariant without transporting a
partner from the outer world through a source rebase.

This supersedes the narrower LG-3j shape shown above; the source-wrapper
endpoint issue remains resolved, and the LG-3l rebase-crossing transformer is
not used.
