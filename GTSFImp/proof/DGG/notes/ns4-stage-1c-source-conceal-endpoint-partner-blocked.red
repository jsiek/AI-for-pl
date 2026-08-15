NS-4 stage 1c source conceal equal-case blocker: endpoint partner witness

Date: 2026-08-14

Surface:

  Equal-mass source wrapper helper for the `CTI2.conceal⊑²` case in
  `StructuralNameInstantiationProof`.

What landed around it:

  The following equal helpers now type-check in the live worker module:

    `structural-name-cast-equal`
    `structural-name-plain-Λ-equal`
    `structural-name-smart-Λ-equal`
    `structural-name-reveal-equal`

  They all follow the intended geometry:

    1. obtain the child `StructuralNamePostPlan`,
    2. transform the caller target package into the premise world when needed,
    3. recurse on that transformed target package,
    4. replay the source wrapper at the original endpoint.

Resisted sub-surface:

  The analogous conceal helper reaches the endpoint replay call

    `structural-conceal-replay plan mono rb sc c⊢ ok′ child-rel`

  but that replay requires an endpoint partner witness:

    `ok′ :
      SourceConcealPartnerOK Wᵖ′ U c
        (mapPivotChanges χs Xᴿ?)
        (StructuralTargetInstantiationPackage.final target)`

  The `CTI2.conceal⊑²` constructor provides only the initial premise witness:

    `ok :
      SourceConcealPartnerOK Wᵖ U c Xᴿ? N`

  The existing target-package transport

    `structural-target-tag-rebase-left rb target`

  supplies the child target trace in the premise world, but it does not
  transport `SourceConcealPartnerOK` from the initial target value `N` to the
  normalized final target.

Why this is not just an omitted argument:

  For `fun`, `all`, and `id` conceal conversions the partner predicate is
  trivial.  For source `seal`, however, `SourceConcealPartnerOK` depends on
  the final target's top tag discipline via `SealPartnerOK`.  A final value is
  not enough by itself: the target may be top-tagged, and the acceptable
  tagged cases depend on the mapped target pivot and center alignment.

Needed support:

  A lemma that transports or reconstructs the source conceal partner witness
  over the exact structural target trace, likely by induction on
  `StructuralWorldExtendᴿ` plus the corresponding target reduction/final
  value information, or a narrower endpoint lemma for the concrete
  name-instantiation target normalization package.

Status:

  The conceal equal helper was not landed.  No premise was added to the live
  worker to work around the missing endpoint witness.
