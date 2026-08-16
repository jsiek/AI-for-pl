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
