NS-4 stage 1n chain-threading resister
=======================================

Date: 2026-08-14

Status
------

The typed-spine surface landed in live Agda:

`GTSFImp/proof/DGG/Catchup/StructuralSpineTypingDef.agda`

The checked predicate is:

`SpineTyped Σ spine`

with the world-indexed abbreviation:

`SpineTypedʷ W spine = SpineTyped (targetStoreʷ W) spine`

It carries target-store conversion typing for reveal/conceal frames and
structurally traverses type, name, and cast frames.  The live transports cover:

- `spine-typed-map-keep`
- `spine-typed-map-bind`
- `spine-typed-map-bindʷ`
- `spine-typed-rebase-left`
- `spine-typed-tag-rebase-left`
- `spine-typed-lift-left`

The generated/root constructors also check:

- `spine-typed-all-child`
- `spine-typed-reveal-child`
- `spine-typed-conceal-child`
- `root-value-instantiation-spine-typed`

The internal name surface and strict surface skeleton were tightened so the
chain and typed spine are sibling inputs/outputs:

- `StructuralNameInstantiationᵀ` now takes
  `TargetFrameAbsorptionChain W γ A (name-type-app-frame B X refl refl ▻ⁱ spine) q`
  and `SpineTypedʷ W (name-type-app-frame B X refl refl ▻ⁱ spine)`.
- `StructuralStrictChild` now returns `child-typed`.
- Each strict view surface now receives the caller's typed parent spine.


Resister: source-wrapper equal cases need hereditary child chains
----------------------------------------------------------------

The remaining Acc/Equal worker threading is not a direct parent-chain
transport.  In every source-wrapper equal helper, the recursive worker premise
changes the source type index of `TargetFrameAbsorptionChain`.

For the inert source-cast equal case, the parent helper has:

`chain : TargetFrameAbsorptionChain W γ A′ S q`

where:

`S = name-type-app-frame B X refl refl ▻ⁱ spine`

The recursive child premise obtained from `StructuralNamePostPlan.cast-child`
needs:

`child-chain : TargetFrameAbsorptionChain W γ A S q₀`

for the child endpoint:

`q₀ : A ⊑ᵂ⟨ W ⟩ E`

The parent chain cannot be reindexed to this child chain.  For example, if the
tail chain contains a target cast frame, the parent constructor stores an
intermediate endpoint:

`qC : A′ ⊑ᵂ⟨ W ⟩ C`

The child chain for the same target frame would need:

`qC₀ : A ⊑ᵂ⟨ W ⟩ C`

The source consistency evidence `ν ⊢ A ∼ A′` used by the source replay lemma
does not construct such target-frame intermediate imprecision endpoints.
Those endpoints are exactly the sibling target-frame plan data, not a
consequence of the source wrapper.

The lambda and conversion-wrapper equal cases have the same obstruction:

- Plain lambda child needs
  `TargetFrameAbsorptionChain (liftWorldLeft X⊑★ W) γᴸ A S q₀`
  from a parent chain indexed by ``∀ A`` in `W`.
- Smart lambda child needs
  `TargetFrameAbsorptionChain Wᵐ γᵐ A S q₀`
  from a parent chain indexed by ``∀ A`` in `W`.
- Source reveal child needs
  `TargetFrameAbsorptionChain Wᵖ γᵖ A S q₀`
  from a parent chain indexed by `A′` in `W`.
- Source conceal child needs
  `TargetFrameAbsorptionChain Wᵖ γᵖ A S q₀`
  from a parent chain indexed by `A′` in `W`.

The typed-spine side is transportable in these cases:

- Cast: same typed spine.
- Plain lambda: `spine-typed-lift-left`.
- Smart lambda: target-store equality from `SmartCommaLiftᴸ`.
- Source reveal: `spine-typed-rebase-left`.
- Source conceal: `spine-typed-tag-rebase-left`.

The chain side is not transportable from the parent chain alone because the
per-frame intermediate endpoints are source-indexed.


Required statement shape
------------------------

To continue the Acc/Equal worker assembly, the worker needs a hereditary
sibling input beside `StructuralNamePostPlan`.  That sibling must supply the
current target chain and typed spine, and for each `StructuralNamePostPlan`
child branch it must supply the corresponding child target chain and typed
spine at the child source type/world.

Equivalently, each source-wrapper equal helper needs an explicit child-chain
premise tied to the child post-plan result.  A single parent
`TargetFrameAbsorptionChain` argument is not enough for arbitrary pending
spines with cast/reveal/conceal frames.


Consequence
-----------

Stop on the Acc/Equal worker-threading surface until the hereditary sibling
chain evidence is added.  Do not try to derive child chains by transporting the
parent chain through source wrappers; that would require inventing
intermediate target-frame endpoints that the source replay lemmas do not
provide.

No live relation was weakened, and no postulates, holes, or catch-all cases
were added for this resister.
