NS-4 stage 1l worker assembly resisters
=======================================

Date: 2026-08-14

Status
------

The non-name target-frame package decompositions landed in live Agda:

- `structural-target-frame-value-peel`
- `structural-target-reveal-frame-keep-peel`
- `structural-target-conceal-frame-keep-peel`

The β-inst target peel needed by the safe-inst cast-frame branch also landed:

- `structural-target-inst-peel`

These close the target-trace decomposition gap from stage 1k.  They do not
close the relation-side absorption gap for target reveal/conceal frames.


Resister 1: target reveal/conceal frame absorption
-------------------------------------------------

The general worker branch for

`reveal-frame c ▻ⁱ spine`

starts with:

`rel : W ∣ γ ⊢² M ⊑ V ∶ p`

`p : A ⊑ᵂ⟨ W ⟩ B`

`q : A ⊑ᵂ⟨ W ⟩ E`

`chain : TargetFrameAbsorptionChain W γ A (reveal-frame c ▻ⁱ spine) q`

After target decomposition, the recursive child package is available for
either `V ↑ c` and `spine`, or for the one-keep reduct and
`mapInstantiationSpine keep spine`.  The missing object is the child relation
needed before the recursive call.

For the value case, `tfa-reveal` stores:

`mono : ImpEnvMono W Wᵖ`

`rb : RebaseAtᴿ W Wᵖ Xᴿ?`

`sc : SameCtx γ γᵖ`

`c⊢ : targetStoreʷ W ⊢↑[ Xᴿ? ] c`

`qC : A ⊑ᵂ⟨ W ⟩ C`

`tail : TargetFrameAbsorptionChain W γ A spine q`

But `⊑reveal²` requires the premise relation in the rebased target world:

`Wᵖ ∣ γᵖ ⊢² M ⊑ V ∶ pᵖ`

for some

`pᵖ : A ⊑ᵂ⟨ Wᵖ ⟩ B`

The worker only has `rel` in `W`, and no live theorem transports a term
imprecision derivation from `W` to `Wᵖ` along `ImpEnvMono`, `RebaseAtᴿ`, and
`SameCtx`.

Diagram:

    M        ⊑        V          : A ⊑ᵂ⟨ W ⟩ B
    |                 |
    | 0 steps         | reveal-frame c
    v                 v
    M        ⊑        V ↑ c      : A ⊑ᵂ⟨ W ⟩ C
                      |
                      | spine*
                      v
                     final       : A ⊑ᵂ⟨ W ⟩ E

The diagram shows the desired conclusion-side square.  The rule that would
build the horizontal bottom edge, `⊑reveal²`, internally wants the top edge in
the rebased premise world `Wᵖ`, not the available top edge in `W`.

The conceal branch has the same shape.  `tfa-conceal` stores

`mono : ImpEnvMono W Wᵖ`

`rb : RebaseAtᴿ Wᵖ W Xᴿ?`

`sc : SameCtx γ γᵖ`

`c⊢ : targetStoreʷ W ⊢↓[ Xᴿ? ] c`

`qC : A ⊑ᵂ⟨ W ⟩ C`

but `⊑conceal²` also requires a premise relation in `Wᵖ`.


Why the new decompositions are not enough
-----------------------------------------

The new target decompositions preserve the caller's completed target trace and
return the exact child package for recursion.  They intentionally do not
invent relation evidence.  In the reveal/conceal branches, the recursive call
still needs a relation to the frame output, and the current
`TargetFrameAbsorptionChain` does not include the rebased premise relation or a
generic transport theorem that can produce it.

The existing `target-frame-cast-absorption` helper works because `⊑cast²` uses
the original relation in the same world:

`W ∣ γ ⊢² M ⊑ V ∶ p`

The reveal/conceal rules are different because their premise world is
explicitly rebased.


Resister 2: public value adapter target package
-----------------------------------------------

Even after the name-spine worker is assembled, the current public
`StructuralValueInstantiationᵀ` surface does not provide the caller-supplied
target package used by `StructuralNameInstantiationᵀ`.

The adapter would need a package for:

`renameᵗᵐ wk↪ᵗ V`

with spine:

`name-type-app-frame (applyBody (bind R) B) zero refl refl ▻ⁱ []ⁱ`

No fuel-free target-only builder for that root head is currently live.  The
available modules provide forward step builders and inverse peels, but not a
total target normalizer from `AllValueView`.


Required next step
------------------

Add a relation-side target-frame absorption surface for reveal/conceal, or
strengthen `TargetFrameAbsorptionChain` so those entries supply exactly the
rebased premise relation required by `⊑reveal²` and `⊑conceal²`.

Separately, either parameterize the public value-instantiation surface by the
root `StructuralTargetInstantiationPackage`, or add a fuel-free target-only
normalizer that constructs it from `AllValueView`.


PARTIAL RESOLUTION postscript, 2026-08-14:

Resister 1 is closed in live Agda.  `TargetFrameAbsorptionChain` reveal and
conceal entries now include supplied premise-relation transport, and
`target-frame-reveal-absorption` / `target-frame-conceal-absorption` use that
transport before calling `⊑reveal²` / `⊑conceal²`.

Resister 2 remains open.  The attempted target-only builder is now tracked as
`ns4-stage-1m-target-only-builder-resister.red`, because the raw
`InstantiationSpine` surface does not carry the target conversion typing
needed by reveal/conceal frame normalization.
