M5 smart comma M-2 continuation blocked at TargetBindLift.

Status: BLOCKED, 2026-08-12.

The TargetExtend off-image finding is resolved in
`proof.DGG.TargetExtend`:

    pushout-off-image-disjoint :
      ∀ {Δ Δ′ Δᵐ}
      → (π : Δ ↪ᵗ Δ′)
      → (old : Δ ↪ᵗ Δᵐ)
      → {Z′ : TyVar Δ′} {Zᵐ : TyVar Δᵐ}
      → preimage? π Z′ ≡ nothing
      → toRenameᵗ (EmbeddingPushout.old′ (embeddingPushout π old)) Z′
        ≢ toRenameᵗ
            (EmbeddingPushout.premise (embeddingPushout π old)) Zᵐ

    target-insert-off-image-center :
      ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
        {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
        {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
        {Y′ : TyVar Δᴿ′}
      → (ins : TargetInsert ρ π W W′)
      → preimage? ρ Y′ ≡ nothing
      → preimage? π (toRenameᵗ (ηᴿʷ W′) Y′) ≡ nothing

Those lemmas close the `Λ⊑²-smart-comma` `smart-fresh-behind` branch of
`⊢²-target-insert`; `TargetExtend.agda` checks.

The next full-tree gate stops at:

    proof.DGG.TargetBindLift.⊢²-target-bind-lift-move

missing the `Λ⊑²-smart-comma` constructor case.

For a smart branch, the conclusion move is:

    mv : TargetBindLiftMove W Wᵗ Y

and the constructor premise has some smart world:

    liftW : SmartCommaLiftᴸ W Wᵐ
    prem  : Wᵐ ∣ γᵐ ⊢² V ⊑ M′ ∶ p

To rebuild the smart constructor at `Wᵗ`, the premise world must have the
moved target store:

    Wᵐᵗ = targetStoreAs Wᵐ (targetStoreʷ Wᵗ)

and the recursive premise would need:

    Wᵐᵗ ∣ moveCtx mvᵐ γᵐ ⊢² V ⊑ M′ ∶ move⊑ᵂ mvᵐ p

The existing recursive theorem needs:

    mvᵐ : TargetBindLiftMove Wᵐ Wᵐᵗ Y

The blocker is the pivot-star field of this premise move:

    impEnvʷ Wᵐᵗ (toRenameᵗ (ηᴿʷ Wᵐᵗ) Y) ≡ X⊑★

Since `targetStoreAs` preserves the premise imp-env and target embedding,
this is the same as:

    impEnvʷ Wᵐ (toRenameᵗ (ηᴿʷ Wᵐ) Y) ≡ X⊑★

The approved M-1 smart rule signature does not provide that fact:

* `SmartAliasMergeGuard` marks only its explicit generated alias/name
  slots `β` and `α` as dynamic.  The generic `TargetBindLiftMove` pivot
  `Y` is not tied to either slot by the constructor.
* `SmartFreshBehindGuard` has no target-pivot mark or conclusion-to-premise
  imp-env monotonicity field.  It only records target-center freezing and
  the source fresh mark.

The conclusion move has:

    impEnvʷ Wᵗ (toRenameᵗ (ηᴿʷ Wᵗ) Y) ≡ X⊑★

and `baseMove mv` preserves the imp-env between `W` and `Wᵗ`, so it also
gives the mark at the conclusion world `W`.  There is still no transport
from that conclusion-world mark to the arbitrary smart premise world `Wᵐ`.

This is a genuine transport-side gap after the off-image TargetExtend fix.
Plausible follow-up options:

* add a premise-side pivot mark/monotonicity transport surface for smart
  target-store moves, without changing the `Λ⊑²-smart-comma` constructor
  itself;
* specialize the smart branch of `TargetBindLift` to the generated
  alias/name pivot and require/prove `Y ≡ β` or `Y ≡ α` at the call site;
* add a separate smart target-bind-lift move record whose guard carries
  exactly the pivot mark needed for the premise world.
