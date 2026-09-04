# Atomic `Λ` split-and-reveal provenance

## Scope

The old `TargetBindLift` route first transported a `Λ⊑Λ²` body through
two worlds assembled by replacing only the target store.  Neither world can be
constructed by the inductive `World` API:

- `LambdaFreshWorldInvariantProbe.fresh-nonvariable-bodies-are-not-imprecise`
  gives the non-variable counterexample `ℕ ⇒ X` for the first world.
- `LambdaFreshWorldInvariantProbe.split-alias-mid-invariants-impossible`
  proves that the second world's desired fields contradict
  `unmatchedTargetsDynamic`.

The obstruction is therefore in the old proof boundary, not in the choice of a
`World` constructor.  A provenance-preserving route has to pass directly from
the paired abstract binder to the final valid world, after both target reveals
have been introduced.

## Existing one-reveal rule

The current route applies this complete rule twice:

```agda
  ⊑reveal² : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A B B′ Xᴿ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c′ : Conv↑ Δᴿ B B′}
    → ImpEnvMono W W′
    → RebaseAtᴿ W W′ Xᴿ?
    → SameCtx γ γ′
    → targetStoreʷ W ⊢↑[ Xᴿ? ] c′
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢² M ⊑ M′ ↑ c′ ∶ q
```

For the `Λ` instantiation route, the first application needs a world in which
the source binder is paired with target pivot `s`, while the unmatched target
pivot `a` has direct entry `a↦s`.  This violates the invariant that an
unmatched target alias must point to another target with no source occupant.
There is consequently no admissible premise world for that first application.

## Proposed atomic interface

The proof-specific interface should live with the `Λ` inversion support, not
as a target-store rewrite.  In schematic Agda, its complete result is:

```agda
record ΛSplitRevealProvenance
    {W₀ : World Δᴸ Δᴿ Δ}
    (W₂ : World Δᴸ (suc (suc Δᴿ)) Δ₂)
    (bodyRel :
      liftWorldBoth X⊑X W₀ ∣ γᴮ ⊢² V ⊑ V′ ∶ body-p)
    : Set₁ where
  field
    γout : CtxImp (liftWorldLeft W₂)
    body-p₂ :
      A ⊑ᵂ⟨ liftWorldLeft W₂ ⟩ substᵗ Λ⊑Λ²TargetSplit₂ B
    lift-out :
      LiftCtxᴸ X⊑★ (mapCtxᴿ postExtend γ) γout
    target-typing :
      ⟨ suc (suc Δᴿ) , targetStoreʷ W₂ , tgtCtxʷ γout ⟩
        ⊢ Λ⊑Λ²PostTerm V′ B ⩘ substᵗ Λ⊑Λ²TargetSplit₂ B
    relation :
      liftWorldLeft W₂ ∣ γout
        ⊢² V ⊑ Λ⊑Λ²PostTerm V′ B ∶ body-p₂
```

`W₂` is built by the two real target insertions and is never reconstructed
from projections.  The record is relation-indexed, so recursive source
reveal/conceal cases carry their exact child insertions and rebases, as in
`StructuralTermProvenance`.

The missing implementation of `relation` cannot be derived by composing two
`⊑reveal²` constructors.  The minimal live-relation extension is a body-level
constructor that consumes this exact split provenance in one step:

```agda
  Λ-split-reveal² : ∀
      {W₀ : World Δᴸ₀ Δᴿ₀ Δ₀}
      {W₂ : World Δᴸ₀ (suc (suc Δᴿ₀)) Δ₂}
      {γᴮ : CtxImp (liftWorldBoth X⊑X W₀)}
      {γout : CtxImp (liftWorldLeft W₂)}
      {V : Term (suc Δᴸ₀)} {V′ : Term (suc Δᴿ₀)}
      {A : Ty (suc Δᴸ₀)} {B : Ty (suc Δᴿ₀)}
      {body-p : A ⊑ᵂ⟨ liftWorldBoth X⊑X W₀ ⟩ B}
      {body-p₂ : A ⊑ᵂ⟨ liftWorldLeft W₂ ⟩
        substᵗ Λ⊑Λ²TargetSplit₂ B}
    → ΛSplitRevealGeometry W₀ W₂ γᴮ γout body-p body-p₂
    → liftWorldBoth X⊑X W₀ ∣ γᴮ ⊢² V ⊑ V′ ∶ body-p
    → liftWorldLeft W₂ ∣ γout
        ⊢² V ⊑ Λ⊑Λ²PostTerm V′ B ∶ body-p₂
```

`LambdaSplitRevealGeometry` is the provenance object.  It must contain the two
target insertions, their runtime-store equalities, the lifted context mapping,
typing for both reveals, and the final type-imprecision transport.  It must not
contain a fabricated intermediate `World`.

This constructor is deliberately body-level.  The existing `Λ⊑²` rule can then
rewrap the resulting relation, so no second `Λ`-specific outer rule is needed.

## Reduction/imprecision square

Let `s` be the first fresh target pivot, with store entry `s↦★`, and let
`a` be the second, with store entry `a↦s`.  Write the two generated reveals
with their normalized named endpoints.  The square needed by the inversion
proof is:

    Λα. V       ⊑       (Λα. V′) ⟨ inst c′ ⟩
      │ 0 steps                  │ β-inst; β-Λ
      ▼                          ▼
    Λα. V       ⊑       ((V′[α ↦ a]
                               ↑ reveal a : s ↦ s)
                               ↑ reveal s : ★ ↦ ★)
                               ⟨ residual c′ ⟩

The bottom body judgment lives only in the final valid world:

    ⟨α: α↦α ⊑[X⊑★] ─ │ a: ─ ⊑[X⊑★] a↦s
       │ s: ─ ⊑[X⊑★] s↦★⟩

There is no horizontal judgment at either operational intermediate state.
Those states remain reduction states, but they are not worlds used as indices
of term imprecision.

The imprecision ladder for this permission request must be generated from the
landed ladder-table generator after this branch is synchronized with `main`;
it must not be copied or hand-maintained in this note.
