# T4 proposal: parked CTI2 term-imprecision transport

## Block

`TransportTermImprecisionᴾᵀ` cannot be inhabited using only the existing
right-side `TargetExtend` machinery.  The fixed closed statement:

```
TransportTermImprecisionᴾᵀ =
  ∀ {χsᴸ χsᴿ W W′ M M′ A B p}
  → ParkedEvolve χsᴸ χsᴿ W W′
  → W ∣ [] ⊢² M ⊑ M′ ∶ p
  → W′ ∣ [] ⊢² applyTerms χsᴸ M ⊑ applyTerms χsᴿ M′
      ∶ transport⊑ᴾ evol p
```

needs a context-generalized theorem to recurse under `ƛ⊑ƛ²`,
`Λ⊑Λ²`, `Λ⊑²`, and wrapper premise worlds:

```
TransportTermImprecisionCtxᴾᵀ : Set
TransportTermImprecisionCtxᴾᵀ =
  ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (evol : ParkedEvolve χsᴸ χsᴿ W W′)
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → W′ ∣ mapCtxᴾ evol γ
      ⊢² applyTerms χsᴸ M ⊑ applyTerms χsᴿ M′
        ∶ transport⊑ᴾ evol p
```

The closed `TransportTermImprecisionᴾᵀ` is the `γ = []` corollary, since
`mapCtxᴾ evol []` computes to `[]`.

## Missing single-bind transports

The `evolve-right-bind` case can be discharged from existing machinery:
`right-only-parked→world-extendᴿ` plus `⊢²-target-extend-bind`.

The missing obligations are the source and paired bind cases:

```
SourceBindTransport²ᵀ : Set
SourceBindTransport²ᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A₀ : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → CTI2.leftOnlyWorld X⊑★ W A₀
      ∣ mapCtxᴾ (evolve-left-bind evolve-refl) γ
      ⊢² applyTerm (bind A₀) M ⊑ M′
        ∶ transport⊑ᴾ (evolve-left-bind evolve-refl) p
```

```
BothBindTransport²ᵀ : Set
BothBindTransport²ᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A₀ : Ty Δᴸ} {B B₀ : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → CTI2.bothBindWorld X⊑X W A₀ B₀
      ∣ mapCtxᴾ (evolve-both-bind evolve-refl) γ
      ⊢² applyTerm (bind A₀) M ⊑ applyTerm (bind B₀) M′
        ∶ transport⊑ᴾ (evolve-both-bind evolve-refl) p
```

Each of these is a new induction over the CTI2 term-imprecision relation
`_∣_⊢²_⊑_∶_`, analogous in size and shape to `TargetExtend.⊢²-target-insert`.
They must also transport the wrapper premises for `RebaseAtᴸ`, `RebaseAtᴿ`,
`TagRebaseAtᴸ`, `SameCtx`, indexed conversion typing, and the seal-partner
predicates through the new source or paired allocation.

## Rationale

`SimProof` consumes `TransportTermImprecisionᴾᵀ` only as uniform transport of
already-related subterms after a `ParkedEvolve`; it does not need a new DGG
top-level shape.  However, proving the surface requires the missing source and
paired allocation transports above.  Those are new major CTI2 induction
lemmas, so this run stops here under the standing rule rather than adding them
directly.
