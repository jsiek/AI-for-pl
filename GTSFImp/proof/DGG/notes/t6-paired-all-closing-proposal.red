Paired ∀ β-closing blocker proposal
===================================

Blocked interface:

`SimPairedAllClosingᵀ`

Reason:

The existing M5/M6 files prove the pieces needed for target instantiation
catchup, but they do not expose the top-down β-closing shape consumed by
`SimProof.agda`.  Building that shape requires a new DGG-level assembly lemma
over value catchup, target all-value views, and M5 name instantiation.  That is
a new top-level DGG proof surface, so the t6 standing rule says to record the
statement instead of implementing it in this arc.

Before context
--------------

`SimProof.agda` calls the interface at every paired type-application root step:

```
sim parked (•⊑•² p∀ M⊑M′ q r) (β-Λ vM) =
  sim-paired-all-closing parked M⊑M′ q r (Λ vM) (β-Λ vM)
```

and similarly for `β-∀`, `β-gen`, `β-reveal-∀`, and `β-conceal-∀`.

The interface starts with:

```
world ∣ [] ⊢² V ⊑ M′ ∶ p∀
Value V
V ⦂∀ C [ A ] —→[ χᴸ ] N
```

and must return a square whose target side starts from:

```
M′ ⦂∀ C′ [ A′ ]
```

The existing components have narrower shapes:

* `ValueCatchupRightAt fuel` can reduce `M′` to a target value, but only after a
  `TargetCastBound fuel M⊑M′` proof is supplied.
* `all-value-view-step-catalog` gives the concrete target β/∀/gen/reveal/conceal
  type-application steps once the target value view is known.
* `structural-value-instantiation` and `structural-name-instantiation` replay
  an instantiation spine through M5, but they start from their structural
  target packages and do not assemble `ParkedEvolve` or the exact Sim closing
  Σ-output.

Proposed statements
-------------------

First reuse the shared M6 closure proposed in
`t6-fun-substitution-proposal.red`:

```
⊢²-target-cast-bound :
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (rel : W ∣ γ ⊢² M ⊑ M′ ∶ p)
  → Σ[ fuel ∈ ℕ ] TargetCastBound fuel rel

value-catchup-right² :
  ValueCatchupRight²
```

Then add the paired all-value redex closing.  This is the M5 adapter after
target value catchup has already exposed the target value and its all-view:

```
PairedAllValueRedexClosingᵀ : Set₁
PairedAllValueRedexClosingᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴸ′} {world : World Δᴸ Δᴿ Δ}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {V : Term Δᴸ} {V′ : Term Δᴿ} {N : Term Δᴸ′}
    {C : Ty (Nat.suc Δᴸ)} {A : Ty Δᴸ}
    {C′ : Ty (Nat.suc Δᴿ)} {A′ : Ty Δᴿ}
    {p∀ : `∀ C ⊑ᵂ⟨ world ⟩ `∀ C′}
  → ParkedWorld world
  → world ∣ [] ⊢² V ⊑ V′ ∶ p∀
  → (q : A ⊑ᵂ⟨ world ⟩ A′)
  → (r : C [ A ]ᵗ ⊑ᵂ⟨ world ⟩ C′ [ A′ ]ᵗ)
  → Value V
  → Value V′
  → AllValueView V′
  → V ⦂∀ C [ A ] —→[ χᴸ ] N
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ world′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ s ∈ applyTy χᴸ (C [ A ]ᵗ) ⊑ᵂ⟨ world′ ⟩
        applyTys χsᴿ (C′ [ A′ ]ᵗ) ]
      (V′ ⦂∀ C′ [ A′ ] —↠[ χsᴿ ] N′) ×
      ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ world world′ ×
      (world′ ∣ [] ⊢² N ⊑ N′ ∶ s)
```

Finally assemble the fixed interface by prepending target value catchup under
the type-application frame:

```
sim-paired-all-closing-from-value-redex :
  value-catchup-right²
  → PairedAllValueRedexClosingᵀ
  → SimPairedAllClosingᵀ
```

The proof of `PairedAllValueRedexClosingᵀ` should be the only place that
dispatches over the source redex shape and the target `AllValueView`.  Its direct
Λ/Λ row uses the `Λ⊑Λ²` body premise plus M5 name-instantiation/opening
transport; its wrapper rows use the existing structural instantiation
descent/peel lemmas.

After context
-------------

Once these surfaces exist, `SimPairedAllClosingProof.agda` should be a thin
adapter:

```
sim-paired-all-closing parked rel q r vV step =
  -- choose fuel and catch up M′ to a target all-value V′
  -- use typeApp-↠ to lift the catchup trace under _⦂∀ C′ [ A′ ]
  -- call PairedAllValueRedexClosingᵀ on V′
  -- compose target reductions and ParkedEvolve evidence
```

This keeps the fixed `SimPairedAllClosingᵀ` statement unchanged while making the
large M5/M6 assembly explicit and reusable.
