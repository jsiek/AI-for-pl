Function β-closing blocker proposal
===================================

Blocked interface:

`SimPairedFunClosingᵀ`

Reason:

The direct λ/β row of the function closing requires a CTI2 term-variable
substitution theorem.  This theorem is a new induction over `⊢²`, so the t6
standing rule says to record the statement and move on instead of implementing
it in this arc.

Before context
--------------

`SimPairedFunClosingᵀ` is consumed by `SimProof.agda` when the source
application reduces at the root, for example:

```
sim parked (·⊑·² L⊑L′ V⊑M′) (pure-step (β vV)) =
  sim-paired-fun-closing parked L⊑L′ V⊑M′ (ƛ _) vV
    (pure-step (β vV))
```

In the direct λ case, inversion of the function relation gives a body relation
under one related term variable:

```
world ∣ ctx-imp A A′ pA ∷ [] ⊢² N ⊑ N′ ∶ pB
```

and the argument premise gives:

```
world ∣ [] ⊢² M ⊑ M′ ∶ pA
```

The source step produces `N [ M ]`.  After the target argument is caught up to a
value and the target β step is taken, the final proof obligation is the
substituted-body relation:

```
world′ ∣ [] ⊢² applyTermχ χsᴸ (N [ M ])
              ⊑ applyTermχs χsᴿ (N′ [ M″ ]) ∶ pB′
```

The existing CTI2 files have type substitution and world/target extension
support, but no term-variable substitution theorem for `⊢²`.

The target argument catchup is also not directly callable from this top-down
closing yet.  The live M6 surface is fuel-indexed:

```
ValueCatchupRightAt fuel
```

and requires:

```
TargetCastBound fuel argRel
```

There is no current builder that chooses a sufficient `fuel` for an arbitrary
CTI2 relation, nor a closed value-catchup theorem that packages the fuel knot
with that bound.

Proposed statements
-------------------

First add the usual environment relation for parallel term substitutions:

```
record TermSubstRel {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ)
    (γ δ : CtxImp W)
    (σᴸ : CastTerms.Subst Δᴸ)
    (σᴿ : CastTerms.Subst Δᴿ) : Set where
  field
    lookup : ∀ {x A B} {p : A ⊑ᵂ⟨ W ⟩ B}
      → γ ∋ʷ x ⦂ ctx-imp A B p
      → W ∣ δ ⊢² σᴸ x ⊑ σᴿ x ∶ p
```

Then prove the CTI2 parallel substitution theorem:

```
⊢²-term-subst :
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ δ : CtxImp W}
    {σᴸ : CastTerms.Subst Δᴸ}
    {σᴿ : CastTerms.Subst Δᴿ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → TermSubstRel W γ δ σᴸ σᴿ
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → W ∣ δ ⊢² CastTerms.subst σᴸ M
             ⊑ CastTerms.subst σᴿ M′ ∶ p
```

The binder cases will also need the standard term-renaming/weakening support
for CTI2, either as a separate theorem:

```
⊢²-term-rename :
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ δ : CtxImp W}
    {ρᴸ : CastTerms.Rename Δᴸ}
    {ρᴿ : CastTerms.Rename Δᴿ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → TermRenameRel W γ δ ρᴸ ρᴿ
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → W ∣ δ ⊢² CastTerms.rename ρᴸ M
             ⊑ CastTerms.rename ρᴿ M′ ∶ p
```

or as the weakening component used internally by the substitution proof.

The function closing only needs the single-variable corollary:

```
⊢²-single-subst :
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {N : Term Δᴸ} {N′ V : Term Δᴿ}
    {M : Term Δᴸ}
    {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
    {pA : A ⊑ᵂ⟨ W ⟩ A′}
    {pB : B ⊑ᵂ⟨ W ⟩ B′}
  → W ∣ ctx-imp A A′ pA ∷ γ ⊢² N ⊑ N′ ∶ pB
  → W ∣ γ ⊢² M ⊑ V ∶ pA
  → W ∣ γ ⊢² N [ M ] ⊑ N′ [ V ] ∶ pB
```

The value-catchup call site also needs a finite-bound builder and the closed
wrapper around the existing M6 knot:

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

`⊢²-target-cast-bound` is another structural recursion over `⊢²`; it should be
proved once near the M6 catchup support and reused by all three t6 β-closing
interfaces.

After context
-------------

With `⊢²-single-subst`, the direct β row of
`SimPairedFunClosingProof.agda` has the intended shape:

```
sim-paired-fun-closing parked (ƛ⊑ƛ² body) argRel
    (ƛ _) vM (pure-step (β vM)) =
  -- use value catchup on argRel to reduce the target argument to V′
  -- take the target β step under appR/appL
  -- return the substituted body relation
  ... , ⊢²-single-subst body finalArgRel
```

The casted function rows (`β-⇒`, `β-reveal-⇒`, and `β-conceal-⇒`) use the same
single-substitution corollary after their existing target-side catchup and
function-cast reductions expose the target λ.
