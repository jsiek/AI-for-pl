# Typed term substitution narrowing: induction-hypothesis shape

These notes record why `proof.Substitution.Term.TermSubstitutionNarrowing` uses a frame-indexed
substitution premise for the typed term-narrowing theorem
`term-parallel-substitution-narrowingᵗ`.

The exported environment premise is:

```agda
TypedSubstNrw Δ σ γ γ′ τ τ′ =
  ∀ {x p A B} →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B →
  γ ∋ x ⦂ p →
  Δ ∣ σ ∣ γ′ ⊢ τ x ⊒ τ′ x ∶ p ⦂ A ⊒ B
```

The examples below explain why the theorem quantifies over a family of such
premises instead of a single store and context.

## Same-store cases

For `x⊒xᵗ`, `⊒blameᵗ`, application, constants, primitive operations, and casts,
the recursive premises stay at the same store and type context.

Example:

```agda
·⊒·ᵗ p↦qᶜ L⊒L′ M⊒M′
```

After substitution, both recursive calls use the same `Δ`, `σ`, `γ`, and `γ′`.
The variable case fixes the lookup shape:

```agda
x⊒xᵗ pᶜ x∋p
```

The proof obligation is:

```agda
Δ ∣ σ ∣ γ′ ⊢ τ x ⊒ τ′ x ∶ p ⦂ A ⊒ B
```

So the environment premise remains lookup-indexed by a coercion typing proof
for the current store, and it also carries the endpoint types needed by the
typed relation.

## Store-changing cases

The `extendᵗ` and `splitᵗ` constructors change the store shape around their
recursive premises.

For `extendᵗ`, the recursive premise lives under the open store entry:

```agda
Δ ∣ (α ꞉= A ⊒) ∷ σ ∣ γ
  ⊢ M ⊒ N′ [ α ]ᵀ ∶ p [ α ]ᶜ ⦂ _ ⊒ _
```

but the conclusion is rebuilt under `(α ꞉ q) ∷ σ`.  If `M` contains a variable,
the recursive substitution call needs the environment premise at the recursive
store, not only at the conclusion store.

For `splitᵗ`, the recursive premise lives under `(α ꞉ q) ∷ σ`, while the
conclusion is rebuilt under:

```agda
(α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ
```

Both cases also need the opening/substitution equation:

```agda
substˣᵐ τ (N [ α ]ᵀ) ≡ (substˣᵐ (↑ᵗᵐ τ) N) [ α ]ᵀ
```

## Store-dropping cases

The `α⊒αᵗ` and `⊒αᵗ` cases recurse on the tail store.

Example:

```agda
α⊒αᵗ γ′≡ qᶜ pαᶜ L⊒L′
```

The conclusion store is `(α ꞉ q) ∷ σ`, but the recursive premise is at `σ`.
The substitution environment therefore has to be available at the tail store
as well.

## Binders

For `ƛ⊒ƛᵗ`, the recursive substitution environments are:

```agda
extˢˣ τ
extˢˣ τ′
```

For `Λ⊒Λᵗ`, they are:

```agda
↑ᵗᵐ τ
↑ᵗᵐ τ′
```

The type-binder cases also rely on:

```agda
substˣᵐ (↑ᵗᵐ τ) (⇑ᵗᵐ N) ≡ ⇑ᵗᵐ (substˣᵐ τ N)
```

## `ν` and asymmetric shift cases

The `ν`-related constructors determine which side of the substitution
environment must be lifted.

For `ν⊒νᵗ`, term substitution descends under `ν` without changing the
substitution environments, so the frame only shifts the contexts:

```agda
frame-νν
```

For `⊒νᵗ` and `⊒⟨ν⟩ᵗ`, the source side is shifted, so the frame uses
`↑ᵗᵐ τ` on the source and keeps `τ′` on the target:

```agda
frame-src⇑
```

For `ν⊒ᵗ`, the target side is shifted:

```agda
frame-tgt⇑
```

## Checked IH shape

The checked Agda formulation uses:

```agda
SubstFrame γ₀ γ₀′ τ₀ τ₀′ γ γ′ τ τ′
```

with constructors:

```agda
frame-id
frame-ƛ
frame-Λ
frame-νν
frame-src⇑
frame-tgt⇑
```

The family premise is:

```agda
TypedSubstNrwFamily γ₀ γ₀′ τ₀ τ₀′ =
  ∀ {Δ σ γ γ′ τ τ′} →
  SubstFrame γ₀ γ₀′ τ₀ τ₀′ γ γ′ τ τ′ →
  TypedSubstNrw Δ σ γ γ′ τ τ′
```

This premise is intentionally store-polymorphic: store-changing constructors
such as `extendᵗ`, `splitᵗ`, `α⊒αᵗ`, and `⊒αᵗ` invoke the family at the
recursive store.

The single-substitution corollary is:

```agda
term-substitution-narrowingᵗ :
  TypedSubstNrwFamily (q ∷ γ) γ (singleEnv V) (singleEnv V′) →
  Δ ∣ σ ∣ q ∷ γ ⊢ N ⊒ N′ ∶ p ⦂ A ⊒ B →
  Δ ∣ σ ∣ γ ⊢ N [ V ] ⊒ N′ [ V′ ] ∶ p ⦂ A ⊒ B
```
