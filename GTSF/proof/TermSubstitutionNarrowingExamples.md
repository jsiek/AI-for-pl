# Term substitution narrowing: induction-hypothesis examples

These are schematic examples for choosing the induction hypothesis for
`term-parallel-substitution-narrowing`.

The current one-store environment premise is:

```agda
SubstNrw Δ σ γ γ′ τ τ′ =
  ∀ {x p A B} →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B →
  γ ∋ x ⦂ p →
  Δ ∣ σ ∣ γ′ ⊢ τ x ⊒ τ′ x ∶ p
```

The examples below show where this premise is too narrow.

## Same-store cases

For `x⊒x`, `⊒blame`, application, constants, primitive operations, and casts,
the recursive premises stay at the same store and type context.

Example:

```agda
·⊒· qᶜ L⊒L′ M⊒M′
```

After substitution the direct recursive calls need exactly the same
substitution environment at the same `Δ`, `σ`, `γ`, and `γ′`.

The variable case fixes the lookup shape:

```agda
x⊒x pᶜ x∋p
```

The proof obligation is:

```agda
Δ ∣ σ ∣ γ′ ⊢ τ x ⊒ τ′ x ∶ p
```

So the environment premise must still be lookup-indexed by a coercion typing
proof for the current store.

## `extend`

Input shape:

```agda
extend qᶜ pαᶜ M⊒N′α

M⊒N′α :
  Δ ∣ (α ꞉= A ⊒) ∷ σ ∣ γ
    ⊢ M ⊒ N′ [ α ]ᵀ ∶ p [ α ]ᶜ
```

The conclusion store is `(α ꞉ q) ∷ σ`, but the recursive premise store is
`(α ꞉= A ⊒) ∷ σ`.  If `M` contains a variable, the recursive substitution proof
needs:

```agda
Δ ∣ (α ꞉= A ⊒) ∷ σ ∣ γ′ ⊢ τ x ⊒ τ′ x ∶ r
```

The current premise only gives the corresponding fact at `(α ꞉ q) ∷ σ`.

There is also an opened-target obligation.  The recursive call on
`M⊒N′α` gives a right term of the form:

```agda
substˣᵐ τ′ (N′ [ α ]ᵀ)
```

but `extend` wants an opened right term:

```agda
N₂ [ α ]ᵀ
```

The useful witness is:

```agda
N₂ = substˣᵐ (↑ᵗᵐ τ′) N′
```

so this case also needs a commutation lemma:

```agda
substˣᵐ τ′ (N′ [ α ]ᵀ) ≡
  (substˣᵐ (↑ᵗᵐ τ′) N′) [ α ]ᵀ
```

## `split`

Input shape:

```agda
split qᶜ pαᶜ Nα⊒N′α

Nα⊒N′α :
  Δ ∣ (α ꞉ q) ∷ σ ∣ γ
    ⊢ N [ α ]ᵀ ⊒ N′ [ α ]ᵀ ∶ p [ α ]ᶜ
```

The conclusion store is `(α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ`, but the recursive
premise store is `(α ꞉ q) ∷ σ`.  So the substitution environment must also be
available at that normal-head store.

Both sides of the recursive result have opened terms, so the same opening
commutation lemma is needed on each side, with witnesses:

```agda
substˣᵐ (↑ᵗᵐ τ)  N
substˣᵐ (↑ᵗᵐ τ′) N′
```

## Store-dropping cases

The `α⊒α` and `⊒α` cases recurse on the tail store.

Example:

```agda
α⊒α qᶜ pαᶜ L⊒L′

L⊒L′ :
  Δ ∣ σ ∣ γ ⊢ L ⊒ L′ ∶ `∀ p
```

The conclusion store is `(α ꞉ q) ∷ σ`, but the recursive premise is at `σ`.
The current one-store premise cannot supply substitution entries at this tail
store.

The `⊒α` case has the same shape, except the conclusion store is
`(α ꞉= A ⊒) ∷ σ`.

## Term binder

Input shape:

```agda
ƛ⊒ƛ p↦qᶜ N⊒N′

N⊒N′ :
  Δ ∣ σ ∣ (- p) ∷ γ ⊢ N ⊒ N′ ∶ q
```

The recursive substitution environment must extend over the term variable:

```agda
extˢˣ τ
extˢˣ τ′
```

The `S` lookup case needs a term-variable weakening lemma for term narrowing:

```agda
Δ ∣ σ ∣ γ′ ⊢ τ x ⊒ τ′ x ∶ r
-------------------------------------------------
Δ ∣ σ ∣ s ∷ γ′
  ⊢ renameˣᵐ suc (τ x) ⊒ renameˣᵐ suc (τ′ x) ∶ r
```

The `Z` lookup case needs `x⊒x` at `- p`; that requires an arrow-coercion
inversion/dual lemma from `p ↦ q`.

## Type binder

Input shape:

```agda
Λ⊒Λ allᶜ vV V⊒V′

V⊒V′ :
  suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ γ ⊢ V ⊒ V′ ∶ p
```

The recursive substitution environment must be lifted:

```agda
↑ᵗᵐ τ
↑ᵗᵐ τ′
```

This needs a type-renaming lemma for term narrowing:

```agda
Δ ∣ σ ∣ γ′ ⊢ τ x ⊒ τ′ x ∶ r
-------------------------------------------------
suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ γ′
  ⊢ renameᵗᵐ suc (τ x) ⊒ renameᵗᵐ suc (τ′ x) ∶ ⇑ᶜ r
```

The same lifted environment is needed for the recursive premise of `⊒Λ`, with
the additional head store:

```agda
(zero ꞉= ★ ⊒) ∷ ⇑ˢ σ
```

Those cases also need the shift/substitution equation:

```agda
substˣᵐ (↑ᵗᵐ τ) (⇑ᵗᵐ N) ≡ ⇑ᵗᵐ (substˣᵐ τ N)
```

## `ν` and source/target-shift cases

The `ν`-related cases are sharper than the ordinary type-binder cases because
the side that appears as `⇑ᵗᵐ _` determines which substitution environment must
be lifted.

Example:

```agda
ν⊒ν pᶜ qᶜ N⊒N′

N⊒N′ :
  suc Δ ∣ (zero ꞉ ⇑ᶜ q) ∷ ⇑ˢ σ ∣ ⇑ᵍ γ
    ⊢ N ⊒ N′ ∶ ⇑ᶜ p
```

To use the IH on `N⊒N′`, the natural lifted environment is:

```agda
τ
τ′
```

This matches the definition of term substitution:

```agda
substˣᵐ τ (ν A N c) = ν A (substˣᵐ τ N) c
```

So `ν⊒ν` needs a frame that shifts the term-variable contexts to `⇑ᵍ γ` and
`⇑ᵍ γ′`, but keeps both substitution environments unchanged.

The asymmetric cases are different:

```agda
⊒ν :
  suc Δ ∣ (zero ꞉= ⇑ᵗ A ⊒) ∷ ⇑ˢ σ ∣ ⇑ᵍ γ
    ⊢ ⇑ᵗᵐ N ⊒ N′ ∶ ⇑ᶜ p

ν⊒ :
  suc Δ ∣ (⊒ zero ꞉=☆) ∷ ⇑ˢ σ ∣ ⇑ᵍ γ
    ⊢ N ⊒ ⇑ᵗᵐ N′ ∶ ⇑ᶜ p
```

For `⊒ν`, the source side appears as `⇑ᵗᵐ N`, so the IH must use source
environment `↑ᵗᵐ τ` and target environment `τ′`.  The reconstruction uses:

```agda
substˣᵐ (↑ᵗᵐ τ) (⇑ᵗᵐ N) ≡ ⇑ᵗᵐ (substˣᵐ τ N)
```

For `ν⊒`, the target side appears as `⇑ᵗᵐ N′`, so the IH must use source
environment `τ` and target environment `↑ᵗᵐ τ′`.

The `⊒⟨ν⟩` case has the same source-lift shape as `⊒ν`: its source premise is
`⇑ᵗᵐ N`, but its target is a casted term `V′ ⟨ s ⟩`, so the target environment
stays `τ′`.

The head stores involved are:

```agda
(zero ꞉ ⇑ᶜ q) ∷ ⇑ˢ σ
(zero ꞉= ⇑ᵗ A ⊒) ∷ ⇑ˢ σ
(⊒ zero ꞉=☆) ∷ ⇑ˢ σ
```

This is not a problem with the definition of `substˣᵐ`; it is a problem with a
one-store, one-context substitution premise.  The induction needs to know which
recursive frames use `τ`, `τ′`, `↑ᵗᵐ τ`, and `↑ᵗᵐ τ′`.

## Candidate IH shape

The examples point to a frame-indexed substitution premise rather than a
single-store premise.

The checked Agda formulation uses frames of the following shape:

```agda
SubstFrame γ₀ γ₀′ τ₀ τ₀′ γ γ′ τ τ′
```

with constructors for:

```agda
frame-id
frame-ƛ
frame-Λ
frame-νν
frame-src⇑
frame-tgt⇑
```

The environment premise is then:

```agda
SubstNrwFamily γ₀ γ₀′ τ₀ τ₀′ =
  ∀ {Δ σ γ γ′ τ τ′} →
  SubstFrame γ₀ γ₀′ τ₀ τ₀′ γ γ′ τ τ′ →
  SubstNrw Δ σ γ γ′ τ τ′
```

This premise is intentionally store-polymorphic: store-changing constructors
such as `extend`, `split`, `α⊒α`, and `⊒α` simply invoke the family at the
recursive store.

The important consequence is that the old single-substitution corollary cannot
be instantiated from only:

```agda
Δ ∣ σ ∣ γ ⊢ V ⊒ V′ ∶ q
```

unless there is an additional lemma or side condition showing that `V ⊒ V′` is
available for all recursive frames, including the asymmetric source/target
shift frames.
