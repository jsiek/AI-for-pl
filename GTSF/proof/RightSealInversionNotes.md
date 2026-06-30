# `right-seal-inversion₁` proof notes

These notes record the local proof search for the postulate in
`proof.DynamicGradualGuarantee`:

```agda
right-seal-inversion₁ :
  ∀ {Δ σ γ M V r A α} →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ seal A α ⟩ ∶ r →
  ∃[ q ] Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ q
```

No new postulates were added during this exploration.

## Attempt 1. Direct structural inversion

The first direct definition tried only the two right-cast constructors:

```agda
right-seal-inversion₁ (⊒cast+ qᶜ q⨟s≈r M⊒M′) = _ , M⊒M′
right-seal-inversion₁ (⊒cast- qᶜ q⨟s≈r M⊒M′) = _ , M⊒M′
```

Agda rejected the `⊒cast+` split because it could not solve
`M′ ⟨ - s ⟩ ≟ V ⟨ seal A α ⟩`.  The blocker is the defined dual
operation `-_`, not the term shape itself.

## Attempt 2. Equality-indexed outer cast

The next attempt used an auxiliary with an arbitrary outer coercion `c` and a
separate equality `c ≡ seal A α`:

```agda
right-seal-inversion₁-aux :
  ∀ {Δ σ γ M V c r A α} →
  c ≡ seal A α →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ c ⟩ ∶ r →
  ∃[ q ] Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ q
```

This avoids asking coverage to reduce `- s`.  Agda then exposed the real
frontier: `extend`, where the right term is stuck as `N′ [ α ]ᵀ`.

## Attempt 3. Equality-indexed right term

The auxiliary was generalized again to carry an arbitrary right term `T`:

```agda
right-seal-inversion₁-aux :
  ∀ {Δ σ γ M T V c r A α} →
  T ≡ V ⟨ c ⟩ →
  c ≡ seal A α →
  Δ ∣ σ ∣ γ ⊢ M ⊒ T ∶ r →
  ∃[ q ] Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ q
```

With this shape, the `extend` case can use the existing transport
`extendReplaceRel-term (replace-here qᶜ)` from `proof.Catchup` after the
recursive call:

```agda
right-seal-inversion₁-aux eq c≡seal (extend qᶜ pαᶜ M⊒Vseal)
    with right-seal-inversion₁-aux eq c≡seal M⊒Vseal
... | q , M⊒V =
  q , extendReplaceRel-term (replace-here qᶜ) M⊒V
```

This got past `extend`.  Agda then stopped at `split`.

## Frontier. `split`

For `split`, the premise strips under `(α ꞉ q) ∷ σ`, but the conclusion must
live under `(α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ` and changes the source opening from
`N [ α ]ᵀ` to `N [ αᵢ ]ᵀ`.

The obvious recursive call gives:

```agda
Δ ∣ (α ꞉ q) ∷ σ ∣ γ ⊢ N [ α ]ᵀ ⊒ V ∶ q′
```

The desired conclusion is:

```agda
Δ ∣ (α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ ∣ γ
  ⊢ N [ αᵢ ]ᵀ ⊒ V ∶ q″
```

This is not the same transport as `extendReplaceRel-term`: it must both change
the source opening and retype or reindex the exposed coercion.  This matches
the existing split warning in `proof.Catchup`, where `catchup-split-catchup`
is still postulated because the split-specific opening transport has not been
mechanized.

## Counterexample search

After merging the latest `main`, the stricter narrowing/widening grammar made
one proof branch clearer: a right `⊒cast+` cannot hide a right seal, because it
would require a `Narrowing (unseal α A)`.  Splitting on the possible ground
casts closes the analogous tag-looking cases.

The actual counterexample is simpler than the earlier `split` search.  It is
mechanized in `proof.RightSealInversionCounterexample`:

```agda
counterexample-premise :
  1 ∣ (0 ꞉ id (‵ `ℕ)) ∷ [] ∣ []
    ⊢ ($ (κℕ 0)) ⟨ seal (‵ `ℕ) 0 ⟩
      ⊒ ($ (κℕ 0)) ⟨ seal (‵ `ℕ) 0 ⟩
    ∶ id (＇ 0)
```

The premise is built by adding a right seal to the bare constant relation and
then adding the same seal on the left:

```agda
right-sealed-constant =
  ⊒cast- idNatᶜ right-seal-compose (κ⊒κ k0)

counterexample-premise =
  cast-⊒ idAlphaᶜ left-seal-compose right-sealed-constant
```

If `right-seal-inversion₁` were true, applying it to
`counterexample-premise` would produce:

```agda
∃[ q ]
  1 ∣ (0 ꞉ id (‵ `ℕ)) ∷ [] ∣ []
    ⊢ ($ (κℕ 0)) ⟨ seal (‵ `ℕ) 0 ⟩ ⊒ $ (κℕ 0) ∶ q
```

The module proves this stripped relation impossible:

```agda
stripped-impossible :
  ∀ {q} →
  1 ∣ (0 ꞉ id (‵ `ℕ)) ∷ [] ∣ []
    ⊢ ($ (κℕ 0)) ⟨ seal (‵ `ℕ) 0 ⟩ ⊒ $ (κℕ 0) ∶ q →
  ⊥
```

The two nontrivial stripped cases are:

- `cast+⊒`: the displayed left seal would have to be `- t`, so `t` would be
  `unseal`.  The post-merge grammar has no `Narrowing (unseal α A)`.
- `cast-⊒`: the premise relates bare constants, forcing its index to be
  `id (‵ `ℕ)`.  The composition side condition then forces the remaining
  narrowing after the visible seal to have type `＇ 0 ⊒ ‵ `ℕ`, which is ruled
  out by `narrowing-var-to-older⊥`.

The final checked statement is:

```agda
right-seal-inversion₁-counterexample :
  (∀ {Δ σ γ M V r A α} →
    Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ seal A α ⟩ ∶ r →
    ∃[ q ] Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ q) →
  ⊥
```

So `right-seal-inversion₁` is false as currently stated.  Any replacement
lemma must exclude left-cast wrappers like this example, or return a weaker
conclusion that permits a compensating left seal.

## Exact DGG `seal-unseal` case search

The DGG redex case is narrower than `right-seal-inversion₁`.  The local goal is
the branch

```agda
dynamicGradualGuarantee okM
    (⊒cast+ {s = seal B α} qᶜ q⨟seal≈r M⊒Vseal)
    (pure-step (seal-unseal vV))
```

where `M⊒Vseal` relates `M` to `V ⟨ seal A α ⟩` and the outer
`⊒cast+` supplies the side condition

```agda
Δ ∣ σ ⊢ q ⨾ⁿ seal B α ≈ r ∶ E ⊒ F .
```

The paper proof uses zero source steps and contracts the relation itself:

```agda
σ ⊢ M ⊒ V ⟨ α♯ ⟩ ⟨ α♭ ⟩ : q
=/⊢→
σ ⊢ M ⊒ V : q .
```

### Attempt 1. Reuse `right-seal-inversion₂`

The current mechanized lemma `right-seal-inversion₂` is intentionally weak.  It
only re-exposes the premise relation at endpoint-normalized composition:

```agda
∃[ u ]
  (Δ ∣ σ ⊢ q ⨾ⁿ seal B α ≈ u ∶ src q ⊒ ＇ α) ×
  Δ ∣ σ ∣ [] ⊢ M ⊒ V ⟨ seal A α ⟩ ∶ u
```

This is enough to document that the right redex was introduced by the exact
outer cast, but it does not strip the remaining right seal.  Returning
`M⊒Vseal` in DGG therefore gives a relation to the pre-step term, not the
right-hand reduct `V`.

### Attempt 2. Prove a `q`-specific zero-step contraction

The strongest DGG-shaped helper is:

```agda
right-seal-strip-zero :
  ∀ {Δ σ M V q r A B C D E F α} →
  Value V →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ q ⨾ⁿ seal B α ≈ r ∶ E ⊒ F →
  Δ ∣ σ ∣ [] ⊢ M ⊒ V ⟨ seal A α ⟩ ∶ r →
  Δ ∣ σ ∣ [] ⊢ M ⊒ V ∶ q
```

The direct `⊒cast-` branch exposes a premise
`M ⊒ V ∶ q₀`.  To return exactly `q`, the proof must cancel two right-seal
compositions:

```agda
q  ⨾ⁿ seal B α ≈ r
q₀ ⨾ⁿ seal A α ≈ r
```

and then reindex the term-narrowing derivation from `q₀` to `q`.  No such
right-seal cancellation lemma currently exists.  Even after cancellation, the
needed reindexing resembles the unfinished `termNarrowing-resp-≈` hole in
`proof.LeftSealNarrowingInversion`.

Left-cast cases need more than cancellation.  For example, a branch shaped by
`cast+⊒` requires a factorization lemma turning

```agda
q ⨾ⁿ seal B α ≈ p
r ≈ t ⨾ⁿ p
```

into some `u` such that

```agda
u ⨾ⁿ seal B α ≈ r
u ≈ t ⨾ⁿ q .
```

The current composition API packages `_⨟ⁿ_` and endpoint equivalence, but it
does not provide this associativity/factorization principle.

### Attempt 3. Weaken the final index existentially

DGG only existentially quantifies the final index, so the branch could use the
weaker helper:

```agda
right-seal-strip-some :
  ∀ {Δ σ M V q r A B C D E F α} →
  Value V →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ q ⨾ⁿ seal B α ≈ r ∶ E ⊒ F →
  Δ ∣ σ ∣ [] ⊢ M ⊒ V ⟨ seal A α ⟩ ∶ r →
  ∃[ p ] Δ ∣ σ ∣ [] ⊢ M ⊒ V ∶ p
```

This removes the `q₀ ≡ q` cancellation obligation in the direct `⊒cast-`
branch, but it still gets stuck before the proof reaches that branch.  Agda's
coverage checker exposes `extend`:

```text
N′ [ α ]ᵀ ≟ V ⟨ seal A α₁ ⟩
p [ α ]ᶜ ≟ r
```

An equality-indexed auxiliary can expose `extend`, and the output can move from
the source-only store to the ordinary store with `extendReplaceRel-term`.  The
corresponding `split` branch still needs the same source-opening transport that
is called out by `catchup-split-catchup`: the proof must change the source term
from `N [ α ]ᵀ` to `N [ αᵢ ]ᵀ` while preserving or reconstructing the stripped
right term and index.

### Attempt 4. Catch up the source first

Another route catches `M` up to a source value using

```agda
catchup-lemma okM (vV ⟨ seal A α ⟩) M⊒Vseal .
```

This produces a value `W` with

```agda
W ⊒ applyTerms χs (V ⟨ seal A α ⟩)
  ∶ applyCoercions χs r .
```

However, this route still needs a value-level version of the same right-seal
stripping/contraction fact to obtain a relation to `applyTerms χs V`.  The
existing left widening/narrowing lemmas move casts on the source side; they do
not remove this remaining right seal.

### Counterexample search

The known `right-seal-inversion₁` counterexample does not satisfy the exact DGG
outer-cast premise.  In that example the sealed relation has index
`id (＇ 0)`, but the DGG branch would require some `q` with

```agda
q ⨾ⁿ seal (‵ `ℕ) 0 ≈ id (＇ 0) .
```

`proof.RightSealInversionCounterexample` already proves this impossible in
`old-counterexample-revised-premise⊥`.

The `right-seal-inversion₂` variable counterexample is also not an exact DGG
counterexample: its right-side core is a variable rather than a `Value`, the
term context is nonempty, and the top-level derivation is `ν⊒`, not the exact
outer `⊒cast+` redex used by DGG.

The closed exact candidates that do type check are harmless.  The basic
constant case

```agda
$ 0 ⊒ (($ 0) ⟨ seal (‵ `ℕ) 0 ⟩) ⟨ unseal 0 (‵ `ℕ) ⟩
```

has the expected post-step relation `$ 0 ⊒ $ 0`.  The closed `ν⊒` candidate
with an admissible identity annotation also has a post-step relation:

```agda
ν ★ ($ 0) (⇑ᶜ (id (‵ `ℕ))) ⊒ $ 0 .
```

The tempting `ν⊒` counterexample would annotate the source `ν` with a shifted
seal coercion.  Agda rejects this shape for the DGG premises: `ν⊒` requires its
index premise to be cast-like, and `∶ᶜ` is `tag-or-idᵈ`, so literal seals are
excluded by `tag-or-id-seal-conflict`.

No exact counterexample was found.  The next productive proof step appears to
be an algebraic package for right-seal composition cancellation/factorization,
paired with a term-narrowing reindexing lemma and the split-specific
source-opening transport already identified by `catchup-split-catchup`.
