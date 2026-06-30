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
