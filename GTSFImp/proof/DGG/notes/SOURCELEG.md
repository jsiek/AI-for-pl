# SOURCE-LEG addendum

Checked scratch: `SourceLegScratch.agda`

Command:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 SourceLegScratch.agda
```

No `GTSFImp/` files were edited.

## Source terms

The scratch defines the literal gradual pair:

```agda
Pᴳ =
  (ƛ ∀X⇒X ⇒
    ((Λ (ƛ ＇ zero ⇒ ((` 1 `[ ＇ zero ]) ·[ ℓ-inner ] ` 0)))
      `[ ★ ])
      ·[ ℓ-body ] $ (κℕ 0))
    ·[ ℓ-outer ] (Λ (ƛ ＇ zero ⇒ ` 0))

Qᴳ =
  (ƛ ∀X⇒X ⇒
    (ƛ ★ ⇒ ((` 1 `[ ★ ]) ·[ ℓ-inner ] ` 0))
      ·[ ℓ-body ] $ (κℕ 0))
    ·[ ℓ-outer ] (ƛ ★ ⇒ ` 0)
```

The gradual typings are checked as:

```agda
P⊢ᴳ : 0 ∣ [] ⊢ᴳ Pᴳ ⦂ ★
Q⊢ᴳ : 0 ∣ [] ⊢ᴳ Qᴳ ⦂ ★
```

## Consistency choices

The typings avoid rigid mixing:

- `g` is typed by `⊢•` at its `∀X⇒X` type in both bodies.
- The left inner app uses `id (＇ zero)`.
- The right inner app uses `id ★`.
- The numeric argument apps use `★∼ℕ = ？ (id (‵ `ℕ))`.
- The exact left outer app uses `∀ᶜ (id X ↦ id X)`.
- The right outer app uses the rule constructor `inst_` for
  `∀X⇒X ∼ ★⇒★`. Its compiled argument cast is the symmetric `gen_` cast,
  matching `InitialPairScratch`'s right-side `genDynIdᶜ`.

## Source imprecision

The source relation succeeds:

```agda
P⊑Qᴳ :
  I.idᵐ GTI.∣ [] ⊢ᴳ Pᴳ ⊑ Qᴳ ⦂ ★ ⊑ ★ ∶ I.★⊑★
```

The argument node is:

```agda
polyId⊑dynIdᴳ :
  I.idᵐ GTI.∣ [] ⊢ᴳ polyIdᴳ ⊑ dynIdᴳ
    ⦂ ∀X⇒X ⊑ ★⇒★ᵗ ∶ ∀X⇒X⊑★⇒★₀
```

It uses `Λ⊑ᴳ` with the `instᵐ`-marked `＇ zero ⊑ ★` premise.  The inner
left-only type abstraction is related to the right dynamic lambda by
`Λ⊑ᴳ`, then eliminated by `[]⊑ᴳ`.

## Compilation and trace result

Both source typings are compiled through `RC.compile-screen`, with skeleton
gates against the ordinary compiler:

```agda
Pᶜ-skeleton-gate : RC.skeleton Pᶜ ≡ RC.skeleton Pᶜ-standard
Qᶜ-skeleton-gate : RC.skeleton Qᶜ ≡ RC.skeleton Qᶜ-standard
```

For both compiled terms, the first step is the `g` beta:

```agda
P-step₀-change : Ex.OneStep.change P-step₀ ≡ keep
Q-step₀-change : Ex.OneStep.change Q-step₀ ≡ keep
```

The right compiled term then exactly reaches the existing right initial pair:

```agda
Q₁-initialpair-gate : Q₁ ≡ IP.Qᶜ
Q₁-tagged-seal-gate : IP.Q₆ ≡ ...
```

The left literal compiled term does **not** reach
`InitialPairScratch`'s two-seal checkpoint.  This is checked, not inferred:

```agda
P₁₄-no-step : Ex.hasStep? (step? P-store₁₄ P₁₄) ≡ false
P₁₄-tagged-zero-skeleton-gate :
  RC.skeleton P₁₄ ≡ RC.skeleton (IP.taggedZeroᶜ ...)
P₁₄-not-two-seal-skeleton :
  RC.skeleton P₁₄ ≢ RC.skeleton IP.P-two-seal-result-context
```

The reason is the exact outer `P` application: compilation still inserts the
identity `∀` cast around the `g` argument.  That cast is inert for the initial
application, so `g` beta fires first, but later the cast is pushed through the
type application and function application.  The literal compiled route
terminates at the tagged-zero shape rather than the post-factored
`InitialPairScratch.Pᶜ` two-seal route.

The existing post-factored pair remains checked separately:

```agda
initialpair-P-two-seal-state-gate :
  IP.P₇ ≡ IP.P-two-seal-result-context
```
