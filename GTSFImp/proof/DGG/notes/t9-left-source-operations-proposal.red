T9 proposal: source operational packages for left catch-up

Date: 2026-08-17

Reason
------

The terminal left catch-up proof must construct source reduction traces.  The
right catch-up stack already has target operational catalogs, but all of its
result packages are target-extension and value-only.  The left packages need
to return either a related source value or source blame, with
`ParkedEvolve χsᴸ []`.

Before context
--------------

Right operational surfaces include:

```agda
ExtraCastRightAt fuel
InstCatchupRightAt fuel
AllValueViewStepCatalogᵀ
StructuralCatchupRightResult
```

They produce target traces such as:

```agda
M′ ⟨ c′ ⟩ —↠[ χsᴿ ] N′
M′ ⦂∀ B [ A ] —↠[ χsᴿ ] N′
```

After context
-------------

Add left analogues under `proof/DGG/Catchup/`, preferably keeping Def
surfaces separate from proof modules:

  `LeftExtraCastDef.agda`
  `LeftInstCatchupDef.agda`
  `LeftSourceWrapperDef.agda`

The statements below intentionally return `LeftCatchupResult`-shaped
disjunctions rather than a value-only result.

Source extra cast
-----------------

```agda
LeftExtraCastAt : ℕ → Set₁
LeftExtraCastAt fuel =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
    {ν : Env∼ Δᴸ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
    {q : A′ ⊑ᵂ⟨ W ⟩ B}
  → (c : ν ⊢ A ∼ A′)
  → castSize c < fuel
  → ParkedWorld W
  → (rel : W ∣ [] ⊢² M ⊑ V′ ∶ p)
  → Value V′
  → SourceCastBound fuel rel
  → LeftCatchupResult
      {W = W} {Wᵖ = W}
      {kind = same-boundary}
      {Xᴸ? = nothing} {Xᴿ? = nothing}
      {M = M ⟨ c ⟩} {V′ = V′}
      {A = A′} {B = B}
```

Important branches:

  * inert source cast: value branch with zero steps,
  * `id`: one `β-id` keep step,
  * ground tag: one `ground` keep step, then smaller source-cast recursion,
  * projection: `tag-untag` value branch or `tag-untag-bad` blame branch,
  * `bot-intro`: blame branch by `blame-bot-intro`,
  * `inst`: delegate to `LeftInstCatchupAt fuel`,
  * inner source non-value: use the boundary value worker on the premise and
    lift the trace by `ξ-⟨⟩`,
  * inner source blame: lift by `ξ-⟨⟩`, then `blame-⟨⟩`.

Source inst cast
----------------

`β-inst` is the main left allocation point for casts:

```agda
V ⟨ (inst c) A′≢★ ⟩
  —→[ bind ★ ]
⇑ᵗᵐ V ⦂∀ applyBody (bind ★) A [ ＇ zero ] ↑
  〖 zero , ★ ↑ A 〗 ⟨ ↑ᶜ (c [ ★/0 ]ᶜ) ⟩
```

Proposed surface:

```agda
LeftInstCatchupAt : ℕ → Set₁
LeftInstCatchupAt fuel =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {V : Term Δᴸ} {V′ : Term Δᴿ}
    {A : Ty (suc Δᴸ)} {A′ : Ty Δᴸ} {B : Ty Δᴿ}
    {ν : Env∼ Δᴸ}
    {p : `∀ A ⊑ᵂ⟨ W ⟩ B}
    {q : A′ ⊑ᵂ⟨ W ⟩ B}
  → ParkedWorld W
  → W ∣ [] ⊢² V ⊑ V′ ∶ p
  → Value V
  → Value V′
  → (c : instᵐ ν ⊢ A ∼ ⇑ᵗ A′)
  → ⦃ Anv : NonVar A ⦄
  → ⦃ zero∈A : Fin.zero ∈ᵗ A ⦄
  → (A′≢★ : A′ ≢ ★)
  → castSize ((inst c) A′≢★) < fuel
  → LeftCatchupResult
      {W = W} {Wᵖ = W}
      {kind = same-boundary}
      {Xᴸ? = nothing} {Xᴿ? = nothing}
      {M = V ⟨ (inst c) A′≢★ ⟩}
      {V′ = V′} {A = A′} {B = B}
```

The proof must:

  1. take the `β-inst` source step with `bind ★`,
  2. evolve the parked world with `evolve-left-bind`,
  3. reconstruct the post-step CTI relation under the left-only world,
  4. use smaller source-cast recursion for the residual
     `↑ᶜ (c [ ★/0 ]ᶜ)`,
  5. preserve the fixed target value across the left allocation.

Source type application
-----------------------

`•⊑²` is the unique CTI2 branch where the source is a type application and the
target may already be a value.

Proposed surface:

```agda
LeftSourceTypeAppCatchupAt : ℕ → Set₁
LeftSourceTypeAppCatchupAt fuel =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {C : Ty (suc Δᴸ)} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p∀ : `∀ C ⊑ᵂ⟨ W ⟩ B}
    {q : A ⊑ᵂ⟨ W ⟩ ★}
    {r : C [ A ]ᵗ ⊑ᵂ⟨ W ⟩ B}
  → ParkedWorld W
  → (rel : W ∣ [] ⊢² M ⊑ V′ ∶ p∀)
  → Value V′
  → SourceCastBound fuel rel
  → LeftCatchupResult
      {W = W} {Wᵖ = W}
      {kind = same-boundary}
      {Xᴸ? = nothing} {Xᴿ? = nothing}
      {M = M ⦂∀ C [ A ]} {V′ = V′}
      {A = C [ A ]ᵗ} {B = B}
```

Operational branches:

  * inner source steps: lift by `ξ-•`,
  * inner source blame: lift then use `blame-•`,
  * `Λ`: `β-Λ` with source `bind A`,
  * `∀ᶜ`: `β-∀` with `keep`,
  * `gen`: `β-gen` with source `bind A`, followed by residual source-cast
    recursion,
  * reveal-`∀`: `β-reveal-∀` with source `bind A`,
  * conceal-`∀`: `β-conceal-∀` with source `bind A`.

This is the left analogue of the M5 step catalog, but it is consumed from
`•⊑²`, not from target extra-cast normalization.

Source reveal/conceal wrappers
------------------------------

Proposed shared wrapper surfaces:

```agda
LeftSourceRevealCatchupAt : ℕ → Set₁
LeftSourceConcealCatchupAt : ℕ → Set₁
```

They should be boundary-general, because `reveal⊑²`, `conceal⊑²`,
`reveal⊑reveal²`, and `conceal⊑conceal²` all move through premise worlds.

Source reveal operational branches:

  * `ξ-reveal`,
  * `blame-reveal`,
  * `id-reveal`,
  * `conceal-reveal`,
  * zero-step value for function and universal reveal conversions.

Source conceal operational branches:

  * `ξ-conceal`,
  * `blame-conceal`,
  * `id-conceal`,
  * zero-step value for seal, function, and universal conceal conversions.

Required endpoint transport fields:

  * source reveal rebase transport through left `ParkedEvolve`,
  * source conceal `SourceConcealPartnerOK` transport through left
    `ParkedEvolve`,
  * matched conceal partner transport through left `ParkedEvolve`,
  * target-wrapper rewrap for paired wrappers whose target is already a value.

Blocked branches covered
------------------------

These operation packages cover the non-routine branches in:

  * `cast⊑²`,
  * `cast⊑cast²`,
  * `•⊑²`,
  * `reveal⊑²`,
  * `conceal⊑²`,
  * `reveal⊑reveal²`,
  * `conceal⊑conceal²`,
  * `packaged-seal-star²`.
