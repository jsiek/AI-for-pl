module proof.Core.Properties.ConversionIndexCompatibilityProperties where

-- File Charter:
--   * Transports source, target, and paired conversion-index replacement
--     evidence through simultaneous endpoint renaming.
--   * Provides structural endpoint-equality transport used to align the
--     renamed evidence with canonical transported imprecision derivations.
--   * Keeps the replacement relation structural and independent of term
--     imprecision, stores, conversions, and simulation.
--   * Exports renaming transport and proof-irrelevant shape reindexing for all
--     three replacement relations.

open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_<_; s<s; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (id)
open import ImprecisionComposition using
  ( ImprecisionShape
  ; ⌊_⌋
  ; id★ˢ
  ; idˣˢ
  ; idιˢ
  ; _↦ˢ_
  ; ∀ˢ_
  ; tagιˢ
  ; tag_⇛ˢ_
  ; tagˣˢ
  ; νˢ_
  ; νˢ-injective
  )
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; subst; sym; trans)

open import ConversionIndexCompatibility
open import ImprecisionWf using
  ( ImpAssm
  ; ImpCtx
  ; _ˣ⊑ˣ_
  ; _∣_⊢_⊑_⊣_
  ; id★
  ; idˣ
  ; idι
  ; _↦_
  ; ∀ⁱ_
  ; tag_
  ; tag_⇛_
  ; tagˣ
  ; ν
  )
open import Types using
  (Renameᵗ; Ty; TyCtx; extᵗ; renameᵗ; singleRenameᵗ; ⇑ᵗ)
open import proof.Core.Properties.TypeProperties using
  ( TyRenameWf
  ; TyRenameWf-ext
  ; renameᵗ-ext-suc-comm
  ; renameᵗ-id
  ; renameᵗ-single-suc-cancel
  ; singleRenameᵗ-Wf-<
  )
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( rename-assm²-∀-leftᵢ
  ; shape-rename
  ; shape-rename-left
  ; ⊑-rename-leftᵢ
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  ( ∀ᵢᶜ
  ; rename-assm²ᵢ
  ; rename-assm²-∀ᵢ
  ; rename-assm²-open∀ᵢ
  ; rename-assm²-source-νᵢ
  ; rename-assm²-⇑ᵢ
  ; rename-assm²-⇑ᴸᵢ
  ; ⊑-lift∀ᵢ
  ; ⊑-open∀ᵢ
  ; ⊑-renameᵗ²ᵢ
  ; ⊑-source-liftνᵢ
  )


transport-imprecision-endpoints :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′} →
  A ≡ A′ →
  B ≡ B′ →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A′ ⊑ B′ ⊣ Δᴿ
transport-imprecision-endpoints refl refl p = p

shape-transport-imprecision-endpoints :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′}
    (eqA : A ≡ A′)
    (eqB : B ≡ B′)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  ⌊ transport-imprecision-endpoints eqA eqB p ⌋ ≡ ⌊ p ⌋
shape-transport-imprecision-endpoints refl refl p = refl


private
  ↦ˢ-injective :
    ∀ {p₁ p₂ q₁ q₂ : ImprecisionShape} →
    p₁ ↦ˢ p₂ ≡ q₁ ↦ˢ q₂ →
    (p₁ ≡ q₁) × (p₂ ≡ q₂)
  ↦ˢ-injective refl = refl , refl

  ∀ˢ-injective :
    ∀ {p q : ImprecisionShape} →
    ∀ˢ p ≡ ∀ˢ q →
    p ≡ q
  ∀ˢ-injective refl = refl

  tag-⇛ˢ-injective :
    ∀ {p₁ p₂ q₁ q₂ : ImprecisionShape} →
    tag p₁ ⇛ˢ p₂ ≡ tag q₁ ⇛ˢ q₂ →
    (p₁ ≡ q₁) × (p₂ ≡ q₂)
  tag-⇛ˢ-injective refl = refl , refl

  shape-lift∀ᵢ :
    ∀ {Φ Δᴸ Δᴿ A B}
      (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
    ⌊ ⊑-lift∀ᵢ p ⌋ ≡ ⌊ p ⌋
  shape-lift∀ᵢ p =
    shape-rename
      rename-assm²-∀ᵢ
      (λ X<Δ → s<s X<Δ)
      (λ Y<Δ → s<s Y<Δ)
      p

  shape-source-liftνᵢ :
    ∀ {Φ Δᴸ Δᴿ A B}
      (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
    ⌊ ⊑-source-liftνᵢ p ⌋ ≡ ⌊ p ⌋
  shape-source-liftνᵢ {B = B} p =
    trans
      (proof.Core.Properties.NuCastImprecisionShapeProperties.shape-subst-target
        (renameᵗ-id B)
        (⊑-renameᵗ²ᵢ
          rename-assm²-source-νᵢ
          (λ X<Δ → s<s X<Δ)
          id
          p))
      (shape-rename
        rename-assm²-source-νᵢ
        (λ X<Δ → s<s X<Δ)
        id
        p)

  replace-paired-transport-evidence-endpoints :
    ∀ {Φ Δᴸ Δᴿ A A′ B B′ α β X X′ Y Y′}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      (eqX : X ≡ Y)
      (eqX′ : X′ ≡ Y′) →
    p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
    p
      [ α ↦ Y
      ⊑⟨ transport-imprecision-endpoints eqX eqX′ pX ⟩
      Y′ ↤ β ]ᴾ
    q
  replace-paired-transport-evidence-endpoints refl refl replace =
    replace


replace-left-transport-endpoints :
  ∀ {Φ Δᴸ Δᴿ A A′ B Ã Ã′ B̃ α X X̃}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ} →
  (eqA : A ≡ Ã) →
  (eqA′ : A′ ≡ Ã′) →
  (eqB : B ≡ B̃) →
  (eqX : X ≡ X̃) →
  p [ α ↦ X ]ᴸ q →
  transport-imprecision-endpoints eqA eqA′ p
    [ α ↦ X̃ ]ᴸ
  transport-imprecision-endpoints eqB eqA′ q
replace-left-transport-endpoints refl refl refl refl replace = replace

replace-right-transport-endpoints :
  ∀ {Φ Δᴸ Δᴿ A A′ B′ Ã Ã′ B̃′ β X′ X̃′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  (eqA : A ≡ Ã) →
  (eqA′ : A′ ≡ Ã′) →
  (eqB′ : B′ ≡ B̃′) →
  (eqX′ : X′ ≡ X̃′) →
  p [ β ↦ X′ ]ᴿ q →
  transport-imprecision-endpoints eqA eqA′ p
    [ β ↦ X̃′ ]ᴿ
  transport-imprecision-endpoints eqA eqB′ q
replace-right-transport-endpoints refl refl refl refl replace = replace

replace-paired-transport-endpoints :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ Ã Ã′ B̃ B̃′ α β
      X X′ X̃ X̃′}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (eqA : A ≡ Ã) →
  (eqA′ : A′ ≡ Ã′) →
  (eqB : B ≡ B̃) →
  (eqB′ : B′ ≡ B̃′) →
  (eqX : X ≡ X̃) →
  (eqX′ : X′ ≡ X̃′) →
  p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
  transport-imprecision-endpoints eqA eqA′ p
    [ α ↦ X̃
    ⊑⟨ transport-imprecision-endpoints eqX eqX′ pX ⟩
    X̃′ ↤ β ]ᴾ
  transport-imprecision-endpoints eqB eqB′ q
replace-paired-transport-endpoints
    refl refl refl refl refl refl replace = replace


replace-paired-evidence-shape :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ α β X X′}
    {pX pY : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  ⌊ pY ⌋ ≡ ⌊ pX ⌋ →
  p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
  p [ α ↦ X ⊑⟨ pY ⟩ X′ ↤ β ]ᴾ q
replace-paired-evidence-shape eq replace-paired-id★ =
  replace-paired-id★
replace-paired-evidence-shape eq replace-paired-idˣ =
  replace-paired-idˣ
replace-paired-evidence-shape eq
    (replace-paired-variables result-shape) =
  replace-paired-variables (trans result-shape (sym eq))
replace-paired-evidence-shape eq replace-paired-idι =
  replace-paired-idι
replace-paired-evidence-shape eq
    (replace-paired-function replace₁ replace₂) =
  replace-paired-function
    (replace-paired-evidence-shape eq replace₁)
    (replace-paired-evidence-shape eq replace₂)
replace-paired-evidence-shape {pX = pX} {pY = pY} eq
    (replace-paired-∀ replace) =
  replace-paired-∀
    (replace-paired-evidence-shape
      (trans
        (shape-lift∀ᵢ pY)
        (trans eq (sym (shape-lift∀ᵢ pX))))
      replace)
replace-paired-evidence-shape eq replace-paired-tag =
  replace-paired-tag
replace-paired-evidence-shape eq
    (replace-paired-function-tag replace₁ replace₂) =
  replace-paired-function-tag
    (replace-paired-evidence-shape eq replace₁)
    (replace-paired-evidence-shape eq replace₂)
replace-paired-evidence-shape eq replace-paired-tagˣ =
  replace-paired-tagˣ
replace-paired-evidence-shape {pX = pX} {pY = pY} eq
    (replace-paired-ν replace) =
  replace-paired-ν
    (replace-paired-evidence-shape
      (trans
        (shape-source-liftνᵢ pY)
        (trans eq (sym (shape-source-liftνᵢ pX))))
      replace)


replace-left-rename²ᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ A A′ B α X}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ} →
  (assm : ∀ {a : ImpAssm} →
    a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ) →
  (hτ : TyRenameWf Δᴸ Θᴸ τ) →
  (hσ : TyRenameWf Δᴿ Θᴿ σ) →
  p [ α ↦ X ]ᴸ q →
  (⊑-renameᵗ²ᵢ assm hτ hσ p)
    [ τ α ↦ renameᵗ τ X ]ᴸ
  (⊑-renameᵗ²ᵢ assm hτ hσ q)
replace-left-rename²ᵢ assm hτ hσ replace-left-id★ =
  replace-left-id★
replace-left-rename²ᵢ assm hτ hσ replace-left-idˣ =
  replace-left-idˣ
replace-left-rename²ᵢ assm hτ hσ
    (replace-left-variable q) =
  replace-left-variable (⊑-renameᵗ²ᵢ assm hτ hσ q)
replace-left-rename²ᵢ assm hτ hσ replace-left-idι =
  replace-left-idι
replace-left-rename²ᵢ assm hτ hσ
    (replace-left-function replace₁ replace₂) =
  replace-left-function
    (replace-left-rename²ᵢ assm hτ hσ replace₁)
    (replace-left-rename²ᵢ assm hτ hσ replace₂)
replace-left-rename²ᵢ
    {τ = τ} {σ = σ} {α = α} {X = X}
    assm hτ hσ (replace-left-∀ replace) =
  replace-left-∀
    (subst
      (λ Y →
        (⊑-renameᵗ²ᵢ
          (rename-assm²-⇑ᵢ assm)
          (TyRenameWf-ext hτ)
          (TyRenameWf-ext hσ)
          _)
          [ suc (τ α) ↦ Y ]ᴸ
        (⊑-renameᵗ²ᵢ
          (rename-assm²-⇑ᵢ assm)
          (TyRenameWf-ext hτ)
          (TyRenameWf-ext hσ)
          _))
      (renameᵗ-ext-suc-comm τ X)
      (replace-left-rename²ᵢ
        (rename-assm²-⇑ᵢ assm)
        (TyRenameWf-ext hτ)
        (TyRenameWf-ext hσ)
        replace))
replace-left-rename²ᵢ assm hτ hσ replace-left-tag =
  replace-left-tag
replace-left-rename²ᵢ assm hτ hσ
    (replace-left-function-tag replace₁ replace₂) =
  replace-left-function-tag
    (replace-left-rename²ᵢ assm hτ hσ replace₁)
    (replace-left-rename²ᵢ assm hτ hσ replace₂)
replace-left-rename²ᵢ assm hτ hσ replace-left-tagˣ =
  replace-left-tagˣ
replace-left-rename²ᵢ assm hτ hσ
    (replace-left-seal q) =
  replace-left-seal (⊑-renameᵗ²ᵢ assm hτ hσ q)
replace-left-rename²ᵢ
    {τ = τ} {α = α} {X = X}
    assm hτ hσ (replace-left-ν replace) =
  replace-left-ν
    (subst
      (λ Y →
        (⊑-renameᵗ²ᵢ
          (rename-assm²-⇑ᴸᵢ assm)
          (TyRenameWf-ext hτ) hσ _)
          [ suc (τ α) ↦ Y ]ᴸ
        (⊑-renameᵗ²ᵢ
          (rename-assm²-⇑ᴸᵢ assm)
          (TyRenameWf-ext hτ) hσ _))
      (renameᵗ-ext-suc-comm τ X)
      (replace-left-rename²ᵢ
        (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ)
        hσ
        replace))


replace-right-rename²ᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ A A′ B′ β X′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  (assm : ∀ {a : ImpAssm} →
    a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ) →
  (hτ : TyRenameWf Δᴸ Θᴸ τ) →
  (hσ : TyRenameWf Δᴿ Θᴿ σ) →
  p [ β ↦ X′ ]ᴿ q →
  (⊑-renameᵗ²ᵢ assm hτ hσ p)
    [ σ β ↦ renameᵗ σ X′ ]ᴿ
  (⊑-renameᵗ²ᵢ assm hτ hσ q)
replace-right-rename²ᵢ assm hτ hσ replace-right-id★ =
  replace-right-id★
replace-right-rename²ᵢ assm hτ hσ replace-right-idˣ =
  replace-right-idˣ
replace-right-rename²ᵢ assm hτ hσ
    (replace-right-variable q) =
  replace-right-variable (⊑-renameᵗ²ᵢ assm hτ hσ q)
replace-right-rename²ᵢ assm hτ hσ replace-right-idι =
  replace-right-idι
replace-right-rename²ᵢ assm hτ hσ
    (replace-right-function replace₁ replace₂) =
  replace-right-function
    (replace-right-rename²ᵢ assm hτ hσ replace₁)
    (replace-right-rename²ᵢ assm hτ hσ replace₂)
replace-right-rename²ᵢ
    {τ = τ} {σ = σ} {β = β} {X′ = X′}
    assm hτ hσ (replace-right-∀ replace) =
  replace-right-∀
    (subst
      (λ Y →
        (⊑-renameᵗ²ᵢ
          (rename-assm²-⇑ᵢ assm)
          (TyRenameWf-ext hτ)
          (TyRenameWf-ext hσ)
          _)
          [ suc (σ β) ↦ Y ]ᴿ
        (⊑-renameᵗ²ᵢ
          (rename-assm²-⇑ᵢ assm)
          (TyRenameWf-ext hτ)
          (TyRenameWf-ext hσ)
          _))
      (renameᵗ-ext-suc-comm σ X′)
      (replace-right-rename²ᵢ
        (rename-assm²-⇑ᵢ assm)
        (TyRenameWf-ext hτ)
        (TyRenameWf-ext hσ)
        replace))
replace-right-rename²ᵢ assm hτ hσ replace-right-tag =
  replace-right-tag
replace-right-rename²ᵢ assm hτ hσ
    (replace-right-function-tag replace₁ replace₂) =
  replace-right-function-tag
    (replace-right-rename²ᵢ assm hτ hσ replace₁)
    (replace-right-rename²ᵢ assm hτ hσ replace₂)
replace-right-rename²ᵢ assm hτ hσ replace-right-tagˣ =
  replace-right-tagˣ
replace-right-rename²ᵢ assm hτ hσ
    (replace-right-ν replace) =
  replace-right-ν
    (replace-right-rename²ᵢ
      (rename-assm²-⇑ᴸᵢ assm)
      (TyRenameWf-ext hτ)
      hσ
      replace)


replace-paired-rename²ᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ A A′ B B′ α β X X′}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (assm : ∀ {a : ImpAssm} →
    a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ) →
  (hτ : TyRenameWf Δᴸ Θᴸ τ) →
  (hσ : TyRenameWf Δᴿ Θᴿ σ) →
  p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
  (⊑-renameᵗ²ᵢ assm hτ hσ p)
    [ τ α ↦ renameᵗ τ X
    ⊑⟨ ⊑-renameᵗ²ᵢ assm hτ hσ pX ⟩
    renameᵗ σ X′ ↤ σ β ]ᴾ
  (⊑-renameᵗ²ᵢ assm hτ hσ q)
replace-paired-rename²ᵢ assm hτ hσ replace-paired-id★ =
  replace-paired-id★
replace-paired-rename²ᵢ assm hτ hσ replace-paired-idˣ =
  replace-paired-idˣ
replace-paired-rename²ᵢ assm hτ hσ
    (replace-paired-variables eq) =
  replace-paired-variables
    (trans (shape-rename assm hτ hσ _)
      (trans eq (sym (shape-rename assm hτ hσ _))))
replace-paired-rename²ᵢ assm hτ hσ replace-paired-idι =
  replace-paired-idι
replace-paired-rename²ᵢ assm hτ hσ
    (replace-paired-function replace₁ replace₂) =
  replace-paired-function
    (replace-paired-rename²ᵢ assm hτ hσ replace₁)
    (replace-paired-rename²ᵢ assm hτ hσ replace₂)
replace-paired-rename²ᵢ
    {τ = τ} {σ = σ} {α = α} {β = β}
    {X = X} {X′ = X′} {pX = pX}
    assm hτ hσ
    (replace-paired-∀
      {α = α} {β = β} {X = X} {X′ = X′} {pX = pX}
      replace) =
  replace-paired-∀
    {α = τ α} {β = σ β}
    {X = renameᵗ τ X} {X′ = renameᵗ σ X′}
    {pX = ⊑-renameᵗ²ᵢ assm hτ hσ pX}
    (replace-paired-evidence-shape
      (trans
        (shape-lift∀ᵢ (⊑-renameᵗ²ᵢ assm hτ hσ pX))
        (trans
          (shape-rename assm hτ hσ pX)
          (sym
            (trans
              (shape-transport-imprecision-endpoints
                (renameᵗ-ext-suc-comm τ X)
                (renameᵗ-ext-suc-comm σ X′)
                (⊑-renameᵗ²ᵢ
                  (rename-assm²-⇑ᵢ assm)
                  (TyRenameWf-ext hτ)
                  (TyRenameWf-ext hσ)
                  (⊑-lift∀ᵢ pX)))
              (trans
                (shape-rename
                  (rename-assm²-⇑ᵢ assm)
                  (TyRenameWf-ext hτ)
                  (TyRenameWf-ext hσ)
                  (⊑-lift∀ᵢ pX))
                (shape-lift∀ᵢ pX))))))
      (replace-paired-transport-evidence-endpoints
        (renameᵗ-ext-suc-comm τ X)
        (renameᵗ-ext-suc-comm σ X′)
        (replace-paired-rename²ᵢ
          {τ = extᵗ τ} {σ = extᵗ σ}
          {α = suc α} {β = suc β}
          {X = ⇑ᵗ X} {X′ = ⇑ᵗ X′}
          {pX = ⊑-lift∀ᵢ pX}
          (rename-assm²-⇑ᵢ assm)
          (TyRenameWf-ext hτ)
          (TyRenameWf-ext hσ)
          replace)))
replace-paired-rename²ᵢ assm hτ hσ replace-paired-tag =
  replace-paired-tag
replace-paired-rename²ᵢ assm hτ hσ
    (replace-paired-function-tag replace₁ replace₂) =
  replace-paired-function-tag
    (replace-paired-rename²ᵢ assm hτ hσ replace₁)
    (replace-paired-rename²ᵢ assm hτ hσ replace₂)
replace-paired-rename²ᵢ assm hτ hσ replace-paired-tagˣ =
  replace-paired-tagˣ
replace-paired-rename²ᵢ
    {τ = τ} {σ = σ} {α = α} {β = β}
    {X = X} {X′ = X′} {pX = pX}
    assm hτ hσ
    (replace-paired-ν
      {α = α} {β = β} {X = X} {X′ = X′} {pX = pX}
      replace) =
  replace-paired-ν
    (replace-paired-evidence-shape
      (trans
        (shape-source-liftνᵢ
          (⊑-renameᵗ²ᵢ assm hτ hσ pX))
        (trans
          (shape-rename assm hτ hσ pX)
          (sym
            (trans
              (shape-transport-imprecision-endpoints
                (renameᵗ-ext-suc-comm τ X)
                refl
                (⊑-renameᵗ²ᵢ
                  (rename-assm²-⇑ᴸᵢ assm)
                  (TyRenameWf-ext hτ)
                  hσ
                  (⊑-source-liftνᵢ pX)))
              (trans
                (shape-rename
                  (rename-assm²-⇑ᴸᵢ assm)
                  (TyRenameWf-ext hτ)
                  hσ
                  (⊑-source-liftνᵢ pX))
                (shape-source-liftνᵢ pX))))))
      (replace-paired-transport-evidence-endpoints
        (renameᵗ-ext-suc-comm τ X)
        refl
        (replace-paired-rename²ᵢ
          {τ = extᵗ τ} {σ = σ}
          {α = suc α} {β = β}
          {X = ⇑ᵗ X} {X′ = X′}
          {pX = ⊑-source-liftνᵢ pX}
          (rename-assm²-⇑ᴸᵢ assm)
          (TyRenameWf-ext hτ)
          hσ
          replace)))


replace-paired-open∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ X X′ α β}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {p : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ suc Δᴿ}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ} →
  (α⊑β : (α ˣ⊑ˣ β) ∈ Φ) →
  (α<Δᴸ : α < Δᴸ) →
  (β<Δᴿ : β < Δᴿ) →
  (∀ⁱ p) [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ (∀ⁱ q) →
  (⊑-open∀ᵢ α⊑β α<Δᴸ β<Δᴿ p)
    [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ
  (⊑-open∀ᵢ α⊑β α<Δᴸ β<Δᴿ q)
replace-paired-open∀ᵢ
    {X = X} {X′ = X′} {α = α} {β = β} {pX = pX}
    α⊑β α<Δᴸ β<Δᴿ
    (replace-paired-∀ replace) =
  replace-paired-evidence-shape
    (sym
      (trans
        (shape-transport-imprecision-endpoints
          (renameᵗ-single-suc-cancel α X)
          (renameᵗ-single-suc-cancel β X′)
          renamed-pX)
        (trans
          (shape-rename
            (rename-assm²-open∀ᵢ α⊑β)
            (singleRenameᵗ-Wf-< α<Δᴸ)
            (singleRenameᵗ-Wf-< β<Δᴿ)
            (⊑-lift∀ᵢ pX))
          (shape-lift∀ᵢ pX))))
    (replace-paired-transport-evidence-endpoints
      (renameᵗ-single-suc-cancel α X)
      (renameᵗ-single-suc-cancel β X′)
      (replace-paired-rename²ᵢ
        (rename-assm²-open∀ᵢ α⊑β)
        (singleRenameᵗ-Wf-< α<Δᴸ)
        (singleRenameᵗ-Wf-< β<Δᴿ)
        replace))
  where
    renamed-pX =
      ⊑-renameᵗ²ᵢ
        (rename-assm²-open∀ᵢ α⊑β)
        (singleRenameᵗ-Wf-< α<Δᴸ)
        (singleRenameᵗ-Wf-< β<Δᴿ)
        (⊑-lift∀ᵢ pX)


replace-left-rename-leftᵢ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ A A′ B α X}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ} →
  (assm : ∀ {a : ImpAssm} →
    a ∈ Φ → rename-assm²ᵢ τ id a ∈ Ψ) →
  (hτ : TyRenameWf Δᴸ Δᴸ′ τ) →
  p [ α ↦ X ]ᴸ q →
  (⊑-rename-leftᵢ τ assm hτ p)
    [ τ α ↦ renameᵗ τ X ]ᴸ
  (⊑-rename-leftᵢ τ assm hτ q)
replace-left-rename-leftᵢ assm hτ replace-left-id★ =
  replace-left-id★
replace-left-rename-leftᵢ assm hτ replace-left-idˣ =
  replace-left-idˣ
replace-left-rename-leftᵢ assm hτ
    (replace-left-variable q) =
  replace-left-variable (⊑-rename-leftᵢ _ assm hτ q)
replace-left-rename-leftᵢ assm hτ replace-left-idι =
  replace-left-idι
replace-left-rename-leftᵢ assm hτ
    (replace-left-function replace₁ replace₂) =
  replace-left-function
    (replace-left-rename-leftᵢ assm hτ replace₁)
    (replace-left-rename-leftᵢ assm hτ replace₂)
replace-left-rename-leftᵢ
    {τ = τ} {α = α} {X = X}
    assm hτ (replace-left-∀ replace) =
  replace-left-∀
    (subst
      (λ Y →
        (⊑-rename-leftᵢ
          (extᵗ τ)
          (rename-assm²-∀-leftᵢ assm)
          (TyRenameWf-ext hτ)
          _)
          [ suc (τ α) ↦ Y ]ᴸ
        (⊑-rename-leftᵢ
          (extᵗ τ)
          (rename-assm²-∀-leftᵢ assm)
          (TyRenameWf-ext hτ)
          _))
      (renameᵗ-ext-suc-comm τ X)
      (replace-left-rename-leftᵢ
        (rename-assm²-∀-leftᵢ assm)
        (TyRenameWf-ext hτ)
        replace))
replace-left-rename-leftᵢ assm hτ replace-left-tag =
  replace-left-tag
replace-left-rename-leftᵢ assm hτ
    (replace-left-function-tag replace₁ replace₂) =
  replace-left-function-tag
    (replace-left-rename-leftᵢ assm hτ replace₁)
    (replace-left-rename-leftᵢ assm hτ replace₂)
replace-left-rename-leftᵢ assm hτ replace-left-tagˣ =
  replace-left-tagˣ
replace-left-rename-leftᵢ assm hτ
    (replace-left-seal q) =
  replace-left-seal (⊑-rename-leftᵢ _ assm hτ q)
replace-left-rename-leftᵢ
    {τ = τ} {α = α} {X = X}
    assm hτ (replace-left-ν replace) =
  replace-left-ν
    (subst
      (λ Y →
        (⊑-rename-leftᵢ
          (extᵗ τ)
          (rename-assm²-⇑ᴸᵢ assm)
          (TyRenameWf-ext hτ)
          _)
          [ suc (τ α) ↦ Y ]ᴸ
        (⊑-rename-leftᵢ
          (extᵗ τ)
          (rename-assm²-⇑ᴸᵢ assm)
          (TyRenameWf-ext hτ)
          _))
      (renameᵗ-ext-suc-comm τ X)
      (replace-left-rename-leftᵢ
        (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ)
        replace))


replace-right-rename-leftᵢ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ A A′ B′ β X′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  (assm : ∀ {a : ImpAssm} →
    a ∈ Φ → rename-assm²ᵢ τ id a ∈ Ψ) →
  (hτ : TyRenameWf Δᴸ Δᴸ′ τ) →
  p [ β ↦ X′ ]ᴿ q →
  (⊑-rename-leftᵢ τ assm hτ p)
    [ β ↦ X′ ]ᴿ
  (⊑-rename-leftᵢ τ assm hτ q)
replace-right-rename-leftᵢ assm hτ replace-right-id★ =
  replace-right-id★
replace-right-rename-leftᵢ assm hτ replace-right-idˣ =
  replace-right-idˣ
replace-right-rename-leftᵢ assm hτ
    (replace-right-variable q) =
  replace-right-variable (⊑-rename-leftᵢ _ assm hτ q)
replace-right-rename-leftᵢ assm hτ replace-right-idι =
  replace-right-idι
replace-right-rename-leftᵢ assm hτ
    (replace-right-function replace₁ replace₂) =
  replace-right-function
    (replace-right-rename-leftᵢ assm hτ replace₁)
    (replace-right-rename-leftᵢ assm hτ replace₂)
replace-right-rename-leftᵢ assm hτ
    (replace-right-∀ replace) =
  replace-right-∀
    (replace-right-rename-leftᵢ
      (rename-assm²-∀-leftᵢ assm)
      (TyRenameWf-ext hτ)
      replace)
replace-right-rename-leftᵢ assm hτ replace-right-tag =
  replace-right-tag
replace-right-rename-leftᵢ assm hτ
    (replace-right-function-tag replace₁ replace₂) =
  replace-right-function-tag
    (replace-right-rename-leftᵢ assm hτ replace₁)
    (replace-right-rename-leftᵢ assm hτ replace₂)
replace-right-rename-leftᵢ assm hτ replace-right-tagˣ =
  replace-right-tagˣ
replace-right-rename-leftᵢ assm hτ
    (replace-right-ν replace) =
  replace-right-ν
    (replace-right-rename-leftᵢ
      (rename-assm²-⇑ᴸᵢ assm)
      (TyRenameWf-ext hτ)
      replace)


replace-paired-rename-leftᵢ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ A A′ B B′ α β X X′}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (assm : ∀ {a : ImpAssm} →
    a ∈ Φ → rename-assm²ᵢ τ id a ∈ Ψ) →
  (hτ : TyRenameWf Δᴸ Δᴸ′ τ) →
  p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
  (⊑-rename-leftᵢ τ assm hτ p)
    [ τ α ↦ renameᵗ τ X
    ⊑⟨ ⊑-rename-leftᵢ τ assm hτ pX ⟩
    X′ ↤ β ]ᴾ
  (⊑-rename-leftᵢ τ assm hτ q)
replace-paired-rename-leftᵢ assm hτ replace-paired-id★ =
  replace-paired-id★
replace-paired-rename-leftᵢ assm hτ replace-paired-idˣ =
  replace-paired-idˣ
replace-paired-rename-leftᵢ assm hτ
    (replace-paired-variables eq) =
  replace-paired-variables
    (trans (shape-rename-left assm hτ _)
      (trans eq (sym (shape-rename-left assm hτ _))))
replace-paired-rename-leftᵢ assm hτ replace-paired-idι =
  replace-paired-idι
replace-paired-rename-leftᵢ assm hτ
    (replace-paired-function replace₁ replace₂) =
  replace-paired-function
    (replace-paired-rename-leftᵢ assm hτ replace₁)
    (replace-paired-rename-leftᵢ assm hτ replace₂)
replace-paired-rename-leftᵢ
    {τ = τ} {α = α} {β = β}
    {X = X} {X′ = X′} {pX = pX}
    assm hτ
    (replace-paired-∀
      {α = α} {β = β} {X = X} {X′ = X′} {pX = pX}
      replace) =
  replace-paired-∀
    {α = τ α} {β = β}
    {X = renameᵗ τ X} {X′ = X′}
    {pX = ⊑-rename-leftᵢ τ assm hτ pX}
    (replace-paired-evidence-shape
      (trans
        (shape-lift∀ᵢ (⊑-rename-leftᵢ τ assm hτ pX))
        (trans
          (shape-rename-left assm hτ pX)
          (sym
            (trans
              (shape-transport-imprecision-endpoints
                (renameᵗ-ext-suc-comm τ X)
                refl
                (⊑-rename-leftᵢ
                  (extᵗ τ)
                  (rename-assm²-∀-leftᵢ assm)
                  (TyRenameWf-ext hτ)
                  (⊑-lift∀ᵢ pX)))
              (trans
                (shape-rename-left
                  (rename-assm²-∀-leftᵢ assm)
                  (TyRenameWf-ext hτ)
                  (⊑-lift∀ᵢ pX))
                (shape-lift∀ᵢ pX))))))
      (replace-paired-transport-evidence-endpoints
        (renameᵗ-ext-suc-comm τ X)
        refl
        (replace-paired-rename-leftᵢ
          {τ = extᵗ τ}
          {α = suc α} {β = suc β}
          {X = ⇑ᵗ X} {X′ = ⇑ᵗ X′}
          {pX = ⊑-lift∀ᵢ pX}
          (rename-assm²-∀-leftᵢ assm)
          (TyRenameWf-ext hτ)
          replace)))
replace-paired-rename-leftᵢ assm hτ replace-paired-tag =
  replace-paired-tag
replace-paired-rename-leftᵢ assm hτ
    (replace-paired-function-tag replace₁ replace₂) =
  replace-paired-function-tag
    (replace-paired-rename-leftᵢ assm hτ replace₁)
    (replace-paired-rename-leftᵢ assm hτ replace₂)
replace-paired-rename-leftᵢ assm hτ replace-paired-tagˣ =
  replace-paired-tagˣ
replace-paired-rename-leftᵢ
    {τ = τ} {α = α} {β = β}
    {X = X} {X′ = X′} {pX = pX}
    assm hτ
    (replace-paired-ν
      {α = α} {β = β} {X = X} {X′ = X′} {pX = pX}
      replace) =
  replace-paired-ν
    (replace-paired-evidence-shape
      (trans
        (shape-source-liftνᵢ
          (⊑-rename-leftᵢ τ assm hτ pX))
        (trans
          (shape-rename-left assm hτ pX)
          (sym
            (trans
              (shape-transport-imprecision-endpoints
                (renameᵗ-ext-suc-comm τ X)
                refl
                (⊑-rename-leftᵢ
                  (extᵗ τ)
                  (rename-assm²-⇑ᴸᵢ assm)
                  (TyRenameWf-ext hτ)
                  (⊑-source-liftνᵢ pX)))
              (trans
                (shape-rename-left
                  (rename-assm²-⇑ᴸᵢ assm)
                  (TyRenameWf-ext hτ)
                  (⊑-source-liftνᵢ pX))
                (shape-source-liftνᵢ pX))))))
      (replace-paired-transport-evidence-endpoints
        (renameᵗ-ext-suc-comm τ X)
        refl
        (replace-paired-rename-leftᵢ
          {τ = extᵗ τ}
          {α = suc α} {β = β}
          {X = ⇑ᵗ X} {X′ = X′}
          {pX = ⊑-source-liftνᵢ pX}
          (rename-assm²-⇑ᴸᵢ assm)
          (TyRenameWf-ext hτ)
          replace)))


replace-left-source-shape :
  ∀ {Φ Δᴸ Δᴿ A A′ B α X}
    {p p′ : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ} →
  ⌊ p′ ⌋ ≡ ⌊ p ⌋ →
  p [ α ↦ X ]ᴸ q →
  p′ [ α ↦ X ]ᴸ q
replace-left-source-shape {p′ = id★} eq replace-left-id★ =
  replace-left-id★
replace-left-source-shape {p′ = idˣ x∈ A<Δ B<Δ} eq
    replace-left-idˣ =
  replace-left-idˣ
replace-left-source-shape {p′ = idˣ x∈ A<Δ B<Δ} eq
    (replace-left-variable q) =
  replace-left-variable q
replace-left-source-shape {p′ = idι} eq replace-left-idι =
  replace-left-idι
replace-left-source-shape {p′ = p₁′ ↦ p₂′} eq
    (replace-left-function replace₁ replace₂) =
  replace-left-function
    (replace-left-source-shape
      (proj₁ (↦ˢ-injective eq)) replace₁)
    (replace-left-source-shape
      (proj₂ (↦ˢ-injective eq)) replace₂)
replace-left-source-shape {p′ = ∀ⁱ p′} eq
    (replace-left-∀ replace) =
  replace-left-∀
    (replace-left-source-shape (∀ˢ-injective eq) replace)
replace-left-source-shape {p′ = tag _} eq replace-left-tag =
  replace-left-tag
replace-left-source-shape {p′ = tag p₁′ ⇛ p₂′} eq
    (replace-left-function-tag replace₁ replace₂) =
  replace-left-function-tag
    (replace-left-source-shape
      (proj₁ (tag-⇛ˢ-injective eq)) replace₁)
    (replace-left-source-shape
      (proj₂ (tag-⇛ˢ-injective eq)) replace₂)
replace-left-source-shape {p′ = tagˣ x∈ A<Δ} eq
    replace-left-tagˣ =
  replace-left-tagˣ
replace-left-source-shape {p′ = tagˣ x∈ A<Δ} eq
    (replace-left-seal q) =
  replace-left-seal q
replace-left-source-shape {p′ = ν safe occ p′} eq
    (replace-left-ν replace) =
  replace-left-ν
    (replace-left-source-shape (νˢ-injective eq) replace)


replace-left-target-shape :
  ∀ {Φ Δᴸ Δᴿ A A′ B α X}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q q′ : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ} →
  ⌊ q′ ⌋ ≡ ⌊ q ⌋ →
  p [ α ↦ X ]ᴸ q →
  p [ α ↦ X ]ᴸ q′
replace-left-target-shape {q′ = id★} eq replace-left-id★ =
  replace-left-id★
replace-left-target-shape {q′ = idˣ x∈ A<Δ B<Δ} eq
    replace-left-idˣ =
  replace-left-idˣ
replace-left-target-shape {q′ = q′} eq
    (replace-left-variable q) =
  replace-left-variable q′
replace-left-target-shape {q′ = idι} eq replace-left-idι =
  replace-left-idι
replace-left-target-shape {q′ = q₁′ ↦ q₂′} eq
    (replace-left-function replace₁ replace₂) =
  replace-left-function
    (replace-left-target-shape
      (proj₁ (↦ˢ-injective eq)) replace₁)
    (replace-left-target-shape
      (proj₂ (↦ˢ-injective eq)) replace₂)
replace-left-target-shape {q′ = ∀ⁱ q′} eq
    (replace-left-∀ replace) =
  replace-left-∀
    (replace-left-target-shape (∀ˢ-injective eq) replace)
replace-left-target-shape {q′ = tag _} eq replace-left-tag =
  replace-left-tag
replace-left-target-shape {q′ = tag q₁′ ⇛ q₂′} eq
    (replace-left-function-tag replace₁ replace₂) =
  replace-left-function-tag
    (replace-left-target-shape
      (proj₁ (tag-⇛ˢ-injective eq)) replace₁)
    (replace-left-target-shape
      (proj₂ (tag-⇛ˢ-injective eq)) replace₂)
replace-left-target-shape {q′ = tagˣ x∈ A<Δ} eq
    replace-left-tagˣ =
  replace-left-tagˣ
replace-left-target-shape {q′ = q′} eq
    (replace-left-seal q) =
  replace-left-seal q′
replace-left-target-shape {q′ = ν safe occ q′} eq
    (replace-left-ν replace) =
  replace-left-ν
    (replace-left-target-shape (νˢ-injective eq) replace)


replace-right-source-shape :
  ∀ {Φ Δᴸ Δᴿ A A′ B′ β X′}
    {p p′ : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  ⌊ p′ ⌋ ≡ ⌊ p ⌋ →
  p [ β ↦ X′ ]ᴿ q →
  p′ [ β ↦ X′ ]ᴿ q
replace-right-source-shape {p′ = id★} eq replace-right-id★ =
  replace-right-id★
replace-right-source-shape {p′ = idˣ x∈ A<Δ B<Δ} eq
    replace-right-idˣ =
  replace-right-idˣ
replace-right-source-shape {p′ = idˣ x∈ A<Δ B<Δ} eq
    (replace-right-variable q) =
  replace-right-variable q
replace-right-source-shape {p′ = idι} eq replace-right-idι =
  replace-right-idι
replace-right-source-shape {p′ = p₁′ ↦ p₂′} eq
    (replace-right-function replace₁ replace₂) =
  replace-right-function
    (replace-right-source-shape
      (proj₁ (↦ˢ-injective eq)) replace₁)
    (replace-right-source-shape
      (proj₂ (↦ˢ-injective eq)) replace₂)
replace-right-source-shape {p′ = ∀ⁱ p′} eq
    (replace-right-∀ replace) =
  replace-right-∀
    (replace-right-source-shape (∀ˢ-injective eq) replace)
replace-right-source-shape {p′ = tag _} eq replace-right-tag =
  replace-right-tag
replace-right-source-shape {p′ = tag p₁′ ⇛ p₂′} eq
    (replace-right-function-tag replace₁ replace₂) =
  replace-right-function-tag
    (replace-right-source-shape
      (proj₁ (tag-⇛ˢ-injective eq)) replace₁)
    (replace-right-source-shape
      (proj₂ (tag-⇛ˢ-injective eq)) replace₂)
replace-right-source-shape {p′ = tagˣ x∈ A<Δ} eq
    replace-right-tagˣ =
  replace-right-tagˣ
replace-right-source-shape {p′ = ν safe occ p′} eq
    (replace-right-ν replace) =
  replace-right-ν
    (replace-right-source-shape (νˢ-injective eq) replace)


replace-right-target-shape :
  ∀ {Φ Δᴸ Δᴿ A A′ B′ β X′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q q′ : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  ⌊ q′ ⌋ ≡ ⌊ q ⌋ →
  p [ β ↦ X′ ]ᴿ q →
  p [ β ↦ X′ ]ᴿ q′
replace-right-target-shape {q′ = id★} eq replace-right-id★ =
  replace-right-id★
replace-right-target-shape {q′ = idˣ x∈ A<Δ B<Δ} eq
    replace-right-idˣ =
  replace-right-idˣ
replace-right-target-shape {q′ = q′} eq
    (replace-right-variable q) =
  replace-right-variable q′
replace-right-target-shape {q′ = idι} eq replace-right-idι =
  replace-right-idι
replace-right-target-shape {q′ = q₁′ ↦ q₂′} eq
    (replace-right-function replace₁ replace₂) =
  replace-right-function
    (replace-right-target-shape
      (proj₁ (↦ˢ-injective eq)) replace₁)
    (replace-right-target-shape
      (proj₂ (↦ˢ-injective eq)) replace₂)
replace-right-target-shape {q′ = ∀ⁱ q′} eq
    (replace-right-∀ replace) =
  replace-right-∀
    (replace-right-target-shape (∀ˢ-injective eq) replace)
replace-right-target-shape {q′ = tag _} eq replace-right-tag =
  replace-right-tag
replace-right-target-shape {q′ = tag q₁′ ⇛ q₂′} eq
    (replace-right-function-tag replace₁ replace₂) =
  replace-right-function-tag
    (replace-right-target-shape
      (proj₁ (tag-⇛ˢ-injective eq)) replace₁)
    (replace-right-target-shape
      (proj₂ (tag-⇛ˢ-injective eq)) replace₂)
replace-right-target-shape {q′ = tagˣ x∈ A<Δ} eq
    replace-right-tagˣ =
  replace-right-tagˣ
replace-right-target-shape {q′ = ν safe occ q′} eq
    (replace-right-ν replace) =
  replace-right-ν
    (replace-right-target-shape (νˢ-injective eq) replace)


replace-paired-source-shape :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ α β X X′}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {p p′ : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  ⌊ p′ ⌋ ≡ ⌊ p ⌋ →
  p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
  p′ [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q
replace-paired-source-shape {p′ = id★} eq
    replace-paired-id★ =
  replace-paired-id★
replace-paired-source-shape {p′ = idˣ x∈ A<Δ B<Δ} eq
    replace-paired-idˣ =
  replace-paired-idˣ
replace-paired-source-shape {p′ = idˣ x∈ A<Δ B<Δ} eq
    (replace-paired-variables result-shape) =
  replace-paired-variables result-shape
replace-paired-source-shape {p′ = idι} eq
    replace-paired-idι =
  replace-paired-idι
replace-paired-source-shape {p′ = p₁′ ↦ p₂′} eq
    (replace-paired-function replace₁ replace₂) =
  replace-paired-function
    (replace-paired-source-shape
      (proj₁ (↦ˢ-injective eq)) replace₁)
    (replace-paired-source-shape
      (proj₂ (↦ˢ-injective eq)) replace₂)
replace-paired-source-shape {p′ = ∀ⁱ p′} eq
    (replace-paired-∀ replace) =
  replace-paired-∀
    (replace-paired-source-shape (∀ˢ-injective eq) replace)
replace-paired-source-shape {p′ = tag _} eq
    replace-paired-tag =
  replace-paired-tag
replace-paired-source-shape {p′ = tag p₁′ ⇛ p₂′} eq
    (replace-paired-function-tag replace₁ replace₂) =
  replace-paired-function-tag
    (replace-paired-source-shape
      (proj₁ (tag-⇛ˢ-injective eq)) replace₁)
    (replace-paired-source-shape
      (proj₂ (tag-⇛ˢ-injective eq)) replace₂)
replace-paired-source-shape {p′ = tagˣ x∈ A<Δ} eq
    replace-paired-tagˣ =
  replace-paired-tagˣ
replace-paired-source-shape {p′ = ν safe occ p′} eq
    (replace-paired-ν replace) =
  replace-paired-ν
    (replace-paired-source-shape (νˢ-injective eq) replace)


replace-paired-target-shape :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ α β X X′}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q q′ : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  ⌊ q′ ⌋ ≡ ⌊ q ⌋ →
  p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
  p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q′
replace-paired-target-shape {q′ = id★} eq
    replace-paired-id★ =
  replace-paired-id★
replace-paired-target-shape {q′ = idˣ x∈ A<Δ B<Δ} eq
    replace-paired-idˣ =
  replace-paired-idˣ
replace-paired-target-shape {q′ = q′} eq
    (replace-paired-variables result-shape) =
  replace-paired-variables (trans eq result-shape)
replace-paired-target-shape {q′ = idι} eq
    replace-paired-idι =
  replace-paired-idι
replace-paired-target-shape {q′ = q₁′ ↦ q₂′} eq
    (replace-paired-function replace₁ replace₂) =
  replace-paired-function
    (replace-paired-target-shape
      (proj₁ (↦ˢ-injective eq)) replace₁)
    (replace-paired-target-shape
      (proj₂ (↦ˢ-injective eq)) replace₂)
replace-paired-target-shape {q′ = ∀ⁱ q′} eq
    (replace-paired-∀ replace) =
  replace-paired-∀
    (replace-paired-target-shape (∀ˢ-injective eq) replace)
replace-paired-target-shape {q′ = tag _} eq
    replace-paired-tag =
  replace-paired-tag
replace-paired-target-shape {q′ = tag q₁′ ⇛ q₂′} eq
    (replace-paired-function-tag replace₁ replace₂) =
  replace-paired-function-tag
    (replace-paired-target-shape
      (proj₁ (tag-⇛ˢ-injective eq)) replace₁)
    (replace-paired-target-shape
      (proj₂ (tag-⇛ˢ-injective eq)) replace₂)
replace-paired-target-shape {q′ = tagˣ x∈ A<Δ} eq
    replace-paired-tagˣ =
  replace-paired-tagˣ
replace-paired-target-shape {q′ = ν safe occ q′} eq
    (replace-paired-ν replace) =
  replace-paired-ν
    (replace-paired-target-shape (νˢ-injective eq) replace)
