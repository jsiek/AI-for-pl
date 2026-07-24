module
  proof.Store.RelEmbedding.NuImprecisionRelCtxRenameAlgebra
  where

-- File Charter:
--   * Proves reflexivity and composition for structural relational-context
--     renaming.
--   * Uses explicit precision-index uniqueness to identify proof-relevant
--     context entries after renaming.
--   * Is independent of term imprecision, simulation, catch-up, and
--     quotiented-term relations.
--   * Contains no postulate, hole, permissive option, termination bypass, or
--     broad DGG import.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import Imprecision using
  (ImpAssm; _ˣ⊑★; _ˣ⊑ˣ_)
open import NuTermImprecision using
  (CtxImp; ctx-imp)
open import Types using
  (Renameᵗ; renameᵗ)
open import
  proof.EndpointMLB.Core.MaximalLowerBoundsWf
  using
  ( rename-assm²-composeᵢ
  ; rename-assm²ᵢ
  ; ⊑-rename-at²ᵢ
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (PrecisionIndexUnique)
open import proof.Core.Properties.TypeProperties using
  (TyRenameWf; renameᵗ-compose; renameᵗ-id)
open import proof.Store.RelEmbedding.NuImprecisionRelCtxRenameDef


compose-rel-assm²ᵢ :
  ∀ {Φ Ψ Ω τ σ υ ω} →
  (∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ) →
  (∀ {a} → a ∈ Ψ → rename-assm²ᵢ υ ω a ∈ Ω) →
  ∀ {a} →
  a ∈ Φ →
  rename-assm²ᵢ (λ X → υ (τ X)) (λ X → ω (σ X)) a ∈ Ω
compose-rel-assm²ᵢ {Ω = Ω} {τ = τ} {σ = σ} {υ = υ} {ω = ω}
    assm₁ assm₂ {a = a} a∈ =
  subst (_∈ Ω) (rename-assm²-composeᵢ τ σ υ ω a)
    (assm₂ (assm₁ a∈))


rename-rel-assm²-idᵢ :
  ∀ (a : ImpAssm) →
  rename-assm²ᵢ (λ X → X) (λ X → X) a ≡ a
rename-rel-assm²-idᵢ (X ˣ⊑★) = refl
rename-rel-assm²-idᵢ (X ˣ⊑ˣ Y) = refl


rel-assm²-id∈ᵢ :
  ∀ {Φ a} →
  a ∈ Φ →
  rename-assm²ᵢ (λ X → X) (λ X → X) a ∈ Φ
rel-assm²-id∈ᵢ {Φ = Φ} {a = a} a∈ =
  subst (_∈ Φ) (sym (rename-rel-assm²-idᵢ a)) a∈


rel-ctx-rename-reflⁱ :
  ∀ {Φ Δᴸ Δᴿ} →
  PrecisionIndexUnique Φ →
  {γ : CtxImp Φ Δᴸ Δᴿ} →
  RelCtxRenameⁱ
    (λ X → X) (λ X → X) rel-assm²-id∈ᵢ
    (λ X<Δᴸ → X<Δᴸ) (λ X<Δᴿ → X<Δᴿ)
    γ γ
rel-ctx-rename-reflⁱ unique {γ = []} =
  rel-ctx-rename-[]
rel-ctx-rename-reflⁱ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} unique
    {γ = ctx-imp A B p ∷ γ} =
  subst
    (λ p′ →
      RelCtxRenameⁱ
        (λ X → X) (λ X → X) rel-assm²-id∈ᵢ
        (λ X<Δᴸ → X<Δᴸ) (λ X<Δᴿ → X<Δᴿ)
        (ctx-imp A B p ∷ γ)
        (ctx-imp A B p′ ∷ γ))
    (unique renamed-p p)
    (rel-ctx-rename-∷
      (sym (renameᵗ-id A))
      (sym (renameᵗ-id B))
      (rel-ctx-rename-reflⁱ unique))
  where
  renamed-p =
    ⊑-rename-at²ᵢ
      rel-assm²-id∈ᵢ
      (λ X<Δᴸ → X<Δᴸ)
      (λ X<Δᴿ → X<Δᴿ)
      (sym (renameᵗ-id A))
      (sym (renameᵗ-id B))
      p


rel-ctx-rename-composeⁱ :
  ∀ {Φ Ψ Ω Δᴸ Δᴿ Θᴸ Θᴿ Υᴸ Υᴿ τ σ υ ω}
    {assm₁ : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {assm₂ : ∀ {a} → a ∈ Ψ → rename-assm²ᵢ υ ω a ∈ Ω}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {hυ : TyRenameWf Θᴸ Υᴸ υ}
    {hω : TyRenameWf Θᴿ Υᴿ ω}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {γ″ : CtxImp Ω Υᴸ Υᴿ} →
  PrecisionIndexUnique Ω →
  RelCtxRenameⁱ τ σ assm₁ hτ hσ γ γ′ →
  RelCtxRenameⁱ υ ω assm₂ hυ hω γ′ γ″ →
  RelCtxRenameⁱ
    (λ X → υ (τ X))
    (λ X → ω (σ X))
    (compose-rel-assm²ᵢ assm₁ assm₂)
    (λ X<Δᴸ → hυ (hτ X<Δᴸ))
    (λ X<Δᴿ → hω (hσ X<Δᴿ))
    γ γ″
rel-ctx-rename-composeⁱ unique
    rel-ctx-rename-[] rel-ctx-rename-[] =
  rel-ctx-rename-[]
rel-ctx-rename-composeⁱ
    {Ω = Ω} {Υᴸ = Υᴸ} {Υᴿ = Υᴿ}
    {τ = τ} {σ = σ} {υ = υ} {ω = ω}
    {assm₁ = assm₁} {assm₂ = assm₂}
    {hτ = hτ} {hσ = hσ} {hυ = hυ} {hω = hω}
    unique
    (rel-ctx-rename-∷
      {γ = γ} {γ′ = γ′}
      {A = A} {A′ = A′} {B = B} {B′ = B′} {p = p}
      eqA₁ eqB₁ renameγ₁)
    (rel-ctx-rename-∷
      {γ = .γ′} {γ′ = γ″}
      {A = .A′} {A′ = A″} {B = .B′} {B′ = B″}
      eqA₂ eqB₂ renameγ₂)
    =
  subst
    (λ p′ →
      RelCtxRenameⁱ
        (λ X → υ (τ X))
        (λ X → ω (σ X))
        (compose-rel-assm²ᵢ assm₁ assm₂)
        (λ X< → hυ (hτ X<))
        (λ X< → hω (hσ X<))
        (ctx-imp A B p ∷ γ)
        (ctx-imp A″ B″ p′ ∷ γ″))
    (unique composed-p twice-renamed-p)
    (rel-ctx-rename-∷ eqA eqB
      (rel-ctx-rename-composeⁱ unique renameγ₁ renameγ₂))
  where
  eqA =
    trans eqA₂
      (trans (cong (renameᵗ υ) eqA₁)
        (renameᵗ-compose τ υ A))

  eqB =
    trans eqB₂
      (trans (cong (renameᵗ ω) eqB₁)
        (renameᵗ-compose σ ω B))

  composed-p =
    ⊑-rename-at²ᵢ
      (compose-rel-assm²ᵢ assm₁ assm₂)
      (λ X< → hυ (hτ X<))
      (λ X< → hω (hσ X<))
      eqA eqB p

  twice-renamed-p =
    ⊑-rename-at²ᵢ assm₂ hυ hω eqA₂ eqB₂
      (⊑-rename-at²ᵢ assm₁ hτ hσ eqA₁ eqB₁ p)
