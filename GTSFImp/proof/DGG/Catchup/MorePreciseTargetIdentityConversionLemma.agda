{-# OPTIONS --safe #-}

module
  proof.DGG.Catchup.MorePreciseTargetIdentityConversionLemma where

-- File Charter:
--   * Catches up one generator-absent target reveal or conceal around two
--     already related values.
--   * Function and universal conversions remain value wrappers; identity
--     leaves take exactly one keep step and expose the underlying value.
--   * Returns the reduction, value, world evolution, and final CTI evidence
--     directly, without a named result wrapper or proof parameter.

open import Data.Product using (_×_; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Types using (Ty; TyVar)
open import TyStore using (TyStore)
open import Conversion using (Conv↑; Conv↓; _⊢↑[_⦂_]_; _⊢↓[_⦂_]_)
import Conversion as Conv
import CastTerms as CT
open import CastTerms using (Term; Value; Ctx; Σᵉ; _↑_; _↓_)
open import Reduction using
  ( StoreChanges; []; _∷_; keep; applyTys
  ; pure-step; id-reveal; id-conceal
  ; _—↠[_]_; _—→[_]⟨_⟩_; _∎[]
  )
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.ConversionPivotAlignment using
  ( generator-absent; revealGeneratorPosition
  ; concealGeneratorPosition
  )
open import proof.DGG.World using (_⊑ᶜ_; _⊑ᵀ⟨_⟩_)
open import proof.DGG.WorldEvolution using (evolution-keep)
open import proof.DGG.WorldEvolutionSequence using
  ( MultiWorldEvolution; evolutions-refl; evolutions-step-right )
import proof.Imprecision as PI


target-identity-reveal-catchup : ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ} {V : Term (CT.Δᵉ Γᴸ)}
    {V′ : Term (CT.Δᵉ Γᴿ)} {A : Ty (CT.Δᵉ Γᴸ)}
    {B B′ Rᴿ : Ty (CT.Δᵉ Γᴿ)} {Xᴿ : TyVar (CT.Δᵉ Γᴿ)}
    {c′ : Conv↑ (CT.Δᵉ Γᴿ) B B′}
    {p : A ⊑ᵀ⟨ γ ⟩ B}
  → (c′⊢ : Σᵉ Γᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
  → revealGeneratorPosition c′⊢ ≡ generator-absent
  → γ ⊢² V ⊑ V′ ∶ p
  → (q : A ⊑ᵀ⟨ γ ⟩ B′)
  → Value V′
  → Σ[ χsᴿ ∈ StoreChanges (CT.Δᵉ Γᴿ) (CT.Δᵉ Γᴿ) ]
    Σ[ W′ ∈ Term (CT.Δᵉ Γᴿ) ]
      (V′ ↑ c′ —↠[ χsᴿ ] W′)
      × Value W′
      × MultiWorldEvolution {W = γ} {W′ = γ} [] χsᴿ
      × (∀ T → applyTys χsᴿ T ≡ T)
      × (γ ⊢² V ⊑ W′ ∶ q)
target-identity-reveal-catchup (Conv.⊢↑-unseal member) () related q vV′
target-identity-reveal-catchup c′⊢@(Conv.⊢↑-⇒ left right)
    absent related q vV′ =
  [] , _ , (_ ∎[]) , (vV′ CT.↑ CT.fun) , evolutions-refl ,
    (λ T → refl) ,
    CTI.⊑reveal-identity c′⊢ absent related q
target-identity-reveal-catchup c′⊢@(Conv.⊢↑-∀ eq body)
    absent related q vV′ =
  [] , _ , (_ ∎[]) , (vV′ CT.↑ CT.all) , evolutions-refl ,
    (λ T → refl) ,
    CTI.⊑reveal-identity c′⊢ absent related q
target-identity-reveal-catchup (Conv.⊢↑-id-var member X≠Y)
    absent related q vV′ =
  keep ∷ [] , _ ,
    (_ —→[ keep ]⟨ pure-step (id-reveal vV′) ⟩ _ ∎[]) , vV′ ,
    evolutions-step-right refl evolution-keep evolutions-refl ,
    (λ T → refl) ,
    subst (λ r → _ CTI.⊢² _ ⊑ _ ∶ r) (PI.⊑-unique _ q) related
target-identity-reveal-catchup (Conv.⊢↑-id-base member)
    absent related q vV′ =
  keep ∷ [] , _ ,
    (_ —→[ keep ]⟨ pure-step (id-reveal vV′) ⟩ _ ∎[]) , vV′ ,
    evolutions-step-right refl evolution-keep evolutions-refl ,
    (λ T → refl) ,
    subst (λ r → _ CTI.⊢² _ ⊑ _ ∶ r) (PI.⊑-unique _ q) related
target-identity-reveal-catchup (Conv.⊢↑-id-star member)
    absent related q vV′ =
  keep ∷ [] , _ ,
    (_ —→[ keep ]⟨ pure-step (id-reveal vV′) ⟩ _ ∎[]) , vV′ ,
    evolutions-step-right refl evolution-keep evolutions-refl ,
    (λ T → refl) ,
    subst (λ r → _ CTI.⊢² _ ⊑ _ ∶ r) (PI.⊑-unique _ q) related


target-identity-conceal-catchup : ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ} {V : Term (CT.Δᵉ Γᴸ)}
    {V′ : Term (CT.Δᵉ Γᴿ)} {A : Ty (CT.Δᵉ Γᴸ)}
    {B B′ Rᴿ : Ty (CT.Δᵉ Γᴿ)} {Xᴿ : TyVar (CT.Δᵉ Γᴿ)}
    {c′ : Conv↓ (CT.Δᵉ Γᴿ) B B′}
    {p : A ⊑ᵀ⟨ γ ⟩ B}
  → (c′⊢ : Σᵉ Γᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
  → concealGeneratorPosition c′⊢ ≡ generator-absent
  → γ ⊢² V ⊑ V′ ∶ p
  → (q : A ⊑ᵀ⟨ γ ⟩ B′)
  → Value V′
  → Σ[ χsᴿ ∈ StoreChanges (CT.Δᵉ Γᴿ) (CT.Δᵉ Γᴿ) ]
    Σ[ W′ ∈ Term (CT.Δᵉ Γᴿ) ]
      (V′ ↓ c′ —↠[ χsᴿ ] W′)
      × Value W′
      × MultiWorldEvolution {W = γ} {W′ = γ} [] χsᴿ
      × (∀ T → applyTys χsᴿ T ≡ T)
      × (γ ⊢² V ⊑ W′ ∶ q)
target-identity-conceal-catchup (Conv.⊢↓-seal member) () related q vV′
target-identity-conceal-catchup c′⊢@(Conv.⊢↓-⇒ left right)
    absent related q vV′ =
  [] , _ , (_ ∎[]) , (vV′ CT.↓ CT.fun) , evolutions-refl ,
    (λ T → refl) ,
    CTI.⊑conceal-identity c′⊢ absent related q
target-identity-conceal-catchup c′⊢@(Conv.⊢↓-∀ eq body)
    absent related q vV′ =
  [] , _ , (_ ∎[]) , (vV′ CT.↓ CT.all) , evolutions-refl ,
    (λ T → refl) ,
    CTI.⊑conceal-identity c′⊢ absent related q
target-identity-conceal-catchup (Conv.⊢↓-id-var member X≠Y)
    absent related q vV′ =
  keep ∷ [] , _ ,
    (_ —→[ keep ]⟨ pure-step (id-conceal vV′) ⟩ _ ∎[]) , vV′ ,
    evolutions-step-right refl evolution-keep evolutions-refl ,
    (λ T → refl) ,
    subst (λ r → _ CTI.⊢² _ ⊑ _ ∶ r) (PI.⊑-unique _ q) related
target-identity-conceal-catchup (Conv.⊢↓-id-base member)
    absent related q vV′ =
  keep ∷ [] , _ ,
    (_ —→[ keep ]⟨ pure-step (id-conceal vV′) ⟩ _ ∎[]) , vV′ ,
    evolutions-step-right refl evolution-keep evolutions-refl ,
    (λ T → refl) ,
    subst (λ r → _ CTI.⊢² _ ⊑ _ ∶ r) (PI.⊑-unique _ q) related
target-identity-conceal-catchup (Conv.⊢↓-id-star member)
    absent related q vV′ =
  keep ∷ [] , _ ,
    (_ —→[ keep ]⟨ pure-step (id-conceal vV′) ⟩ _ ∎[]) , vV′ ,
    evolutions-step-right refl evolution-keep evolutions-refl ,
    (λ T → refl) ,
    subst (λ r → _ CTI.⊢² _ ⊑ _ ∶ r) (PI.⊑-unique _ q) related
