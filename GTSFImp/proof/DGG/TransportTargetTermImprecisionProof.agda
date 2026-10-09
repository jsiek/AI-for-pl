{-# OPTIONS --safe #-}

module proof.DGG.TransportTargetTermImprecisionProof where

-- File Charter:
--   * Proves target-only CTI transport by induction on an evolution whose
--     source store-change trace is empty.
--   * Uses the canonical target-bind CTI induction for target allocation.
--   * Has no source-allocation or aligned-source-allocation case.

open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; subst)

open import Types using (Ty)
open import CastTerms using (Ctx; Δᵉ; Term)
open import Reduction using
  (StoreChange; StoreChanges; applyTerms)
  renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.TransportTargetTermImprecisionDef using
  (TransportTargetTermImprecisionᵀ)
open import proof.DGG.TransportTermImprecisionStepDef using
  (TransportTargetBindᵀ)
open import proof.DGG.World
open import proof.DGG.WorldEvolution using
  ( CtxChange
  ; WorldEvolution
  ; keep-ctx
  ; storeChange
  ; evolution-keep
  ; evolution-bind-right
  ; evolution-⊑ᵀ
  )
open import proof.DGG.WorldEvolutionSequence using
  ( MultiWorldEvolution
  ; evolutions-refl
  ; evolutions-step-right
  ; multi-⊑ᵀ
  ; ctx-change-term-value
  ; ctx-change-term-value-as
  )


module _ (transport-target-bind : TransportTargetBindᵀ) where

  transport-target-step : ∀
      {Γᴸ Γᴿ Γᴿ¹ : Ctx}
      {γ : Γᴸ ⊑ᶜ Γᴿ} {γ¹ : Γᴸ ⊑ᶜ Γᴿ¹}
      {stepᴿ : CtxChange Γᴿ Γᴿ¹}
      {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
      {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
    → (one : WorldEvolution
        {W = γ} {W′ = γ¹} keep-ctx stepᴿ)
    → γ ⊢² M ⊑ M′ ∶ p
    → γ¹ ⊢² M ⊑ ctx-change-term-value stepᴿ M′
        ∶ evolution-⊑ᵀ one p
  transport-target-step evolution-keep related = related
  transport-target-step
      (evolution-bind-right fresh eqᴿ) related =
    transport-target-bind fresh eqᴿ related

  finish-target-step : ∀
      {Γᴸ Γᴿ Γᴿ¹ Γᴿ′ : Ctx}
      {γ : Γᴸ ⊑ᶜ Γᴿ} {γ¹ : Γᴸ ⊑ᶜ Γᴿ¹}
      {γ′ : Γᴸ ⊑ᶜ Γᴿ′}
      {χᴿ : StoreChange (Δᵉ Γᴿ) (Δᵉ Γᴿ¹)}
      {χsᴿ : StoreChanges (Δᵉ Γᴿ¹) (Δᵉ Γᴿ′)}
      {stepᴿ : CtxChange Γᴿ Γᴿ¹}
      {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
      {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
    → (eqᴿ : storeChange stepᴿ ≡ χᴿ)
    → (one : WorldEvolution
        {W = γ} {W′ = γ¹} keep-ctx stepᴿ)
    → (tail : MultiWorldEvolution
        {W = γ¹} {W′ = γ′} []ˢ χsᴿ)
    → γ′ ⊢² M ⊑
        applyTerms χsᴿ (ctx-change-term-value stepᴿ M′)
        ∶ multi-⊑ᵀ tail (evolution-⊑ᵀ one p)
    → γ′ ⊢² M ⊑ applyTerms (χᴿ ∷ˢ χsᴿ) M′
        ∶ multi-⊑ᵀ (evolutions-step-right eqᴿ one tail) p
  finish-target-step {γ′ = γ′} {χsᴿ = χsᴿ}
      {stepᴿ = stepᴿ} {M = M} {M′ = M′} {p = p}
      refl one tail related =
    subst
      (λ N′ → γ′ ⊢² M ⊑ N′
        ∶ multi-⊑ᵀ tail (evolution-⊑ᵀ one p))
      (cong (applyTerms χsᴿ)
        (ctx-change-term-value-as {step = stepᴿ} refl M′))
      related

  transport-target-term-imprecision : TransportTargetTermImprecisionᵀ
  transport-target-term-imprecision evolutions-refl related = related
  transport-target-term-imprecision
      (evolutions-step-right refl one tail) related =
    finish-target-step refl one tail
      (transport-target-term-imprecision tail
        (transport-target-step one related))
