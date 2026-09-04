{-# OPTIONS --safe #-}

module proof.DGG.TransportTermImprecisionProof where

-- File Charter:
--   * Lifts a canonical one-step CTI transport through a sequence of world
--     evolutions.
--   * Instantiates the one-step theorem from the five structural allocation
--     inductions, which remain explicit module parameters.
--   * Imports no parked world, compatibility world, or legacy context layer.

open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; subst)

open import Types using (Ty)
open import CastTerms using (Ctx; Δᵉ; Term)
open import Reduction using
  (StoreChange; StoreChanges; _∷_; applyTerm; applyTerms)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.TransportTermImprecisionDef
open import proof.DGG.TransportTermImprecisionStepDef
import proof.DGG.TransportTermImprecisionStepProof as Step
open import proof.DGG.World
open import proof.DGG.WorldEvolution using
  ( CtxChange
  ; WorldEvolution
  ; keep-ctx
  ; storeChange
  ; evolution-keep
  ; evolution-⊑ᵀ
  )
open import proof.DGG.WorldEvolutionSequence using
  ( MultiWorldEvolution
  ; evolutions-refl
  ; evolutions-step-left
  ; evolutions-step-right
  ; evolutions-step-both
  ; multi-⊑ᵀ
  ; ctx-change-term-value
  ; ctx-change-term-value-as
  )


module _ (transport-step : TransportTermImprecisionStepᵀ) where

  finish-left : ∀
      {Γᴸ Γᴿ Γᴸ¹ Γᴸ′ Γᴿ′ : Ctx}
      {γ : Γᴸ ⊑ᶜ Γᴿ} {γ¹ : Γᴸ¹ ⊑ᶜ Γᴿ}
      {γ′ : Γᴸ′ ⊑ᶜ Γᴿ′}
      {χᴸ : StoreChange (Δᵉ Γᴸ) (Δᵉ Γᴸ¹)}
      {χsᴸ : StoreChanges (Δᵉ Γᴸ¹) (Δᵉ Γᴸ′)}
      {χsᴿ : StoreChanges (Δᵉ Γᴿ) (Δᵉ Γᴿ′)}
      {stepᴸ : CtxChange Γᴸ Γᴸ¹}
      {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
      {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
    → (eqᴸ : storeChange stepᴸ ≡ χᴸ)
    → (one : WorldEvolution {W = γ} {W′ = γ¹} stepᴸ keep-ctx)
    → (tail : MultiWorldEvolution
        {W = γ¹} {W′ = γ′} χsᴸ χsᴿ)
    → γ′ ⊢² applyTerms χsᴸ (ctx-change-term-value stepᴸ M)
        ⊑ applyTerms χsᴿ M′
        ∶ multi-⊑ᵀ tail (evolution-⊑ᵀ one p)
    → γ′ ⊢² applyTerms (χᴸ ∷ χsᴸ) M
        ⊑ applyTerms χsᴿ M′
        ∶ multi-⊑ᵀ (evolutions-step-left eqᴸ one tail) p
  finish-left {γ′ = γ′} {χsᴸ = χsᴸ} {χsᴿ = χsᴿ}
      {stepᴸ = stepᴸ}
      {M = M} {M′ = M′} {p = p} refl one tail related =
    subst
      (λ N → γ′ ⊢² N ⊑ applyTerms χsᴿ M′
        ∶ multi-⊑ᵀ tail (evolution-⊑ᵀ one p))
      (cong (applyTerms χsᴸ)
        (ctx-change-term-value-as {step = stepᴸ} refl M))
      related

  finish-right : ∀
      {Γᴸ Γᴿ Γᴿ¹ Γᴸ′ Γᴿ′ : Ctx}
      {γ : Γᴸ ⊑ᶜ Γᴿ} {γ¹ : Γᴸ ⊑ᶜ Γᴿ¹}
      {γ′ : Γᴸ′ ⊑ᶜ Γᴿ′}
      {χᴿ : StoreChange (Δᵉ Γᴿ) (Δᵉ Γᴿ¹)}
      {χsᴸ : StoreChanges (Δᵉ Γᴸ) (Δᵉ Γᴸ′)}
      {χsᴿ : StoreChanges (Δᵉ Γᴿ¹) (Δᵉ Γᴿ′)}
      {stepᴿ : CtxChange Γᴿ Γᴿ¹}
      {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
      {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
    → (eqᴿ : storeChange stepᴿ ≡ χᴿ)
    → (one : WorldEvolution {W = γ} {W′ = γ¹} keep-ctx stepᴿ)
    → (tail : MultiWorldEvolution
        {W = γ¹} {W′ = γ′} χsᴸ χsᴿ)
    → γ′ ⊢² applyTerms χsᴸ M
        ⊑ applyTerms χsᴿ (ctx-change-term-value stepᴿ M′)
        ∶ multi-⊑ᵀ tail (evolution-⊑ᵀ one p)
    → γ′ ⊢² applyTerms χsᴸ M
        ⊑ applyTerms (χᴿ ∷ χsᴿ) M′
        ∶ multi-⊑ᵀ (evolutions-step-right eqᴿ one tail) p
  finish-right {γ′ = γ′} {χsᴸ = χsᴸ} {χsᴿ = χsᴿ}
      {stepᴿ = stepᴿ}
      {M = M} {M′ = M′} {p = p} refl one tail related =
    subst
      (λ N′ → γ′ ⊢² applyTerms χsᴸ M ⊑ N′
        ∶ multi-⊑ᵀ tail (evolution-⊑ᵀ one p))
      (cong (applyTerms χsᴿ)
        (ctx-change-term-value-as {step = stepᴿ} refl M′))
      related

  finish-both : ∀
      {Γᴸ Γᴿ Γᴸ¹ Γᴿ¹ Γᴸ′ Γᴿ′ : Ctx}
      {γ : Γᴸ ⊑ᶜ Γᴿ} {γ¹ : Γᴸ¹ ⊑ᶜ Γᴿ¹}
      {γ′ : Γᴸ′ ⊑ᶜ Γᴿ′}
      {χᴸ : StoreChange (Δᵉ Γᴸ) (Δᵉ Γᴸ¹)}
      {χᴿ : StoreChange (Δᵉ Γᴿ) (Δᵉ Γᴿ¹)}
      {χsᴸ : StoreChanges (Δᵉ Γᴸ¹) (Δᵉ Γᴸ′)}
      {χsᴿ : StoreChanges (Δᵉ Γᴿ¹) (Δᵉ Γᴿ′)}
      {stepᴸ : CtxChange Γᴸ Γᴸ¹}
      {stepᴿ : CtxChange Γᴿ Γᴿ¹}
      {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
      {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
    → (eqᴸ : storeChange stepᴸ ≡ χᴸ)
    → (eqᴿ : storeChange stepᴿ ≡ χᴿ)
    → (one : WorldEvolution {W = γ} {W′ = γ¹} stepᴸ stepᴿ)
    → (tail : MultiWorldEvolution
        {W = γ¹} {W′ = γ′} χsᴸ χsᴿ)
    → γ′ ⊢² applyTerms χsᴸ (ctx-change-term-value stepᴸ M)
        ⊑ applyTerms χsᴿ (ctx-change-term-value stepᴿ M′)
        ∶ multi-⊑ᵀ tail (evolution-⊑ᵀ one p)
    → γ′ ⊢² applyTerms (χᴸ ∷ χsᴸ) M
        ⊑ applyTerms (χᴿ ∷ χsᴿ) M′
        ∶ multi-⊑ᵀ
          (evolutions-step-both eqᴸ eqᴿ one tail) p
  finish-both {γ′ = γ′} {χsᴸ = χsᴸ} {χsᴿ = χsᴿ}
      {stepᴸ = stepᴸ} {stepᴿ = stepᴿ}
      {M = M} {M′ = M′} {p = p}
      refl refl one tail related =
    subst
      (λ N′ → γ′ ⊢² applyTerms χsᴸ
          (applyTerm (storeChange stepᴸ) M) ⊑ N′
        ∶ multi-⊑ᵀ tail (evolution-⊑ᵀ one p))
      (cong (applyTerms χsᴿ)
        (ctx-change-term-value-as {step = stepᴿ} refl M′))
      (subst
        (λ N → γ′ ⊢² N ⊑ applyTerms χsᴿ
            (ctx-change-term-value stepᴿ M′)
          ∶ multi-⊑ᵀ tail (evolution-⊑ᵀ one p))
        (cong (applyTerms χsᴸ)
          (ctx-change-term-value-as {step = stepᴸ} refl M))
        related)

  transport-term-imprecision-from-step : TransportTermImprecisionᵀ
  transport-term-imprecision-from-step evolutions-refl related =
    related

  transport-term-imprecision-from-step
      (evolutions-step-left eqᴸ one tail) related =
    finish-left eqᴸ one tail
      (transport-term-imprecision-from-step
        tail (transport-step one related))

  transport-term-imprecision-from-step
      (evolutions-step-right eqᴿ one tail) related =
    finish-right eqᴿ one tail
      (transport-term-imprecision-from-step
        tail (transport-step one related))

  transport-term-imprecision-from-step
      (evolutions-step-both eqᴸ eqᴿ one tail) related =
    finish-both eqᴸ eqᴿ one tail
      (transport-term-imprecision-from-step
        tail (transport-step one related))


module _
    (transport-source-bind : TransportSourceBindᵀ)
    (transport-aligned-source-bind : TransportAlignedSourceBindᵀ)
    (transport-target-bind : TransportTargetBindᵀ)
    (transport-paired-bind : TransportPairedBindᵀ)
    (transport-paired-star-bind : TransportPairedStarBindᵀ)
    where

  transport-term-imprecision : TransportTermImprecisionᵀ
  transport-term-imprecision =
    transport-term-imprecision-from-step
      (Step.transport-term-imprecision-step
        transport-source-bind transport-aligned-source-bind
        transport-target-bind
        transport-paired-bind transport-paired-star-bind)
