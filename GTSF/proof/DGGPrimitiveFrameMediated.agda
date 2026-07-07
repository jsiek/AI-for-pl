module proof.DGGPrimitiveFrameMediated where

-- File Charter:
--   * Mediated-store DGG helpers for primitive addition frame cases.
--   * Keeps the larger source-catchup/right-frame proof scripts out of
--     proof.DynamicGradualGuaranteeMediated and the primitive delta helper.
--   * Currently exports the pure target-step `ξ-⊕₂` helper used after
--     source-side catchup of the left operand.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _++_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

open import Types
open import Coercions
open import Primitives using (addℕ)
open import NuTerms
open import NuReduction
open import StoreCorrespondence
open import MediatedNarrowing
open import proof.CatchupSeparated using
  ( applyLeftChanges
  ; applyRightChange
  ; applyLeftChanges-++
  )
open import proof.MediatedLeftInsertion using
  (left-changes-term-narrowingᵐ)
open import proof.ReductionProperties using
  ( applyTyCtxs-++
  ; applyTys-ℕ
  ; applyTys-ℕ-applyTys
  ; ⊕₁-↠
  ; ⊕₂-↠
  ; ↠-trans
  )
open import proof.DGGPrimitiveMediated using
  ( id-ℕ-narrowingᵐᶜ
  ; typed-id-ℕ-index-determinedᵐ
  )

primitive-right-after-left-frame-keepᵐ :
  ∀ {ΔL ΔR ρ M N WM M′ S′ χsM ΔL₁} →
  No• N →
  Value WM →
  No• WM →
  M —↠[ χsM ] WM →
  ΔL₁ ≡ applyTyCtxs χsM ΔL →
  StoreCorr ΔL₁ ΔR (applyLeftChanges χsM ρ) →
  ΔL₁ ∣ ΔR ∣ applyLeftChanges χsM ρ ∣ []
    ⊢ WM ⊒ M′ ∶ id (‵ `ℕ)
      ⦂ applyTys χsM (‵ `ℕ) ⊒ᵐ ‵ `ℕ →
  (∃[ χsN ] ∃[ P ] ∃[ ΔL₂ ] ∃[ ΔR′ ] ∃[ ρ′ ]
   ∃[ C ] ∃[ D ] ∃[ r ]
    (applyTerms χsM N —↠[ χsN ] P) ×
    (ΔL₂ ≡ applyTyCtxs χsN ΔL₁) ×
    (ΔR′ ≡ applyTyCtx keep ΔR) ×
    (ρ′ ≡ applyRightChange keep
      (applyLeftChanges χsN (applyLeftChanges χsM ρ))) ×
    (C ≡ applyTys χsN (applyTys χsM (‵ `ℕ))) ×
    (D ≡ applyTy keep (‵ `ℕ)) ×
    ΔL₂ ∣ ΔR′ ∣ ρ′ ∣ []
      ⊢ P ⊒ S′ ∶ r ⦂ C ⊒ᵐ D) →
  ∃[ χs ] ∃[ P ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
  ∃[ C ] ∃[ D ] ∃[ r ]
    (M ⊕[ addℕ ] N —↠[ χs ] P) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ΔR′ ≡ applyTyCtx keep ΔR) ×
    (ρ′ ≡ applyRightChange keep (applyLeftChanges χs ρ)) ×
    (C ≡ applyTys χs (‵ `ℕ)) ×
    (D ≡ applyTy keep (‵ `ℕ)) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
      ⊢ P ⊒ M′ ⊕[ addℕ ] S′ ∶ r ⦂ C ⊒ᵐ D
primitive-right-after-left-frame-keepᵐ
    {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ} {M = M} {N = N}
    {WM = WM} {M′ = M′} {S′ = S′} {χsM = χsM}
    {ΔL₁ = ΔL₁}
    noN vWM noWM M↠WM ΔL₁≡ corrM WM⊒M′
    (χsN , P , .(applyTyCtxs χsN ΔL₁) , .(applyTyCtx keep ΔR) ,
     .(applyRightChange keep
        (applyLeftChanges χsN (applyLeftChanges χsM ρ))) ,
     .(applyTys χsN (applyTys χsM (‵ `ℕ))) ,
     .(applyTy keep (‵ `ℕ)) , r ,
     N↠P , refl , refl , refl , refl , refl , P⊒S′) =
  let
    μP , rᶜ = typed-term-narrowing-coercionᵐ P⊒S′

    corrN :
      StoreCorr (applyTyCtxs χsN ΔL₁) ΔR
        (applyLeftChanges χsN (applyLeftChanges χsM ρ))
    corrN = narrowing-store-corrᵐᶜ rᶜ

    pℕᶜ :
      applyTyCtxs χsN ΔL₁ ∣ ΔR
        ∣ applyLeftChanges χsN (applyLeftChanges χsM ρ)
        ⊢ id (‵ `ℕ) ∶ᶜ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    pℕᶜ = id-ℕ-narrowingᵐᶜ corrN

    WM⊒M′N :
      applyTyCtxs χsN ΔL₁ ∣ ΔR
        ∣ applyLeftChanges χsN (applyLeftChanges χsM ρ) ∣ []
        ⊢ applyTerms χsN WM ⊒ M′ ∶ id (‵ `ℕ)
          ⦂ applyTys χsN (applyTys χsM (‵ `ℕ)) ⊒ᵐ ‵ `ℕ
    WM⊒M′N = left-changes-term-narrowingᵐ χsN corrN WM⊒M′

    endpointℕ :
      applyTys χsN (applyTys χsM (‵ `ℕ)) ≡ ‵ `ℕ
    endpointℕ = applyTys-ℕ-applyTys χsM χsN

    WM⊒M′ℕ :
      applyTyCtxs χsN ΔL₁ ∣ ΔR
        ∣ applyLeftChanges χsN (applyLeftChanges χsM ρ) ∣ []
        ⊢ applyTerms χsN WM ⊒ M′ ∶ id (‵ `ℕ)
          ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    WM⊒M′ℕ =
      subst
        (λ A →
          applyTyCtxs χsN ΔL₁ ∣ ΔR
            ∣ applyLeftChanges χsN (applyLeftChanges χsM ρ) ∣ []
            ⊢ applyTerms χsN WM ⊒ M′ ∶ id (‵ `ℕ)
              ⦂ A ⊒ᵐ ‵ `ℕ)
        endpointℕ
        WM⊒M′N

    P⊒S′ℕ :
      applyTyCtxs χsN ΔL₁ ∣ ΔR
        ∣ applyLeftChanges χsN (applyLeftChanges χsM ρ) ∣ []
        ⊢ P ⊒ S′ ∶ r ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    P⊒S′ℕ =
      subst
        (λ A →
          applyTyCtxs χsN ΔL₁ ∣ ΔR
            ∣ applyLeftChanges χsN (applyLeftChanges χsM ρ) ∣ []
            ⊢ P ⊒ S′ ∶ r ⦂ A ⊒ᵐ ‵ `ℕ)
        endpointℕ
        P⊒S′

    P⊒S′id :
      applyTyCtxs χsN ΔL₁ ∣ ΔR
        ∣ applyLeftChanges χsN (applyLeftChanges χsM ρ) ∣ []
        ⊢ P ⊒ S′ ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    P⊒S′id =
      subst
        (λ q →
          applyTyCtxs χsN ΔL₁ ∣ ΔR
            ∣ applyLeftChanges χsN (applyLeftChanges χsM ρ) ∣ []
            ⊢ P ⊒ S′ ∶ q ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ)
        (typed-id-ℕ-index-determinedᵐ P⊒S′ℕ)
        P⊒S′ℕ

    framed⊒ :
      applyTyCtxs χsN ΔL₁ ∣ ΔR
        ∣ applyLeftChanges χsN (applyLeftChanges χsM ρ) ∣ []
        ⊢ applyTerms χsN WM ⊕[ addℕ ] P
          ⊒ M′ ⊕[ addℕ ] S′
          ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    framed⊒ = ⊕⊒⊕ᵗ pℕᶜ WM⊒M′ℕ P⊒S′id

    χs : StoreChanges
    χs = χsM ++ χsN

    source-steps :
      M ⊕[ addℕ ] N —↠[ χs ] applyTerms χsN WM ⊕[ addℕ ] P
    source-steps =
      ↠-trans (⊕₁-↠ noN M↠WM) (⊕₂-↠ vWM noWM N↠P)

    ΔL₂≡total :
      applyTyCtxs χsN ΔL₁ ≡ applyTyCtxs χs ΔL
    ΔL₂≡total =
      trans (cong (applyTyCtxs χsN) ΔL₁≡)
        (sym (applyTyCtxs-++ χsM χsN ΔL))

    ρ≡total :
      applyLeftChanges χsN (applyLeftChanges χsM ρ) ≡
        applyLeftChanges χs ρ
    ρ≡total = sym (applyLeftChanges-++ χsM χsN ρ)
  in
  χs ,
  applyTerms χsN WM ⊕[ addℕ ] P ,
  applyTyCtxs χsN ΔL₁ ,
  ΔR ,
  applyLeftChanges χsN (applyLeftChanges χsM ρ) ,
  ‵ `ℕ ,
  ‵ `ℕ ,
  id (‵ `ℕ) ,
  source-steps ,
  ΔL₂≡total ,
  refl ,
  ρ≡total ,
  sym (applyTys-ℕ χs) ,
  refl ,
  framed⊒
