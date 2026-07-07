{-# OPTIONS --allow-unsolved-metas #-}

module proof.DynamicGradualGuaranteeMediated where

-- File Charter:
--   * Main dynamic gradual guarantee skeleton for the mediated narrowing
--     relation.
--   * Ports the recursive shape of `DynamicGradualGuaranteeSeparated` to
--     `MediatedNarrowing`: source-side store changes use
--     `left-changes-term-narrowingᵐ`, so mediated coercion raws are not
--     rewritten by the IH setup.
--   * Deliberately leaves the framing, beta/delta packaging, and ν/seal
--     simulation obligations as holes while recording the intended
--     recursive calls.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (subst; sym)

open import Types
open import Coercions
open import NarrowWiden using (cross; id-‵; id-＇; id★)
open import Primitives using (addℕ)
open import NuTerms
open import NuReduction
open import StoreCorrespondence
open import MediatedNarrowing
open import proof.CatchupSeparated using
  ( applyLeftChanges
  ; applyRightChange
  )
open import proof.CatchupMediated using (catchup-lemmaᵐ)
open import proof.MediatedLeftInsertion using
  (left-changes-term-narrowingᵐ)
open import proof.NuTermProperties using
  ( renameᵗᵐ-preserves-No•
  ; renameᵗᵐ-preserves-Value
  )
open import proof.NuPreservation using (runtime-⟨⟩)
open import proof.DGGBetaMediated using (mediated-dgg-beta)
open import proof.DGGBetaCastMediated using (mediated-dgg-beta-cast)
open import proof.DGGPrimitiveMediated using
  ( mediated-⊕-δ
  ; primitive-left-frame-keepᵐ
  ; primitive-right-frame-keepᵐ
  )
open import proof.DGGCastMediated using
  ( source-cast-minus-resultᵐ
  ; target-cast-plus-inner-resultᵐ
  ; target-blameᵐ
  ; target-cast-minus-β-idᵐ
  ; target-cast-plus-β-idᵐ
  )

------------------------------------------------------------------------
-- Runtime transport used by IH setup after source catchup
------------------------------------------------------------------------

runtime-⇑ᵗᵐ :
  ∀ {M} →
  RuntimeOK M →
  RuntimeOK (⇑ᵗᵐ M)
runtime-⇑ᵗᵐ (ok-no noM) =
  ok-no (renameᵗᵐ-preserves-No• suc noM)
runtime-⇑ᵗᵐ (ok-• vV noV) =
  ok-• (renameᵗᵐ-preserves-Value suc vV)
       (renameᵗᵐ-preserves-No• suc noV)
runtime-⇑ᵗᵐ (ok-·₁ okL noM) =
  ok-·₁ (runtime-⇑ᵗᵐ okL) (renameᵗᵐ-preserves-No• suc noM)
runtime-⇑ᵗᵐ (ok-·₂ vV noV okM) =
  ok-·₂ (renameᵗᵐ-preserves-Value suc vV)
        (renameᵗᵐ-preserves-No• suc noV)
        (runtime-⇑ᵗᵐ okM)
runtime-⇑ᵗᵐ (ok-ν okL) = ok-ν (runtime-⇑ᵗᵐ okL)
runtime-⇑ᵗᵐ (ok-⊕₁ okL noM) =
  ok-⊕₁ (runtime-⇑ᵗᵐ okL) (renameᵗᵐ-preserves-No• suc noM)
runtime-⇑ᵗᵐ (ok-⊕₂ vL noL okM) =
  ok-⊕₂ (renameᵗᵐ-preserves-Value suc vL)
        (renameᵗᵐ-preserves-No• suc noL)
        (runtime-⇑ᵗᵐ okM)
runtime-⇑ᵗᵐ (ok-⟨⟩ okM) = ok-⟨⟩ (runtime-⇑ᵗᵐ okM)

applyTerm-preserves-RuntimeOK :
  ∀ χ {M} →
  RuntimeOK M →
  RuntimeOK (applyTerm χ M)
applyTerm-preserves-RuntimeOK keep okM = okM
applyTerm-preserves-RuntimeOK (bind A) okM = runtime-⇑ᵗᵐ okM

applyTerms-preserves-RuntimeOK :
  ∀ χs {M} →
  RuntimeOK M →
  RuntimeOK (applyTerms χs M)
applyTerms-preserves-RuntimeOK [] okM = okM
applyTerms-preserves-RuntimeOK (χ ∷ χs) okM =
  applyTerms-preserves-RuntimeOK χs
    (applyTerm-preserves-RuntimeOK χ okM)

------------------------------------------------------------------------
-- Full mediated DGG skeleton
------------------------------------------------------------------------

dynamicGradualGuaranteeᵐ :
  ∀ {ΔL ΔR ρ M M′ N′ A B p χ′} →
  RuntimeOK M →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ᵐ B →
  M′ —→[ χ′ ] N′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
  ∃[ C ] ∃[ D ] ∃[ r ]
    (M —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
    (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
    (C ≡ applyTys χs A) ×
    (D ≡ applyTy χ′ B) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ N ⊒ N′ ∶ r ⦂ C ⊒ᵐ D
dynamicGradualGuaranteeᵐ okM (⊒blameᵗ M⊢ q⊒)
    (pure-step ())
dynamicGradualGuaranteeᵐ okM (x⊒xᵗ qᶜ x∋q)
    (pure-step ())
dynamicGradualGuaranteeᵐ okM (ƛ⊒ƛᵗ p↦qᶜ N⊒N′)
    (pure-step ())
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R} {M′ = (ƛ N′) · V′}
    okLR
    (·⊒·ᵗ p↦q-wholeᶜ L⊒ƛ R⊒V′)
    (pure-step (β vV′)) =
  let
    rec =
      mediated-dgg-beta
        okLR
        vV′
        p↦q-wholeᶜ
        (fun-narrow-domain-dual-typingᵐᶜ p↦q-wholeᶜ)
        L⊒ƛ
        R⊒V′
  in
  let
    χs , N , ΔL′ , ρ′ , C , D , r ,
      source-steps , ΔL′≡ , ρ′≡ , C≡ , D≡ , N⊒N′[V′] = rec
  in
  χs ,
  N ,
  ΔL′ ,
  ΔR ,
  ρ′ ,
  C ,
  D ,
  r ,
  source-steps ,
  ΔL′≡ ,
  refl ,
  ρ′≡ ,
  C≡ ,
  D≡ ,
  N⊒N′[V′]
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R}
    okM
    (·⊒·ᵗ p↦qᶜ L⊒L′ R⊒R′)
    (pure-step (β-↦ {V = V′} {W = W′} vV′ vW′)) =
  let
    rec =
      mediated-dgg-beta-cast
        okM
        vV′
        vW′
        p↦qᶜ
        (fun-narrow-domain-dual-typingᵐᶜ p↦qᶜ)
        L⊒L′
        R⊒R′
  in
  let
    χs , N , ΔL′ , ρ′ , C , D , r ,
      source-steps , ΔL′≡ , ρ′≡ , C≡ , D≡ , N⊒target = rec
  in
  χs ,
  N ,
  ΔL′ ,
  ΔR ,
  ρ′ ,
  C ,
  D ,
  r ,
  source-steps ,
  ΔL′≡ ,
  refl ,
  ρ′≡ ,
  C≡ ,
  D≡ ,
  N⊒target
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R}
    okM
    app@(·⊒·ᵗ p↦qᶜ L⊒L′ R⊒R′)
    (pure-step blame-·₁) =
  target-blameᵐ app
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R}
    okM
    app@(·⊒·ᵗ p↦qᶜ L⊒L′ R⊒R′)
    (pure-step (blame-·₂ vV)) =
  target-blameᵐ app
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R} {M′ = L′ · R′} {χ′ = χ′}
    (ok-no (no•-· noL noR))
    (·⊒·ᵗ p↦q-wholeᶜ L⊒L′ R⊒R′)
    (ξ-·₁ {L′ = S′} L′→S′ shiftR′) =
  let
    rec = dynamicGradualGuaranteeᵐ (ok-no noL) L⊒L′ L′→S′
  in
  {! ξ-·₁-mediated-frame-no-source-bullet !}
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R} {M′ = L′ · R′} {χ′ = χ′}
    (ok-·₁ okL noR)
    (·⊒·ᵗ p↦q-wholeᶜ L⊒L′ R⊒R′)
    (ξ-·₁ {L′ = S′} L′→S′ shiftR′) =
  let
    rec = dynamicGradualGuaranteeᵐ okL L⊒L′ L′→S′
  in
  {! ξ-·₁-mediated-frame-source-left-running !}
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R} {M′ = L′ · R′} {χ′ = χ′}
    (ok-·₂ vL noL okR)
    app@(·⊒·ᵗ p↦q-wholeᶜ L⊒L′ R⊒R′)
    (ξ-·₁ {L′ = S′} L′→S′ shiftR′) =
  {! ξ-·₁-mediated-frame-source-left-already-value !}
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R} {M′ = L′ · R′} {χ′ = χ′}
    (ok-no (no•-· noL noR))
    (·⊒·ᵗ {A = A} p↦q-wholeᶜ L⊒L′ R⊒R′)
    (ξ-·₂ {M′ = S′} vL′ shiftL′ R′→S′) =
  let
    χsL , WL , ΔL₁ ,
      vWL , noWL , L↠WL , ΔL₁≡ , ρL-corr ,
      leftL≡ , rightL≡ , pLᶜ , WL⊒L′ =
      catchup-lemmaᵐ (ok-no noL) vL′ L⊒L′

    corrL :
      StoreCorr (applyTyCtxs χsL ΔL) ΔR (applyLeftChanges χsL ρ)
    corrL =
      subst (λ Δ → StoreCorr Δ ΔR (applyLeftChanges χsL ρ))
        ΔL₁≡
        ρL-corr

    R⊒R′L :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
        ⊢ applyTerms χsL R ⊒ R′
          ∶ fun-narrow-domain-dualᵐᶜ p↦q-wholeᶜ
            ⦂ applyTys χsL A ⊒ᵐ _
    R⊒R′L =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
            ⊢ applyTerms χsL R ⊒ R′
              ∶ fun-narrow-domain-dualᵐᶜ p↦q-wholeᶜ
                ⦂ applyTys χsL A ⊒ᵐ _)
        (sym ΔL₁≡)
        (left-changes-term-narrowingᵐ χsL corrL R⊒R′)

    rec =
      dynamicGradualGuaranteeᵐ
        (applyTerms-preserves-RuntimeOK χsL (ok-no noR))
        R⊒R′L
        R′→S′
  in
  {! ξ-·₂-mediated-frame-after-left-catchup-no-source-bullet !}
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R} {M′ = L′ · R′} {χ′ = χ′}
    (ok-·₁ okL noR)
    (·⊒·ᵗ {A = A} p↦q-wholeᶜ L⊒L′ R⊒R′)
    (ξ-·₂ {M′ = S′} vL′ shiftL′ R′→S′) =
  let
    χsL , WL , ΔL₁ ,
      vWL , noWL , L↠WL , ΔL₁≡ , ρL-corr ,
      leftL≡ , rightL≡ , pLᶜ , WL⊒L′ =
      catchup-lemmaᵐ okL vL′ L⊒L′

    corrL :
      StoreCorr (applyTyCtxs χsL ΔL) ΔR (applyLeftChanges χsL ρ)
    corrL =
      subst (λ Δ → StoreCorr Δ ΔR (applyLeftChanges χsL ρ))
        ΔL₁≡
        ρL-corr

    R⊒R′L :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
        ⊢ applyTerms χsL R ⊒ R′
          ∶ fun-narrow-domain-dualᵐᶜ p↦q-wholeᶜ
            ⦂ applyTys χsL A ⊒ᵐ _
    R⊒R′L =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
            ⊢ applyTerms χsL R ⊒ R′
              ∶ fun-narrow-domain-dualᵐᶜ p↦q-wholeᶜ
                ⦂ applyTys χsL A ⊒ᵐ _)
        (sym ΔL₁≡)
        (left-changes-term-narrowingᵐ χsL corrL R⊒R′)

    rec =
      dynamicGradualGuaranteeᵐ
        (applyTerms-preserves-RuntimeOK χsL (ok-no noR))
        R⊒R′L
        R′→S′
  in
  {! ξ-·₂-mediated-frame-after-left-catchup-source-left-running !}
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R} {M′ = L′ · R′} {χ′ = χ′}
    (ok-·₂ vL noL okR)
    (·⊒·ᵗ p↦q-wholeᶜ L⊒L′ R⊒R′)
    (ξ-·₂ {M′ = S′} vL′ shiftL′ R′→S′) =
  let
    rec = dynamicGradualGuaranteeᵐ okR R⊒R′ R′→S′
  in
  {! ξ-·₂-mediated-frame-source-left-already-value !}
dynamicGradualGuaranteeᵐ okM (Λ⊒Λᵗ allᶜ vV vV′ V⊒V′)
    (pure-step ())
dynamicGradualGuaranteeᵐ okM (⊒Λᵗ N⊢ genᶜ vV′ N⊒V′)
    (pure-step ())
dynamicGradualGuaranteeᵐ okM (κ⊒κᵗ κ qᶜ)
    (pure-step ())
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N}
    okMN
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (pure-step (δ-⊕ {m = m′} {n = n′})) =
  let
    rec = mediated-⊕-δ okMN M⊒M′ N⊒N′

    χs , P , ΔL′ , ρ′ , C , D , r ,
      source-steps , ΔL′≡ , ρ′≡ , C≡ℕ , D≡ℕ , P⊒P′ = rec
  in
  χs ,
  P ,
  ΔL′ ,
  ΔR ,
  ρ′ ,
  C ,
  D ,
  r ,
  source-steps ,
  ΔL′≡ ,
  refl ,
  ρ′≡ ,
  C≡ℕ ,
  D≡ℕ ,
  P⊒P′
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N}
    okMN
    add@(⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (pure-step blame-⊕₁) =
  target-blameᵐ add
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N}
    okMN
    add@(⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (pure-step (blame-⊕₂ vV)) =
  target-blameᵐ add
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N} {M′ = M′ ⊕[ addℕ ] N′}
    {χ′ = keep}
    (ok-no (no•-⊕ noM noN))
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (ξ-⊕₁ {χ = keep} {L′ = S′} M′→S′ shiftN′) =
  let
    rec = dynamicGradualGuaranteeᵐ (ok-no noM) M⊒M′ M′→S′
  in
  primitive-left-frame-keepᵐ noN N⊒N′ rec
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N} {M′ = M′ ⊕[ addℕ ] N′}
    {χ′ = bind X}
    (ok-no (no•-⊕ noM noN))
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (ξ-⊕₁ {χ = bind X} {L′ = S′} M′→S′ shiftN′) =
  let
    rec = dynamicGradualGuaranteeᵐ (ok-no noM) M⊒M′ M′→S′
  in
  {! ξ-⊕₁-mediated-frame-no-source-bullet-target-bind !}
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N} {M′ = M′ ⊕[ addℕ ] N′}
    {χ′ = keep}
    (ok-⊕₁ okM noN)
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (ξ-⊕₁ {χ = keep} {L′ = S′} M′→S′ shiftN′) =
  let
    rec = dynamicGradualGuaranteeᵐ okM M⊒M′ M′→S′
  in
  primitive-left-frame-keepᵐ noN N⊒N′ rec
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N} {M′ = M′ ⊕[ addℕ ] N′}
    {χ′ = bind X}
    (ok-⊕₁ okM noN)
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (ξ-⊕₁ {χ = bind X} {L′ = S′} M′→S′ shiftN′) =
  let
    rec = dynamicGradualGuaranteeᵐ okM M⊒M′ M′→S′
  in
  {! ξ-⊕₁-mediated-frame-source-left-running-target-bind !}
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N} {M′ = M′ ⊕[ addℕ ] N′}
    {χ′ = χ′}
    (ok-⊕₂ vM noM okN)
    add@(⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (ξ-⊕₁ {L′ = S′} M′→S′ shiftN′) =
  {! ξ-⊕₁-mediated-frame-source-left-already-value !}
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N} {M′ = M′ ⊕[ addℕ ] N′}
    {χ′ = χ′}
    (ok-no (no•-⊕ noM noN))
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (ξ-⊕₂ {M′ = S′} vM′ shiftM′ N′→S′) =
  let
    χsM , WM , ΔL₁ ,
      vWM , noWM , M↠WM , ΔL₁≡ , ρM-corr ,
      leftM≡ , rightM≡ , pMᶜ , WM⊒M′ =
      catchup-lemmaᵐ (ok-no noM) vM′ M⊒M′

    corrM :
      StoreCorr (applyTyCtxs χsM ΔL) ΔR (applyLeftChanges χsM ρ)
    corrM =
      subst (λ Δ → StoreCorr Δ ΔR (applyLeftChanges χsM ρ))
        ΔL₁≡
        ρM-corr

    N⊒N′M :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsM ρ ∣ []
        ⊢ applyTerms χsM N ⊒ N′ ∶ id (‵ `ℕ)
          ⦂ applyTys χsM (‵ `ℕ) ⊒ᵐ ‵ `ℕ
    N⊒N′M =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ applyLeftChanges χsM ρ ∣ []
            ⊢ applyTerms χsM N ⊒ N′ ∶ id (‵ `ℕ)
              ⦂ applyTys χsM (‵ `ℕ) ⊒ᵐ ‵ `ℕ)
        (sym ΔL₁≡)
        (left-changes-term-narrowingᵐ χsM corrM N⊒N′)

    rec =
      dynamicGradualGuaranteeᵐ
        (applyTerms-preserves-RuntimeOK χsM (ok-no noN))
        N⊒N′M
        N′→S′
  in
  {! ξ-⊕₂-mediated-frame-after-left-catchup-no-source-bullet !}
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N} {M′ = M′ ⊕[ addℕ ] N′}
    {χ′ = χ′}
    (ok-⊕₁ okM noN)
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (ξ-⊕₂ {M′ = S′} vM′ shiftM′ N′→S′) =
  let
    χsM , WM , ΔL₁ ,
      vWM , noWM , M↠WM , ΔL₁≡ , ρM-corr ,
      leftM≡ , rightM≡ , pMᶜ , WM⊒M′ =
      catchup-lemmaᵐ okM vM′ M⊒M′

    corrM :
      StoreCorr (applyTyCtxs χsM ΔL) ΔR (applyLeftChanges χsM ρ)
    corrM =
      subst (λ Δ → StoreCorr Δ ΔR (applyLeftChanges χsM ρ))
        ΔL₁≡
        ρM-corr

    N⊒N′M :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsM ρ ∣ []
        ⊢ applyTerms χsM N ⊒ N′ ∶ id (‵ `ℕ)
          ⦂ applyTys χsM (‵ `ℕ) ⊒ᵐ ‵ `ℕ
    N⊒N′M =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ applyLeftChanges χsM ρ ∣ []
            ⊢ applyTerms χsM N ⊒ N′ ∶ id (‵ `ℕ)
              ⦂ applyTys χsM (‵ `ℕ) ⊒ᵐ ‵ `ℕ)
        (sym ΔL₁≡)
        (left-changes-term-narrowingᵐ χsM corrM N⊒N′)

    rec =
      dynamicGradualGuaranteeᵐ
        (applyTerms-preserves-RuntimeOK χsM (ok-no noN))
        N⊒N′M
        N′→S′
  in
  {! ξ-⊕₂-mediated-frame-after-left-catchup-source-left-running !}
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N} {M′ = M′ ⊕[ addℕ ] N′}
    {χ′ = keep}
    (ok-⊕₂ vM noM okN)
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (ξ-⊕₂ {χ = keep} {M′ = S′} vM′ shiftM′ N′→S′) =
  let
    rec = dynamicGradualGuaranteeᵐ okN N⊒N′ N′→S′
  in
  primitive-right-frame-keepᵐ vM noM M⊒M′ rec
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N} {M′ = M′ ⊕[ addℕ ] N′}
    {χ′ = bind X}
    (ok-⊕₂ vM noM okN)
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (ξ-⊕₂ {χ = bind X} {M′ = S′} vM′ shiftM′ N′→S′) =
  let
    rec = dynamicGradualGuaranteeᵐ okN N⊒N′ N′→S′
  in
  {! ξ-⊕₂-mediated-frame-source-left-already-value-target-bind !}
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M}
    okM
    castRel@(⊒cast-ᵗ p′ᶜ rᶜ t⊒ M⊒M′)
    (pure-step blame-⟨⟩) =
  target-blameᵐ castRel
dynamicGradualGuaranteeᵐ {M = M}
    okM
    castRel@(⊒cast+ᵗ p′ᶜ rᶜ t⊒ M⊒M′)
    (ξ-⟨⟩ {M′ = S′} M′→S′) =
  let
    rec = dynamicGradualGuaranteeᵐ okM M⊒M′ M′→S′
  in
  target-cast-plus-inner-resultᵐ p′ᶜ t⊒ rec
dynamicGradualGuaranteeᵐ
    okM
    (⊒cast+ᵗ p′ᶜ rᶜ
      (cast-id h ok , cross (id-‵ ι))
      M⊒M′)
    (pure-step (β-id vV)) =
  target-cast-plus-β-idᵐ (cast-id h ok , cross (id-‵ ι)) M⊒M′
dynamicGradualGuaranteeᵐ
    okM
    (⊒cast+ᵗ p′ᶜ rᶜ
      (cast-id h ok , cross (id-＇ α))
      M⊒M′)
    (pure-step (β-id vV)) =
  target-cast-plus-β-idᵐ (cast-id h ok , cross (id-＇ α)) M⊒M′
dynamicGradualGuaranteeᵐ
    okM
    (⊒cast+ᵗ p′ᶜ rᶜ
      (cast-id h ok , id★)
      M⊒M′)
    (pure-step (β-id vV)) =
  target-cast-plus-β-idᵐ (cast-id h ok , id★) M⊒M′
dynamicGradualGuaranteeᵐ
    okM
    castRel@(⊒cast+ᵗ p′ᶜ rᶜ t⊒ M⊒M′)
    target-step =
  {! target-cast-plus-mediated-direct-step !}
dynamicGradualGuaranteeᵐ {M = M}
    okM
    castRel@(⊒cast-ᵗ p′ᶜ rᶜ t⊒ M⊒M′)
    (ξ-⟨⟩ {M′ = S′} M′→S′) =
  let
    rec = dynamicGradualGuaranteeᵐ okM M⊒M′ M′→S′
  in
  {! target-cast-minus-mediated-inner-step !}
dynamicGradualGuaranteeᵐ
    okM
    (⊒cast-ᵗ {t = id T} p′ᶜ rᶜ t⊒ M⊒M′)
    (pure-step (β-id vV)) =
  target-cast-minus-β-idᵐ t⊒ M⊒M′
dynamicGradualGuaranteeᵐ
    okM
    castRel@(⊒cast-ᵗ p′ᶜ rᶜ t⊒ M⊒M′)
    (pure-step (tag-untag-bad vV G≢H)) =
  target-blameᵐ castRel
dynamicGradualGuaranteeᵐ
    okM
    castRel@(⊒cast-ᵗ p′ᶜ rᶜ t⊒ M⊒M′)
    (pure-step st) =
  {! target-cast-minus-mediated-direct-step !}
dynamicGradualGuaranteeᵐ {M = M ⟨ c ⟩}
    okM
    castRel@(cast+⊒ᵗ qᶜ rᶜ s⊒ M⊒M′)
    M′→N′ =
  let
    rec = dynamicGradualGuaranteeᵐ (runtime-⟨⟩ okM) M⊒M′ M′→N′
  in
  {! source-cast-plus-mediated-result !}
dynamicGradualGuaranteeᵐ {M = M ⟨ c ⟩}
    okM
    castRel@(cast-⊒ᵗ qᶜ rᶜ s⊒ M⊒M′)
    M′→N′ =
  let
    rec = dynamicGradualGuaranteeᵐ (runtime-⟨⟩ okM) M⊒M′ M′→N′
  in
  source-cast-minus-resultᵐ qᶜ s⊒ rec
dynamicGradualGuaranteeᵐ okM rel@(⊒⟨ν⟩ᵗ _ _ _ _ _ _)
    (pure-step blame-⟨⟩) =
  target-blameᵐ rel
dynamicGradualGuaranteeᵐ okM (⊒⟨ν⟩ᵗ _ _ _ _ _ _) (pure-step st) =
  {! target-gen-cast-mediated-pure-step !}
dynamicGradualGuaranteeᵐ okM (⊒⟨ν⟩ᵗ _ _ _ _ _ _) (ξ-⟨⟩ st) =
  {! target-gen-cast-mediated-inner-step !}
dynamicGradualGuaranteeᵐ okM
    (α⊒αᵗ vL noL vL′ noL′ qᶜ pᶜ L⊒L′)
    (pure-step st) =
  {! matched-seal-mediated-pure-step !}
dynamicGradualGuaranteeᵐ okM (⊒αᵗ vL′ noL′ pᶜ L⊒L′)
    (pure-step st) =
  {! target-seal-mediated-pure-step !}
dynamicGradualGuaranteeᵐ (ok-ν okN)
    (ν⊒νᵗ hA hA′ N⊢ N′⊢ sₗ⊢ sᵣ⊢ pᶜ qᶜ N⊒N′)
    (ξ-ν N′→S′) =
  let
    rec = dynamicGradualGuaranteeᵐ okN N⊒N′ N′→S′
  in
  {! nu-nu-mediated-inner-step !}
dynamicGradualGuaranteeᵐ (ok-no (no•-ν noN))
    (ν⊒νᵗ hA hA′ N⊢ N′⊢ sₗ⊢ sᵣ⊢ pᶜ qᶜ N⊒N′)
    (ξ-ν N′→S′) =
  let
    rec = dynamicGradualGuaranteeᵐ (ok-no noN) N⊒N′ N′→S′
  in
  {! nu-nu-mediated-inner-step-no-source-bullet !}
dynamicGradualGuaranteeᵐ okM
    (ν⊒νᵗ hA hA′ N⊢ N′⊢ sₗ⊢ sᵣ⊢ pᶜ qᶜ N⊒N′)
    (ν-step vV noV) =
  {! nu-nu-mediated-allocation !}
dynamicGradualGuaranteeᵐ okM
    rel@(ν⊒νᵗ hA hA′ N⊢ N′⊢ sₗ⊢ sᵣ⊢ pᶜ qᶜ N⊒N′)
    blame-ν =
  target-blameᵐ rel
dynamicGradualGuaranteeᵐ okN
    (⊒νᵗ N⊢ hA N′⊢ s⊢ pᶜ N⊒N′)
    (ξ-ν N′→S′) =
  let
    rec = dynamicGradualGuaranteeᵐ okN N⊒N′ N′→S′
  in
  {! target-nu-mediated-inner-step !}
dynamicGradualGuaranteeᵐ okM (⊒νᵗ N⊢ hA N′⊢ s⊢ pᶜ N⊒N′)
    (ν-step vV noV) =
  {! target-nu-mediated-allocation !}
dynamicGradualGuaranteeᵐ okM rel@(⊒νᵗ N⊢ hA N′⊢ s⊢ pᶜ N⊒N′)
    blame-ν =
  target-blameᵐ rel
