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
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
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
  ; applyLeftChanges-++
  ; applyRightChange
  )
open import proof.CatchupMediated using (catchup-lemmaᵐ)
open import proof.MediatedLeftInsertion using
  (left-changes-term-narrowingᵐ)
open import proof.MediationProperties using
  ( left-changes-transportᵐ
  ; fun-narrow-domain-dualᵐ-determined
  )
open import proof.NuTermProperties using
  ( renameᵗᵐ-preserves-No•
  ; renameᵗᵐ-preserves-Value
  )
open import proof.NuPreservation using (runtime-⟨⟩)
open import proof.LeftChangeNarrowingSeparated using (applyTys-⇒)
open import proof.ReductionProperties using
  ( applyTyCtxs-++
  ; applyTys-++
  ; applyTerms-preserves-No•
  ; applyTerms-preserves-Value
  ; ·₁-↠
  ; ·₂-↠
  ; ⊕₁-↠
  ; ⊕₂-↠
  ; cast-↠
  ; ↠-trans
  )
open import proof.SimBetaMediated using (sim-betaᵐ)

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
-- Application beta packaging
------------------------------------------------------------------------

mediated-dgg-beta-left-first :
  ∀ {ΔL ΔR ρ L R N′ V′ p q A A′ B B′} →
  RuntimeOK L →
  RuntimeOK R →
  No• R →
  Value V′ →
  (p↦qᶜ : ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ᶜ A ⇒ B ⊒ᵐ A′ ⇒ B′) →
  ΔL ∣ ΔR ∣ ρ ⊢ fun-narrow-domain-dualᵐᶜ p↦qᶜ ∶ᶜ A ⊒ᵐ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ ƛ N′ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ᵐ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ∣ []
    ⊢ R ⊒ V′ ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜ ⦂ A ⊒ᵐ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    (C ≡ applyTys χs B) ×
    (D ≡ B′) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ N′ [ V′ ] ∶ r ⦂ C ⊒ᵐ D
mediated-dgg-beta-left-first {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {N′ = N′} {V′ = V′}
    {p = p} {q = q} {A = A} {A′ = A′}
    {B = B} {B′ = B′}
    okL okR noR-ready vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  let
    χsL , WL , ΔL₁ ,
      vWL , noWL , L↠WL , ΔL₁≡ , ρL-corr ,
      leftL≡ , rightL≡ , pLᶜ , WL⊒ƛraw =
      catchup-lemmaᵐ okL (ƛ N′) L⊒ƛ

    corrL :
      StoreCorr (applyTyCtxs χsL ΔL) ΔR (applyLeftChanges χsL ρ)
    corrL =
      subst (λ Δ → StoreCorr Δ ΔR (applyLeftChanges χsL ρ))
        ΔL₁≡
        ρL-corr

    WL⊒ƛ :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
        ⊢ WL ⊒ ƛ N′ ∶ p ↦ q
          ⦂ applyTys χsL A ⇒ applyTys χsL B ⊒ᵐ A′ ⇒ B′
    WL⊒ƛ =
      subst
        (λ C →
          ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
            ⊢ WL ⊒ ƛ N′ ∶ p ↦ q ⦂ C ⊒ᵐ A′ ⇒ B′)
        (applyTys-⇒ χsL A B)
        WL⊒ƛraw

    p↦qᶜL :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ
        ⊢ p ↦ q ∶ᶜ applyTys χsL A ⇒ applyTys χsL B
          ⊒ᵐ A′ ⇒ B′
    p↦qᶜL =
      subst
        (λ C →
          ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ
            ⊢ p ↦ q ∶ᶜ C ⊒ᵐ A′ ⇒ B′)
        (applyTys-⇒ χsL A B)
        pLᶜ

    R⊒V′L :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
        ⊢ applyTerms χsL R ⊒ V′
          ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜ ⦂ applyTys χsL A ⊒ᵐ A′
    R⊒V′L =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
            ⊢ applyTerms χsL R ⊒ V′
              ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜ
                ⦂ applyTys χsL A ⊒ᵐ A′)
        (sym ΔL₁≡)
        (left-changes-term-narrowingᵐ χsL corrL R⊒V′)

    χsR , WR , ΔL₂ ,
      vWR , noWR , R↠WR , ΔL₂≡ , ρR-corr ,
      leftR≡ , rightR≡ , pRᶜ , WR⊒V′raw =
      catchup-lemmaᵐ
        (applyTerms-preserves-RuntimeOK χsL okR)
        vV′
        R⊒V′L

    ρLR = applyLeftChanges χsR (applyLeftChanges χsL ρ)

    corrR :
      StoreCorr (applyTyCtxs χsR ΔL₁) ΔR ρLR
    corrR =
      subst (λ Δ → StoreCorr Δ ΔR ρLR) ΔL₂≡ ρR-corr

    WLF⊒ƛraw :
      applyTyCtxs χsR ΔL₁ ∣ ΔR ∣ ρLR ∣ []
        ⊢ applyTerms χsR WL ⊒ ƛ N′ ∶ p ↦ q
          ⦂ applyTys χsR (applyTys χsL A ⇒ applyTys χsL B)
            ⊒ᵐ A′ ⇒ B′
    WLF⊒ƛraw = left-changes-term-narrowingᵐ χsR corrR WL⊒ƛ

    WLF⊒ƛ :
      ΔL₂ ∣ ΔR ∣ ρLR ∣ []
        ⊢ applyTerms χsR WL ⊒ ƛ N′ ∶ p ↦ q
          ⦂ applyTys χsR (applyTys χsL A)
              ⇒ applyTys χsR (applyTys χsL B)
            ⊒ᵐ A′ ⇒ B′
    WLF⊒ƛ =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ ρLR ∣ []
            ⊢ applyTerms χsR WL ⊒ ƛ N′ ∶ p ↦ q
              ⦂ applyTys χsR (applyTys χsL A)
                  ⇒ applyTys χsR (applyTys χsL B)
                ⊒ᵐ A′ ⇒ B′)
        (sym ΔL₂≡)
        (subst
          (λ C →
            applyTyCtxs χsR ΔL₁ ∣ ΔR ∣ ρLR ∣ []
              ⊢ applyTerms χsR WL ⊒ ƛ N′ ∶ p ↦ q
                ⦂ C ⊒ᵐ A′ ⇒ B′)
          (applyTys-⇒ χsR (applyTys χsL A) (applyTys χsL B))
          WLF⊒ƛraw)

    p↦qᶜLRraw :
      applyTyCtxs χsR ΔL₁ ∣ ΔR ∣ ρLR
        ⊢ p ↦ q
          ∶ᶜ applyTys χsR (applyTys χsL A ⇒ applyTys χsL B)
            ⊒ᵐ A′ ⇒ B′
    p↦qᶜLRraw = left-changes-transportᵐ χsR corrR p↦qᶜL

    p↦qᶜLR :
      ΔL₂ ∣ ΔR ∣ ρLR
        ⊢ p ↦ q
          ∶ᶜ applyTys χsR (applyTys χsL A)
              ⇒ applyTys χsR (applyTys χsL B)
            ⊒ᵐ A′ ⇒ B′
    p↦qᶜLR =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ ρLR ⊢ p ↦ q
            ∶ᶜ applyTys χsR (applyTys χsL A)
                ⇒ applyTys χsR (applyTys χsL B)
              ⊒ᵐ A′ ⇒ B′)
        (sym ΔL₂≡)
        (subst
          (λ C →
            applyTyCtxs χsR ΔL₁ ∣ ΔR ∣ ρLR
              ⊢ p ↦ q ∶ᶜ C ⊒ᵐ A′ ⇒ B′)
          (applyTys-⇒ χsR (applyTys χsL A) (applyTys χsL B))
          p↦qᶜLRraw)

    pd-eq :
      fun-narrow-domain-dualᵐᶜ p↦qᶜLR
        ≡ fun-narrow-domain-dualᵐᶜ p↦qᶜ
    pd-eq = fun-narrow-domain-dualᵐ-determined p↦qᶜLR p↦qᶜ

    WR⊒V′ :
      ΔL₂ ∣ ΔR ∣ ρLR ∣ []
        ⊢ WR ⊒ V′ ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜLR
          ⦂ applyTys χsR (applyTys χsL A) ⊒ᵐ A′
    WR⊒V′ =
      subst
        (λ pd →
          ΔL₂ ∣ ΔR ∣ ρLR ∣ []
            ⊢ WR ⊒ V′ ∶ pd
              ⦂ applyTys χsR (applyTys χsL A) ⊒ᵐ A′)
        (sym pd-eq)
        WR⊒V′raw

    left-ready :
      L · R —↠[ χsL ] WL · applyTerms χsL R
    left-ready = ·₁-↠ noR-ready L↠WL

    right-ready :
      WL · applyTerms χsL R —↠[ χsR ] applyTerms χsR WL · WR
    right-ready = ·₂-↠ vWL noWL R↠WR

    tail =
      sim-betaᵐ
        WLF⊒ƛ
        (applyTerms-preserves-Value χsR vWL)
        (applyTerms-preserves-No• χsR noWL)
        p↦qᶜLR
        (fun-narrow-domain-dual-typingᵐᶜ p↦qᶜLR)
        WR⊒V′
        vWR
        noWR
        vV′
  in
  let
    χsT , N , ΔL′ , ρ′ ,
      tail-red , ΔT≡ , ρT≡ , N⊒N′[V′] = tail

    source-steps :
      L · R —↠[ (χsL ++ χsR) ++ χsT ] N
    source-steps = ↠-trans (↠-trans left-ready right-ready) tail-red

    ΔL′≡ :
      ΔL′ ≡ applyTyCtxs ((χsL ++ χsR) ++ χsT) ΔL
    ΔL′≡ =
      trans ΔT≡
        (trans
          (cong (applyTyCtxs χsT) ΔL₂≡)
          (trans
            (cong (λ Δ → applyTyCtxs χsT (applyTyCtxs χsR Δ))
              ΔL₁≡)
            (sym
              (trans
                (applyTyCtxs-++ (χsL ++ χsR) χsT ΔL)
                (cong (applyTyCtxs χsT)
                  (applyTyCtxs-++ χsL χsR ΔL))))))

    ρ′≡ :
      ρ′ ≡ applyLeftChanges ((χsL ++ χsR) ++ χsT) ρ
    ρ′≡ =
      trans ρT≡
        (sym
          (trans
            (applyLeftChanges-++ (χsL ++ χsR) χsT ρ)
            (cong (applyLeftChanges χsT)
              (applyLeftChanges-++ χsL χsR ρ))))

    C≡ :
      applyTys χsT (applyTys χsR (applyTys χsL B)) ≡
        applyTys ((χsL ++ χsR) ++ χsT) B
    C≡ =
      sym
        (trans
          (applyTys-++ (χsL ++ χsR) χsT B)
          (cong (applyTys χsT) (applyTys-++ χsL χsR B)))
  in
  (χsL ++ χsR) ++ χsT ,
  N ,
  ΔL′ ,
  ρ′ ,
  _ ,
  _ ,
  _ ,
  source-steps ,
  ΔL′≡ ,
  ρ′≡ ,
  C≡ ,
  refl ,
  N⊒N′[V′]

mediated-dgg-beta-right-first :
  ∀ {ΔL ΔR ρ L R N′ V′ p q A A′ B B′} →
  Value L →
  No• L →
  RuntimeOK R →
  Value V′ →
  (p↦qᶜ : ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ᶜ A ⇒ B ⊒ᵐ A′ ⇒ B′) →
  ΔL ∣ ΔR ∣ ρ ⊢ fun-narrow-domain-dualᵐᶜ p↦qᶜ ∶ᶜ A ⊒ᵐ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ ƛ N′ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ᵐ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ∣ []
    ⊢ R ⊒ V′ ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜ ⦂ A ⊒ᵐ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    (C ≡ applyTys χs B) ×
    (D ≡ B′) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ N′ [ V′ ] ∶ r ⦂ C ⊒ᵐ D
mediated-dgg-beta-right-first {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {N′ = N′} {V′ = V′}
    {p = p} {q = q} {A = A} {A′ = A′}
    {B = B} {B′ = B′}
    vL noL okR vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  let
    χsR , WR , ΔL₁ ,
      vWR , noWR , R↠WR , ΔL₁≡ , ρR-corr ,
      leftR≡ , rightR≡ , pRᶜ , WR⊒V′raw =
      catchup-lemmaᵐ okR vV′ R⊒V′

    ρR = applyLeftChanges χsR ρ

    corrR :
      StoreCorr (applyTyCtxs χsR ΔL) ΔR ρR
    corrR =
      subst (λ Δ → StoreCorr Δ ΔR ρR) ΔL₁≡ ρR-corr

    LF⊒ƛraw :
      applyTyCtxs χsR ΔL ∣ ΔR ∣ ρR ∣ []
        ⊢ applyTerms χsR L ⊒ ƛ N′ ∶ p ↦ q
          ⦂ applyTys χsR (A ⇒ B) ⊒ᵐ A′ ⇒ B′
    LF⊒ƛraw = left-changes-term-narrowingᵐ χsR corrR L⊒ƛ

    LF⊒ƛ :
      ΔL₁ ∣ ΔR ∣ ρR ∣ []
        ⊢ applyTerms χsR L ⊒ ƛ N′ ∶ p ↦ q
          ⦂ applyTys χsR A ⇒ applyTys χsR B ⊒ᵐ A′ ⇒ B′
    LF⊒ƛ =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ ρR ∣ []
            ⊢ applyTerms χsR L ⊒ ƛ N′ ∶ p ↦ q
              ⦂ applyTys χsR A ⇒ applyTys χsR B ⊒ᵐ A′ ⇒ B′)
        (sym ΔL₁≡)
        (subst
          (λ C →
            applyTyCtxs χsR ΔL ∣ ΔR ∣ ρR ∣ []
              ⊢ applyTerms χsR L ⊒ ƛ N′ ∶ p ↦ q
                ⦂ C ⊒ᵐ A′ ⇒ B′)
          (applyTys-⇒ χsR A B)
          LF⊒ƛraw)

    p↦qᶜRraw :
      applyTyCtxs χsR ΔL ∣ ΔR ∣ ρR
        ⊢ p ↦ q ∶ᶜ applyTys χsR (A ⇒ B) ⊒ᵐ A′ ⇒ B′
    p↦qᶜRraw = left-changes-transportᵐ χsR corrR p↦qᶜ

    p↦qᶜR :
      ΔL₁ ∣ ΔR ∣ ρR
        ⊢ p ↦ q ∶ᶜ applyTys χsR A ⇒ applyTys χsR B ⊒ᵐ A′ ⇒ B′
    p↦qᶜR =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ ρR
            ⊢ p ↦ q ∶ᶜ applyTys χsR A ⇒ applyTys χsR B
              ⊒ᵐ A′ ⇒ B′)
        (sym ΔL₁≡)
        (subst
          (λ C →
            applyTyCtxs χsR ΔL ∣ ΔR ∣ ρR
              ⊢ p ↦ q ∶ᶜ C ⊒ᵐ A′ ⇒ B′)
          (applyTys-⇒ χsR A B)
          p↦qᶜRraw)

    pd-eq :
      fun-narrow-domain-dualᵐᶜ p↦qᶜR
        ≡ fun-narrow-domain-dualᵐᶜ p↦qᶜ
    pd-eq = fun-narrow-domain-dualᵐ-determined p↦qᶜR p↦qᶜ

    WR⊒V′ :
      ΔL₁ ∣ ΔR ∣ ρR ∣ []
        ⊢ WR ⊒ V′ ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜR
          ⦂ applyTys χsR A ⊒ᵐ A′
    WR⊒V′ =
      subst
        (λ pd →
          ΔL₁ ∣ ΔR ∣ ρR ∣ []
            ⊢ WR ⊒ V′ ∶ pd ⦂ applyTys χsR A ⊒ᵐ A′)
        (sym pd-eq)
        WR⊒V′raw

    ready :
      L · R —↠[ χsR ] applyTerms χsR L · WR
    ready = ·₂-↠ vL noL R↠WR

    tail =
      sim-betaᵐ
        LF⊒ƛ
        (applyTerms-preserves-Value χsR vL)
        (applyTerms-preserves-No• χsR noL)
        p↦qᶜR
        (fun-narrow-domain-dual-typingᵐᶜ p↦qᶜR)
        WR⊒V′
        vWR
        noWR
        vV′
  in
  let
    χsT , N , ΔL′ , ρ′ ,
      tail-red , ΔT≡ , ρT≡ , N⊒N′[V′] = tail

    source-steps :
      L · R —↠[ χsR ++ χsT ] N
    source-steps = ↠-trans ready tail-red

    ΔL′≡ :
      ΔL′ ≡ applyTyCtxs (χsR ++ χsT) ΔL
    ΔL′≡ =
      trans ΔT≡
        (trans
          (cong (applyTyCtxs χsT) ΔL₁≡)
          (sym (applyTyCtxs-++ χsR χsT ΔL)))

    ρ′≡ :
      ρ′ ≡ applyLeftChanges (χsR ++ χsT) ρ
    ρ′≡ = trans ρT≡ (sym (applyLeftChanges-++ χsR χsT ρ))

    C≡ :
      applyTys χsT (applyTys χsR B) ≡ applyTys (χsR ++ χsT) B
    C≡ = sym (applyTys-++ χsR χsT B)
  in
  χsR ++ χsT ,
  N ,
  ΔL′ ,
  ρ′ ,
  _ ,
  _ ,
  _ ,
  source-steps ,
  ΔL′≡ ,
  ρ′≡ ,
  C≡ ,
  refl ,
  N⊒N′[V′]

mediated-dgg-beta :
  ∀ {ΔL ΔR ρ L R N′ V′ p q A A′ B B′} →
  RuntimeOK (L · R) →
  Value V′ →
  (p↦qᶜ : ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ᶜ A ⇒ B ⊒ᵐ A′ ⇒ B′) →
  ΔL ∣ ΔR ∣ ρ ⊢ fun-narrow-domain-dualᵐᶜ p↦qᶜ ∶ᶜ A ⊒ᵐ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ ƛ N′ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ᵐ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ∣ []
    ⊢ R ⊒ V′ ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜ ⦂ A ⊒ᵐ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    (C ≡ applyTys χs B) ×
    (D ≡ B′) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ N′ [ V′ ] ∶ r ⦂ C ⊒ᵐ D
mediated-dgg-beta (ok-no (no•-· noL noR))
    vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  mediated-dgg-beta-left-first
    (ok-no noL) (ok-no noR) noR vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′
mediated-dgg-beta (ok-·₁ okL noR)
    vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  mediated-dgg-beta-left-first
    okL (ok-no noR) noR vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′
mediated-dgg-beta (ok-·₂ vL noL okR)
    vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  mediated-dgg-beta-right-first
    vL noL okR vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′

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
    (pure-step (β-↦ vV′ vW′)) =
  {! mediated-β-cast-simulation !}
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R}
    okM
    app@(·⊒·ᵗ p↦qᶜ L⊒L′ R⊒R′)
    (pure-step blame-·₁) =
  [] ,
  L · R ,
  ΔL ,
  ΔR ,
  ρ ,
  _ ,
  _ ,
  _ ,
  ↠-refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  ⊒blameᵗ (typed-term-narrowing-source-typingᵐᶜ app)
    (proj₂ (typed-term-narrowing-coercionᵐ app))
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R}
    okM
    app@(·⊒·ᵗ p↦qᶜ L⊒L′ R⊒R′)
    (pure-step (blame-·₂ vV)) =
  [] ,
  L · R ,
  ΔL ,
  ΔR ,
  ρ ,
  _ ,
  _ ,
  _ ,
  ↠-refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  ⊒blameᵗ (typed-term-narrowing-source-typingᵐᶜ app)
    (proj₂ (typed-term-narrowing-coercionᵐ app))
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
    (pure-step δ-⊕) =
  {! mediated-primitive-delta-simulation !}
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N}
    okMN
    add@(⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (pure-step blame-⊕₁) =
  [] ,
  M ⊕[ addℕ ] N ,
  ΔL ,
  ΔR ,
  ρ ,
  _ ,
  _ ,
  _ ,
  ↠-refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  ⊒blameᵗ (typed-term-narrowing-source-typingᵐᶜ add)
    (proj₂ (typed-term-narrowing-coercionᵐ add))
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N}
    okMN
    add@(⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (pure-step (blame-⊕₂ vV)) =
  [] ,
  M ⊕[ addℕ ] N ,
  ΔL ,
  ΔR ,
  ρ ,
  _ ,
  _ ,
  _ ,
  ↠-refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  ⊒blameᵗ (typed-term-narrowing-source-typingᵐᶜ add)
    (proj₂ (typed-term-narrowing-coercionᵐ add))
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N} {M′ = M′ ⊕[ addℕ ] N′}
    {χ′ = χ′}
    (ok-no (no•-⊕ noM noN))
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (ξ-⊕₁ {L′ = S′} M′→S′ shiftN′) =
  let
    rec = dynamicGradualGuaranteeᵐ (ok-no noM) M⊒M′ M′→S′
  in
  {! ξ-⊕₁-mediated-frame-no-source-bullet !}
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N} {M′ = M′ ⊕[ addℕ ] N′}
    {χ′ = χ′}
    (ok-⊕₁ okM noN)
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (ξ-⊕₁ {L′ = S′} M′→S′ shiftN′) =
  let
    rec = dynamicGradualGuaranteeᵐ okM M⊒M′ M′→S′
  in
  {! ξ-⊕₁-mediated-frame-source-left-running !}
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
    {χ′ = χ′}
    (ok-⊕₂ vM noM okN)
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (ξ-⊕₂ {M′ = S′} vM′ shiftM′ N′→S′) =
  let
    rec = dynamicGradualGuaranteeᵐ okN N⊒N′ N′→S′
  in
  {! ξ-⊕₂-mediated-frame-source-left-already-value !}
dynamicGradualGuaranteeᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M}
    okM
    castRel@(⊒cast-ᵗ p′ᶜ rᶜ t⊒ M⊒M′)
    (pure-step blame-⟨⟩) =
  [] ,
  M ,
  ΔL ,
  ΔR ,
  ρ ,
  _ ,
  _ ,
  _ ,
  ↠-refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  ⊒blameᵗ (typed-term-narrowing-source-typingᵐᶜ castRel)
    (proj₂ (typed-term-narrowing-coercionᵐ castRel))
dynamicGradualGuaranteeᵐ {M = M}
    okM
    castRel@(⊒cast+ᵗ p′ᶜ rᶜ t⊒ M⊒M′)
    (ξ-⟨⟩ {M′ = S′} M′→S′) =
  let
    rec = dynamicGradualGuaranteeᵐ okM M⊒M′ M′→S′
  in
  {! target-cast-plus-mediated-inner-step !}
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
  {! source-cast-minus-mediated-result !}
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
    (ν⊒νᵗ hA hA′ N⊢ N′⊢ sₗ⊢ sᵣ⊢ pᶜ qᶜ N⊒N′)
    blame-ν =
  {! nu-nu-mediated-blame !}
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
dynamicGradualGuaranteeᵐ okM (⊒νᵗ N⊢ hA N′⊢ s⊢ pᶜ N⊒N′)
    blame-ν =
  {! target-nu-mediated-blame !}
