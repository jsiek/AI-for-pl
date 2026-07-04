{-# OPTIONS --allow-unsolved-metas #-}

module proof.DynamicGradualGuaranteeSeparated where

-- File Charter:
--   * Top-down separated-store surface for resuming the DGG beta proof.
--   * Keeps the target term/store unchanged while left-side catchup advances
--     the source term through `SealCorr`.
--   * Wires the separated beta caller to `proof.SimBetaSeparated` while the
--     full DGG skeleton is migrated top-down.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

open import Types
open import Coercions
open import Primitives using (addℕ)
open import NuTerms
open import NuReduction
open import StoreCorrespondence
open import TermNarrowingSeparated
open import proof.CatchupSeparated using
  ( applyLeftChanges
  ; applyLeftChanges-++
  ; applyRightChange
  ; catchup-lemmaˡ
  )
open import proof.NuPreservation using (runtime-⟨⟩)
open import proof.ReductionProperties using
  ( applyTerms-preserves-No•
  ; applyTerms-preserves-Value
  ; applyCoercions
  ; applyCoercions-dual
  ; applyTyCtxs-++
  ; ↠-trans
  ; ·₁-↠
  ; ·₂-↠
  )
open import proof.SimBetaSeparated using
  ( applyTerms-preserves-RuntimeOK
  ; applyTys-⇒
  ; applyCoercions-↦
  ; applyCoercions-dual-applyCoercions
  ; advance-left-term-narrowing
  ; advance-left-lambda-narrowing
  ; sim-beta
  )

------------------------------------------------------------------------
-- Application beta caller
------------------------------------------------------------------------

separated-dgg-beta-left-first :
  ∀ {ΔL ΔR ρ L R N′ V′ pᵈ p q A A′ B B′} →
  RuntimeOK L →
  RuntimeOK R →
  No• R →
  Value V′ →
  ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ᶜ A ⇒ B ⊒ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ⊢ pᵈ ∶ᶜ A ⊒ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ ƛ N′ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ R ⊒ V′ ∶ pᵈ ⦂ A ⊒ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ N′ [ V′ ] ∶ r ⦂ C ⊒ D
separated-dgg-beta-left-first {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {N′ = N′} {V′ = V′}
    {pᵈ = pᵈ} {p = p} {q = q} {A = A} {A′ = A′}
    {B = B} {B′ = B′}
    okL okR noR-ready vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  let
    χsL , WL , ΔL₁ ,
      vWL , noWL , L↠WL , ΔL₁≡ , ρL-corr ,
      leftL≡ , rightL≡ , p₁ᶜ , WL⊒ƛraw =
      catchup-lemmaˡ
        okL
        (ƛ N′)
        L⊒ƛ

    WL⊒ƛ :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
        ⊢ WL ⊒ ƛ N′
          ∶ applyCoercions χsL p ↦ applyCoercions χsL q
          ⦂ applyTys χsL A ⇒ applyTys χsL B ⊒ A′ ⇒ B′
    WL⊒ƛ =
      subst
        (λ c →
          ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
            ⊢ WL ⊒ ƛ N′ ∶ c
              ⦂ applyTys χsL A ⇒ applyTys χsL B ⊒ A′ ⇒ B′)
        (applyCoercions-↦ χsL p q)
        (subst
          (λ C →
            ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
              ⊢ WL ⊒ ƛ N′ ∶ applyCoercions χsL (p ↦ q)
                ⦂ C ⊒ A′ ⇒ B′)
          (applyTys-⇒ χsL A B)
          WL⊒ƛraw)

    R⊒V′L =
      advance-left-term-narrowing χsL ΔL₁≡ ρL-corr R⊒V′

    χsR , WR , ΔL₂ ,
      vWR , noWR , R↠WR , ΔL₂≡ , ρR-corr ,
      leftR≡ , rightR≡ , p₂ᶜ , WR⊒V′raw =
      catchup-lemmaˡ
        (applyTerms-preserves-RuntimeOK χsL okR)
        vV′
        R⊒V′L

    WLF⊒ƛ =
      advance-left-lambda-narrowing χsR ΔL₂≡ ρR-corr WL⊒ƛ

    WR⊒V′ :
      ΔL₂ ∣ ΔR ∣ applyLeftChanges χsR (applyLeftChanges χsL ρ) ∣ []
        ⊢ WR ⊒ V′
          ∶ applyCoercions χsR (applyCoercions χsL pᵈ)
          ⦂ applyTys χsR (applyTys χsL A) ⊒ A′
    WR⊒V′ = WR⊒V′raw

    p₂-domainᶜ :
      ΔL₂ ∣ ΔR ∣ applyLeftChanges χsR (applyLeftChanges χsL ρ)
        ⊢ applyCoercions χsR (applyCoercions χsL pᵈ)
          ∶ᶜ applyTys χsR (applyTys χsL A) ⊒ A′
    p₂-domainᶜ = p₂ᶜ

    left-ready :
      L · R —↠[ χsL ] WL · applyTerms χsL R
    left-ready = ·₁-↠ noR-ready L↠WL

    right-ready :
      WL · applyTerms χsL R —↠[ χsR ] applyTerms χsR WL · WR
    right-ready = ·₂-↠ vWL noWL R↠WR

    ready :
      ∃[ χs₀ ] (L · R —↠[ χs₀ ] applyTerms χsR WL · WR)
    ready = χsL ++ χsR , ↠-trans left-ready right-ready

    tail :
      ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ]
        (applyTerms χsR WL · WR —↠[ χs ] N) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL₂) ×
        (ρ′ ≡
          applyLeftChanges χs (applyLeftChanges χsR
            (applyLeftChanges χsL ρ))) ×
        ΔL′ ∣ ΔR ∣ ρ′ ∣ []
          ⊢ N ⊒ N′ [ V′ ]
            ∶ applyCoercions χs
                (applyCoercions χsR (applyCoercions χsL q))
            ⦂ applyTys χs (applyTys χsR (applyTys χsL B)) ⊒ B′
    tail =
      sim-beta
        WLF⊒ƛ
        (applyTerms-preserves-Value χsR vWL)
        (applyTerms-preserves-No• χsR noWL)
        WR⊒V′
        p₂-domainᶜ
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
  N⊒N′[V′]

separated-dgg-beta-right-first :
  ∀ {ΔL ΔR ρ L R N′ V′ pᵈ p q A A′ B B′} →
  Value L →
  No• L →
  RuntimeOK R →
  Value V′ →
  ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ᶜ A ⇒ B ⊒ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ⊢ pᵈ ∶ᶜ A ⊒ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ ƛ N′ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ R ⊒ V′ ∶ pᵈ ⦂ A ⊒ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ N′ [ V′ ] ∶ r ⦂ C ⊒ D
separated-dgg-beta-right-first {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {N′ = N′} {V′ = V′}
    {pᵈ = pᵈ} {p = p} {q = q} {A = A} {A′ = A′}
    {B = B} {B′ = B′}
    vL noL okR vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  let
    χsR , WR , ΔL₁ ,
      vWR , noWR , R↠WR , ΔL₁≡ , ρR-corr ,
      leftR≡ , rightR≡ , p₁ᶜ , WR⊒V′raw =
      catchup-lemmaˡ
        okR
        vV′
        R⊒V′

    LF⊒ƛ =
      advance-left-lambda-narrowing χsR ΔL₁≡ ρR-corr L⊒ƛ

    WR⊒V′ :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsR ρ ∣ []
        ⊢ WR ⊒ V′
          ∶ applyCoercions χsR pᵈ ⦂ applyTys χsR A ⊒ A′
    WR⊒V′ = WR⊒V′raw

    p₁-domainᶜ :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsR ρ
        ⊢ applyCoercions χsR pᵈ ∶ᶜ applyTys χsR A ⊒ A′
    p₁-domainᶜ = p₁ᶜ

    ready :
      L · R —↠[ χsR ] applyTerms χsR L · WR
    ready = ·₂-↠ vL noL R↠WR

    tail :
      ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ]
        (applyTerms χsR L · WR —↠[ χs ] N) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL₁) ×
        (ρ′ ≡ applyLeftChanges χs (applyLeftChanges χsR ρ)) ×
        ΔL′ ∣ ΔR ∣ ρ′ ∣ []
          ⊢ N ⊒ N′ [ V′ ]
            ∶ applyCoercions χs (applyCoercions χsR q)
            ⦂ applyTys χs (applyTys χsR B) ⊒ B′
    tail =
      sim-beta
        LF⊒ƛ
        (applyTerms-preserves-Value χsR vL)
        (applyTerms-preserves-No• χsR noL)
        WR⊒V′
        p₁-domainᶜ
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
    ρ′≡ =
      trans ρT≡ (sym (applyLeftChanges-++ χsR χsT ρ))
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
  N⊒N′[V′]

separated-dgg-beta :
  ∀ {ΔL ΔR ρ L R N′ V′ pᵈ p q A A′ B B′} →
  RuntimeOK (L · R) →
  Value V′ →
  ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ᶜ A ⇒ B ⊒ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ⊢ pᵈ ∶ᶜ A ⊒ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ ƛ N′ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ R ⊒ V′ ∶ pᵈ ⦂ A ⊒ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ N′ [ V′ ] ∶ r ⦂ C ⊒ D
separated-dgg-beta okLR@(ok-no (no•-· noL noR))
    vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  separated-dgg-beta-left-first
    (ok-no noL) (ok-no noR) noR vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′
separated-dgg-beta okLR@(ok-·₁ okL noR)
    vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  separated-dgg-beta-left-first
    okL (ok-no noR) noR vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′
separated-dgg-beta okLR@(ok-·₂ vL noL (ok-no noR))
    vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  separated-dgg-beta-left-first
    (ok-no noL) (ok-no noR) noR vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′
separated-dgg-beta (ok-·₂ vL noL (ok-• vV noV))
    vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  separated-dgg-beta-right-first
    vL noL (ok-• vV noV) vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′
separated-dgg-beta (ok-·₂ vL noL (ok-·₁ okR₁ noR₂))
    vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  separated-dgg-beta-right-first
    vL noL (ok-·₁ okR₁ noR₂) vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′
separated-dgg-beta (ok-·₂ vL noL (ok-·₂ vR₁ noR₁ okR₂))
    vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  separated-dgg-beta-right-first
    vL noL (ok-·₂ vR₁ noR₁ okR₂) vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′
separated-dgg-beta (ok-·₂ vL noL (ok-ν okR))
    vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  separated-dgg-beta-right-first
    vL noL (ok-ν okR) vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′
separated-dgg-beta (ok-·₂ vL noL (ok-⊕₁ okR₁ noR₂))
    vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  separated-dgg-beta-right-first
    vL noL (ok-⊕₁ okR₁ noR₂) vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′
separated-dgg-beta (ok-·₂ vL noL (ok-⊕₂ vR₁ noR₁ okR₂))
    vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  separated-dgg-beta-right-first
    vL noL (ok-⊕₂ vR₁ noR₁ okR₂) vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′
separated-dgg-beta (ok-·₂ vL noL (ok-⟨⟩ okR))
    vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  separated-dgg-beta-right-first
    vL noL (ok-⟨⟩ okR) vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′

------------------------------------------------------------------------
-- Full separated DGG skeleton
------------------------------------------------------------------------

dynamicGradualGuarantee :
  ∀ {ΔL ΔR ρ M M′ N′ A B p χ′} →
  RuntimeOK M →
  ΔL ∣ ΔR ∣ ρ ⊢ p ∶ᶜ A ⊒ B →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  M′ —→[ χ′ ] N′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
  ∃[ C ] ∃[ D ] ∃[ r ]
    (M —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
    (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ N ⊒ N′ ∶ r ⦂ C ⊒ D
dynamicGradualGuarantee okM pᶜ (⊒blameᵗ M⊢ qᶜ)
    (pure-step ())
dynamicGradualGuarantee okM pᶜ (x⊒xᵗ qᶜ x∋q)
    (pure-step ())
dynamicGradualGuarantee okM pᶜ
    (ƛ⊒ƛᵗ p↦qᶜ N⊒N′)
    (pure-step ())
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R} {M′ = (ƛ N′) · V′}
    okLR qᶜ
    (·⊒·ᵗ p↦q-wholeᶜ L⊒ƛ R⊒V′)
    (pure-step (β vV′)) =
  let
    rec =
      separated-dgg-beta
        okLR
        vV′
        p↦q-wholeᶜ
        (fun-narrow-domain-dual-typingᶜ p↦q-wholeᶜ)
        L⊒ƛ
        R⊒V′
  in
  let
    χs , N , ΔL′ , ρ′ , C , D , r ,
      source-steps , ΔL′≡ , ρ′≡ , N⊒N′[V′] = rec
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
  N⊒N′[V′]
dynamicGradualGuarantee okM qᶜ
    (·⊒·ᵗ p↦qᶜ L⊒L′ R⊒R′)
    (pure-step (β-↦ vV vW)) =
  {! ? !}
dynamicGradualGuarantee okM qᶜ
    (·⊒·ᵗ p↦qᶜ L⊒L′ R⊒R′)
    (pure-step blame-·₁) =
  {! ? !}
dynamicGradualGuarantee okM qᶜ
    (·⊒·ᵗ p↦qᶜ L⊒L′ R⊒R′)
    (pure-step (blame-·₂ vV)) =
  {! ? !}
dynamicGradualGuarantee okM qᶜ
    (·⊒·ᵗ p↦q-wholeᶜ L⊒L′ R⊒R′)
    (ξ-·₁ L′→N′ shiftR′) =
  let
    rec = dynamicGradualGuarantee {! ? !} p↦q-wholeᶜ L⊒L′ L′→N′
  in
  {! ? !}
dynamicGradualGuarantee okM qᶜ
    (·⊒·ᵗ p↦q-wholeᶜ L⊒L′ R⊒R′)
    (ξ-·₂ vL′ shiftL′ R′→N′) =
  let
    rec =
      dynamicGradualGuarantee
        {! ? !}
        (fun-narrow-domain-dual-typingᶜ p↦q-wholeᶜ)
        R⊒R′
        R′→N′
  in
  {! ? !}
dynamicGradualGuarantee okM pᶜ
    (Λ⊒Λᵗ allᶜ vV vV′ V⊒V′)
    (pure-step ())
dynamicGradualGuarantee okM pᶜ (κ⊒κᵗ κ qᶜ)
    (pure-step ())
dynamicGradualGuarantee okM pᶜ
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (pure-step δ-⊕) =
  {! ? !}
dynamicGradualGuarantee okM pᶜ
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (pure-step blame-⊕₁) =
  {! ? !}
dynamicGradualGuarantee okM pᶜ
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (pure-step (blame-⊕₂ vV)) =
  {! ? !}
dynamicGradualGuarantee okM pᶜ
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (ξ-⊕₁ M′→P′ shiftN′) =
  let
    rec = dynamicGradualGuarantee {! ? !} pᶜ M⊒M′ M′→P′
  in
  {! ? !}
dynamicGradualGuarantee okM pᶜ
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (ξ-⊕₂ vM′ shiftM′ N′→P′) =
  let
    rec = dynamicGradualGuarantee {! ? !} pᶜ N⊒N′ N′→P′
  in
  {! ? !}
dynamicGradualGuarantee okM pᶜ
    (⊒cast+ᵗ p′ᶜ rᶜ t⊒ M⊒M′)
    M′⟨s⟩→N′ =
  {! ? !}
dynamicGradualGuarantee okM pᶜ
    (⊒cast-ᵗ p′ᶜ rᶜ t⊒ M⊒M′)
    M′⟨s⟩→N′ =
  {! ? !}
dynamicGradualGuarantee okM pᶜ
    (cast+⊒ᵗ qᶜ rᶜ s⊒ M⊒M′) M′→N′ =
  let
    rec = dynamicGradualGuarantee (runtime-⟨⟩ okM) qᶜ M⊒M′ M′→N′
  in
  {! ? !}
dynamicGradualGuarantee okM pᶜ
    (cast-⊒ᵗ qᶜ rᶜ s⊒ M⊒M′) M′→N′ =
  {! ? !}
