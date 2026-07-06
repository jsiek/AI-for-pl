{-# OPTIONS --allow-unsolved-metas #-}

module proof.DGGBetaSeparated where

-- File Charter:
--   * Separated-store DGG helpers for application beta steps.
--   * Packages catchup on the source function/argument with sim-beta.
--   * Exported by proof.DynamicGradualGuaranteeSeparated for the main DGG.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_+_)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

open import Types
open import Coercions
open import NarrowWiden using
  ( cross
  ; dualʷ
  ; id★
  ; id-＇
  ; id-‵
  ; _？︔_
  ; _︔seal_
  ; _∣_∣_⊢_∶_⊒_
  )
  renaming (_↦_ to _↦ⁿʷ_)
open import Primitives using (addℕ; κℕ)
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
open import proof.CoercionProperties using
  ( coercion-src-tgtᵐ
  ; dualActionOk-normal
  ; dualStoreAt-normal
  )
open import proof.NarrowWidenProperties using
  ( dualʷ-flips-typingᵐ
  )
open import proof.ReductionProperties using
  ( applyTerms-preserves-No•
  ; applyTerms-preserves-Value
  ; applyCoercions
  ; applyCoercions-++
  ; applyCoercions-dual
  ; applyTys-++
  ; applyTys-ℕ
  ; applyTys-ℕ-applyTys
  ; applyTyCtxs-++
  ; ↠-trans
  ; cast-↠
  ; ·₁-↠
  ; ·₂-↠
  ; ⊕₁-↠
  ; ⊕₂-↠
  )
open import proof.SimBetaSeparated using
  ( applyTerms-preserves-RuntimeOK
  ; applyTys-⇒
  ; applyCoercions-↦
  ; applyCoercions-dual-applyCoercions
  ; no•-cast-inv
  ; ⟨⟩-term-injective
  ; ⟨⟩-coercion-injective
  ; left-change-coercion-narrowing
  ; left-change-source-coercion-narrowing
  ; left-change-fun-coercion-narrowing
  ; advance-left-term-narrowing
  ; advance-left-function-term-narrowing
  ; advance-left-lambda-narrowing
  ; widen-fun-domainᵐ
  ; separated-fun-domain-dual
  ; separated-fun-codomain
  ; separated-left-coercionᵐ
  ; separated-right-coercionᵐ
  ; ↦-domain
  ; ↦-codomain
  ; ↦-left-injective
  ; ↦-right-injective
  ; dualʷ-raw-determined
  ; dualʷ-involutive-raw
  ; sim-beta
  )
open import proof.NuProgress using
  (FunView; fv-ƛ; fv-↦; canonical-⇒)
open import proof.DGGPrimitiveSeparated using
  ( id-ℕ-narrowingᶜ
  ; applyCoercions-id-ℕ
  ; applyCoercions-id-ℕ-applyCoercions
  ; source-nat-typingᶜ
  ; typed-term-narrowing-endpointsᶜ
  ; typed-term-narrowing-coercion-endpointsᶜ
  ; constant-⊕-δ-step
  ; const-narrowing-targetᶜ
  ; value-id-ℕ-narrowing-target-constᶜ
  ; value-normalized-id-ℕ-target-constᶜ
  )
------------------------------------------------------------------------
-- Application beta caller
------------------------------------------------------------------------

separated-dgg-beta-left-first :
  ∀ {ΔL ΔR ρ L R N′ V′ p q A A′ B B′} →
  RuntimeOK L →
  RuntimeOK R →
  No• R →
  Value V′ →
  (p↦qᶜ : ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ᶜ A ⇒ B ⊒ A′ ⇒ B′) →
  ΔL ∣ ΔR ∣ ρ ⊢ fun-narrow-domain-dualᶜ p↦qᶜ ∶ᶜ A ⊒ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ ƛ N′ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ∣ []
    ⊢ R ⊒ V′ ∶ fun-narrow-domain-dualᶜ p↦qᶜ ⦂ A ⊒ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ N′ [ V′ ] ∶ r ⦂ C ⊒ D
separated-dgg-beta-left-first {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {N′ = N′} {V′ = V′}
    {p = p} {q = q} {A = A} {A′ = A′}
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

    p↦q₁ = left-change-fun-coercion-narrowing χsL ΔL₁≡ ρL-corr p↦qᶜ

    p↦q₂ =
      left-change-fun-coercion-narrowing χsR ΔL₂≡ ρR-corr
        (proj₁ p↦q₁)

    dual-eq :
      fun-narrow-domain-dual (proj₁ p↦q₂) ≡
        applyCoercions χsR
          (applyCoercions χsL (fun-narrow-domain-dualᶜ p↦qᶜ))
    dual-eq =
      trans (proj₂ p↦q₂) (cong (applyCoercions χsR) (proj₂ p↦q₁))

    WR⊒V′ :
      ΔL₂ ∣ ΔR ∣ applyLeftChanges χsR (applyLeftChanges χsL ρ) ∣ []
        ⊢ WR ⊒ V′
          ∶ fun-narrow-domain-dual (proj₁ p↦q₂)
          ⦂ applyTys χsR (applyTys χsL A) ⊒ A′
    WR⊒V′ =
      subst
        (λ pd →
          ΔL₂ ∣ ΔR ∣ applyLeftChanges χsR (applyLeftChanges χsL ρ)
            ∣ [] ⊢ WR ⊒ V′ ∶ pd
              ⦂ applyTys χsR (applyTys χsL A) ⊒ A′)
        (sym dual-eq)
        WR⊒V′raw

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
        (proj₁ p↦q₂)
        (separated-fun-domain-dual (proj₁ p↦q₂))
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
  ∀ {ΔL ΔR ρ L R N′ V′ p q A A′ B B′} →
  Value L →
  No• L →
  RuntimeOK R →
  Value V′ →
  (p↦qᶜ : ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ᶜ A ⇒ B ⊒ A′ ⇒ B′) →
  ΔL ∣ ΔR ∣ ρ ⊢ fun-narrow-domain-dualᶜ p↦qᶜ ∶ᶜ A ⊒ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ ƛ N′ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ∣ []
    ⊢ R ⊒ V′ ∶ fun-narrow-domain-dualᶜ p↦qᶜ ⦂ A ⊒ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ N′ [ V′ ] ∶ r ⦂ C ⊒ D
separated-dgg-beta-right-first {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {N′ = N′} {V′ = V′}
    {p = p} {q = q} {A = A} {A′ = A′}
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

    p↦q₁ = left-change-fun-coercion-narrowing χsR ΔL₁≡ ρR-corr p↦qᶜ

    WR⊒V′ :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsR ρ ∣ []
        ⊢ WR ⊒ V′
          ∶ fun-narrow-domain-dual (proj₁ p↦q₁)
          ⦂ applyTys χsR A ⊒ A′
    WR⊒V′ =
      subst
        (λ pd →
          ΔL₁ ∣ ΔR ∣ applyLeftChanges χsR ρ ∣ []
            ⊢ WR ⊒ V′ ∶ pd ⦂ applyTys χsR A ⊒ A′)
        (sym (proj₂ p↦q₁))
        WR⊒V′raw

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
        (proj₁ p↦q₁)
        (separated-fun-domain-dual (proj₁ p↦q₁))
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
  ∀ {ΔL ΔR ρ L R N′ V′ p q A A′ B B′} →
  RuntimeOK (L · R) →
  Value V′ →
  (p↦qᶜ : ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ᶜ A ⇒ B ⊒ A′ ⇒ B′) →
  ΔL ∣ ΔR ∣ ρ ⊢ fun-narrow-domain-dualᶜ p↦qᶜ ∶ᶜ A ⊒ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ ƛ N′ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ∣ []
    ⊢ R ⊒ V′ ∶ fun-narrow-domain-dualᶜ p↦qᶜ ⦂ A ⊒ A′ →
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
