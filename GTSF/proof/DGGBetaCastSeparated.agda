{-# OPTIONS --allow-unsolved-metas #-}

module proof.DGGBetaCastSeparated where

-- File Charter:
--   * Separated-store DGG helpers for application beta-through-cast steps.
--   * Handles function-cast value shapes and source/target catchup packaging.
--   * Keeps the large beta-cast proof separate from the main recursive DGG.

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
  ; left-change-source-coercion-narrowing-dual
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

separated-source-cast-plus-result :
  ∀ {ΔL ΔR ρ ΔLA ΔLT ρT Target N qᵢ qₒ dₛ d Bₒ BL BR μq μd}
    {χsA χsT} →
  ΔL ∣ ΔR ∣ ρ ⊢ qᵢ ∶ᶜ BL ⊒ BR →
  μq ∣ ΔL ∣ ΔR ∣ ρ ⊢ qₒ ∶ Bₒ ⊒ BR →
  (dₛ⊒ : μd ∣ ΔL ∣ ΔR ∣ ρ ⊢ dₛ ∶ Bₒ ⊒ BL) →
  narrowing-dual dₛ⊒ ≡ d →
  ΔLA ≡ applyTyCtxs χsA ΔL →
  StoreCorr ΔLA ΔR (applyLeftChanges χsA ρ) →
  ΔLT ≡ applyTyCtxs χsT ΔLA →
  ρT ≡ applyLeftChanges χsT (applyLeftChanges χsA ρ) →
  ΔLT ∣ ΔR ∣ ρT ∣ []
    ⊢ N ⊒ Target ∶ applyCoercions χsT (applyCoercions χsA qᵢ)
      ⦂ applyTys χsT (applyTys χsA BL) ⊒ BR →
  ΔLT ∣ ΔR ∣ ρT ∣ []
    ⊢ N ⟨ applyCoercions χsT (applyCoercions χsA d) ⟩
      ⊒ Target ∶ applyCoercions ((keep ∷ χsA) ++ χsT) qₒ
      ⦂ applyTys ((keep ∷ χsA) ++ χsT) Bₒ ⊒ BR
separated-source-cast-plus-result {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {ΔLA = ΔLA} {ΔLT = ΔLT} {ρT = ρT} {Target = Target}
    {N = N} {qᵢ = qᵢ} {qₒ = qₒ} {dₛ = dₛ} {d = d}
    {Bₒ = Bₒ} {BL = BL} {BR = BR} {μq = μq} {μd = μd}
    {χsA = χsA} {χsT = χsT}
    qᵢᶜ qₒ⊒ dₛ⊒ dₛ-dual-eq ΔLA≡ ρA-corr ΔT≡ ρT≡
    N⊒Target =
  let
    μN , nᶜ = typed-term-narrowing-coercion N⊒Target

    ρT-corr :
      StoreCorr ΔLT ΔR
        (applyLeftChanges χsT (applyLeftChanges χsA ρ))
    ρT-corr =
      subst (StoreCorr ΔLT ΔR)
        ρT≡
        (narrowing-store-corrᶜ {μ = μN} nᶜ)

    N⊒TargetT :
      ΔLT ∣ ΔR
        ∣ applyLeftChanges χsT (applyLeftChanges χsA ρ) ∣ []
        ⊢ N ⊒ Target ∶ applyCoercions χsT (applyCoercions χsA qᵢ)
          ⦂ applyTys χsT (applyTys χsA BL) ⊒ BR
    N⊒TargetT =
      subst
        (λ ρ₀ →
          ΔLT ∣ ΔR ∣ ρ₀ ∣ []
            ⊢ N ⊒ Target
              ∶ applyCoercions χsT (applyCoercions χsA qᵢ)
              ⦂ applyTys χsT (applyTys χsA BL) ⊒ BR)
        ρT≡
        N⊒Target

    qᵢᶜA :
      ΔLA ∣ ΔR ∣ applyLeftChanges χsA ρ
        ⊢ applyCoercions χsA qᵢ ∶ᶜ applyTys χsA BL ⊒ BR
    qᵢᶜA =
      left-change-coercion-narrowing χsA {μ = tag-or-idᵈ}
        ΔLA≡ ρA-corr qᵢᶜ

    qᵢᶜT :
      ΔLT ∣ ΔR ∣ applyLeftChanges χsT (applyLeftChanges χsA ρ)
        ⊢ applyCoercions χsT (applyCoercions χsA qᵢ)
          ∶ᶜ applyTys χsT (applyTys χsA BL) ⊒ BR
    qᵢᶜT =
      left-change-coercion-narrowing χsT {μ = tag-or-idᵈ}
        ΔT≡ ρT-corr qᵢᶜA

    qₒ⊒A :
      μq ∣ ΔLA ∣ ΔR ∣ applyLeftChanges χsA ρ
        ⊢ applyCoercions χsA qₒ ∶ applyTys χsA Bₒ ⊒ BR
    qₒ⊒A =
      left-change-coercion-narrowing χsA {μ = μq}
        ΔLA≡ ρA-corr qₒ⊒

    qₒ⊒T :
      μq ∣ ΔLT ∣ ΔR
        ∣ applyLeftChanges χsT (applyLeftChanges χsA ρ)
        ⊢ applyCoercions χsT (applyCoercions χsA qₒ)
          ∶ applyTys χsT (applyTys χsA Bₒ) ⊒ BR
    qₒ⊒T =
      left-change-coercion-narrowing χsT {μ = μq}
        ΔT≡ ρT-corr qₒ⊒A

    dₛ⊒A :
      μd ∣ ΔLA ∣ ΔR ∣ applyLeftChanges χsA ρ
        ⊢ applyCoercions χsA dₛ
          ∶ applyTys χsA Bₒ ⊒ applyTys χsA BL
    dₛ⊒A =
      left-change-source-coercion-narrowing χsA {μ = μd}
        ΔLA≡ ρA-corr dₛ⊒

    dₛ⊒T :
      μd ∣ ΔLT ∣ ΔR
        ∣ applyLeftChanges χsT (applyLeftChanges χsA ρ)
        ⊢ applyCoercions χsT (applyCoercions χsA dₛ)
          ∶ applyTys χsT (applyTys χsA Bₒ)
          ⊒ applyTys χsT (applyTys χsA BL)
    dₛ⊒T =
      left-change-source-coercion-narrowing χsT {μ = μd}
        ΔT≡ ρT-corr dₛ⊒A

    dₛ-dual-A :
      narrowing-dual dₛ⊒A ≡ applyCoercions χsA (narrowing-dual dₛ⊒)
    dₛ-dual-A =
      left-change-source-coercion-narrowing-dual
        χsA ΔLA≡ ρA-corr dₛ⊒

    dₛ-dual-T :
      narrowing-dual dₛ⊒T ≡ applyCoercions χsT (applyCoercions χsA d)
    dₛ-dual-T =
      trans
        (left-change-source-coercion-narrowing-dual
          χsT ΔT≡ ρT-corr dₛ⊒A)
        (trans
          (cong (applyCoercions χsT) dₛ-dual-A)
          (cong
            (λ d₀ → applyCoercions χsT (applyCoercions χsA d₀))
            dₛ-dual-eq))

    N-cast⊒T :
      ΔLT ∣ ΔR ∣ applyLeftChanges χsT (applyLeftChanges χsA ρ) ∣ []
        ⊢ N ⟨ applyCoercions χsT (applyCoercions χsA d) ⟩
          ⊒ Target ∶ applyCoercions χsT (applyCoercions χsA qₒ)
          ⦂ applyTys χsT (applyTys χsA Bₒ) ⊒ BR
    N-cast⊒T =
      subst
        (λ d₀ →
          ΔLT ∣ ΔR
            ∣ applyLeftChanges χsT (applyLeftChanges χsA ρ) ∣ []
            ⊢ N ⟨ d₀ ⟩ ⊒ Target
              ∶ applyCoercions χsT (applyCoercions χsA qₒ)
              ⦂ applyTys χsT (applyTys χsA Bₒ) ⊒ BR)
        dₛ-dual-T
        (cast+⊒ᵗ
          {ΔL = ΔLT}
          {ΔR = ΔR}
          {ρ = applyLeftChanges χsT (applyLeftChanges χsA ρ)}
          {γ = []}
          {M = N}
          {M′ = Target}
          {q = applyCoercions χsT (applyCoercions χsA qᵢ)}
          {r = applyCoercions χsT (applyCoercions χsA qₒ)}
          {s = applyCoercions χsT (applyCoercions χsA dₛ)}
          {A = applyTys χsT (applyTys χsA Bₒ)}
          {B = BR}
          {C = applyTys χsT (applyTys χsA BL)}
          {μ = μq}
          {η = μd}
          qᵢᶜT
          qₒ⊒T
          dₛ⊒T
          {! beta-cast-tail-composition !}
          N⊒TargetT)
  in
  subst
    (λ ρ₀ →
      ΔLT ∣ ΔR ∣ ρ₀ ∣ []
        ⊢ N ⟨ applyCoercions χsT (applyCoercions χsA d) ⟩
          ⊒ Target ∶ applyCoercions ((keep ∷ χsA) ++ χsT) qₒ
          ⦂ applyTys ((keep ∷ χsA) ++ χsT) Bₒ ⊒ BR)
    (sym ρT≡)
    (subst
      (λ q →
        ΔLT ∣ ΔR ∣ applyLeftChanges χsT (applyLeftChanges χsA ρ) ∣ []
          ⊢ N ⟨ applyCoercions χsT (applyCoercions χsA d) ⟩
            ⊒ Target ∶ q
            ⦂ applyTys ((keep ∷ χsA) ++ χsT) Bₒ ⊒ BR)
      (sym (applyCoercions-++ χsA χsT qₒ))
      (subst
        (λ B →
          ΔLT ∣ ΔR
            ∣ applyLeftChanges χsT (applyLeftChanges χsA ρ) ∣ []
            ⊢ N ⟨ applyCoercions χsT (applyCoercions χsA d) ⟩
              ⊒ Target
              ∶ applyCoercions χsT (applyCoercions χsA qₒ)
              ⦂ B ⊒ BR)
        (sym (applyTys-++ χsA χsT Bₒ))
        N-cast⊒T))

-- Temporarily TERMINATING for the same reason as `sim-beta`: the recursive
-- call goes through catchup projections that Agda cannot see as structural.
{-# TERMINATING #-}
separated-dgg-beta-cast-value-shape :
  ∀ {ΔL ΔR ρ L R T V′ W′ c d pᵈ p q A A′ B B′} →
  Value L →
  No• L →
  Value R →
  No• R →
  Value V′ →
  Value W′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ T ∶ p ↦ q ⦂ A ⇒ B ⊒ A′ ⇒ B′ →
  T ≡ V′ ⟨ c ↦ d ⟩ →
  ΔL ∣ ΔR ∣ ρ ⊢ pᵈ ∶ᶜ A ⊒ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ R ⊒ W′ ∶ pᵈ ⦂ A ⊒ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩
        ∶ applyCoercions χs q ⦂ applyTys χs B ⊒ B′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′ (⊒blameᵗ M⊢ pᶜ) () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′ (x⊒xᵗ pᶜ x∋p) () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′ (ƛ⊒ƛᵗ p↦qᶜ N⊒N′) () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′ (·⊒·ᵗ p↦qᶜ L⊒L′ M⊒M′) () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d} {A′ = A′} {B′ = B′}
    vL noL vR noR vV′ vW′
    targetCast@(⊒cast+ᵗ {M′ = F′} {r = pᵢ ↦ qᵢ}
      {t = cₜ ↦ dₜ} {B = Aᵢ ⇒ Bᵢ} {η = ηCast}
      pᶜ rᶜ t⊒ _ L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′ =
  let
    relation-obligation :
      ΔL ∣ ΔR ∣ ρ ∣ []
        ⊢ L · R ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ _ ⦂ _ ⊒ _
    relation-obligation =
      let
        target-shape : T ≡ V′ ⟨ c ↦ d ⟩
        target-shape = T≡V′cd

        target-head-eq : F′ ≡ V′
        target-head-eq = ⟨⟩-term-injective T≡V′cd

        target-cast-eq : narrowing-dual t⊒ ≡ c ↦ d
        target-cast-eq = ⟨⟩-coercion-injective T≡V′cd

        target-domain-eq : ↦-domain (narrowing-dual t⊒) ≡ c
        target-domain-eq = cong ↦-domain target-cast-eq

        target-codomain-eq : ↦-codomain (narrowing-dual t⊒) ≡ d
        target-codomain-eq = cong ↦-codomain target-cast-eq

        target-function-cast :
          ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ T ∶ _ ⦂ _ ⊒ _
        target-function-cast = targetCast

        inner-function-relation :
          ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ F′ ∶ _ ⦂ _ ⊒ _
        inner-function-relation = L⊒F′

        target-argument :
          ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ R ⊒ W′ ∶ _ ⦂ _ ⊒ _
        target-argument = R⊒W′

        obligation :
          ΔL ∣ ΔR ∣ ρ ∣ []
            ⊢ L · R ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ _ ⦂ _ ⊒ _
        obligation = {! separated-dgg-beta-cast-target-plus-relation !}
      in
      obligation
  in
  [] ,
  L · R ,
  ΔL ,
  ρ ,
  ↠-refl ,
  refl ,
  refl ,
  relation-obligation
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {t = id A} pᶜ rᶜ t⊒ _ L⊒F′)
    () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {t = t₁ ︔ t₂} pᶜ rᶜ t⊒ _ L⊒F′)
    () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {t = `∀ t} pᶜ rᶜ t⊒ _ L⊒F′)
    () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {t = G !} pᶜ rᶜ t⊒ _ L⊒F′)
    () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {t = G ？} pᶜ rᶜ t⊒ _ L⊒F′)
    () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {t = seal A α} pᶜ rᶜ t⊒ _ L⊒F′)
    () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {t = unseal α A} pᶜ rᶜ t⊒ _ L⊒F′)
    () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {t = gen A t} pᶜ rᶜ t⊒ _ L⊒F′)
    () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {t = inst A t} pᶜ rᶜ t⊒ _ L⊒F′)
    () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {r = id P} {t = cₜ ↦ dₜ} pᶜ rᶜ t⊒ _ L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′ =
  {! separated-dgg-beta-cast-target-plus-id-inner-coercion !}
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {r = r₁ ︔ r₂} {t = cₜ ↦ dₜ} pᶜ rᶜ t⊒ _ L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′ =
  {! separated-dgg-beta-cast-target-plus-seq-inner-coercion !}
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {r = G !} {t = cₜ ↦ dₜ} pᶜ
      (_ , _ , refl , _ , _ , _ , _)
      (_ , _ , () , _ , _ , _ , _)
      _ L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {r = seal P α} {t = cₜ ↦ dₜ} pᶜ
      (_ , _ , refl , _ , _ , _ , _)
      (_ , _ , () , _ , _ , _ , _)
      _ L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {r = gen P r} {t = cₜ ↦ dₜ} pᶜ
      (_ , _ , refl , _ , _ , _ , _)
      (_ , _ , () , _ , _ , _ , _)
      _ L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d} {A′ = A′} {B′ = B′}
    vL noL vR noR vV′ vW′
    targetCast@(⊒cast-ᵗ {M′ = F′} {p = pᵢ ↦ qᵢ}
      {t = cₜ ↦ dₜ} {C = Aᵢ ⇒ Bᵢ} {η = ηCast}
      pᶜ rᶜ
      t⊒@(storesCast , _ , _ , wf⇒ hAᵢ hBᵢ , wf⇒ hA′ hB′ ,
        (cast-fun cₜ⊢L _ , cross (cₜʷL ↦ⁿʷ _)) ,
        (cast-fun cₜ⊢R _ , cross (cₜʷR ↦ⁿʷ _)))
      _ L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′ =
  let
    relation-obligation :
      ΔL ∣ ΔR ∣ ρ ∣ []
        ⊢ L · R ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ _ ⦂ _ ⊒ _
    relation-obligation =
      let
        target-shape : T ≡ V′ ⟨ c ↦ d ⟩
        target-shape = T≡V′cd

        target-head-eq : F′ ≡ V′
        target-head-eq = ⟨⟩-term-injective T≡V′cd

        target-cast-eq : cₜ ↦ dₜ ≡ c ↦ d
        target-cast-eq = ⟨⟩-coercion-injective T≡V′cd

        target-domain-eq : cₜ ≡ c
        target-domain-eq = ↦-left-injective target-cast-eq

        target-codomain-eq : dₜ ≡ d
        target-codomain-eq = ↦-right-injective target-cast-eq

        target-function-cast :
          ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ T ∶ _ ⦂ _ ⊒ _
        target-function-cast = targetCast

        inner-function-relation :
          ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ F′ ∶ _ ⦂ _ ⊒ _
        inner-function-relation = L⊒F′

        target-argument :
          ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ R ⊒ W′ ∶ _ ⦂ _ ⊒ _
        target-argument = R⊒W′

        target-domain-cast :
          ηCast ∣ ΔL ∣ ΔR ∣ ρ ⊢ fun-narrow-domain-dual t⊒ ∶ Aᵢ ⊒ A′
        target-domain-cast =
          let
            cₜᵈ⊒L =
              proj₁
                (dualʷ-flips-typingᵐ
                  dualActionOk-normal
                  dualStoreAt-normal
                  (leftStore-wf storesCast)
                  (cₜ⊢L , cₜʷL)) ,
              proj₂ (dualʷ normalᵃ cₜʷL)

            cₜᵈ⊒R =
              proj₁
                (dualʷ-flips-typingᵐ
                  dualActionOk-normal
                  dualStoreAt-normal
                  (rightStore-wf storesCast)
                  (cₜ⊢R , cₜʷR)) ,
              proj₂ (dualʷ normalᵃ cₜʷR)
          in
          storesCast ,
          proj₁ (coercion-src-tgtᵐ (proj₁ cₜᵈ⊒L)) ,
          proj₂ (coercion-src-tgtᵐ (proj₁ cₜᵈ⊒L)) ,
          hAᵢ ,
          hA′ ,
          cₜᵈ⊒L ,
          subst
            (λ p₀ → ηCast ∣ ΔR ∣ rightStore ρ ⊢ p₀ ∶ Aᵢ ⊒ A′)
            (dualʷ-raw-determined normalᵃ cₜʷR cₜʷL)
            cₜᵈ⊒R

        target-domain-dual-eq :
          narrowing-dual target-domain-cast ≡ c
        target-domain-dual-eq =
          trans (dualʷ-involutive-raw cₜʷL) target-domain-eq

        target-codomain-cast :
          ηCast ∣ ΔL ∣ ΔR ∣ ρ ⊢ d ∶ Bᵢ ⊒ B′
        target-codomain-cast =
          subst
            (λ d₀ → ηCast ∣ ΔL ∣ ΔR ∣ ρ ⊢ d₀ ∶ Bᵢ ⊒ B′)
            target-codomain-eq
            (separated-fun-codomain t⊒)

        target-argument-cast :
          ΔL ∣ ΔR ∣ ρ ∣ []
            ⊢ R ⊒ W′ ⟨ c ⟩
              ∶ fun-narrow-domain-dualᶜ pᶜ ⦂ _ ⊒ _
        target-argument-cast =
          subst
            (λ c₀ →
              ΔL ∣ ΔR ∣ ρ ∣ []
                ⊢ R ⊒ W′ ⟨ c₀ ⟩
                  ∶ fun-narrow-domain-dualᶜ pᶜ ⦂ _ ⊒ _)
            target-domain-dual-eq
            (⊒cast+ᵗ
              (fun-narrow-domain-dual-typingᶜ pᶜ)
              p-domainᶜ
              target-domain-cast
              {! target-argument-cast-composition !}
              R⊒W′)

        inner-application :
          ΔL ∣ ΔR ∣ ρ ∣ []
            ⊢ L · R ⊒ F′ · (W′ ⟨ c ⟩)
              ∶ qᵢ ⦂ _ ⊒ _
        inner-application =
          ·⊒·ᵗ pᶜ L⊒F′ target-argument-cast

        target-result-cast :
          ΔL ∣ ΔR ∣ ρ ∣ []
            ⊢ L · R ⊒ (F′ · (W′ ⟨ c ⟩)) ⟨ d ⟩
              ∶ _ ⦂ _ ⊒ _
        target-result-cast =
          ⊒cast-ᵗ
            (fun-narrow-codomainᶜ pᶜ)
            (separated-fun-codomain rᶜ)
            target-codomain-cast
            {! target-result-cast-composition !}
            inner-application

        obligation :
          ΔL ∣ ΔR ∣ ρ ∣ []
            ⊢ L · R ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ _ ⦂ _ ⊒ _
        obligation =
          subst
            (λ F →
              ΔL ∣ ΔR ∣ ρ ∣ []
                ⊢ L · R ⊒ (F · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ _ ⦂ _ ⊒ _)
            target-head-eq
            target-result-cast
      in
      obligation
  in
  [] ,
  L · R ,
  ΔL ,
  ρ ,
  ↠-refl ,
  refl ,
  refl ,
  relation-obligation
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {t = id A} pᶜ rᶜ t⊒ _ L⊒F′)
    () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {t = t₁ ︔ t₂} pᶜ rᶜ t⊒ _ L⊒F′)
    () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {t = `∀ t} pᶜ rᶜ t⊒ _ L⊒F′)
    () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {t = G !} pᶜ rᶜ t⊒ _ L⊒F′)
    () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {t = G ？} pᶜ rᶜ t⊒ _ L⊒F′)
    () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {t = seal A α} pᶜ rᶜ t⊒ _ L⊒F′)
    () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {t = unseal α A} pᶜ rᶜ t⊒ _ L⊒F′)
    () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {t = gen A t} pᶜ rᶜ t⊒ _ L⊒F′)
    () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {t = inst A t} pᶜ rᶜ t⊒ _ L⊒F′)
    () p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {V′ = V′} {W′ = W′} {c = c} {d = d}
    vL noL vR noR vV′ vW′
    targetCast@(⊒cast-ᵗ {M′ = F′} {p = id P}
      {t = cₜ ↦ dₜ}
      (_ , () , _ , _ , _ , (_ , cross (id-＇ α)) , _)
      rᶜ t⊒ _ L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {V′ = V′} {W′ = W′} {c = c} {d = d}
    vL noL vR noR vV′ vW′
    targetCast@(⊒cast-ᵗ {M′ = F′} {p = id P}
      {t = cₜ ↦ dₜ}
      (_ , () , _ , _ , _ , (_ , cross (id-‵ ι)) , _)
      rᶜ t⊒ _ L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {V′ = V′} {W′ = W′} {c = c} {d = d}
    vL noL vR noR vV′ vW′
    targetCast@(⊒cast-ᵗ {M′ = F′} {p = id P}
      {t = cₜ ↦ dₜ}
      (_ , () , _ , _ , _ , (_ , id★) , _)
      rᶜ t⊒ _ L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {V′ = V′} {W′ = W′} {c = c} {d = d}
    vL noL vR noR vV′ vW′
    targetCast@(⊒cast-ᵗ {M′ = F′} {p = p₀ ︔ p₁}
      {t = cₜ ↦ dₜ}
      (_ , () , _ , _ , _ , (_ , G ？︔ gⁿ) , _)
      rᶜ t⊒ _ L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {V′ = V′} {W′ = W′} {c = c} {d = d}
    vL noL vR noR vV′ vW′
    targetCast@(⊒cast-ᵗ {M′ = F′} {p = p₀ ︔ p₁}
      {t = cₜ ↦ dₜ}
      (_ , _ , refl , _ , _ , (_ , gⁿ ︔seal α) , _)
      rᶜ (_ , () , _ , _ , _ , _ , _) _ L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d}
    vL noL vR noR vV′ vW′
    sourceCast@(cast+⊒ᵗ {M = F₀} qᶜ rᶜ s⊒ _ F₀⊒T)
    T≡V′cd p-domainᶜ R⊒W′
    with canonical-⇒ vL (typed-term-narrowing-source-typingᶜ sourceCast)
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d}
    vL noL vR noR vV′ vW′
    sourceCast@(cast+⊒ᵗ {M = F₀} qᶜ rᶜ s⊒ _ F₀⊒T)
    T≡V′cd p-domainᶜ R⊒W′
    | fv-ƛ ()
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d}
    vL noL vR noR vV′ vW′
    sourceCast@(cast+⊒ᵗ {M = F₀} {q = pᵢ ↦ qᵢ}
      {r = pₒ ↦ qₒ} {s = c₀ ↦ d₀}
      {A = Aₒ ⇒ Bₒ} {B = AR ⇒ BR} {C = AL ⇒ BL}
      {μ = μOuter} {η = ηCast}
      qInner
      rOuter
      sCast@(storesCast , _ , _ , wf⇒ hAₒs hBₒs ,
        wf⇒ hALs hBLs ,
        (cast-fun c₀⊢L d₀⊢L , cross (c₀ʷL ↦ⁿʷ d₀ⁿL)) ,
        (cast-fun c₀⊢R d₀⊢R , cross (c₀ʷR ↦ⁿʷ d₀ⁿR)))
      compᵏ
      F₀⊒T)
    T≡V′cd p-domainᶜ R⊒W′
    | fv-↦ {W = F} {c = cₛ} {d = dₛ} vF L≡Fcd =
  let
    source-cast-shape : L ≡ F ⟨ cₛ ↦ dₛ ⟩
    source-cast-shape = L≡Fcd

    source-head-eq : F₀ ≡ F
    source-head-eq = ⟨⟩-term-injective L≡Fcd

    source-cast-eq : narrowing-dual sCast ≡ cₛ ↦ dₛ
    source-cast-eq = ⟨⟩-coercion-injective L≡Fcd

    source-domain-eq : ↦-domain (narrowing-dual sCast) ≡ cₛ
    source-domain-eq = cong ↦-domain source-cast-eq

    source-codomain-eq : ↦-codomain (narrowing-dual sCast) ≡ dₛ
    source-codomain-eq = cong ↦-codomain source-cast-eq

    source-head-no• : No• F
    source-head-no• = no•-cast-inv (subst No• L≡Fcd noL)

    source-head-step :
      L · R —↠[ keep ∷ [] ] (F · (R ⟨ cₛ ⟩)) ⟨ dₛ ⟩
    source-head-step =
      subst
        (λ H → H · R —↠[ keep ∷ [] ] (F · (R ⟨ cₛ ⟩)) ⟨ dₛ ⟩)
        (sym L≡Fcd)
        (↠-step (pure-step (β-↦ vF vR)) ↠-refl)

    source-head-relation :
      ΔL ∣ ΔR ∣ ρ ∣ []
        ⊢ F ⊒ T ∶ pᵢ ↦ qᵢ ⦂ AL ⇒ BL ⊒ AR ⇒ BR
    source-head-relation =
      subst
        (λ F₁ →
          ΔL ∣ ΔR ∣ ρ ∣ []
            ⊢ F₁ ⊒ T ∶ pᵢ ↦ qᵢ ⦂ AL ⇒ BL ⊒ AR ⇒ BR)
        source-head-eq
        F₀⊒T

    qₒ⊒ :
      μOuter ∣ ΔL ∣ ΔR ∣ ρ ⊢ qₒ ∶ Bₒ ⊒ BR
    qₒ⊒ = separated-fun-codomain rOuter

    d₀⊒ :
      ηCast ∣ ΔL ∣ ΔR ∣ ρ ⊢ d₀ ∶ Bₒ ⊒ BL
    d₀⊒ =
      storesCast ,
      proj₁ (coercion-src-tgtᵐ d₀⊢L) ,
      proj₂ (coercion-src-tgtᵐ d₀⊢L) ,
      hBₒs ,
      hBLs ,
      (d₀⊢L , d₀ⁿL) ,
      (d₀⊢R , d₀ⁿR)

    d₀-dual-eq :
      narrowing-dual d₀⊒ ≡ dₛ
    d₀-dual-eq = source-codomain-eq

    c₀-dual⊒ :
      ηCast ∣ ΔL ∣ ΔR ∣ ρ
        ⊢ proj₁ (dualʷ normalᵃ c₀ʷL) ∶ Aₒ ⊒ AL
    c₀-dual⊒ =
      let
        c₀ᵈ⊒L =
          proj₁
            (dualʷ-flips-typingᵐ
              dualActionOk-normal
              dualStoreAt-normal
              (leftStore-wf storesCast)
              (c₀⊢L , c₀ʷL)) ,
          proj₂ (dualʷ normalᵃ c₀ʷL)

        c₀ᵈ⊒R =
          proj₁
            (dualʷ-flips-typingᵐ
              dualActionOk-normal
              dualStoreAt-normal
              (rightStore-wf storesCast)
              (c₀⊢R , c₀ʷR)) ,
          proj₂ (dualʷ normalᵃ c₀ʷR)
      in
      storesCast ,
      proj₁ (coercion-src-tgtᵐ (proj₁ c₀ᵈ⊒L)) ,
      proj₂ (coercion-src-tgtᵐ (proj₁ c₀ᵈ⊒L)) ,
      hAₒs ,
      hALs ,
      c₀ᵈ⊒L ,
      subst
        (λ c₁ → ηCast ∣ ΔR ∣ rightStore ρ ⊢ c₁ ∶ Aₒ ⊒ AL)
        (dualʷ-raw-determined normalᵃ c₀ʷR c₀ʷL)
        c₀ᵈ⊒R

    cₛ⊒ :
      ηCast ∣ ΔL ∣ ΔR ∣ ρ ⊢ cₛ ∶ Aₒ ⊒ AL
    cₛ⊒ =
      subst
        (λ c₁ → ηCast ∣ ΔL ∣ ΔR ∣ ρ ⊢ c₁ ∶ Aₒ ⊒ AL)
        source-domain-eq
        c₀-dual⊒

    R-c⊒W′ :
      ΔL ∣ ΔR ∣ ρ ∣ []
        ⊢ R ⟨ cₛ ⟩ ⊒ W′ ∶ fun-narrow-domain-dualᶜ qInner
          ⦂ AL ⊒ AR
    R-c⊒W′ =
      cast-⊒ᵗ
        (fun-narrow-domain-dual-typingᶜ qInner)
        p-domainᶜ
        cₛ⊒
        {! source-argument-cast-composition !}
        R⊒W′

    χsA , WRA , ΔLA ,
      vWRA , noWRA , R-c↠WRA , ΔLA≡ , ρA-corr ,
      leftA≡ , rightA≡ , pAᶜ , WRA⊒W′ =
      catchup-lemmaˡ
        (ok-⟨⟩ (ok-no noR))
        vW′
        R-c⊒W′

    F-left⊒T =
      advance-left-function-term-narrowing
        χsA ΔLA≡ ρA-corr source-head-relation

    arg-ready :
      F · (R ⟨ cₛ ⟩) —↠[ χsA ] applyTerms χsA F · WRA
    arg-ready = ·₂-↠ vF source-head-no• R-c↠WRA

    cast-arg-ready :
      (F · (R ⟨ cₛ ⟩)) ⟨ dₛ ⟩ —↠[ χsA ]
        (applyTerms χsA F · WRA) ⟨ applyCoercions χsA dₛ ⟩
    cast-arg-ready = cast-↠ {c = dₛ} arg-ready

    prefix-ready :
      L · R —↠[ keep ∷ χsA ]
        (applyTerms χsA F · WRA) ⟨ applyCoercions χsA dₛ ⟩
    prefix-ready = ↠-trans source-head-step cast-arg-ready

    rec =
      separated-dgg-beta-cast-value-shape
        (applyTerms-preserves-Value χsA vF)
        (applyTerms-preserves-No• χsA source-head-no•)
        vWRA
        noWRA
        vV′
        vW′
        F-left⊒T
        T≡V′cd
        pAᶜ
        WRA⊒W′

    χsT , N , ΔLT , ρT ,
      tail-red , ΔT≡ , ρT≡ , N⊒target = rec

    tail-ready :
      (applyTerms χsA F · WRA) ⟨ applyCoercions χsA dₛ ⟩
        —↠[ χsT ]
      N ⟨ applyCoercions χsT (applyCoercions χsA dₛ) ⟩
    tail-ready = cast-↠ {c = applyCoercions χsA dₛ} tail-red

    source-steps :
      L · R —↠[ (keep ∷ χsA) ++ χsT ]
        N ⟨ applyCoercions χsT (applyCoercions χsA dₛ) ⟩
    source-steps = ↠-trans prefix-ready tail-ready

    ΔLT-total≡ :
      ΔLT ≡ applyTyCtxs ((keep ∷ χsA) ++ χsT) ΔL
    ΔLT-total≡ =
      trans ΔT≡
        (trans
          (cong (applyTyCtxs χsT) ΔLA≡)
          (sym (applyTyCtxs-++ χsA χsT ΔL)))

    ρT-total≡ :
      ρT ≡ applyLeftChanges ((keep ∷ χsA) ++ χsT) ρ
    ρT-total≡ =
      trans ρT≡ (sym (applyLeftChanges-++ χsA χsT ρ))

    final⊒ :
      ΔLT ∣ ΔR ∣ ρT ∣ []
        ⊢ N ⟨ applyCoercions χsT (applyCoercions χsA dₛ) ⟩
          ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩
          ∶ applyCoercions ((keep ∷ χsA) ++ χsT) qₒ
          ⦂ applyTys ((keep ∷ χsA) ++ χsT) Bₒ ⊒ BR
    final⊒ =
      separated-source-cast-plus-result
        {ΔL = ΔL}
        {ΔR = ΔR}
        {ρ = ρ}
        {ΔLA = ΔLA}
        {ΔLT = ΔLT}
        {ρT = ρT}
        {Target = (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩}
        {N = N}
        {qᵢ = qᵢ}
        {qₒ = qₒ}
        {dₛ = d₀}
        {d = dₛ}
        {Bₒ = Bₒ}
        {BL = BL}
        {BR = BR}
        {μq = μOuter}
        {μd = ηCast}
        {χsA = χsA}
        {χsT = χsT}
        (fun-narrow-codomainᶜ qInner)
        qₒ⊒
        d₀⊒
        d₀-dual-eq
        ΔLA≡
        ρA-corr
        ΔT≡
        ρT≡
        N⊒target
  in
  (keep ∷ χsA) ++ χsT ,
  N ⟨ applyCoercions χsT (applyCoercions χsA dₛ) ⟩ ,
  ΔLT ,
  ρT ,
  source-steps ,
  ΔLT-total≡ ,
  ρT-total≡ ,
  final⊒
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d}
    vL noL vR noR vV′ vW′
    sourceCast@(cast+⊒ᵗ {M = F₀} qᶜ rᶜ s⊒ _ F₀⊒T)
    T≡V′cd p-domainᶜ R⊒W′
    | fv-↦ vF L≡Fcd =
  {! separated-dgg-beta-cast-source-plus-noncanonical-inner-coercion !}
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d}
    vL noL vR noR vV′ vW′
    sourceCast@(cast-⊒ᵗ {M = F₀} {q = pₒ ↦ qₒ} {r = pᵢ ↦ qᵢ}
      {s = c₀ ↦ d₀} {A = AL ⇒ BL} {C = Aₒ ⇒ Bₒ}
      {η = ηCast}
      (storesOuter , _ , _ , wf⇒ hAₒ hBₒ , wf⇒ hAR hBR ,
        (cast-fun _ qₒ⊢L , cross (_ ↦ⁿʷ qₒⁿL)) ,
        (cast-fun _ qₒ⊢R , cross (_ ↦ⁿʷ qₒⁿR)))
      rInner@(storesInner , _ , _ , wf⇒ hAL hBL , wf⇒ hARᵢ hBRᵢ ,
        (cast-fun pᵢ⊢L _ , cross (pᵢʷL ↦ⁿʷ _)) ,
        (cast-fun pᵢ⊢R _ , cross (pᵢʷR ↦ⁿʷ _)))
      (storesCast , _ , _ , wf⇒ hALs hBLs , wf⇒ hAₒs hBₒs ,
        (cast-fun c₀⊢L d₀⊢L , cross (c₀ʷL ↦ⁿʷ d₀ⁿL)) ,
        (cast-fun c₀⊢R d₀⊢R , cross (c₀ʷR ↦ⁿʷ d₀ⁿR)))
      compᵏ
      F₀⊒T)
    T≡V′cd p-domainᶜ R⊒W′
    with canonical-⇒ vL (typed-term-narrowing-source-typingᶜ sourceCast)
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d}
    vL noL vR noR vV′ vW′
    sourceCast@(cast-⊒ᵗ {M = F₀} {q = pₒ ↦ qₒ} {r = pᵢ ↦ qᵢ}
      {s = c₀ ↦ d₀} {A = AL ⇒ BL} {C = Aₒ ⇒ Bₒ}
      {η = ηCast}
      (storesOuter , _ , _ , wf⇒ hAₒ hBₒ , wf⇒ hAR hBR ,
        (cast-fun _ qₒ⊢L , cross (_ ↦ⁿʷ qₒⁿL)) ,
        (cast-fun _ qₒ⊢R , cross (_ ↦ⁿʷ qₒⁿR)))
      rInner@(storesInner , _ , _ , wf⇒ hAL hBL , wf⇒ hARᵢ hBRᵢ ,
        (cast-fun pᵢ⊢L _ , cross (pᵢʷL ↦ⁿʷ _)) ,
        (cast-fun pᵢ⊢R _ , cross (pᵢʷR ↦ⁿʷ _)))
      (storesCast , _ , _ , wf⇒ hALs hBLs , wf⇒ hAₒs hBₒs ,
        (cast-fun c₀⊢L d₀⊢L , cross (c₀ʷL ↦ⁿʷ d₀ⁿL)) ,
        (cast-fun c₀⊢R d₀⊢R , cross (c₀ʷR ↦ⁿʷ d₀ⁿR)))
      compᵏ
      F₀⊒T)
    T≡V′cd p-domainᶜ R⊒W′
    | fv-ƛ ()
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d}
    vL noL vR noR vV′ vW′
    sourceCast@(cast-⊒ᵗ {M = F₀} {q = pₒ ↦ qₒ} {r = pᵢ ↦ qᵢ}
      {s = c₀ ↦ d₀} {A = AL ⇒ BL} {C = Aₒ ⇒ Bₒ}
      {η = ηCast}
      (storesOuter , _ , _ , wf⇒ hAₒ hBₒ , wf⇒ hAR hBR ,
        (cast-fun _ qₒ⊢L , cross (_ ↦ⁿʷ qₒⁿL)) ,
        (cast-fun _ qₒ⊢R , cross (_ ↦ⁿʷ qₒⁿR)))
      rInner@(storesInner , _ , _ , wf⇒ hAL hBL , wf⇒ hARᵢ hBRᵢ ,
        (cast-fun pᵢ⊢L _ , cross (pᵢʷL ↦ⁿʷ _)) ,
        (cast-fun pᵢ⊢R _ , cross (pᵢʷR ↦ⁿʷ _)))
      (storesCast , _ , _ , wf⇒ hALs hBLs , wf⇒ hAₒs hBₒs ,
        (cast-fun c₀⊢L d₀⊢L , cross (c₀ʷL ↦ⁿʷ d₀ⁿL)) ,
        (cast-fun c₀⊢R d₀⊢R , cross (c₀ʷR ↦ⁿʷ d₀ⁿR)))
      compᵏ
      F₀⊒T)
    T≡V′cd p-domainᶜ R⊒W′
    | fv-↦ {W = F} {c = cₛ} {d = dₛ} vF L≡Fcd =
  let
    source-head-eq : F₀ ≡ F
    source-head-eq = ⟨⟩-term-injective L≡Fcd

    source-cast-eq : c₀ ↦ d₀ ≡ cₛ ↦ dₛ
    source-cast-eq = ⟨⟩-coercion-injective L≡Fcd

    source-domain-eq : c₀ ≡ cₛ
    source-domain-eq = ↦-left-injective source-cast-eq

    source-codomain-eq : d₀ ≡ dₛ
    source-codomain-eq = ↦-right-injective source-cast-eq

    source-head-no• : No• F
    source-head-no• = no•-cast-inv (subst No• L≡Fcd noL)

    source-head-step :
      L · R —↠[ keep ∷ [] ] (F · (R ⟨ cₛ ⟩)) ⟨ dₛ ⟩
    source-head-step =
      subst
        (λ H → H · R —↠[ keep ∷ [] ] (F · (R ⟨ cₛ ⟩)) ⟨ dₛ ⟩)
        (sym L≡Fcd)
        (↠-step (pure-step (β-↦ vF vR)) ↠-refl)

    source-head-relation :
      ΔL ∣ ΔR ∣ ρ ∣ []
        ⊢ F ⊒ T ∶ pᵢ ↦ qᵢ ⦂ AL ⇒ BL ⊒ _ ⇒ _
    source-head-relation =
      subst
        (λ F₁ →
          ΔL ∣ ΔR ∣ ρ ∣ []
            ⊢ F₁ ⊒ T ∶ pᵢ ↦ qᵢ ⦂ AL ⇒ BL ⊒ _ ⇒ _)
        source-head-eq
        F₀⊒T

    qₒ⊒ :
      tag-or-idᵈ ∣ ΔL ∣ ΔR ∣ ρ ⊢ qₒ ∶ Bₒ ⊒ _
    qₒ⊒ =
      storesOuter ,
      proj₁ (coercion-src-tgtᵐ qₒ⊢L) ,
      proj₂ (coercion-src-tgtᵐ qₒ⊢L) ,
      hBₒ ,
      hBR ,
      (qₒ⊢L , qₒⁿL) ,
      (qₒ⊢R , qₒⁿR)

    d₀⊒ :
      ηCast ∣ ΔL ∣ ΔR ∣ ρ ⊢ d₀ ∶ BL ⊒ Bₒ
    d₀⊒ =
      storesCast ,
      proj₁ (coercion-src-tgtᵐ d₀⊢L) ,
      proj₂ (coercion-src-tgtᵐ d₀⊢L) ,
      hBLs ,
      hBₒs ,
      (d₀⊢L , d₀ⁿL) ,
      (d₀⊢R , d₀ⁿR)

    dₛ⊒ :
      ηCast ∣ ΔL ∣ ΔR ∣ ρ ⊢ dₛ ∶ BL ⊒ Bₒ
    dₛ⊒ =
      subst
        (λ d₁ → ηCast ∣ ΔL ∣ ΔR ∣ ρ ⊢ d₁ ∶ BL ⊒ Bₒ)
        source-codomain-eq
        d₀⊒

    pᵢ-domain⊒ :
      _ ∣ ΔL ∣ ΔR ∣ ρ
        ⊢ fun-narrow-domain-dual rInner ∶ AL ⊒ _
    pᵢ-domain⊒ = separated-fun-domain-dual rInner

    c-dual⊒ :
      ηCast ∣ ΔL ∣ ΔR ∣ ρ
        ⊢ proj₁ (dualʷ normalᵃ c₀ʷL) ∶ AL ⊒ Aₒ
    c-dual⊒ =
      let
        cᵈ⊒L =
          proj₁
            (dualʷ-flips-typingᵐ
              dualActionOk-normal
              dualStoreAt-normal
              (leftStore-wf storesCast)
              (c₀⊢L , c₀ʷL)) ,
          proj₂ (dualʷ normalᵃ c₀ʷL)

        cᵈ⊒R =
          proj₁
            (dualʷ-flips-typingᵐ
              dualActionOk-normal
              dualStoreAt-normal
              (rightStore-wf storesCast)
              (c₀⊢R , c₀ʷR)) ,
          proj₂ (dualʷ normalᵃ c₀ʷR)
      in
      storesCast ,
      proj₁ (coercion-src-tgtᵐ (proj₁ cᵈ⊒L)) ,
      proj₂ (coercion-src-tgtᵐ (proj₁ cᵈ⊒L)) ,
      hALs ,
      hAₒs ,
      cᵈ⊒L ,
      subst
        (λ c₁ → ηCast ∣ ΔR ∣ rightStore ρ ⊢ c₁ ∶ AL ⊒ Aₒ)
        (dualʷ-raw-determined normalᵃ c₀ʷR c₀ʷL)
        cᵈ⊒R

    c-dual-eq :
      narrowing-dual c-dual⊒ ≡ cₛ
    c-dual-eq = trans (dualʷ-involutive-raw c₀ʷL) source-domain-eq

    R-c⊒W′ :
      ΔL ∣ ΔR ∣ ρ ∣ []
        ⊢ R ⟨ cₛ ⟩ ⊒ W′ ∶ fun-narrow-domain-dual rInner
          ⦂ AL ⊒ _
    R-c⊒W′ =
      subst
        (λ c₁ →
          ΔL ∣ ΔR ∣ ρ ∣ []
            ⊢ R ⟨ c₁ ⟩ ⊒ W′ ∶ fun-narrow-domain-dual rInner
              ⦂ AL ⊒ _)
        c-dual-eq
        (cast+⊒ᵗ p-domainᶜ pᵢ-domain⊒ c-dual⊒
          {! source-argument-domain-composition !}
          R⊒W′)

    χsA , WRA , ΔLA ,
      vWRA , noWRA , R-c↠WRA , ΔLA≡ , ρA-corr ,
      leftA≡ , rightA≡ , pAᶜ , WRA⊒W′ =
      catchup-lemmaˡ
        (ok-⟨⟩ (ok-no noR))
        vW′
        R-c⊒W′

    F-left⊒T =
      advance-left-function-term-narrowing
        χsA ΔLA≡ ρA-corr source-head-relation

    arg-ready :
      F · (R ⟨ cₛ ⟩) —↠[ χsA ] applyTerms χsA F · WRA
    arg-ready = ·₂-↠ vF source-head-no• R-c↠WRA

    cast-arg-ready :
      (F · (R ⟨ cₛ ⟩)) ⟨ dₛ ⟩ —↠[ χsA ]
        (applyTerms χsA F · WRA) ⟨ applyCoercions χsA dₛ ⟩
    cast-arg-ready = cast-↠ {c = dₛ} arg-ready

    prefix-ready :
      L · R —↠[ keep ∷ χsA ]
        (applyTerms χsA F · WRA) ⟨ applyCoercions χsA dₛ ⟩
    prefix-ready = ↠-trans source-head-step cast-arg-ready

    rec =
      separated-dgg-beta-cast-value-shape
        (applyTerms-preserves-Value χsA vF)
        (applyTerms-preserves-No• χsA source-head-no•)
        vWRA
        noWRA
        vV′
        vW′
        F-left⊒T
        T≡V′cd
        pAᶜ
        WRA⊒W′

    χsT , N , ΔLT , ρT ,
      tail-red , ΔT≡ , ρT≡ , N⊒target = rec

    tail-ready :
      (applyTerms χsA F · WRA) ⟨ applyCoercions χsA dₛ ⟩
        —↠[ χsT ]
      N ⟨ applyCoercions χsT (applyCoercions χsA dₛ) ⟩
    tail-ready = cast-↠ {c = applyCoercions χsA dₛ} tail-red

    source-steps :
      L · R —↠[ (keep ∷ χsA) ++ χsT ]
        N ⟨ applyCoercions χsT (applyCoercions χsA dₛ) ⟩
    source-steps = ↠-trans prefix-ready tail-ready

    ΔLT-total≡ :
      ΔLT ≡ applyTyCtxs ((keep ∷ χsA) ++ χsT) ΔL
    ΔLT-total≡ =
      trans ΔT≡
        (trans
          (cong (applyTyCtxs χsT) ΔLA≡)
          (sym (applyTyCtxs-++ χsA χsT ΔL)))

    ρT-total≡ :
      ρT ≡ applyLeftChanges ((keep ∷ χsA) ++ χsT) ρ
    ρT-total≡ =
      trans ρT≡ (sym (applyLeftChanges-++ χsA χsT ρ))

    final⊒ :
      ΔLT ∣ ΔR ∣ ρT ∣ []
        ⊢ N ⟨ applyCoercions χsT (applyCoercions χsA dₛ) ⟩
          ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩
          ∶ applyCoercions ((keep ∷ χsA) ++ χsT) qₒ
          ⦂ applyTys ((keep ∷ χsA) ++ χsT) Bₒ ⊒ _
    final⊒ =
      let
        μN , nᶜ = typed-term-narrowing-coercion N⊒target

        ρT-corr :
          StoreCorr ΔLT ΔR
            (applyLeftChanges χsT (applyLeftChanges χsA ρ))
        ρT-corr =
          subst (StoreCorr ΔLT ΔR)
            ρT≡
            (narrowing-store-corrᶜ {μ = μN} nᶜ)

        qₒ⊒A =
          left-change-coercion-narrowing χsA {μ = tag-or-idᵈ}
            ΔLA≡ ρA-corr qₒ⊒

        qₒ⊒T =
          left-change-coercion-narrowing χsT {μ = tag-or-idᵈ}
            ΔT≡ ρT-corr qₒ⊒A

        qₒ⊒Tρ =
          subst
            (λ ρ₀ →
              tag-or-idᵈ ∣ ΔLT ∣ ΔR ∣ ρ₀
                ⊢ applyCoercions χsT (applyCoercions χsA qₒ)
                  ∶ _ ⊒ _)
            (sym ρT≡)
            qₒ⊒T

        dₛ⊒A =
          left-change-source-coercion-narrowing χsA {μ = ηCast}
            ΔLA≡ ρA-corr dₛ⊒

        dₛ⊒T =
          left-change-source-coercion-narrowing χsT {μ = ηCast}
            ΔT≡ ρT-corr dₛ⊒A

        dₛ⊒Tρ =
          subst
            (λ ρ₀ →
              ηCast ∣ ΔLT ∣ ΔR ∣ ρ₀
                ⊢ applyCoercions χsT (applyCoercions χsA dₛ)
                  ∶ applyTys χsT (applyTys χsA BL)
                  ⊒ applyTys χsT (applyTys χsA Bₒ))
            (sym ρT≡)
            dₛ⊒T
        casted :
          ΔLT ∣ ΔR ∣ ρT ∣ []
            ⊢ N ⟨ applyCoercions χsT (applyCoercions χsA dₛ) ⟩
              ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩
              ∶ applyCoercions χsT (applyCoercions χsA qₒ)
              ⦂ applyTys χsT (applyTys χsA Bₒ) ⊒ _
        casted =
          cast-⊒ᵗ {μ = μN} {η = ηCast}
            qₒ⊒Tρ
            nᶜ
            dₛ⊒Tρ
            {! source-cast-tail-composition !}
            N⊒target
      in
      subst
        (λ qT →
          ΔLT ∣ ΔR ∣ ρT ∣ []
            ⊢ N ⟨ applyCoercions χsT (applyCoercions χsA dₛ) ⟩
              ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ qT
              ⦂ applyTys ((keep ∷ χsA) ++ χsT) Bₒ ⊒ _)
        (sym (applyCoercions-++ χsA χsT qₒ))
        (subst
          (λ BT →
            ΔLT ∣ ΔR ∣ ρT ∣ []
              ⊢ N ⟨ applyCoercions χsT (applyCoercions χsA dₛ) ⟩
                ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩
                ∶ applyCoercions χsT (applyCoercions χsA qₒ)
                ⦂ BT ⊒ _)
          (sym (applyTys-++ χsA χsT Bₒ))
          casted)
  in
  (keep ∷ χsA) ++ χsT ,
  N ⟨ applyCoercions χsT (applyCoercions χsA dₛ) ⟩ ,
  ΔLT ,
  ρT ,
  source-steps ,
  ΔLT-total≡ ,
  ρT-total≡ ,
  final⊒
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d}
    vL noL vR noR vV′ vW′
    sourceCast@(cast-⊒ᵗ {M = F₀} {s = s} qᶜ rᶜ s⊒ _ F₀⊒T)
    T≡V′cd p-domainᶜ R⊒W′
    with canonical-⇒ vL (typed-term-narrowing-source-typingᶜ sourceCast)
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d}
    vL noL vR noR vV′ vW′
    sourceCast@(cast-⊒ᵗ {M = F₀} {s = s} qᶜ rᶜ s⊒ _ F₀⊒T)
    T≡V′cd p-domainᶜ R⊒W′
    | fv-ƛ ()
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d}
    vL noL vR noR vV′ vW′
    sourceCast@(cast-⊒ᵗ {M = F₀} {s = id A} qᶜ rᶜ s⊒ _ F₀⊒T)
    T≡V′cd p-domainᶜ R⊒W′
    | fv-↦ vF ()
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d}
    vL noL vR noR vV′ vW′
    sourceCast@(cast-⊒ᵗ {M = F₀} {s = s₁ ︔ s₂} qᶜ rᶜ s⊒ _ F₀⊒T)
    T≡V′cd p-domainᶜ R⊒W′
    | fv-↦ vF ()
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d}
    vL noL vR noR vV′ vW′
    sourceCast@(cast-⊒ᵗ {M = F₀} {s = `∀ s} qᶜ rᶜ s⊒ _ F₀⊒T)
    T≡V′cd p-domainᶜ R⊒W′
    | fv-↦ vF ()
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d}
    vL noL vR noR vV′ vW′
    sourceCast@(cast-⊒ᵗ {M = F₀} {s = G !} qᶜ rᶜ s⊒ _ F₀⊒T)
    T≡V′cd p-domainᶜ R⊒W′
    | fv-↦ vF ()
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d}
    vL noL vR noR vV′ vW′
    sourceCast@(cast-⊒ᵗ {M = F₀} {s = G ？} qᶜ rᶜ s⊒ _ F₀⊒T)
    T≡V′cd p-domainᶜ R⊒W′
    | fv-↦ vF ()
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d}
    vL noL vR noR vV′ vW′
    sourceCast@(cast-⊒ᵗ {M = F₀} {s = seal A α} qᶜ rᶜ s⊒ _ F₀⊒T)
    T≡V′cd p-domainᶜ R⊒W′
    | fv-↦ vF ()
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d}
    vL noL vR noR vV′ vW′
    sourceCast@(cast-⊒ᵗ {M = F₀} {s = unseal α A} qᶜ rᶜ s⊒ _ F₀⊒T)
    T≡V′cd p-domainᶜ R⊒W′
    | fv-↦ vF ()
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d}
    vL noL vR noR vV′ vW′
    sourceCast@(cast-⊒ᵗ {M = F₀} {s = gen A s} qᶜ rᶜ s⊒ _ F₀⊒T)
    T≡V′cd p-domainᶜ R⊒W′
    | fv-↦ vF ()
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d}
    vL noL vR noR vV′ vW′
    sourceCast@(cast-⊒ᵗ {M = F₀} {s = inst A s} qᶜ rᶜ s⊒ _ F₀⊒T)
    T≡V′cd p-domainᶜ R⊒W′
    | fv-↦ vF ()
separated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d}
    vL noL vR noR vV′ vW′
    sourceCast@(cast-⊒ᵗ {M = F₀} {s = s₁ ↦ s₂} qᶜ rᶜ s⊒ _ F₀⊒T)
    T≡V′cd p-domainᶜ R⊒W′
    | fv-↦ vF L≡Fcd =
  {! separated-dgg-beta-cast-source-minus-general-fun-cast !}

separated-dgg-beta-cast-value :
  ∀ {ΔL ΔR ρ L R V′ W′ c d pᵈ p q A A′ B B′} →
  Value L →
  No• L →
  Value R →
  No• R →
  Value V′ →
  Value W′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ V′ ⟨ c ↦ d ⟩ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ⊢ pᵈ ∶ᶜ A ⊒ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ R ⊒ W′ ∶ pᵈ ⦂ A ⊒ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    (C ≡ applyTys χs B) ×
    (D ≡ B′) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ r ⦂ C ⊒ D
separated-dgg-beta-cast-value
    vL noL vR noR vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′ =
  let
    χs , N , ΔL′ , ρ′ ,
      red , ΔL′≡ , ρ′≡ , N⊒target =
      separated-dgg-beta-cast-value-shape
        vL noL vR noR vV′ vW′ L⊒V′cd refl p-domainᶜ R⊒W′
  in
  χs ,
  N ,
  ΔL′ ,
  ρ′ ,
  _ ,
  _ ,
  _ ,
  red ,
  ΔL′≡ ,
  ρ′≡ ,
  refl ,
  refl ,
  N⊒target

separated-dgg-beta-cast-left-first :
  ∀ {ΔL ΔR ρ L R V′ W′ c d pᵈ p q A A′ B B′} →
  RuntimeOK L →
  RuntimeOK R →
  No• R →
  Value V′ →
  Value W′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ V′ ⟨ c ↦ d ⟩ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ⊢ pᵈ ∶ᶜ A ⊒ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ R ⊒ W′ ∶ pᵈ ⦂ A ⊒ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    (C ≡ applyTys χs B) ×
    (D ≡ B′) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ r ⦂ C ⊒ D
separated-dgg-beta-cast-left-first {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {V′ = V′} {W′ = W′} {c = c} {d = d}
    {pᵈ = pᵈ} {p = p} {q = q} {A = A} {A′ = A′}
    {B = B} {B′ = B′}
    okL okR noR-ready vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′ =
  let
    χsL , WL , ΔL₁ ,
      vWL , noWL , L↠WL , ΔL₁≡ , ρL-corr ,
      leftL≡ , rightL≡ , p₁ᶜ , WL⊒V′cdraw =
      catchup-lemmaˡ
        okL
        (vV′ ⟨ c ↦ d ⟩)
        L⊒V′cd

    WL⊒V′cd :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
        ⊢ WL ⊒ V′ ⟨ c ↦ d ⟩
          ∶ applyCoercions χsL p ↦ applyCoercions χsL q
          ⦂ applyTys χsL A ⇒ applyTys χsL B ⊒ A′ ⇒ B′
    WL⊒V′cd =
      subst
        (λ pc →
          ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
            ⊢ WL ⊒ V′ ⟨ c ↦ d ⟩ ∶ pc
              ⦂ applyTys χsL A ⇒ applyTys χsL B ⊒ A′ ⇒ B′)
        (applyCoercions-↦ χsL p q)
        (subst
          (λ C →
            ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
              ⊢ WL ⊒ V′ ⟨ c ↦ d ⟩
                ∶ applyCoercions χsL (p ↦ q) ⦂ C ⊒ A′ ⇒ B′)
          (applyTys-⇒ χsL A B)
          WL⊒V′cdraw)

    R⊒W′L =
      advance-left-term-narrowing χsL ΔL₁≡ ρL-corr R⊒W′

    χsR , WR , ΔL₂ ,
      vWR , noWR , R↠WR , ΔL₂≡ , ρR-corr ,
      leftR≡ , rightR≡ , p₂ᶜ , WR⊒W′ =
      catchup-lemmaˡ
        (applyTerms-preserves-RuntimeOK χsL okR)
        vW′
        R⊒W′L

    WLF⊒V′cd =
      advance-left-function-term-narrowing χsR ΔL₂≡ ρR-corr
        WL⊒V′cd

    left-ready :
      L · R —↠[ χsL ] WL · applyTerms χsL R
    left-ready = ·₁-↠ noR-ready L↠WL

    right-ready :
      WL · applyTerms χsL R —↠[ χsR ] applyTerms χsR WL · WR
    right-ready = ·₂-↠ vWL noWL R↠WR

    tail :
      ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
        (applyTerms χsR WL · WR —↠[ χs ] N) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL₂) ×
        (ρ′ ≡
          applyLeftChanges χs (applyLeftChanges χsR
            (applyLeftChanges χsL ρ))) ×
        (C ≡ applyTys χs (applyTys χsR (applyTys χsL B))) ×
        (D ≡ B′) ×
        ΔL′ ∣ ΔR ∣ ρ′ ∣ []
          ⊢ N ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ r ⦂ C ⊒ D
    tail =
      separated-dgg-beta-cast-value
        (applyTerms-preserves-Value χsR vWL)
        (applyTerms-preserves-No• χsR noWL)
        vWR
        noWR
        vV′
        vW′
        WLF⊒V′cd
        p₂ᶜ
        WR⊒W′
  in
  let
    χsT , N , ΔL′ , ρ′ , C , D , r ,
      tail-red , ΔT≡ , ρT≡ , C≡ᵀ , D≡ᵀ , N⊒target = tail

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
      C ≡ applyTys ((χsL ++ χsR) ++ χsT) B
    C≡ =
      trans C≡ᵀ
        (sym
          (trans
            (applyTys-++ (χsL ++ χsR) χsT B)
            (cong (applyTys χsT) (applyTys-++ χsL χsR B))))
  in
  (χsL ++ χsR) ++ χsT ,
  N ,
  ΔL′ ,
  ρ′ ,
  C ,
  D ,
  r ,
  source-steps ,
  ΔL′≡ ,
  ρ′≡ ,
  C≡ ,
  D≡ᵀ ,
  N⊒target

separated-dgg-beta-cast-right-first :
  ∀ {ΔL ΔR ρ L R V′ W′ c d pᵈ p q A A′ B B′} →
  Value L →
  No• L →
  RuntimeOK R →
  Value V′ →
  Value W′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ V′ ⟨ c ↦ d ⟩ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ⊢ pᵈ ∶ᶜ A ⊒ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ R ⊒ W′ ∶ pᵈ ⦂ A ⊒ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    (C ≡ applyTys χs B) ×
    (D ≡ B′) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ r ⦂ C ⊒ D
separated-dgg-beta-cast-right-first {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {V′ = V′} {W′ = W′} {c = c} {d = d}
    {pᵈ = pᵈ} {p = p} {q = q} {A = A} {A′ = A′}
    {B = B} {B′ = B′}
    vL noL okR vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′ =
  let
    χsR , WR , ΔL₁ ,
      vWR , noWR , R↠WR , ΔL₁≡ , ρR-corr ,
      leftR≡ , rightR≡ , p₁ᶜ , WR⊒W′ =
      catchup-lemmaˡ
        okR
        vW′
        R⊒W′

    LF⊒V′cd =
      advance-left-function-term-narrowing χsR ΔL₁≡ ρR-corr L⊒V′cd

    ready :
      L · R —↠[ χsR ] applyTerms χsR L · WR
    ready = ·₂-↠ vL noL R↠WR

    tail :
      ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
        (applyTerms χsR L · WR —↠[ χs ] N) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL₁) ×
        (ρ′ ≡ applyLeftChanges χs (applyLeftChanges χsR ρ)) ×
        (C ≡ applyTys χs (applyTys χsR B)) ×
        (D ≡ B′) ×
        ΔL′ ∣ ΔR ∣ ρ′ ∣ []
          ⊢ N ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ r ⦂ C ⊒ D
    tail =
      separated-dgg-beta-cast-value
        (applyTerms-preserves-Value χsR vL)
        (applyTerms-preserves-No• χsR noL)
        vWR
        noWR
        vV′
        vW′
        LF⊒V′cd
        p₁ᶜ
        WR⊒W′
  in
  let
    χsT , N , ΔL′ , ρ′ , C , D , r ,
      tail-red , ΔT≡ , ρT≡ , C≡ᵀ , D≡ᵀ , N⊒target = tail

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

    C≡ :
      C ≡ applyTys (χsR ++ χsT) B
    C≡ = trans C≡ᵀ (sym (applyTys-++ χsR χsT B))
  in
  χsR ++ χsT ,
  N ,
  ΔL′ ,
  ρ′ ,
  C ,
  D ,
  r ,
  source-steps ,
  ΔL′≡ ,
  ρ′≡ ,
  C≡ ,
  D≡ᵀ ,
  N⊒target

separated-dgg-beta-cast :
  ∀ {ΔL ΔR ρ L R V′ W′ c d pᵈ p q A A′ B B′} →
  RuntimeOK (L · R) →
  Value V′ →
  Value W′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ V′ ⟨ c ↦ d ⟩ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ⊢ pᵈ ∶ᶜ A ⊒ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ R ⊒ W′ ∶ pᵈ ⦂ A ⊒ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    (C ≡ applyTys χs B) ×
    (D ≡ B′) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ r ⦂ C ⊒ D
separated-dgg-beta-cast okLR@(ok-no (no•-· noL noR))
    vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′ =
  separated-dgg-beta-cast-left-first
    (ok-no noL) (ok-no noR) noR vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′
separated-dgg-beta-cast okLR@(ok-·₁ okL noR)
    vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′ =
  separated-dgg-beta-cast-left-first
    okL (ok-no noR) noR vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′
separated-dgg-beta-cast okLR@(ok-·₂ vL noL (ok-no noR))
    vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′ =
  separated-dgg-beta-cast-left-first
    (ok-no noL) (ok-no noR) noR vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′
separated-dgg-beta-cast (ok-·₂ vL noL (ok-• vV noV))
    vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′ =
  separated-dgg-beta-cast-right-first
    vL noL (ok-• vV noV) vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′
separated-dgg-beta-cast (ok-·₂ vL noL (ok-·₁ okR₁ noR₂))
    vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′ =
  separated-dgg-beta-cast-right-first
    vL noL (ok-·₁ okR₁ noR₂) vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′
separated-dgg-beta-cast (ok-·₂ vL noL (ok-·₂ vR₁ noR₁ okR₂))
    vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′ =
  separated-dgg-beta-cast-right-first
    vL noL (ok-·₂ vR₁ noR₁ okR₂) vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′
separated-dgg-beta-cast (ok-·₂ vL noL (ok-ν okR))
    vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′ =
  separated-dgg-beta-cast-right-first
    vL noL (ok-ν okR) vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′
separated-dgg-beta-cast (ok-·₂ vL noL (ok-⊕₁ okR₁ noR₂))
    vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′ =
  separated-dgg-beta-cast-right-first
    vL noL (ok-⊕₁ okR₁ noR₂) vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′
separated-dgg-beta-cast (ok-·₂ vL noL (ok-⊕₂ vR₁ noR₁ okR₂))
    vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′ =
  separated-dgg-beta-cast-right-first
    vL noL (ok-⊕₂ vR₁ noR₁ okR₂) vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′
separated-dgg-beta-cast (ok-·₂ vL noL (ok-⟨⟩ okR))
    vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′ =
  separated-dgg-beta-cast-right-first
    vL noL (ok-⟨⟩ okR) vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′
