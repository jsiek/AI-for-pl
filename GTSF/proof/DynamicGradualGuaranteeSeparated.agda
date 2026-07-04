{-# OPTIONS --allow-unsolved-metas #-}

module proof.DynamicGradualGuaranteeSeparated where

-- File Charter:
--   * Main recursive separated-store dynamic gradual guarantee skeleton.
--   * Delegates beta, beta-cast, and primitive delta packaging to focused
--     helper modules so this file stays centered on the induction cases.
--   * Keeps the target term/store unchanged while left-side catchup advances
--     the source term through `SealCorr`.

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
open import proof.DGGBetaSeparated using (separated-dgg-beta)
open import proof.DGGBetaCastSeparated using (separated-dgg-beta-cast)
open import proof.DGGDeltaSeparated using
  ( separated-⊕-δ-left-first
  ; separated-⊕-δ-right-first
  )

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
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R}
    okM qᶜ
    app@(·⊒·ᵗ p↦qᶜ L⊒L′ R⊒R′)
    (pure-step (β-↦ {V = V′} {W = W′} {p = c′} {q = d′} vV′ vW′)) =
  let
    rec =
      separated-dgg-beta-cast
        okM
        vV′
        vW′
        L⊒L′
        (fun-narrow-domain-dual-typingᶜ p↦qᶜ)
        R⊒R′
  in
  let
    χs , N , ΔL′ , ρ′ , C , D , r ,
      source-steps , ΔL′≡ , ρ′≡ , N⊒target = rec
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
  N⊒target
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R}
    okM qᶜ
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
  ⊒blameᵗ (typed-term-narrowing-source-typingᶜ app) qᶜ
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R}
    okM qᶜ
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
  ⊒blameᵗ (typed-term-narrowing-source-typingᶜ app) qᶜ
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R} {M′ = L′ · R′} {χ′ = χ′}
    (ok-no (no•-· noL noR)) qᶜ
    (·⊒·ᵗ p↦q-wholeᶜ L⊒L′ R⊒R′)
    (ξ-·₁ {L′ = S′} L′→N′ shiftR′) =
  let
    rec =
      dynamicGradualGuarantee
        (ok-no noL)
        p↦q-wholeᶜ
        L⊒L′
        L′→N′

    χs , N , ΔL′ , ΔR′ , ρ′ ,
      C , D , r ,
      L↠N , ΔL′≡ , ΔR′≡ , ρ′≡ , N⊒N′ = rec

    framed⊒ :
      ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
        ⊢ N · applyTerms χs R ⊒ S′ · applyTerm χ′ R′ ∶ _ ⦂ _ ⊒ _
    framed⊒ =
      let
        N⊒S′-fun :
          ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
            ⊢ N ⊒ S′ ∶ _ ↦ _ ⦂ _ ⇒ _ ⊒ _ ⇒ _
        N⊒S′-fun =
          let
            ih : ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ N ⊒ S′ ∶ r ⦂ C ⊒ D
            ih = N⊒N′
          in
          {! ξ-·₁-IH-result-function !}

        p↦q′ :
          ΔL′ ∣ ΔR′ ∣ ρ′ ⊢ _ ↦ _ ∶ᶜ _ ⇒ _ ⊒ _ ⇒ _
        p↦q′ = {! ξ-·₁-updated-function-coercion !}

        R⊒R′′ :
          ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
            ⊢ applyTerms χs R ⊒ applyTerm χ′ R′
              ∶ fun-narrow-domain-dualᶜ p↦q′ ⦂ _ ⊒ _
        R⊒R′′ = {! ξ-·₁-updated-argument-narrowing !}
      in
      ·⊒·ᵗ p↦q′ N⊒S′-fun R⊒R′′

    obligation :
      ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (L · R —↠[ χs ] N) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL) ×
        (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
        (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
        ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
          ⊢ N ⊒ S′ · applyTerm χ′ R′ ∶ r ⦂ C ⊒ D
    obligation =
      χs ,
      N · applyTerms χs R ,
      ΔL′ ,
      ΔR′ ,
      ρ′ ,
      _ ,
      _ ,
      _ ,
      ·₁-↠ noR L↠N ,
      ΔL′≡ ,
      ΔR′≡ ,
      ρ′≡ ,
      framed⊒
  in
  obligation
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R} {M′ = L′ · R′} {χ′ = χ′}
    (ok-·₁ okL noR) qᶜ
    (·⊒·ᵗ p↦q-wholeᶜ L⊒L′ R⊒R′)
    (ξ-·₁ {L′ = S′} L′→N′ shiftR′) =
  let
    rec =
      dynamicGradualGuarantee
        okL
        p↦q-wholeᶜ
        L⊒L′
        L′→N′

    χs , N , ΔL′ , ΔR′ , ρ′ ,
      C , D , r ,
      L↠N , ΔL′≡ , ΔR′≡ , ρ′≡ , N⊒N′ = rec

    framed⊒ :
      ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
        ⊢ N · applyTerms χs R ⊒ S′ · applyTerm χ′ R′ ∶ _ ⦂ _ ⊒ _
    framed⊒ =
      let
        N⊒S′-fun :
          ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
            ⊢ N ⊒ S′ ∶ _ ↦ _ ⦂ _ ⇒ _ ⊒ _ ⇒ _
        N⊒S′-fun =
          let
            ih : ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ N ⊒ S′ ∶ r ⦂ C ⊒ D
            ih = N⊒N′
          in
          {! ξ-·₁-IH-result-function !}

        p↦q′ :
          ΔL′ ∣ ΔR′ ∣ ρ′ ⊢ _ ↦ _ ∶ᶜ _ ⇒ _ ⊒ _ ⇒ _
        p↦q′ = {! ξ-·₁-updated-function-coercion !}

        R⊒R′′ :
          ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
            ⊢ applyTerms χs R ⊒ applyTerm χ′ R′
              ∶ fun-narrow-domain-dualᶜ p↦q′ ⦂ _ ⊒ _
        R⊒R′′ = {! ξ-·₁-updated-argument-narrowing !}
      in
      ·⊒·ᵗ p↦q′ N⊒S′-fun R⊒R′′

    obligation :
      ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (L · R —↠[ χs ] N) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL) ×
        (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
        (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
        ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
          ⊢ N ⊒ S′ · applyTerm χ′ R′ ∶ r ⦂ C ⊒ D
    obligation =
      χs ,
      N · applyTerms χs R ,
      ΔL′ ,
      ΔR′ ,
      ρ′ ,
      _ ,
      _ ,
      _ ,
      ·₁-↠ noR L↠N ,
      ΔL′≡ ,
      ΔR′≡ ,
      ρ′≡ ,
      framed⊒
  in
  obligation
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R} {M′ = L′ · R′} {χ′ = χ′}
    (ok-·₂ vL noL okR) qᶜ
    app@(·⊒·ᵗ p↦q-wholeᶜ L⊒L′ R⊒R′)
    (ξ-·₁ {L′ = S′} L′→S′ shiftR′) =
  let
    relation-obligation :
      ΔL ∣ applyTyCtx χ′ ΔR ∣ applyRightChange χ′ ρ ∣ []
        ⊢ L · R ⊒ S′ · applyTerm χ′ R′ ∶ _ ⦂ _ ⊒ _
    relation-obligation =
      let
        source-relation :
          ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L · R ⊒ L′ · R′
            ∶ _ ⦂ _ ⊒ _
        source-relation = app

        target-left-step : L′ —→[ χ′ ] S′
        target-left-step = L′→S′

        target-right-shift : Shiftable χ′ R′
        target-right-shift = shiftR′

        obligation :
          ΔL ∣ applyTyCtx χ′ ΔR ∣ applyRightChange χ′ ρ ∣ []
            ⊢ L · R ⊒ S′ · applyTerm χ′ R′ ∶ _ ⦂ _ ⊒ _
        obligation = {! ξ-·₁-source-left-already-value-relation !}
      in
      obligation

    obligation :
      ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (L · R —↠[ χs ] N) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL) ×
        (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
        (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
        ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
          ⊢ N ⊒ S′ · applyTerm χ′ R′ ∶ r ⦂ C ⊒ D
    obligation =
      [] ,
      L · R ,
      ΔL ,
      applyTyCtx χ′ ΔR ,
      applyRightChange χ′ ρ ,
      _ ,
      _ ,
      _ ,
      ↠-refl ,
      refl ,
      refl ,
      refl ,
      relation-obligation
  in
  obligation
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R} {M′ = L′ · R′} {χ′ = χ′}
    (ok-no (no•-· noL noR)) qᶜ
    (·⊒·ᵗ {p = p} {q = q} {A = A} {A′ = A′}
      {B = B} {B′ = B′} p↦q-wholeᶜ L⊒L′ R⊒R′)
    (ξ-·₂ {M′ = S′} vL′ shiftL′ R′→S′) =
  let
    χsL , WL , ΔL₁ ,
      vWL , noWL , L↠WL , ΔL₁≡ , ρL-corr ,
      leftL≡ , rightL≡ , pLᶜ , WL⊒L′raw =
      catchup-lemmaˡ
        (ok-no noL)
        vL′
        L⊒L′

    WL⊒L′ :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
        ⊢ WL ⊒ L′
          ∶ applyCoercions χsL p ↦ applyCoercions χsL q
          ⦂ applyTys χsL A ⇒ applyTys χsL B ⊒ A′ ⇒ B′
    WL⊒L′ =
      subst
        (λ c →
          ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
            ⊢ WL ⊒ L′ ∶ c
              ⦂ applyTys χsL A ⇒ applyTys χsL B ⊒ A′ ⇒ B′)
        (applyCoercions-↦ χsL p q)
        (subst
          (λ C →
            ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
              ⊢ WL ⊒ L′ ∶ applyCoercions χsL (p ↦ q)
                ⦂ C ⊒ A′ ⇒ B′)
          (applyTys-⇒ χsL A B)
          WL⊒L′raw)

    R⊒R′L :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
        ⊢ applyTerms χsL R ⊒ R′
          ∶ applyCoercions χsL (fun-narrow-domain-dualᶜ p↦q-wholeᶜ)
          ⦂ applyTys χsL A ⊒ A′
    R⊒R′L =
      advance-left-term-narrowing χsL ΔL₁≡ ρL-corr R⊒R′

    p-domain-Lᶜ :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ
        ⊢ applyCoercions χsL (fun-narrow-domain-dualᶜ p↦q-wholeᶜ)
          ∶ᶜ applyTys χsL A ⊒ A′
    p-domain-Lᶜ =
      left-change-coercion-narrowing
        χsL
        ΔL₁≡
        ρL-corr
        (fun-narrow-domain-dual-typingᶜ p↦q-wholeᶜ)

    rec =
      dynamicGradualGuarantee
        (applyTerms-preserves-RuntimeOK χsL (ok-no noR))
        p-domain-Lᶜ
        R⊒R′L
        R′→S′

    χsR , P , ΔL₂ , ΔR′ , ρ′ ,
      C , D , r ,
      R↠P , ΔL₂≡ , ΔR′≡ , ρ′≡ , P⊒S′ = rec

    source-left :
      L · R —↠[ χsL ] WL · applyTerms χsL R
    source-left = ·₁-↠ noR L↠WL

    source-right :
      WL · applyTerms χsL R —↠[ χsR ] applyTerms χsR WL · P
    source-right = ·₂-↠ vWL noWL R↠P

    source-steps :
      L · R —↠[ χsL ++ χsR ] applyTerms χsR WL · P
    source-steps = ↠-trans source-left source-right

    ΔL₂≡total :
      ΔL₂ ≡ applyTyCtxs (χsL ++ χsR) ΔL
    ΔL₂≡total =
      trans ΔL₂≡
        (trans
          (cong (applyTyCtxs χsR) ΔL₁≡)
          (sym (applyTyCtxs-++ χsL χsR ΔL)))

    ρ′≡total :
      ρ′ ≡ applyRightChange χ′ (applyLeftChanges (χsL ++ χsR) ρ)
    ρ′≡total =
      trans ρ′≡
        (cong (applyRightChange χ′)
          (sym (applyLeftChanges-++ χsL χsR ρ)))

    framed⊒ :
      ΔL₂ ∣ ΔR′ ∣ ρ′ ∣ []
        ⊢ applyTerms χsR WL · P ⊒ applyTerm χ′ L′ · S′
          ∶ _ ⦂ _ ⊒ _
    framed⊒ =
      let
        ih : ΔL₂ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ P ⊒ S′ ∶ r ⦂ C ⊒ D
        ih = P⊒S′

        function-before-right-change :
          ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
            ⊢ WL ⊒ L′
              ∶ applyCoercions χsL p ↦ applyCoercions χsL q
              ⦂ applyTys χsL A ⇒ applyTys χsL B ⊒ A′ ⇒ B′
        function-before-right-change = WL⊒L′

        obligation :
          ΔL₂ ∣ ΔR′ ∣ ρ′ ∣ []
            ⊢ applyTerms χsR WL · P ⊒ applyTerm χ′ L′ · S′
              ∶ _ ⦂ _ ⊒ _
        obligation = {! ξ-·₂-source-left-not-yet-value-frame !}
      in
      obligation

    obligation :
      ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (L · R —↠[ χs ] N) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL) ×
        (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
        (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
        ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
          ⊢ N ⊒ applyTerm χ′ L′ · S′ ∶ r ⦂ C ⊒ D
    obligation =
      χsL ++ χsR ,
      applyTerms χsR WL · P ,
      ΔL₂ ,
      ΔR′ ,
      ρ′ ,
      _ ,
      _ ,
      _ ,
      source-steps ,
      ΔL₂≡total ,
      ΔR′≡ ,
      ρ′≡total ,
      framed⊒
  in
  obligation
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R} {M′ = L′ · R′} {χ′ = χ′}
    (ok-·₁ okL noR) qᶜ
    (·⊒·ᵗ {p = p} {q = q} {A = A} {A′ = A′}
      {B = B} {B′ = B′} p↦q-wholeᶜ L⊒L′ R⊒R′)
    (ξ-·₂ {M′ = S′} vL′ shiftL′ R′→S′) =
  let
    χsL , WL , ΔL₁ ,
      vWL , noWL , L↠WL , ΔL₁≡ , ρL-corr ,
      leftL≡ , rightL≡ , pLᶜ , WL⊒L′raw =
      catchup-lemmaˡ
        okL
        vL′
        L⊒L′

    WL⊒L′ :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
        ⊢ WL ⊒ L′
          ∶ applyCoercions χsL p ↦ applyCoercions χsL q
          ⦂ applyTys χsL A ⇒ applyTys χsL B ⊒ A′ ⇒ B′
    WL⊒L′ =
      subst
        (λ c →
          ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
            ⊢ WL ⊒ L′ ∶ c
              ⦂ applyTys χsL A ⇒ applyTys χsL B ⊒ A′ ⇒ B′)
        (applyCoercions-↦ χsL p q)
        (subst
          (λ C →
            ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
              ⊢ WL ⊒ L′ ∶ applyCoercions χsL (p ↦ q)
                ⦂ C ⊒ A′ ⇒ B′)
          (applyTys-⇒ χsL A B)
          WL⊒L′raw)

    R⊒R′L :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
        ⊢ applyTerms χsL R ⊒ R′
          ∶ applyCoercions χsL (fun-narrow-domain-dualᶜ p↦q-wholeᶜ)
          ⦂ applyTys χsL A ⊒ A′
    R⊒R′L =
      advance-left-term-narrowing χsL ΔL₁≡ ρL-corr R⊒R′

    p-domain-Lᶜ :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ
        ⊢ applyCoercions χsL (fun-narrow-domain-dualᶜ p↦q-wholeᶜ)
          ∶ᶜ applyTys χsL A ⊒ A′
    p-domain-Lᶜ =
      left-change-coercion-narrowing
        χsL
        ΔL₁≡
        ρL-corr
        (fun-narrow-domain-dual-typingᶜ p↦q-wholeᶜ)

    rec =
      dynamicGradualGuarantee
        (applyTerms-preserves-RuntimeOK χsL (ok-no noR))
        p-domain-Lᶜ
        R⊒R′L
        R′→S′

    χsR , P , ΔL₂ , ΔR′ , ρ′ ,
      C , D , r ,
      R↠P , ΔL₂≡ , ΔR′≡ , ρ′≡ , P⊒S′ = rec

    source-left :
      L · R —↠[ χsL ] WL · applyTerms χsL R
    source-left = ·₁-↠ noR L↠WL

    source-right :
      WL · applyTerms χsL R —↠[ χsR ] applyTerms χsR WL · P
    source-right = ·₂-↠ vWL noWL R↠P

    source-steps :
      L · R —↠[ χsL ++ χsR ] applyTerms χsR WL · P
    source-steps = ↠-trans source-left source-right

    ΔL₂≡total :
      ΔL₂ ≡ applyTyCtxs (χsL ++ χsR) ΔL
    ΔL₂≡total =
      trans ΔL₂≡
        (trans
          (cong (applyTyCtxs χsR) ΔL₁≡)
          (sym (applyTyCtxs-++ χsL χsR ΔL)))

    ρ′≡total :
      ρ′ ≡ applyRightChange χ′ (applyLeftChanges (χsL ++ χsR) ρ)
    ρ′≡total =
      trans ρ′≡
        (cong (applyRightChange χ′)
          (sym (applyLeftChanges-++ χsL χsR ρ)))

    framed⊒ :
      ΔL₂ ∣ ΔR′ ∣ ρ′ ∣ []
        ⊢ applyTerms χsR WL · P ⊒ applyTerm χ′ L′ · S′
          ∶ _ ⦂ _ ⊒ _
    framed⊒ =
      let
        ih : ΔL₂ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ P ⊒ S′ ∶ r ⦂ C ⊒ D
        ih = P⊒S′

        function-before-right-change :
          ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
            ⊢ WL ⊒ L′
              ∶ applyCoercions χsL p ↦ applyCoercions χsL q
              ⦂ applyTys χsL A ⇒ applyTys χsL B ⊒ A′ ⇒ B′
        function-before-right-change = WL⊒L′

        obligation :
          ΔL₂ ∣ ΔR′ ∣ ρ′ ∣ []
            ⊢ applyTerms χsR WL · P ⊒ applyTerm χ′ L′ · S′
              ∶ _ ⦂ _ ⊒ _
        obligation = {! ξ-·₂-source-left-still-reducing-frame !}
      in
      obligation

    obligation :
      ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (L · R —↠[ χs ] N) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL) ×
        (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
        (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
        ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
          ⊢ N ⊒ applyTerm χ′ L′ · S′ ∶ r ⦂ C ⊒ D
    obligation =
      χsL ++ χsR ,
      applyTerms χsR WL · P ,
      ΔL₂ ,
      ΔR′ ,
      ρ′ ,
      _ ,
      _ ,
      _ ,
      source-steps ,
      ΔL₂≡total ,
      ΔR′≡ ,
      ρ′≡total ,
      framed⊒
  in
  obligation
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = L · R} {M′ = L′ · R′} {N′ = T′} {χ′ = χ′}
    (ok-·₂ vL noL okR) qᶜ
    (·⊒·ᵗ p↦q-wholeᶜ L⊒L′ R⊒R′)
    (ξ-·₂ {M′ = S′} vL′ shiftL′ R′→N′) =
  let
    runtimeR : RuntimeOK R
    runtimeR = okR

    rec =
      dynamicGradualGuarantee
        runtimeR
        (fun-narrow-domain-dual-typingᶜ p↦q-wholeᶜ)
        R⊒R′
        R′→N′

    χs , N , ΔL′ , ΔR′ , ρ′ ,
      C , D , r ,
      R↠N , ΔL′≡ , ΔR′≡ , ρ′≡ , N⊒N′ = rec

    framed⊒ :
      ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
        ⊢ applyTerms χs L · N ⊒ applyTerm χ′ L′ · S′
          ∶ _ ⦂ _ ⊒ _
    framed⊒ =
      let
        p↦q′ :
          ΔL′ ∣ ΔR′ ∣ ρ′ ⊢ _ ↦ _ ∶ᶜ _ ⇒ _ ⊒ _ ⇒ _
        p↦q′ = {! ξ-·₂-updated-function-coercion !}

        L⊒L′′ :
          ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
            ⊢ applyTerms χs L ⊒ applyTerm χ′ L′
              ∶ _ ↦ _ ⦂ _ ⇒ _ ⊒ _ ⇒ _
        L⊒L′′ = {! ξ-·₂-updated-function-narrowing !}

        N⊒S′-arg :
          ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
            ⊢ N ⊒ S′ ∶ fun-narrow-domain-dualᶜ p↦q′ ⦂ _ ⊒ _
        N⊒S′-arg =
          let
            ih : ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ N ⊒ S′ ∶ r ⦂ C ⊒ D
            ih = N⊒N′
          in
          {! ξ-·₂-IH-result-argument !}
      in
      ·⊒·ᵗ p↦q′ L⊒L′′ N⊒S′-arg

    obligation :
      ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (L · R —↠[ χs ] N) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL) ×
        (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
        (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
        ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ N ⊒ T′ ∶ r ⦂ C ⊒ D
    obligation =
      χs ,
      applyTerms χs L · N ,
      ΔL′ ,
      ΔR′ ,
      ρ′ ,
      _ ,
      _ ,
      _ ,
      ·₂-↠ vL noL R↠N ,
      ΔL′≡ ,
      ΔR′≡ ,
      ρ′≡ ,
      framed⊒
  in
  obligation
dynamicGradualGuarantee okM pᶜ
    (Λ⊒Λᵗ allᶜ vV vV′ V⊒V′)
    (pure-step ())
dynamicGradualGuarantee okM pᶜ (κ⊒κᵗ κ qᶜ)
    (pure-step ())
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N}
    (ok-no (no•-⊕ noM noN)) pᶜ
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (pure-step (δ-⊕ {m = m′} {n = n′})) =
  let
    rec =
      separated-⊕-δ-left-first
        (ok-no noM)
        noN
        M⊒M′
        N⊒N′

    χs , P , ΔL′ , ρ′ , C , D , r ,
      source-steps , ΔL′≡ , ρ′≡ , P⊒P′ = rec
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
  P⊒P′
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N}
    (ok-⊕₁ okM noN) pᶜ
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (pure-step (δ-⊕ {m = m′} {n = n′})) =
  let
    rec =
      separated-⊕-δ-left-first
        okM
        noN
        M⊒M′
        N⊒N′

    χs , P , ΔL′ , ρ′ , C , D , r ,
      source-steps , ΔL′≡ , ρ′≡ , P⊒P′ = rec
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
  P⊒P′
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N}
    (ok-⊕₂ vM noM okN) pᶜ
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (pure-step (δ-⊕ {m = m′} {n = n′})) =
  let
    rec =
      separated-⊕-δ-right-first
        vM
        noM
        okN
        M⊒M′
        N⊒N′

    χs , P , ΔL′ , ρ′ , C , D , r ,
      source-steps , ΔL′≡ , ρ′≡ , P⊒P′ = rec
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
  P⊒P′
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N}
    okM pᶜ
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
  ⊒blameᵗ (typed-term-narrowing-source-typingᶜ add) pᶜ
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N}
    okM pᶜ
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
  ⊒blameᵗ (typed-term-narrowing-source-typingᶜ add) pᶜ
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N} {M′ = M′ ⊕[ addℕ ] N′}
    {N′ = P′} {χ′ = χ′}
    (ok-no (no•-⊕ noM noN)) pᶜ
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (ξ-⊕₁ {L′ = S′} M′→P′ shiftN′) =
  let
    rec =
      dynamicGradualGuarantee
        (ok-no noM)
        pᶜ
        M⊒M′
        M′→P′

    χs , P , ΔL′ , ΔR′ , ρ′ ,
      C , D , r ,
      M↠P , ΔL′≡ , ΔR′≡ , ρ′≡ , P⊒P′ = rec

    framed⊒ :
      ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
        ⊢ P ⊕[ addℕ ] applyTerms χs N
          ⊒ S′ ⊕[ addℕ ] applyTerm χ′ N′ ∶ _ ⦂ _ ⊒ _
    framed⊒ =
      let
        pℕ′ :
          ΔL′ ∣ ΔR′ ∣ ρ′ ⊢ id (‵ `ℕ) ∶ᶜ ‵ `ℕ ⊒ ‵ `ℕ
        pℕ′ =
          let μ , p′ᶜ = typed-term-narrowing-coercion P⊒P′ in
          id-ℕ-narrowingᶜ (narrowing-store-corrᶜ p′ᶜ)

        N⊒N′′ :
          ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
            ⊢ applyTerms χs N ⊒ applyTerm χ′ N′
              ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ
        N⊒N′′ = {! ξ-⊕₁-updated-right-narrowing !}

        P⊒P′ℕ :
          ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
            ⊢ P ⊒ S′
              ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ
        P⊒P′ℕ =
          let
            ih : ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ P ⊒ S′ ∶ r ⦂ C ⊒ D
            ih = P⊒P′
          in
          {! ξ-⊕₁-IH-result-nat !}
      in
      ⊕⊒⊕ᵗ pℕ′ P⊒P′ℕ N⊒N′′

    obligation :
      ∃[ χs ] ∃[ P ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (M ⊕[ addℕ ] N —↠[ χs ] P) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL) ×
        (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
        (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
        ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ P ⊒ P′ ∶ r ⦂ C ⊒ D
    obligation =
      χs ,
      P ⊕[ addℕ ] applyTerms χs N ,
      ΔL′ ,
      ΔR′ ,
      ρ′ ,
      _ ,
      _ ,
      _ ,
      ⊕₁-↠ noN M↠P ,
      ΔL′≡ ,
      ΔR′≡ ,
      ρ′≡ ,
      framed⊒
  in
  obligation
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N} {M′ = M′ ⊕[ addℕ ] N′}
    {N′ = P′} {χ′ = χ′}
    (ok-⊕₁ okM noN) pᶜ
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (ξ-⊕₁ {L′ = S′} M′→P′ shiftN′) =
  let
    rec =
      dynamicGradualGuarantee
        okM
        pᶜ
        M⊒M′
        M′→P′

    χs , P , ΔL′ , ΔR′ , ρ′ ,
      C , D , r ,
      M↠P , ΔL′≡ , ΔR′≡ , ρ′≡ , P⊒P′ = rec

    framed⊒ :
      ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
        ⊢ P ⊕[ addℕ ] applyTerms χs N
          ⊒ S′ ⊕[ addℕ ] applyTerm χ′ N′ ∶ _ ⦂ _ ⊒ _
    framed⊒ =
      let
        pℕ′ :
          ΔL′ ∣ ΔR′ ∣ ρ′ ⊢ id (‵ `ℕ) ∶ᶜ ‵ `ℕ ⊒ ‵ `ℕ
        pℕ′ =
          let μ , p′ᶜ = typed-term-narrowing-coercion P⊒P′ in
          id-ℕ-narrowingᶜ (narrowing-store-corrᶜ p′ᶜ)

        N⊒N′′ :
          ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
            ⊢ applyTerms χs N ⊒ applyTerm χ′ N′
              ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ
        N⊒N′′ = {! ξ-⊕₁-updated-right-narrowing !}

        P⊒P′ℕ :
          ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
            ⊢ P ⊒ S′ ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ
        P⊒P′ℕ =
          let
            ih : ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ P ⊒ S′ ∶ r ⦂ C ⊒ D
            ih = P⊒P′
          in
          {! ξ-⊕₁-IH-result-nat !}
      in
      ⊕⊒⊕ᵗ pℕ′ P⊒P′ℕ N⊒N′′

    obligation :
      ∃[ χs ] ∃[ P ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (M ⊕[ addℕ ] N —↠[ χs ] P) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL) ×
        (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
        (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
        ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ P ⊒ P′ ∶ r ⦂ C ⊒ D
    obligation =
      χs ,
      P ⊕[ addℕ ] applyTerms χs N ,
      ΔL′ ,
      ΔR′ ,
      ρ′ ,
      _ ,
      _ ,
      _ ,
      ⊕₁-↠ noN M↠P ,
      ΔL′≡ ,
      ΔR′≡ ,
      ρ′≡ ,
      framed⊒
  in
  obligation
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N} {M′ = M′ ⊕[ addℕ ] N′}
    {χ′ = χ′}
    (ok-⊕₂ vM noM okN) pᶜ
    add@(⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (ξ-⊕₁ {L′ = S′} M′→S′ shiftN′) =
  let
    relation-obligation :
      ΔL ∣ applyTyCtx χ′ ΔR ∣ applyRightChange χ′ ρ ∣ []
        ⊢ M ⊕[ addℕ ] N
          ⊒ S′ ⊕[ addℕ ] applyTerm χ′ N′ ∶ _ ⦂ _ ⊒ _
    relation-obligation =
      let
        source-relation :
          ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊕[ addℕ ] N
            ⊒ M′ ⊕[ addℕ ] N′ ∶ _ ⦂ _ ⊒ _
        source-relation = add

        target-left-step : M′ —→[ χ′ ] S′
        target-left-step = M′→S′

        target-right-shift : Shiftable χ′ N′
        target-right-shift = shiftN′

        obligation :
          ΔL ∣ applyTyCtx χ′ ΔR ∣ applyRightChange χ′ ρ ∣ []
            ⊢ M ⊕[ addℕ ] N
              ⊒ S′ ⊕[ addℕ ] applyTerm χ′ N′ ∶ _ ⦂ _ ⊒ _
        obligation = {! ξ-⊕₁-source-left-already-value-relation !}
      in
      obligation

    obligation :
      ∃[ χs ] ∃[ P ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (M ⊕[ addℕ ] N —↠[ χs ] P) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL) ×
        (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
        (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
        ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
          ⊢ P ⊒ S′ ⊕[ addℕ ] applyTerm χ′ N′ ∶ r ⦂ C ⊒ D
    obligation =
      [] ,
      M ⊕[ addℕ ] N ,
      ΔL ,
      applyTyCtx χ′ ΔR ,
      applyRightChange χ′ ρ ,
      _ ,
      _ ,
      _ ,
      ↠-refl ,
      refl ,
      refl ,
      refl ,
      relation-obligation
  in
  obligation
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N} {M′ = M′ ⊕[ addℕ ] N′}
    {χ′ = χ′}
    (ok-no (no•-⊕ noM noN)) pᶜ
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (ξ-⊕₂ {M′ = S′} vM′ shiftM′ N′→S′) =
  let
    χsM , WM , ΔL₁ ,
      vWM , noWM , M↠WM , ΔL₁≡ , ρM-corr ,
      leftM≡ , rightM≡ , pMᶜ , WM⊒M′ =
      catchup-lemmaˡ
        (ok-no noM)
        vM′
        M⊒M′

    N⊒N′M :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsM ρ ∣ []
        ⊢ applyTerms χsM N ⊒ N′
          ∶ applyCoercions χsM (id (‵ `ℕ))
          ⦂ applyTys χsM (‵ `ℕ) ⊒ ‵ `ℕ
    N⊒N′M =
      advance-left-term-narrowing χsM ΔL₁≡ ρM-corr N⊒N′

    pℕMᶜ :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsM ρ
        ⊢ applyCoercions χsM (id (‵ `ℕ))
          ∶ᶜ applyTys χsM (‵ `ℕ) ⊒ ‵ `ℕ
    pℕMᶜ =
      left-change-coercion-narrowing
        χsM
        ΔL₁≡
        ρM-corr
        pℕᶜ

    rec =
      dynamicGradualGuarantee
        (applyTerms-preserves-RuntimeOK χsM (ok-no noN))
        pℕMᶜ
        N⊒N′M
        N′→S′

    χsN , P , ΔL₂ , ΔR′ , ρ′ ,
      C , D , r ,
      N↠P , ΔL₂≡ , ΔR′≡ , ρ′≡ , P⊒S′ = rec

    source-left :
      M ⊕[ addℕ ] N
        —↠[ χsM ] WM ⊕[ addℕ ] applyTerms χsM N
    source-left = ⊕₁-↠ noN M↠WM

    source-right :
      WM ⊕[ addℕ ] applyTerms χsM N
        —↠[ χsN ] applyTerms χsN WM ⊕[ addℕ ] P
    source-right = ⊕₂-↠ vWM noWM N↠P

    source-steps :
      M ⊕[ addℕ ] N
        —↠[ χsM ++ χsN ] applyTerms χsN WM ⊕[ addℕ ] P
    source-steps = ↠-trans source-left source-right

    ΔL₂≡total :
      ΔL₂ ≡ applyTyCtxs (χsM ++ χsN) ΔL
    ΔL₂≡total =
      trans ΔL₂≡
        (trans
          (cong (applyTyCtxs χsN) ΔL₁≡)
          (sym (applyTyCtxs-++ χsM χsN ΔL)))

    ρ′≡total :
      ρ′ ≡ applyRightChange χ′ (applyLeftChanges (χsM ++ χsN) ρ)
    ρ′≡total =
      trans ρ′≡
        (cong (applyRightChange χ′)
          (sym (applyLeftChanges-++ χsM χsN ρ)))

    framed⊒ :
      ΔL₂ ∣ ΔR′ ∣ ρ′ ∣ []
        ⊢ applyTerms χsN WM ⊕[ addℕ ] P
          ⊒ applyTerm χ′ M′ ⊕[ addℕ ] S′ ∶ _ ⦂ _ ⊒ _
    framed⊒ =
      let
        ih : ΔL₂ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ P ⊒ S′ ∶ r ⦂ C ⊒ D
        ih = P⊒S′

        left-before-right-change :
          ΔL₁ ∣ ΔR ∣ applyLeftChanges χsM ρ ∣ []
            ⊢ WM ⊒ M′
              ∶ applyCoercions χsM (id (‵ `ℕ))
              ⦂ applyTys χsM (‵ `ℕ) ⊒ ‵ `ℕ
        left-before-right-change = WM⊒M′

        obligation :
          ΔL₂ ∣ ΔR′ ∣ ρ′ ∣ []
            ⊢ applyTerms χsN WM ⊕[ addℕ ] P
              ⊒ applyTerm χ′ M′ ⊕[ addℕ ] S′ ∶ _ ⦂ _ ⊒ _
        obligation = {! ξ-⊕₂-source-left-not-yet-value-frame !}
      in
      obligation

    obligation :
      ∃[ χs ] ∃[ P ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (M ⊕[ addℕ ] N —↠[ χs ] P) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL) ×
        (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
        (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
        ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
          ⊢ P ⊒ applyTerm χ′ M′ ⊕[ addℕ ] S′ ∶ r ⦂ C ⊒ D
    obligation =
      χsM ++ χsN ,
      applyTerms χsN WM ⊕[ addℕ ] P ,
      ΔL₂ ,
      ΔR′ ,
      ρ′ ,
      _ ,
      _ ,
      _ ,
      source-steps ,
      ΔL₂≡total ,
      ΔR′≡ ,
      ρ′≡total ,
      framed⊒
  in
  obligation
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N} {M′ = M′ ⊕[ addℕ ] N′}
    {χ′ = χ′}
    (ok-⊕₁ okM noN) pᶜ
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (ξ-⊕₂ {M′ = S′} vM′ shiftM′ N′→S′) =
  let
    χsM , WM , ΔL₁ ,
      vWM , noWM , M↠WM , ΔL₁≡ , ρM-corr ,
      leftM≡ , rightM≡ , pMᶜ , WM⊒M′ =
      catchup-lemmaˡ
        okM
        vM′
        M⊒M′

    N⊒N′M :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsM ρ ∣ []
        ⊢ applyTerms χsM N ⊒ N′
          ∶ applyCoercions χsM (id (‵ `ℕ))
          ⦂ applyTys χsM (‵ `ℕ) ⊒ ‵ `ℕ
    N⊒N′M =
      advance-left-term-narrowing χsM ΔL₁≡ ρM-corr N⊒N′

    pℕMᶜ :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsM ρ
        ⊢ applyCoercions χsM (id (‵ `ℕ))
          ∶ᶜ applyTys χsM (‵ `ℕ) ⊒ ‵ `ℕ
    pℕMᶜ =
      left-change-coercion-narrowing
        χsM
        ΔL₁≡
        ρM-corr
        pℕᶜ

    rec =
      dynamicGradualGuarantee
        (applyTerms-preserves-RuntimeOK χsM (ok-no noN))
        pℕMᶜ
        N⊒N′M
        N′→S′

    χsN , P , ΔL₂ , ΔR′ , ρ′ ,
      C , D , r ,
      N↠P , ΔL₂≡ , ΔR′≡ , ρ′≡ , P⊒S′ = rec

    source-left :
      M ⊕[ addℕ ] N
        —↠[ χsM ] WM ⊕[ addℕ ] applyTerms χsM N
    source-left = ⊕₁-↠ noN M↠WM

    source-right :
      WM ⊕[ addℕ ] applyTerms χsM N
        —↠[ χsN ] applyTerms χsN WM ⊕[ addℕ ] P
    source-right = ⊕₂-↠ vWM noWM N↠P

    source-steps :
      M ⊕[ addℕ ] N
        —↠[ χsM ++ χsN ] applyTerms χsN WM ⊕[ addℕ ] P
    source-steps = ↠-trans source-left source-right

    ΔL₂≡total :
      ΔL₂ ≡ applyTyCtxs (χsM ++ χsN) ΔL
    ΔL₂≡total =
      trans ΔL₂≡
        (trans
          (cong (applyTyCtxs χsN) ΔL₁≡)
          (sym (applyTyCtxs-++ χsM χsN ΔL)))

    ρ′≡total :
      ρ′ ≡ applyRightChange χ′ (applyLeftChanges (χsM ++ χsN) ρ)
    ρ′≡total =
      trans ρ′≡
        (cong (applyRightChange χ′)
          (sym (applyLeftChanges-++ χsM χsN ρ)))

    framed⊒ :
      ΔL₂ ∣ ΔR′ ∣ ρ′ ∣ []
        ⊢ applyTerms χsN WM ⊕[ addℕ ] P
          ⊒ applyTerm χ′ M′ ⊕[ addℕ ] S′ ∶ _ ⦂ _ ⊒ _
    framed⊒ =
      let
        ih : ΔL₂ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ P ⊒ S′ ∶ r ⦂ C ⊒ D
        ih = P⊒S′

        left-before-right-change :
          ΔL₁ ∣ ΔR ∣ applyLeftChanges χsM ρ ∣ []
            ⊢ WM ⊒ M′
              ∶ applyCoercions χsM (id (‵ `ℕ))
              ⦂ applyTys χsM (‵ `ℕ) ⊒ ‵ `ℕ
        left-before-right-change = WM⊒M′

        obligation :
          ΔL₂ ∣ ΔR′ ∣ ρ′ ∣ []
            ⊢ applyTerms χsN WM ⊕[ addℕ ] P
              ⊒ applyTerm χ′ M′ ⊕[ addℕ ] S′ ∶ _ ⦂ _ ⊒ _
        obligation = {! ξ-⊕₂-source-left-still-reducing-frame !}
      in
      obligation

    obligation :
      ∃[ χs ] ∃[ P ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (M ⊕[ addℕ ] N —↠[ χs ] P) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL) ×
        (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
        (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
        ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
          ⊢ P ⊒ applyTerm χ′ M′ ⊕[ addℕ ] S′ ∶ r ⦂ C ⊒ D
    obligation =
      χsM ++ χsN ,
      applyTerms χsN WM ⊕[ addℕ ] P ,
      ΔL₂ ,
      ΔR′ ,
      ρ′ ,
      _ ,
      _ ,
      _ ,
      source-steps ,
      ΔL₂≡total ,
      ΔR′≡ ,
      ρ′≡total ,
      framed⊒
  in
  obligation
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⊕[ addℕ ] N} {M′ = M′ ⊕[ addℕ ] N′}
    {N′ = P′} {χ′ = χ′}
    (ok-⊕₂ vM noM okN) pᶜ
    (⊕⊒⊕ᵗ pℕᶜ M⊒M′ N⊒N′)
    (ξ-⊕₂ {M′ = S′} vM′ shiftM′ N′→P′) =
  let
    runtimeN : RuntimeOK N
    runtimeN = okN

    rec =
      dynamicGradualGuarantee
        runtimeN
        pᶜ
        N⊒N′
        N′→P′

    χs , P , ΔL′ , ΔR′ , ρ′ ,
      C , D , r ,
      N↠P , ΔL′≡ , ΔR′≡ , ρ′≡ , P⊒P′ = rec

    framed⊒ :
      ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
        ⊢ applyTerms χs M ⊕[ addℕ ] P
          ⊒ applyTerm χ′ M′ ⊕[ addℕ ] S′ ∶ _ ⦂ _ ⊒ _
    framed⊒ =
      let
        pℕ′ :
          ΔL′ ∣ ΔR′ ∣ ρ′ ⊢ id (‵ `ℕ) ∶ᶜ ‵ `ℕ ⊒ ‵ `ℕ
        pℕ′ =
          let μ , p′ᶜ = typed-term-narrowing-coercion P⊒P′ in
          id-ℕ-narrowingᶜ (narrowing-store-corrᶜ p′ᶜ)

        M⊒M′′ :
          ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
            ⊢ applyTerms χs M ⊒ applyTerm χ′ M′
              ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ
        M⊒M′′ = {! ξ-⊕₂-updated-left-narrowing !}

        P⊒P′ℕ :
          ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
            ⊢ P ⊒ S′ ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ
        P⊒P′ℕ =
          let
            ih : ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ P ⊒ S′ ∶ r ⦂ C ⊒ D
            ih = P⊒P′
          in
          {! ξ-⊕₂-IH-result-nat !}
      in
      ⊕⊒⊕ᵗ pℕ′ M⊒M′′ P⊒P′ℕ

    obligation :
      ∃[ χs ] ∃[ P ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (M ⊕[ addℕ ] N —↠[ χs ] P) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL) ×
        (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
        (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
        ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ P ⊒ P′ ∶ r ⦂ C ⊒ D
    obligation =
      χs ,
      applyTerms χs M ⊕[ addℕ ] P ,
      ΔL′ ,
      ΔR′ ,
      ρ′ ,
      _ ,
      _ ,
      _ ,
      ⊕₂-↠ vM noM N↠P ,
      ΔL′≡ ,
      ΔR′≡ ,
      ρ′≡ ,
      framed⊒
  in
  obligation
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M}
    okM pᶜ
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
  ⊒blameᵗ (typed-term-narrowing-source-typingᶜ castRel) pᶜ
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M}
    okM pᶜ
    (⊒cast-ᵗ p′ᶜ rᶜ t⊒ M⊒M′)
    (pure-step (β-id vV)) =
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
  M⊒M′
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M}
    okM pᶜ
    (⊒cast+ᵗ p′ᶜ rᶜ
      (_ , _ , _ , _ , _ , (cast-id _ _ , cross (id-‵ ι)) , _)
      M⊒M′)
    (pure-step (β-id vV)) =
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
  M⊒M′
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M}
    okM pᶜ
    (⊒cast+ᵗ p′ᶜ rᶜ
      (_ , _ , _ , _ , _ , (cast-id _ _ , cross (id-＇ α)) , _)
      M⊒M′)
    (pure-step (β-id vV)) =
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
  M⊒M′
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M}
    okM pᶜ
    (⊒cast+ᵗ p′ᶜ rᶜ
      (_ , _ , _ , _ , _ , (cast-id _ _ , id★) , _)
      M⊒M′)
    (pure-step (β-id vV)) =
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
  M⊒M′
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M} {χ′ = χ′}
    okM pᶜ
    (⊒cast+ᵗ {M′ = M′} {t = t} p′ᶜ rᶜ t⊒ M⊒M′)
    (ξ-⟨⟩ {M′ = S′} M′→S′) =
  let
    rec :
      ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (M —↠[ χs ] N) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL) ×
        (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
        (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
        ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ N ⊒ S′ ∶ r ⦂ C ⊒ D
    rec =
      let
        inner-runtime : RuntimeOK M
        inner-runtime = okM

        inner-step : M′ —→[ χ′ ] S′
        inner-step = M′→S′

        inner-narrowing :
          ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ M′ ∶ _ ⦂ _ ⊒ _
        inner-narrowing = M⊒M′
      in
      {! target-cast-plus-inner-step-simulation !}

    χs , N , ΔL′ , ΔR′ , ρ′ ,
      C , D , r ,
      source-steps , ΔL′≡ , ΔR′≡ , ρ′≡ , N⊒S′ = rec

    cast-result⊒ :
      ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
        ⊢ N ⊒ S′ ⟨ applyCoercion χ′ (narrowing-dual t⊒) ⟩
          ∶ _ ⦂ _ ⊒ _
    cast-result⊒ =
      let
        ih : ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ N ⊒ S′ ∶ r ⦂ C ⊒ D
        ih = N⊒S′
      in
      {! target-cast-plus-inner-step-result !}

    obligation :
      ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (M —↠[ χs ] N) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL) ×
        (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
        (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
        ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
          ⊢ N ⊒ S′ ⟨ applyCoercion χ′ (narrowing-dual t⊒) ⟩
            ∶ r ⦂ C ⊒ D
    obligation =
      χs ,
      N ,
      ΔL′ ,
      ΔR′ ,
      ρ′ ,
      _ ,
      _ ,
      _ ,
      source-steps ,
      ΔL′≡ ,
      ΔR′≡ ,
      ρ′≡ ,
      cast-result⊒
  in
  obligation
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M} {N′ = N′} {χ′ = χ′}
    okM pᶜ
    castRel@(⊒cast+ᵗ {M′ = M′} p′ᶜ rᶜ t⊒ M⊒M′)
    M′⟨s⟩→N′ =
  let
    relation-obligation :
      ΔL ∣ applyTyCtx χ′ ΔR ∣ applyRightChange χ′ ρ ∣ []
        ⊢ M ⊒ N′ ∶ _ ⦂ _ ⊒ _
    relation-obligation =
      let
        source-relation :
          ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M
            ⊒ M′ ⟨ narrowing-dual t⊒ ⟩ ∶ _ ⦂ _ ⊒ _
        source-relation = castRel

        target-cast-step :
          M′ ⟨ narrowing-dual t⊒ ⟩ —→[ χ′ ] N′
        target-cast-step = M′⟨s⟩→N′

        obligation :
          ΔL ∣ applyTyCtx χ′ ΔR ∣ applyRightChange χ′ ρ ∣ []
            ⊢ M ⊒ N′ ∶ _ ⦂ _ ⊒ _
        obligation = {! target-cast-plus-simulation-relation !}
      in
      obligation

    obligation :
      ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (M —↠[ χs ] N) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL) ×
        (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
        (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
        ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ N ⊒ N′ ∶ r ⦂ C ⊒ D
    obligation =
      [] ,
      M ,
      ΔL ,
      applyTyCtx χ′ ΔR ,
      applyRightChange χ′ ρ ,
      _ ,
      _ ,
      _ ,
      ↠-refl ,
      refl ,
      refl ,
      refl ,
      relation-obligation
  in
  obligation
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M} {χ′ = χ′}
    okM pᶜ
    (⊒cast-ᵗ {t = t} p′ᶜ rᶜ t⊒ M⊒M′)
    (ξ-⟨⟩ {M′ = S′} M′→S′) =
  let
    rec = dynamicGradualGuarantee okM p′ᶜ M⊒M′ M′→S′

    χs , N , ΔL′ , ΔR′ , ρ′ ,
      C , D , r ,
      source-steps , ΔL′≡ , ΔR′≡ , ρ′≡ , N⊒S′ = rec

    cast-result⊒ :
      ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
        ⊢ N ⊒ S′ ⟨ applyCoercion χ′ t ⟩ ∶ _ ⦂ _ ⊒ _
    cast-result⊒ =
      let
        ih : ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ N ⊒ S′ ∶ r ⦂ C ⊒ D
        ih = N⊒S′
      in
      {! target-cast-minus-inner-step-result !}

    obligation :
      ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (M —↠[ χs ] N) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL) ×
        (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
        (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
        ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
          ⊢ N ⊒ S′ ⟨ applyCoercion χ′ t ⟩ ∶ r ⦂ C ⊒ D
    obligation =
      χs ,
      N ,
      ΔL′ ,
      ΔR′ ,
      ρ′ ,
      _ ,
      _ ,
      _ ,
      source-steps ,
      ΔL′≡ ,
      ΔR′≡ ,
      ρ′≡ ,
      cast-result⊒
  in
  obligation
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M} {N′ = N′} {χ′ = χ′}
    okM pᶜ
    castRel@(⊒cast-ᵗ {M′ = M′} {t = t} p′ᶜ rᶜ t⊒ M⊒M′)
    M′⟨s⟩→N′ =
  let
    relation-obligation :
      ΔL ∣ applyTyCtx χ′ ΔR ∣ applyRightChange χ′ ρ ∣ []
        ⊢ M ⊒ N′ ∶ _ ⦂ _ ⊒ _
    relation-obligation =
      let
        source-relation :
          ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ M′ ⟨ t ⟩
            ∶ _ ⦂ _ ⊒ _
        source-relation = castRel

        target-cast-step : M′ ⟨ t ⟩ —→[ χ′ ] N′
        target-cast-step = M′⟨s⟩→N′

        obligation :
          ΔL ∣ applyTyCtx χ′ ΔR ∣ applyRightChange χ′ ρ ∣ []
            ⊢ M ⊒ N′ ∶ _ ⦂ _ ⊒ _
        obligation = {! target-cast-minus-simulation-relation !}
      in
      obligation

    obligation :
      ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (M —↠[ χs ] N) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL) ×
        (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
        (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
        ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ N ⊒ N′ ∶ r ⦂ C ⊒ D
    obligation =
      [] ,
      M ,
      ΔL ,
      applyTyCtx χ′ ΔR ,
      applyRightChange χ′ ρ ,
      _ ,
      _ ,
      _ ,
      ↠-refl ,
      refl ,
      refl ,
      refl ,
      relation-obligation
  in
  obligation
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⟨ c ⟩} {N′ = N′} {χ′ = χ′}
    okM pᶜ
    (cast+⊒ᵗ qᶜ rᶜ s⊒ M⊒M′) M′→N′ =
  let
    rec = dynamicGradualGuarantee (runtime-⟨⟩ okM) qᶜ M⊒M′ M′→N′

    χs , N , ΔL′ , ΔR′ , ρ′ ,
      C , D , r ,
      source-steps , ΔL′≡ , ΔR′≡ , ρ′≡ , N⊒N′ = rec

    cast-result⊒ :
      ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
        ⊢ N ⟨ applyCoercions χs c ⟩ ⊒ N′ ∶ _ ⦂ _ ⊒ _
    cast-result⊒ =
      let
        ih : ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ N ⊒ N′ ∶ r ⦂ C ⊒ D
        ih = N⊒N′

        source-cast-evidence :
          _ ∣ ΔL ∣ ΔR ∣ ρ ⊢ _ ∶ _ ⊒ _
        source-cast-evidence = s⊒

        obligation :
          ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
            ⊢ N ⟨ applyCoercions χs c ⟩ ⊒ N′ ∶ _ ⦂ _ ⊒ _
        obligation = {! source-cast-plus-result-narrowing !}
      in
      obligation

    obligation :
      ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (M ⟨ c ⟩ —↠[ χs ] N) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL) ×
        (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
        (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
        ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ N ⊒ N′ ∶ r ⦂ C ⊒ D
    obligation =
      χs ,
      N ⟨ applyCoercions χs c ⟩ ,
      ΔL′ ,
      ΔR′ ,
      ρ′ ,
      _ ,
      _ ,
      _ ,
      cast-↠ {c = c} source-steps ,
      ΔL′≡ ,
      ΔR′≡ ,
      ρ′≡ ,
      cast-result⊒
  in
  obligation
dynamicGradualGuarantee {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M ⟨ c ⟩} {N′ = N′} {χ′ = χ′}
    okM pᶜ
    (cast-⊒ᵗ {M′ = M′} qᶜ rᶜ s⊒ M⊒M′) M′→N′ =
  let
    rec :
      ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (M —↠[ χs ] N) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL) ×
        (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
        (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
        ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ N ⊒ N′ ∶ r ⦂ C ⊒ D
    rec =
      let
        inner-runtime : RuntimeOK M
        inner-runtime = runtime-⟨⟩ okM

        inner-step : M′ —→[ χ′ ] N′
        inner-step = M′→N′

        inner-narrowing :
          ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ M′ ∶ _ ⦂ _ ⊒ _
        inner-narrowing = M⊒M′
      in
      {! source-cast-minus-inner-simulation !}

    χs , N , ΔL′ , ΔR′ , ρ′ ,
      C , D , r ,
      source-steps , ΔL′≡ , ΔR′≡ , ρ′≡ , N⊒N′ = rec

    cast-result⊒ :
      ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
        ⊢ N ⟨ applyCoercions χs c ⟩ ⊒ N′ ∶ _ ⦂ _ ⊒ _
    cast-result⊒ =
      let
        ih : ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ N ⊒ N′ ∶ r ⦂ C ⊒ D
        ih = N⊒N′
      in
      {! source-cast-minus-result-narrowing !}

    obligation :
      ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (M ⟨ c ⟩ —↠[ χs ] N) ×
        (ΔL′ ≡ applyTyCtxs χs ΔL) ×
        (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
        (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
        ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ N ⊒ N′ ∶ r ⦂ C ⊒ D
    obligation =
      χs ,
      N ⟨ applyCoercions χs c ⟩ ,
      ΔL′ ,
      ΔR′ ,
      ρ′ ,
      _ ,
      _ ,
      _ ,
      cast-↠ {c = c} source-steps ,
      ΔL′≡ ,
      ΔR′≡ ,
      ρ′≡ ,
      cast-result⊒
  in
  obligation
