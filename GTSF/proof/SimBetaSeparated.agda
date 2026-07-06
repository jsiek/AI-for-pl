{-# OPTIONS --allow-unsolved-metas #-}

module proof.SimBetaSeparated where

-- File Charter:
--   * Isolates the separated-store function-application simulation proof.
--   * Keeps the target term/store unchanged while left-side catchup advances
--     the source term through `SealCorr`.
--   * Provides `sim-beta` and the left-advancement helpers used by the
--     separated DGG beta caller.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

open import Types
open import Coercions
open import NarrowWiden using
  ( cross
  ; dualⁿ
  ; dualʷ
  ; Widening
  ; _？︔_
  ; _︔seal_
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
  renaming (_↦_ to _↦ⁿʷ_)
open import NuTerms
open import NuReduction
open import StoreCorrespondence
open import TermNarrowingSeparated
open import proof.Catchup using (runtime-⇑ᵗᵐ)
open import proof.CatchupSeparated using
  ( applyLeftChanges
  ; applyLeftChanges-++
  ; catchup-lemmaˡ
  )
open import proof.CoercionProperties using
  ( coercion-src-tgtᵐ
  ; coercion-wfᵐ
  ; dualActionOk-normal
  ; dualStoreAt-normal
  ; minus-flips-typingᵐ
  )
open import proof.NarrowWidenProperties using
  ( dualⁿ-flips-typingᵐ
  ; dualʷ-flips-typingᵐ
  ; narrowing-determinedᵐ
  )
open import proof.NuProgress using (canonical-⇒; fv-ƛ; fv-↦)
open import proof.ReductionProperties using
  ( applyTerms-preserves-No•
  ; applyTerms-preserves-Value
  ; applyCoercions
  ; applyCoercions-++
  ; applyCoercions-dual
  ; applyTys-++
  ; applyTyCtxs-++
  ; cast-↠
  ; cast-dual-↠
  ; ↠-trans
  ; ·₁-↠
  ; ·₂-↠
  )
open import proof.LeftChangeNarrowingSeparated public using
  ( applyTerm-preserves-RuntimeOK
  ; applyTerms-preserves-RuntimeOK
  ; applyTys-⇒
  ; applyCoercions-↦
  ; applyCoercions-dual-applyCoercions
  ; applyLeftCtxEntry
  ; applyLeftCtx
  ; no•-cast-inv
  ; ⟨⟩-term-injective
  ; ⟨⟩-coercion-injective
  ; widen-fun-domainᵐ
  ; narrow-fun-codomainᵐ
  ; separated-fun-codomain
  ; ↦-codomain
  ; ↦-right-injective
  ; ↦-domain
  ; ↦-left-injective
  ; separated-left-coercionᵐ
  ; separated-right-coercionᵐ
  ; left-change-term-narrowing
  ; left-change-coercion-narrowing
  ; left-change-source-coercion-narrowing
  ; left-change-source-coercion-narrowing-dual
  ; left-change-fun-coercion-narrowing
  ; dualʷ-raw-determined
  ; dualʷ-involutive-raw
  ; fun-narrow-domain-dual-determined
  ; composed-index-raws-≡
  ; fun-domain-dual-composed
  ; cast-fun-comp-domain-dual
  ; cast-fun-comp-domain-dual₂
  ; cast-fun-comp-codomain
  ; left-change-composed-index
  ; separated-fun-domain-dual
  ; advance-left-term-narrowing
  ; advance-left-function-term-narrowing
  ; advance-left-lambda-narrowing
  )

------------------------------------------------------------------------
-- Function application simulation
------------------------------------------------------------------------

postulate
  term-substitution-narrowingᶜ :
    ∀ {ΔL ΔR ρ N N′ V V′ p q A A′ B B′} →
    ΔL ∣ ΔR ∣ ρ ∣ ctx-entry A A′ p ∷ []
      ⊢ N ⊒ N′ ∶ q ⦂ B ⊒ B′ →
    ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ V ⊒ V′ ∶ p ⦂ A ⊒ A′ →
    ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ N [ V ] ⊒ N′ [ V′ ] ∶ q ⦂ B ⊒ B′

sim-beta-cast-tail :
  ∀ {ΔL ΔR ρ M₀ M₁ NL V WRA VR qᵢ qₒ d Bₒ BL BR D₁ D₂ μq μd}
    {χsA ΔLA} →
  (castN : StoreChanges → Term → Term) →
  M₀ —↠[ keep ∷ χsA ] M₁ →
  (∀ {χsT N} →
    applyTerms χsA V · WRA —↠[ χsT ] N →
    M₁ —↠[ χsT ] castN χsT N) →
  μq ∣ ΔL ∣ ΔR ∣ ρ ⊢ qₒ ∶ Bₒ ⊒ BR →
  μd ∣ ΔL ∣ ΔR ∣ ρ ⊢ d ∶ D₁ ⊒ D₂ →
  ΔL ∣ ΔR ∣ ρ ⊢ d ⨟ qₒ ≈ qᵢ ∶ D₁ ⊒ BR →
  ΔLA ≡ applyTyCtxs χsA ΔL →
  StoreCorr ΔLA ΔR (applyLeftChanges χsA ρ) →
  (∀ {χsT N ΔLT ρT} →
    ρT ≡ applyLeftChanges χsT (applyLeftChanges χsA ρ) →
    ΔLT ∣ ΔR ∣ ρT ∣ []
      ⊢ N ⊒ NL [ VR ] ∶ applyCoercions χsT (applyCoercions χsA qᵢ)
        ⦂ applyTys χsT (applyTys χsA BL) ⊒ BR →
    μq ∣ ΔLT ∣ ΔR ∣ ρT
      ⊢ applyCoercions χsT (applyCoercions χsA qₒ)
        ∶ applyTys χsT (applyTys χsA Bₒ) ⊒ BR →
    μd ∣ ΔLT ∣ ΔR ∣ ρT
      ⊢ applyCoercions χsT (applyCoercions χsA d)
        ∶ applyTys χsT (applyTys χsA D₁)
        ⊒ applyTys χsT (applyTys χsA D₂) →
    ΔLT ∣ ΔR ∣ ρT
      ⊢ applyCoercions χsT (applyCoercions χsA d)
        ⨟ applyCoercions χsT (applyCoercions χsA qₒ)
        ≈ applyCoercions χsT (applyCoercions χsA qᵢ)
        ∶ applyTys χsT (applyTys χsA D₁) ⊒ BR →
    ΔLT ∣ ΔR ∣ ρT ∣ []
      ⊢ castN χsT N ⊒ NL [ VR ]
        ∶ applyCoercions χsT (applyCoercions χsA qₒ)
        ⦂ applyTys χsT (applyTys χsA Bₒ) ⊒ BR) →
  (∃[ χsT ] ∃[ N ] ∃[ ΔLT ] ∃[ ρT ]
    (applyTerms χsA V · WRA —↠[ χsT ] N) ×
    (ΔLT ≡ applyTyCtxs χsT ΔLA) ×
    (ρT ≡ applyLeftChanges χsT (applyLeftChanges χsA ρ)) ×
    ΔLT ∣ ΔR ∣ ρT ∣ []
      ⊢ N ⊒ NL [ VR ] ∶ applyCoercions χsT (applyCoercions χsA qᵢ)
        ⦂ applyTys χsT (applyTys χsA BL) ⊒ BR) →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ]
    (M₀ —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ NL [ VR ] ∶ applyCoercions χs qₒ
        ⦂ applyTys χs Bₒ ⊒ BR
sim-beta-cast-tail {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ} {M₀ = M₀}
    {NL = NL} {VR = VR} {qᵢ = qᵢ} {qₒ = qₒ} {d = d} {Bₒ = Bₒ}
    {BR = BR} {D₁ = D₁} {D₂ = D₂} {μq = μq} {μd = μd}
    {χsA = χsA} {ΔLA = ΔLA}
    castN prefix-red tail-cast qₒ⊒ d⊒ comp₀ ΔLA≡ ρA-corr wrap
    rec =
  let
    χsT , N , ΔLT , ρT ,
      tail-red , ΔT≡ , ρT≡ , N⊒NL[VR] = rec

    μN , nᶜ = typed-term-narrowing-coercion N⊒NL[VR]

    ρT-corr :
      StoreCorr ΔLT ΔR
        (applyLeftChanges χsT (applyLeftChanges χsA ρ))
    ρT-corr =
      subst (StoreCorr ΔLT ΔR)
        ρT≡
        (narrowing-store-corrᶜ {μ = μN} nᶜ)

    qₒ⊒A :
      μq ∣ ΔLA ∣ ΔR ∣ applyLeftChanges χsA ρ
        ⊢ applyCoercions χsA qₒ ∶ applyTys χsA Bₒ ⊒ BR
    qₒ⊒A =
      left-change-coercion-narrowing χsA {μ = μq} ΔLA≡ ρA-corr qₒ⊒

    qₒ⊒T :
      μq ∣ ΔLT ∣ ΔR
        ∣ applyLeftChanges χsT (applyLeftChanges χsA ρ)
        ⊢ applyCoercions χsT (applyCoercions χsA qₒ)
          ∶ applyTys χsT (applyTys χsA Bₒ) ⊒ BR
    qₒ⊒T =
      left-change-coercion-narrowing χsT {μ = μq} ΔT≡ ρT-corr qₒ⊒A

    qₒ⊒Tρ :
      μq ∣ ΔLT ∣ ΔR ∣ ρT
        ⊢ applyCoercions χsT (applyCoercions χsA qₒ)
          ∶ applyTys χsT (applyTys χsA Bₒ) ⊒ BR
    qₒ⊒Tρ =
      subst
        (λ ρ₀ →
          μq ∣ ΔLT ∣ ΔR ∣ ρ₀
            ⊢ applyCoercions χsT (applyCoercions χsA qₒ)
              ∶ applyTys χsT (applyTys χsA Bₒ) ⊒ BR)
        (sym ρT≡)
        qₒ⊒T

    d⊒A :
      μd ∣ ΔLA ∣ ΔR ∣ applyLeftChanges χsA ρ
        ⊢ applyCoercions χsA d
          ∶ applyTys χsA D₁ ⊒ applyTys χsA D₂
    d⊒A =
      left-change-source-coercion-narrowing χsA {μ = μd}
        ΔLA≡ ρA-corr d⊒

    d⊒T :
      μd ∣ ΔLT ∣ ΔR
        ∣ applyLeftChanges χsT (applyLeftChanges χsA ρ)
        ⊢ applyCoercions χsT (applyCoercions χsA d)
          ∶ applyTys χsT (applyTys χsA D₁)
          ⊒ applyTys χsT (applyTys χsA D₂)
    d⊒T =
      left-change-source-coercion-narrowing χsT {μ = μd}
        ΔT≡ ρT-corr d⊒A

    d⊒Tρ :
      μd ∣ ΔLT ∣ ΔR ∣ ρT
        ⊢ applyCoercions χsT (applyCoercions χsA d)
          ∶ applyTys χsT (applyTys χsA D₁)
          ⊒ applyTys χsT (applyTys χsA D₂)
    d⊒Tρ =
      subst
        (λ ρ₀ →
          μd ∣ ΔLT ∣ ΔR ∣ ρ₀
            ⊢ applyCoercions χsT (applyCoercions χsA d)
              ∶ applyTys χsT (applyTys χsA D₁)
              ⊒ applyTys χsT (applyTys χsA D₂))
        (sym ρT≡)
        d⊒T

    compA :
      ΔLA ∣ ΔR ∣ applyLeftChanges χsA ρ
        ⊢ applyCoercions χsA d ⨟ applyCoercions χsA qₒ
          ≈ applyCoercions χsA qᵢ ∶ applyTys χsA D₁ ⊒ BR
    compA = left-change-composed-index χsA ΔLA≡ ρA-corr comp₀

    compT :
      ΔLT ∣ ΔR ∣ applyLeftChanges χsT (applyLeftChanges χsA ρ)
        ⊢ applyCoercions χsT (applyCoercions χsA d)
          ⨟ applyCoercions χsT (applyCoercions χsA qₒ)
          ≈ applyCoercions χsT (applyCoercions χsA qᵢ)
          ∶ applyTys χsT (applyTys χsA D₁) ⊒ BR
    compT = left-change-composed-index χsT ΔT≡ ρT-corr compA

    compTρ :
      ΔLT ∣ ΔR ∣ ρT
        ⊢ applyCoercions χsT (applyCoercions χsA d)
          ⨟ applyCoercions χsT (applyCoercions χsA qₒ)
          ≈ applyCoercions χsT (applyCoercions χsA qᵢ)
          ∶ applyTys χsT (applyTys χsA D₁) ⊒ BR
    compTρ =
      subst
        (λ ρ₀ →
          ΔLT ∣ ΔR ∣ ρ₀
            ⊢ applyCoercions χsT (applyCoercions χsA d)
              ⨟ applyCoercions χsT (applyCoercions χsA qₒ)
              ≈ applyCoercions χsT (applyCoercions χsA qᵢ)
              ∶ applyTys χsT (applyTys χsA D₁) ⊒ BR)
        (sym ρT≡)
        compT

    source-steps :
      M₀ —↠[ (keep ∷ χsA) ++ χsT ] castN χsT N
    source-steps = ↠-trans prefix-red (tail-cast tail-red)

    ΔLT≡ :
      ΔLT ≡ applyTyCtxs ((keep ∷ χsA) ++ χsT) ΔL
    ΔLT≡ =
      trans ΔT≡
        (trans
          (cong (applyTyCtxs χsT) ΔLA≡)
          (sym (applyTyCtxs-++ χsA χsT ΔL)))

    ρT-total≡ :
      ρT ≡ applyLeftChanges ((keep ∷ χsA) ++ χsT) ρ
    ρT-total≡ =
      trans ρT≡ (sym (applyLeftChanges-++ χsA χsT ρ))

    N-cast⊒ =
      wrap ρT≡ N⊒NL[VR] qₒ⊒Tρ d⊒Tρ compTρ

    N-cast⊒total :
      ΔLT ∣ ΔR ∣ ρT ∣ []
        ⊢ castN χsT N ⊒ NL [ VR ]
          ∶ applyCoercions ((keep ∷ χsA) ++ χsT) qₒ
          ⦂ applyTys ((keep ∷ χsA) ++ χsT) Bₒ ⊒ BR
    N-cast⊒total =
      subst
        (λ p →
          ΔLT ∣ ΔR ∣ ρT ∣ []
            ⊢ castN χsT N ⊒ NL [ VR ] ∶ p
              ⦂ applyTys ((keep ∷ χsA) ++ χsT) Bₒ ⊒ BR)
        (sym (applyCoercions-++ χsA χsT qₒ))
        (subst
          (λ A₀ →
            ΔLT ∣ ΔR ∣ ρT ∣ []
              ⊢ castN χsT N ⊒ NL [ VR ]
                ∶ applyCoercions χsT (applyCoercions χsA qₒ)
                ⦂ A₀ ⊒ BR)
          (sym (applyTys-++ χsA χsT Bₒ))
          N-cast⊒)
  in
  (keep ∷ χsA) ++ χsT ,
  castN χsT N ,
  ΔLT ,
  ρT ,
  source-steps ,
  ΔLT≡ ,
  ρT-total≡ ,
  N-cast⊒total

sim-beta-cast+-result :
  ∀ {ΔL ΔR ρ ΔLA ΔLT ρT NL VR N qᵢ qₒ dₛ d Bₒ BL BR μq μd}
    {χsA χsT} →
  ΔL ∣ ΔR ∣ ρ ⊢ qᵢ ∶ᶜ BL ⊒ BR →
  μq ∣ ΔL ∣ ΔR ∣ ρ ⊢ qₒ ∶ Bₒ ⊒ BR →
  (dₛ⊒ : μd ∣ ΔL ∣ ΔR ∣ ρ ⊢ dₛ ∶ Bₒ ⊒ BL) →
  narrowing-dual dₛ⊒ ≡ d →
  ΔL ∣ ΔR ∣ ρ ⊢ dₛ ⨟ qᵢ ≈ qₒ ∶ Bₒ ⊒ BR →
  ΔLA ≡ applyTyCtxs χsA ΔL →
  StoreCorr ΔLA ΔR (applyLeftChanges χsA ρ) →
  ΔLT ≡ applyTyCtxs χsT ΔLA →
  ρT ≡ applyLeftChanges χsT (applyLeftChanges χsA ρ) →
  ΔLT ∣ ΔR ∣ ρT ∣ []
    ⊢ N ⊒ NL [ VR ] ∶ applyCoercions χsT (applyCoercions χsA qᵢ)
      ⦂ applyTys χsT (applyTys χsA BL) ⊒ BR →
  ΔLT ∣ ΔR ∣ ρT ∣ []
    ⊢ N ⟨ applyCoercions χsT (applyCoercions χsA d) ⟩
      ⊒ NL [ VR ] ∶ applyCoercions ((keep ∷ χsA) ++ χsT) qₒ
      ⦂ applyTys ((keep ∷ χsA) ++ χsT) Bₒ ⊒ BR
sim-beta-cast+-result {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {ΔLA = ΔLA} {ΔLT = ΔLT} {ρT = ρT} {NL = NL}
    {VR = VR} {N = N} {qᵢ = qᵢ} {qₒ = qₒ} {dₛ = dₛ}
    {d = d} {Bₒ = Bₒ} {BL = BL} {BR = BR} {μq = μq}
    {μd = μd} {χsA = χsA} {χsT = χsT}
    qᵢᶜ qₒ⊒ dₛ⊒ dₛ-dual-eq comp₀ ΔLA≡ ρA-corr ΔT≡ ρT≡
    N⊒NL[VR] =
  let
    μN , nᶜ = typed-term-narrowing-coercion N⊒NL[VR]

    ρT-corr :
      StoreCorr ΔLT ΔR
        (applyLeftChanges χsT (applyLeftChanges χsA ρ))
    ρT-corr =
      subst (StoreCorr ΔLT ΔR)
        ρT≡
        (narrowing-store-corrᶜ {μ = μN} nᶜ)

    N⊒NL[VR]T :
      ΔLT ∣ ΔR
        ∣ applyLeftChanges χsT (applyLeftChanges χsA ρ) ∣ []
        ⊢ N ⊒ NL [ VR ]
          ∶ applyCoercions χsT (applyCoercions χsA qᵢ)
          ⦂ applyTys χsT (applyTys χsA BL) ⊒ BR
    N⊒NL[VR]T =
      subst
        (λ ρ₀ →
          ΔLT ∣ ΔR ∣ ρ₀ ∣ []
            ⊢ N ⊒ NL [ VR ]
              ∶ applyCoercions χsT (applyCoercions χsA qᵢ)
              ⦂ applyTys χsT (applyTys χsA BL) ⊒ BR)
        ρT≡
        N⊒NL[VR]

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
          ⊒ NL [ VR ] ∶ applyCoercions χsT (applyCoercions χsA qₒ)
          ⦂ applyTys χsT (applyTys χsA Bₒ) ⊒ BR
    N-cast⊒T =
      subst
        (λ d₀ →
          ΔLT ∣ ΔR
            ∣ applyLeftChanges χsT (applyLeftChanges χsA ρ) ∣ []
            ⊢ N ⟨ d₀ ⟩ ⊒ NL [ VR ]
              ∶ applyCoercions χsT (applyCoercions χsA qₒ)
              ⦂ applyTys χsT (applyTys χsA Bₒ) ⊒ BR)
        dₛ-dual-T
        (cast+⊒ᵗ
          {ΔL = ΔLT}
          {ΔR = ΔR}
          {ρ = applyLeftChanges χsT (applyLeftChanges χsA ρ)}
          {γ = []}
          {M = N}
          {M′ = NL [ VR ]}
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
          (left-change-composed-index χsT ΔT≡ ρT-corr
            (left-change-composed-index χsA ΔLA≡ ρA-corr
              comp₀))
          N⊒NL[VR]T)
  in
  subst
    (λ ρ₀ →
      ΔLT ∣ ΔR ∣ ρ₀ ∣ []
        ⊢ N ⟨ applyCoercions χsT (applyCoercions χsA d) ⟩
          ⊒ NL [ VR ]
          ∶ applyCoercions ((keep ∷ χsA) ++ χsT) qₒ
          ⦂ applyTys ((keep ∷ χsA) ++ χsT) Bₒ ⊒ BR)
    (sym ρT≡)
    (subst
      (λ p →
        ΔLT ∣ ΔR ∣ applyLeftChanges χsT (applyLeftChanges χsA ρ) ∣ []
          ⊢ N ⟨ applyCoercions χsT (applyCoercions χsA d) ⟩
            ⊒ NL [ VR ] ∶ p
            ⦂ applyTys ((keep ∷ χsA) ++ χsT) Bₒ ⊒ BR)
      (sym (applyCoercions-++ χsA χsT qₒ))
      (subst
        (λ B →
          ΔLT ∣ ΔR
            ∣ applyLeftChanges χsT (applyLeftChanges χsA ρ) ∣ []
            ⊢ N ⟨ applyCoercions χsT (applyCoercions χsA d) ⟩
              ⊒ NL [ VR ]
              ∶ applyCoercions χsT (applyCoercions χsA qₒ)
              ⦂ B ⊒ BR)
        (sym (applyTys-++ χsA χsT Bₒ))
        N-cast⊒T))

term-function-domain-dual :
  ∀ {ΔL ΔR ρ WL NL p q A A′ B B′} →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ WL ⊒ ƛ NL ∶ p ↦ q
    ⦂ A ⇒ B ⊒ A′ ⇒ B′ →
  Coercion
term-function-domain-dual (ƛ⊒ƛᵗ p↦qᶜ N⊒NL) =
  fun-narrow-domain-dualᶜ p↦qᶜ
term-function-domain-dual (cast+⊒ᵗ qᶜ rᶜ s⊒ _ M⊒M′) =
  fun-narrow-domain-dual rᶜ
term-function-domain-dual (cast-⊒ᵗ qᶜ rᶜ s⊒ _ M⊒M′) =
  fun-narrow-domain-dual qᶜ

{-# TERMINATING #-}
sim-beta :
  ∀ {ΔL ΔR ρ WL NL WR VR p q A A′ B B′ μsim} →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ WL ⊒ ƛ NL ∶ p ↦ q
    ⦂ A ⇒ B ⊒ A′ ⇒ B′ →
  Value WL →
  No• WL →
  (p↦q-sim⊒ : μsim ∣ ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q
                ∶ (A ⇒ B) ⊒ (A′ ⇒ B′)) →
  ΔL ∣ ΔR ∣ ρ
    ⊢ fun-narrow-domain-dual p↦q-sim⊒ ∶ᶜ A ⊒ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ []
    ⊢ WR ⊒ VR ∶ fun-narrow-domain-dual p↦q-sim⊒ ⦂ A ⊒ A′ →
  Value WR →
  No• WR →
  Value VR →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ]
    (WL · WR —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ NL [ VR ] ∶ applyCoercions χs q
        ⦂ applyTys χs B ⊒ B′
sim-beta {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {WR = WR} {VR = VR} {A = A} {A′ = A′}
    (ƛ⊒ƛᵗ p↦qᶜ N⊒NL)
    (ƛ N) noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR =
  let
    WR⊒VR′ :
      ΔL ∣ ΔR ∣ ρ ∣ []
        ⊢ WR ⊒ VR ∶ fun-narrow-domain-dualᶜ p↦qᶜ
          ⦂ A ⊒ A′
    WR⊒VR′ =
      subst
        (λ p → ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ WR ⊒ VR ∶ p ⦂ A ⊒ A′)
        (fun-narrow-domain-dual-determined p↦q-sim⊒ p↦qᶜ)
        WR⊒VR
  in
  keep ∷ [] ,
  N [ WR ] ,
  ΔL ,
  ρ ,
  ↠-step (pure-step (β vWR)) ↠-refl ,
  refl ,
  refl ,
  term-substitution-narrowingᶜ N⊒NL WR⊒VR′
sim-beta castCase@(cast+⊒ᵗ rᶜ p↦qᶜ t⊒ _ V⊒ƛ)
    vWL noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR
    with canonical-⇒ vWL (typed-term-narrowing-source-typingᶜ castCase)
sim-beta castCase@(cast+⊒ᵗ rᶜ p↦qᶜ t⊒ _ V⊒ƛ)
    vWL noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR
    | fv-ƛ ()
sim-beta {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ} {WL = WL} {NL = NL}
    {WR = WR} {VR = VR} {A′ = AR}
    castCase@(cast+⊒ᵗ {M = M} {q = pᵢ ↦ qᵢ} {r = pₒ ↦ qₒ}
      {s = cₛ ↦ dₛ}
      {A = Aₒ ⇒ Bₒ} {B = AR ⇒ BR} {C = AL ⇒ BL}
      {μ = μOuter} {η = ηCast}
      pᵢ↦qᵢᶜ pₒ↦qₒᶜ
      t⊒@(storesCast , _ , _ , _ , _ ,
        (cast-fun cₛ⊢L dₛ⊢L , cross (cₛʷL ↦ⁿʷ dₛⁿL)) ,
        (cast-fun cₛ⊢R dₛ⊢R , cross (cₛʷR ↦ⁿʷ dₛⁿR)))
      compᵏ
      V⊒ƛ)
    vWL noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR
    | fv-↦ {W = VF} {c = c} {d = d} vVF eq =
  let
    M≡VF : M ≡ VF
    M≡VF = ⟨⟩-term-injective eq

    noVF : No• VF
    noVF = no•-cast-inv (subst No• eq noWL)

    VF⊒ƛ :
      ΔL ∣ ΔR ∣ ρ ∣ []
        ⊢ VF ⊒ ƛ NL ∶ pᵢ ↦ qᵢ ⦂ AL ⇒ BL ⊒ AR ⇒ BR
    VF⊒ƛ =
      subst
        (λ F →
          ΔL ∣ ΔR ∣ ρ ∣ []
            ⊢ F ⊒ ƛ NL ∶ pᵢ ↦ qᵢ ⦂ AL ⇒ BL ⊒ AR ⇒ BR)
        M≡VF
        V⊒ƛ

    head-β↦ :
      (VF ⟨ c ↦ d ⟩) · WR —↠[ keep ∷ [] ]
        (VF · (WR ⟨ c ⟩)) ⟨ d ⟩
    head-β↦ = ↠-step (pure-step (β-↦ vVF vWR)) ↠-refl

    head-ready :
      WL · WR —↠[ keep ∷ [] ] (VF · (WR ⟨ c ⟩)) ⟨ d ⟩
    head-ready =
      subst
        (λ L → L · WR —↠[ keep ∷ [] ] (VF · (WR ⟨ c ⟩)) ⟨ d ⟩)
        (sym eq)
        head-β↦

    t⊒L = separated-left-coercionᵐ t⊒

    t⊒R = separated-right-coercionᵐ t⊒

    dₛ⊒L = dₛ⊢L , dₛⁿL

    dₛ⊒R = dₛ⊢R , dₛⁿR

    dₛ⊒ :
      ηCast ∣ ΔL ∣ ΔR ∣ ρ ⊢ dₛ ∶ Bₒ ⊒ BL
    dₛ⊒ =
      storesCast ,
      proj₁ (coercion-src-tgtᵐ (proj₁ dₛ⊒L)) ,
      proj₂ (coercion-src-tgtᵐ (proj₁ dₛ⊒L)) ,
      proj₁ (coercion-wfᵐ (leftStore-wf storesCast) (proj₁ dₛ⊒L)) ,
      proj₂ (coercion-wfᵐ (rightStore-wf storesCast) (proj₁ dₛ⊒R)) ,
      dₛ⊒L ,
      dₛ⊒R

    cast-eq : narrowing-dual t⊒ ≡ c ↦ d
    cast-eq = ⟨⟩-coercion-injective eq

    dₛ-dual-eq : narrowing-dual dₛ⊒ ≡ d
    dₛ-dual-eq =
      ↦-right-injective
        {c = proj₁ (dualʷ normalᵃ cₛʷL)}
        {c′ = c}
        {d = proj₁ (dualⁿ normalᵃ dₛⁿL)}
        {d′ = d}
        cast-eq

    t-dual-left :
      ηCast ∣ ΔL ∣ leftStore ρ
        ⊢ narrowing-dual t⊒ ∶ AL ⇒ BL ⊑ Aₒ ⇒ Bₒ
    t-dual-left =
      dualⁿ-flips-typingᵐ
        {μ = ηCast}
        {η = normalᵃ}
        {ν = ηCast}
        dualActionOk-normal
        dualStoreAt-normal
        (leftStore-wf storesCast)
        t⊒L

    t-dual-right :
      ηCast ∣ ΔR ∣ rightStore ρ
        ⊢ narrowing-dual t⊒ ∶ AL ⇒ BL ⊑ Aₒ ⇒ Bₒ
    t-dual-right =
      dualⁿ-flips-typingᵐ
        {μ = ηCast}
        {η = normalᵃ}
        {ν = ηCast}
        dualActionOk-normal
        dualStoreAt-normal
        (rightStore-wf storesCast)
        (proj₁ t⊒R , proj₂ t⊒L)

    c⊒L :
      ηCast ∣ ΔL ∣ leftStore ρ ⊢ c ∶ Aₒ ⊒ AL
    c⊒L =
      widen-fun-domainᵐ
        (subst
          (λ s → ηCast ∣ ΔL ∣ leftStore ρ
            ⊢ s ∶ AL ⇒ BL ⊑ Aₒ ⇒ Bₒ)
          cast-eq
          t-dual-left)

    c⊒R :
      ηCast ∣ ΔR ∣ rightStore ρ ⊢ c ∶ Aₒ ⊒ AL
    c⊒R =
      widen-fun-domainᵐ
        (subst
          (λ s → ηCast ∣ ΔR ∣ rightStore ρ
            ⊢ s ∶ AL ⇒ BL ⊑ Aₒ ⇒ Bₒ)
          cast-eq
          t-dual-right)

    c⊒ :
      ηCast ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ∶ Aₒ ⊒ AL
    c⊒ =
      storesCast ,
      proj₁ (coercion-src-tgtᵐ (proj₁ c⊒L)) ,
      proj₂ (coercion-src-tgtᵐ (proj₁ c⊒L)) ,
      proj₁ (coercion-wfᵐ (leftStore-wf storesCast) (proj₁ c⊒L)) ,
      proj₂ (coercion-wfᵐ (rightStore-wf storesCast) (proj₁ c⊒R)) ,
      c⊒L ,
      c⊒R

    comp-final :
      ΔL ∣ ΔR ∣ ρ
        ⊢ c ⨟ fun-narrow-domain-dualᶜ pᵢ↦qᵢᶜ
          ≈ fun-narrow-domain-dual p↦q-sim⊒ ∶ Aₒ ⊒ AR
    comp-final =
      cast-fun-comp-domain-dual compᵏ t⊒ cast-eq pᵢ↦qᵢᶜ
        p↦q-sim⊒

    WR-c⊒VR :
      ΔL ∣ ΔR ∣ ρ ∣ []
        ⊢ WR ⟨ c ⟩ ⊒ VR ∶ fun-narrow-domain-dualᶜ pᵢ↦qᵢᶜ
          ⦂ AL ⊒ AR
    WR-c⊒VR =
      cast-⊒ᵗ
        (fun-narrow-domain-dual-typingᶜ pᵢ↦qᵢᶜ)
        p-domainᶜ
        c⊒
        comp-final
        WR⊒VR

    χsA , WRA , ΔLA ,
      vWRA , noWRA , WR-c↠WRA , ΔLA≡ , ρA-corr ,
      leftA≡ , rightA≡ , pAᶜ , WRA⊒VR =
      catchup-lemmaˡ
        (ok-⟨⟩ (ok-no noWR))
        vVR
        WR-c⊒VR

    VFA⊒ƛ =
      advance-left-lambda-narrowing χsA ΔLA≡ ρA-corr VF⊒ƛ

    pᵢ↦qᵢ⊒A =
      left-change-fun-coercion-narrowing χsA
        ΔLA≡ ρA-corr pᵢ↦qᵢᶜ

    pAᶜ′ :
      ΔLA ∣ ΔR ∣ applyLeftChanges χsA ρ
        ⊢ fun-narrow-domain-dual (proj₁ pᵢ↦qᵢ⊒A)
          ∶ᶜ applyTys χsA AL ⊒ AR
    pAᶜ′ =
      subst
        (λ pd →
          ΔLA ∣ ΔR ∣ applyLeftChanges χsA ρ
            ⊢ pd ∶ᶜ applyTys χsA AL ⊒ AR)
        (sym (proj₂ pᵢ↦qᵢ⊒A))
        pAᶜ

    WRA⊒VR′ :
      ΔLA ∣ ΔR ∣ applyLeftChanges χsA ρ ∣ []
        ⊢ WRA ⊒ VR ∶ fun-narrow-domain-dual (proj₁ pᵢ↦qᵢ⊒A)
          ⦂ applyTys χsA AL ⊒ AR
    WRA⊒VR′ =
      subst
        (λ pd →
          ΔLA ∣ ΔR ∣ applyLeftChanges χsA ρ ∣ []
            ⊢ WRA ⊒ VR ∶ pd ⦂ applyTys χsA AL ⊒ AR)
        (sym (proj₂ pᵢ↦qᵢ⊒A))
        WRA⊒VR

    arg-ready :
      VF · (WR ⟨ c ⟩) —↠[ χsA ] applyTerms χsA VF · WRA
    arg-ready = ·₂-↠ vVF noVF WR-c↠WRA

    cast-arg-ready :
      (VF · (WR ⟨ c ⟩)) ⟨ d ⟩ —↠[ χsA ]
        (applyTerms χsA VF · WRA) ⟨ applyCoercions χsA d ⟩
    cast-arg-ready = cast-↠ {c = d} arg-ready

    prefix-ready :
      WL · WR —↠[ keep ∷ χsA ]
        (applyTerms χsA VF · WRA) ⟨ applyCoercions χsA d ⟩
    prefix-ready = ↠-trans head-ready cast-arg-ready

    rec =
      sim-beta
        VFA⊒ƛ
        (applyTerms-preserves-Value χsA vVF)
        (applyTerms-preserves-No• χsA noVF)
        (proj₁ pᵢ↦qᵢ⊒A)
        pAᶜ′
        WRA⊒VR′
        vWRA
        noWRA
        vVR

    χsT , N , ΔLT , ρT ,
      tail-red , ΔT≡ , ρT≡ , N⊒NL[VR] = rec

    tail-ready :
      (applyTerms χsA VF · WRA) ⟨ applyCoercions χsA d ⟩
        —↠[ χsT ]
      N ⟨ applyCoercions χsT (applyCoercions χsA d) ⟩
    tail-ready = cast-↠ {c = applyCoercions χsA d} tail-red

    source-steps :
      WL · WR —↠[ (keep ∷ χsA) ++ χsT ]
        N ⟨ applyCoercions χsT (applyCoercions χsA d) ⟩
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

    N-cast⊒ :
      ΔLT ∣ ΔR ∣ ρT ∣ []
        ⊢ N ⟨ applyCoercions χsT (applyCoercions χsA d) ⟩
          ⊒ NL [ VR ] ∶ applyCoercions ((keep ∷ χsA) ++ χsT) qₒ
          ⦂ applyTys ((keep ∷ χsA) ++ χsT) Bₒ ⊒ BR
    N-cast⊒ =
      sim-beta-cast+-result
        {ΔL = ΔL}
        {ΔR = ΔR}
        {ρ = ρ}
        {ΔLA = ΔLA}
        {ΔLT = ΔLT}
        {ρT = ρT}
        {NL = NL}
        {VR = VR}
        {N = N}
        {qᵢ = qᵢ}
        {qₒ = qₒ}
        {dₛ = dₛ}
        {d = d}
        {Bₒ = Bₒ}
        {BL = BL}
        {BR = BR}
        {μq = μOuter}
        {μd = ηCast}
        {χsA = χsA}
        {χsT = χsT}
        (fun-narrow-codomainᶜ pᵢ↦qᵢᶜ)
        (separated-fun-codomain pₒ↦qₒᶜ)
        dₛ⊒
        dₛ-dual-eq
        (cast-fun-comp-codomain compᵏ t⊒)
        ΔLA≡
        ρA-corr
        ΔT≡
        ρT≡
        N⊒NL[VR]
  in
  (keep ∷ χsA) ++ χsT ,
  N ⟨ applyCoercions χsT (applyCoercions χsA d) ⟩ ,
  ΔLT ,
  ρT ,
  source-steps ,
  ΔLT-total≡ ,
  ρT-total≡ ,
  N-cast⊒
sim-beta
    (cast+⊒ᵗ {q = id A}
      (_ , _ , _ , _ , _ , (cast-id _ _ , cross ()) , _)
      p↦qᶜ
      (storesCast , _ , _ , _ , _ ,
        (cast-fun _ _ , cross (_ ↦ⁿʷ _)) ,
        (cast-fun _ _ , cross (_ ↦ⁿʷ _)))
      _
      V⊒ƛ)
    vWL noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR
    | fv-↦ vVF eq
sim-beta
    (cast+⊒ᵗ {q = (G ？) ︔ g}
      (_ , _ , _ , _ , _ , (cast-seq () _ , _ ？︔ _) , _)
      p↦qᶜ
      (storesCast , _ , _ , _ , _ ,
        (cast-fun _ _ , cross (_ ↦ⁿʷ _)) ,
        (cast-fun _ _ , cross (_ ↦ⁿʷ _)))
      _
      V⊒ƛ)
    vWL noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR
    | fv-↦ vVF eq
sim-beta
    (cast+⊒ᵗ {q = g ︔ seal A α}
      (_ , _ , _ , _ , _ , (cast-seq _ () , _ ︔seal _) , _)
      p↦qᶜ
      (storesCast , _ , _ , _ , _ ,
        (cast-fun _ _ , cross (_ ↦ⁿʷ _)) ,
        (cast-fun _ _ , cross (_ ↦ⁿʷ _)))
      _
      V⊒ƛ)
    vWL noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR
    | fv-↦ vVF eq
sim-beta
    (cast-⊒ᵗ {s = id A} p↦qᶜ rᶜ t⊒ _ V⊒ƛ)
    (vV ⟨ () ⟩)
sim-beta
    (cast-⊒ᵗ {s = c ︔ d} p↦qᶜ rᶜ t⊒ _ V⊒ƛ)
    (vV ⟨ () ⟩)
sim-beta {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ} {NL = NL}
    {WR = WR} {VR = VR}
    (cast-⊒ᵗ {M = V} {q = pₒ ↦ qₒ} {r = pᵢ ↦ qᵢ}
      {s = c ↦ d} {A = AL ⇒ BL}
      {B = AR ⇒ BR} {C = Aₒ ⇒ Bₒ} {η = ηCast}
      (storesOuter , _ , _ , wf⇒ hAₒ hBₒ , wf⇒ hAR hBR ,
        (cast-fun _ qₒ⊢L , cross (_ ↦ⁿʷ qₒⁿL)) ,
        (cast-fun _ qₒ⊢R , cross (_ ↦ⁿʷ qₒⁿR)))
      rInner@(storesInner , _ , _ , wf⇒ hAL hBL , _ ,
        (cast-fun pᵢ⊢L _ , cross (pᵢʷL ↦ⁿʷ _)) ,
        (cast-fun pᵢ⊢R _ , cross (pᵢʷR ↦ⁿʷ _)))
      s⊒ᵗᵘᵖ@(storesCast , _ , _ , _ , wf⇒ hAₒʳ hBₒʳ ,
        (cast-fun c⊢L d⊢L , cross (cʷL ↦ⁿʷ dⁿL)) ,
        (cast-fun c⊢R d⊢R , cross (cʷR ↦ⁿʷ dⁿR)))
      compᵏ
      V⊒ƛ)
    (vV ⟨ i ⟩)
    (no•-⟨⟩ noV) p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR =
  let
    head-β↦ :
      (V ⟨ c ↦ d ⟩) · WR —↠[ keep ∷ [] ]
        (V · (WR ⟨ c ⟩)) ⟨ d ⟩
    head-β↦ = ↠-step (pure-step (β-↦ vV vWR)) ↠-refl

    qₒ⊒ :
      tag-or-idᵈ ∣ ΔL ∣ ΔR ∣ ρ ⊢ qₒ ∶ Bₒ ⊒ BR
    qₒ⊒ =
      storesOuter ,
      proj₁ (coercion-src-tgtᵐ qₒ⊢L) ,
      proj₂ (coercion-src-tgtᵐ qₒ⊢L) ,
      hBₒ ,
      hBR ,
      (qₒ⊢L , qₒⁿL) ,
      (qₒ⊢R , qₒⁿR)

    d⊒ :
      ηCast ∣ ΔL ∣ ΔR ∣ ρ ⊢ d ∶ BL ⊒ Bₒ
    d⊒ =
      storesCast ,
      proj₁ (coercion-src-tgtᵐ d⊢L) ,
      proj₂ (coercion-src-tgtᵐ d⊢L) ,
      hBL ,
      hBₒʳ ,
      (d⊢L , dⁿL) ,
      (d⊢R , dⁿR)

    pᵢ-domain⊒ :
      _ ∣ ΔL ∣ ΔR ∣ ρ
        ⊢ fun-narrow-domain-dual rInner ∶ AL ⊒ AR
    pᵢ-domain⊒ =
      let
        pᵢᵈ⊒L =
          proj₁
            (dualʷ-flips-typingᵐ
              dualActionOk-normal
              dualStoreAt-normal
              (leftStore-wf storesInner)
              (pᵢ⊢L , pᵢʷL)) ,
          proj₂ (dualʷ normalᵃ pᵢʷL)

        pᵢᵈ⊒R =
          proj₁
            (dualʷ-flips-typingᵐ
              dualActionOk-normal
              dualStoreAt-normal
              (rightStore-wf storesInner)
              (pᵢ⊢R , pᵢʷR)) ,
          proj₂ (dualʷ normalᵃ pᵢʷR)
      in
      storesInner ,
      proj₁ (coercion-src-tgtᵐ (proj₁ pᵢᵈ⊒L)) ,
      proj₂ (coercion-src-tgtᵐ (proj₁ pᵢᵈ⊒L)) ,
      hAL ,
      hAR ,
      pᵢᵈ⊒L ,
      subst
        (λ p → _ ∣ ΔR ∣ rightStore ρ ⊢ p ∶ AL ⊒ AR)
        (dualʷ-raw-determined normalᵃ pᵢʷR pᵢʷL)
        pᵢᵈ⊒R

    c-dual⊒ :
      ηCast ∣ ΔL ∣ ΔR ∣ ρ
        ⊢ proj₁ (dualʷ normalᵃ cʷL) ∶ AL ⊒ Aₒ
    c-dual⊒ =
      let
        cᵈ⊒L =
          proj₁
            (dualʷ-flips-typingᵐ
              dualActionOk-normal
              dualStoreAt-normal
              (leftStore-wf storesCast)
              (c⊢L , cʷL)) ,
          proj₂ (dualʷ normalᵃ cʷL)

        cᵈ⊒R =
          proj₁
            (dualʷ-flips-typingᵐ
              dualActionOk-normal
              dualStoreAt-normal
              (rightStore-wf storesCast)
              (c⊢R , cʷR)) ,
          proj₂ (dualʷ normalᵃ cʷR)
      in
      storesCast ,
      proj₁ (coercion-src-tgtᵐ (proj₁ cᵈ⊒L)) ,
      proj₂ (coercion-src-tgtᵐ (proj₁ cᵈ⊒L)) ,
      hAL ,
      hAₒʳ ,
      cᵈ⊒L ,
      subst
        (λ d → ηCast ∣ ΔR ∣ rightStore ρ ⊢ d ∶ AL ⊒ Aₒ)
        (dualʷ-raw-determined normalᵃ cʷR cʷL)
        cᵈ⊒R

    c-dual-eq :
      narrowing-dual c-dual⊒ ≡ c
    c-dual-eq = dualʷ-involutive-raw cʷL

    WR-c⊒VR :
      ΔL ∣ ΔR ∣ ρ ∣ []
        ⊢ WR ⟨ c ⟩ ⊒ VR ∶ fun-narrow-domain-dual rInner
          ⦂ AL ⊒ AR
    WR-c⊒VR =
      subst
        (λ s →
          ΔL ∣ ΔR ∣ ρ ∣ []
            ⊢ WR ⟨ s ⟩ ⊒ VR ∶ fun-narrow-domain-dual rInner
              ⦂ AL ⊒ AR)
        c-dual-eq
        (cast+⊒ᵗ p-domainᶜ pᵢ-domain⊒ c-dual⊒
          (cast-fun-comp-domain-dual₂ compᵏ s⊒ᵗᵘᵖ p↦q-sim⊒
            rInner)
          WR⊒VR)

    χsA , WRA , ΔLA ,
      vWRA , noWRA , WR-c↠WRA , ΔLA≡ , ρA-corr ,
      leftA≡ , rightA≡ , pAᶜ , WRA⊒VRraw =
      catchup-lemmaˡ
        (ok-⟨⟩ (ok-no noWR))
        vVR
        WR-c⊒VR

    VFA⊒ƛ =
      advance-left-lambda-narrowing χsA ΔLA≡ ρA-corr V⊒ƛ

    WRA⊒VR :
      ΔLA ∣ ΔR ∣ applyLeftChanges χsA ρ ∣ []
        ⊢ WRA ⊒ VR ∶ applyCoercions χsA
            (fun-narrow-domain-dual rInner)
          ⦂ applyTys χsA AL ⊒ AR
    WRA⊒VR = WRA⊒VRraw

    arg-ready :
      V · (WR ⟨ c ⟩) —↠[ χsA ] applyTerms χsA V · WRA
    arg-ready = ·₂-↠ vV noV WR-c↠WRA

    cast-arg-ready :
      (V · (WR ⟨ c ⟩)) ⟨ d ⟩ —↠[ χsA ]
        (applyTerms χsA V · WRA) ⟨ applyCoercions χsA d ⟩
    cast-arg-ready = cast-↠ {c = d} arg-ready

    pᵢ↦qᵢ⊒A =
      left-change-fun-coercion-narrowing χsA
        ΔLA≡ ρA-corr rInner

    pAᶜ′ :
      ΔLA ∣ ΔR ∣ applyLeftChanges χsA ρ
        ⊢ fun-narrow-domain-dual (proj₁ pᵢ↦qᵢ⊒A)
          ∶ᶜ applyTys χsA AL ⊒ AR
    pAᶜ′ =
      subst
        (λ pd →
          ΔLA ∣ ΔR ∣ applyLeftChanges χsA ρ
            ⊢ pd ∶ᶜ applyTys χsA AL ⊒ AR)
        (sym (proj₂ pᵢ↦qᵢ⊒A))
        pAᶜ

    WRA⊒VR′ :
      ΔLA ∣ ΔR ∣ applyLeftChanges χsA ρ ∣ []
        ⊢ WRA ⊒ VR ∶ fun-narrow-domain-dual (proj₁ pᵢ↦qᵢ⊒A)
          ⦂ applyTys χsA AL ⊒ AR
    WRA⊒VR′ =
      subst
        (λ pd →
          ΔLA ∣ ΔR ∣ applyLeftChanges χsA ρ ∣ []
            ⊢ WRA ⊒ VR ∶ pd ⦂ applyTys χsA AL ⊒ AR)
        (sym (proj₂ pᵢ↦qᵢ⊒A))
        WRA⊒VR

    rec =
      sim-beta
        VFA⊒ƛ
        (applyTerms-preserves-Value χsA vV)
        (applyTerms-preserves-No• χsA noV)
        (proj₁ pᵢ↦qᵢ⊒A)
        pAᶜ′
        WRA⊒VR′
        vWRA
        noWRA
        vVR
  in
  sim-beta-cast-tail
    {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M₀ = (V ⟨ c ↦ d ⟩) · WR}
    {NL = NL} {V = V} {WRA = WRA} {VR = VR}
    {qᵢ = qᵢ} {qₒ = qₒ} {d = d} {Bₒ = Bₒ}
    {BL = BL} {BR = BR} {D₁ = BL} {D₂ = Bₒ}
    {μq = tag-or-idᵈ} {μd = ηCast} {χsA = χsA} {ΔLA = ΔLA}
    (λ χsT N → N ⟨ applyCoercions χsT (applyCoercions χsA d) ⟩)
    (↠-trans head-β↦ cast-arg-ready)
    (λ tail-red → cast-↠ {c = applyCoercions χsA d} tail-red)
    qₒ⊒
    d⊒
    (cast-fun-comp-codomain compᵏ s⊒ᵗᵘᵖ)
    ΔLA≡
    ρA-corr
    (λ _ N⊒NL[VR] qₒ⊒Tρ d⊒Tρ compTρ →
      let μN , nᶜ = typed-term-narrowing-coercion N⊒NL[VR] in
      cast-⊒ᵗ {μ = μN} {η = ηCast}
        qₒ⊒Tρ
        nᶜ
        d⊒Tρ
        compTρ
        N⊒NL[VR])
    rec
sim-beta castCase@(cast-⊒ᵗ {s = `∀ c}
      p↦qᶜ rᶜ t⊒ _ V⊒ƛ)
    (vV ⟨ `∀ c ⟩) (no•-⟨⟩ noV) p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR
    with canonical-⇒ (vV ⟨ `∀ c ⟩)
           (typed-term-narrowing-source-typingᶜ castCase)
sim-beta castCase@(cast-⊒ᵗ {s = `∀ c}
      p↦qᶜ rᶜ t⊒ _ V⊒ƛ)
    (vV ⟨ `∀ c ⟩) (no•-⟨⟩ noV) p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR
    | fv-ƛ ()
sim-beta castCase@(cast-⊒ᵗ {s = `∀ c}
      p↦qᶜ rᶜ t⊒ _ V⊒ƛ)
    (vV ⟨ `∀ c ⟩) (no•-⟨⟩ noV) p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR
    | fv-↦ vW ()
sim-beta castCase@(cast-⊒ᵗ {s = G !}
      p↦qᶜ rᶜ t⊒ _ V⊒ƛ)
    (vV ⟨ G ! ⟩) (no•-⟨⟩ noV) p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR
    with canonical-⇒ (vV ⟨ G ! ⟩)
           (typed-term-narrowing-source-typingᶜ castCase)
sim-beta castCase@(cast-⊒ᵗ {s = G !}
      p↦qᶜ rᶜ t⊒ _ V⊒ƛ)
    (vV ⟨ G ! ⟩) (no•-⟨⟩ noV) p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR
    | fv-ƛ ()
sim-beta castCase@(cast-⊒ᵗ {s = G !}
      p↦qᶜ rᶜ t⊒ _ V⊒ƛ)
    (vV ⟨ G ! ⟩) (no•-⟨⟩ noV) p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR
    | fv-↦ vW ()
sim-beta
    (cast-⊒ᵗ {s = G ？} p↦qᶜ rᶜ t⊒ _ V⊒ƛ)
    (vV ⟨ () ⟩)
sim-beta castCase@(cast-⊒ᵗ {s = seal A α}
      p↦qᶜ rᶜ t⊒ _ V⊒ƛ)
    (vV ⟨ seal A α ⟩) (no•-⟨⟩ noV) p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR
    with canonical-⇒ (vV ⟨ seal A α ⟩)
           (typed-term-narrowing-source-typingᶜ castCase)
sim-beta castCase@(cast-⊒ᵗ {s = seal A α}
      p↦qᶜ rᶜ t⊒ _ V⊒ƛ)
    (vV ⟨ seal A α ⟩) (no•-⟨⟩ noV) p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR
    | fv-ƛ ()
sim-beta castCase@(cast-⊒ᵗ {s = seal A α}
      p↦qᶜ rᶜ t⊒ _ V⊒ƛ)
    (vV ⟨ seal A α ⟩) (no•-⟨⟩ noV) p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR
    | fv-↦ vW ()
sim-beta
    (cast-⊒ᵗ {s = unseal α A}
      p↦qᶜ rᶜ t⊒ _ V⊒ƛ)
    (vV ⟨ () ⟩)
sim-beta castCase@(cast-⊒ᵗ {s = gen A c}
      p↦qᶜ rᶜ t⊒ _ V⊒ƛ)
    (vV ⟨ gen A c ⟩) (no•-⟨⟩ noV) p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR
    with canonical-⇒ (vV ⟨ gen A c ⟩)
           (typed-term-narrowing-source-typingᶜ castCase)
sim-beta castCase@(cast-⊒ᵗ {s = gen A c}
      p↦qᶜ rᶜ t⊒ _ V⊒ƛ)
    (vV ⟨ gen A c ⟩) (no•-⟨⟩ noV) p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR
    | fv-ƛ ()
sim-beta castCase@(cast-⊒ᵗ {s = gen A c}
      p↦qᶜ rᶜ t⊒ _ V⊒ƛ)
    (vV ⟨ gen A c ⟩) (no•-⟨⟩ noV) p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR
    | fv-↦ vW ()
sim-beta
    (cast-⊒ᵗ {s = inst A c}
      p↦qᶜ rᶜ t⊒ _ V⊒ƛ)
    (vV ⟨ () ⟩)
