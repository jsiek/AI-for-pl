module alt.probes.ProgressGaps where

-- File Charter:
--   * Checks the former stranded-ν gap as a positive reduction trace.
--   * The region first floats through reveal, strict conceal/reveal then fires,
--     and the persistent allocation remains around the final constant.
--   * Records three remaining progress obstructions as typed closed terms with
--     checked proofs that `Progress` is impossible.
--   * Checks both outward-injection laws as positive reduction traces,
--     including a variable projection that reaches ordinary tag blame.
--   * Checks the former region-Λ type-application gap as a positive trace:
--     β-Λ accepts its ν-prefixed Result body and guarded floating continues.

open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
import Data.Vec.Base as Vec

open import Types
open import TermCtx
open import Consistency
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction
open import alt.ThetaTermSubst using (rep?-bracket; rep?-here)
open import alt.ThetaProgress using
  (CanonicalFun; Progress; step; done; failed)

infix 2 _⊢_—↠_

data _⊢_—↠_ {Θ Δ σ} (Ψ : TyEnv Θ Δ σ) :
    Term Θ Δ → Term Θ Δ → Set where
  ↠-refl : ∀ {M} → Ψ ⊢ M —↠ M
  ↠-step : ∀ {M N P}
    → Ψ ⊢ M —→ N
    → Ψ ⊢ N —↠ P
    → Ψ ⊢ M —↠ P

infix 3 _∎
pattern _∎ M = ↠-refl {M = M}

infixr 2 _—→⟨_⟩_
pattern _—→⟨_⟩_ M M→N N↠P = ↠-step {M = M} M→N N↠P

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

ℕ⇒ℕ : ∀ {Δ} → Ty Δ
ℕ⇒ℕ = ℕᵗ ⇒ ℕᵗ

baseEnv : TyEnv 1 zero Vec.[]
baseEnv = ∅ ,:= ℕ⇒ℕ

no-live-anchor : ∀ {Θ} {α : TyVar Θ} → α ∉ᵛ Vec.[]
no-live-anchor ()

crossedEnv : TyEnv 1 1 (just zero Vec.∷ Vec.[])
crossedEnv = baseEnv ,begin[ zero ≔ zero ]⟨ no-live-anchor ⟩

regionEnv : TyEnv 2 1 (just (suc zero) Vec.∷ Vec.[])
regionEnv = crossedEnv ,:= ℕᵗ

identity : ∀ {Θ} → Term Θ zero
identity = ƛ ℕᵗ ˙ ` zero

sealedTerm : Term 2 1
sealedTerm = identity ↓[ zero ≔ suc zero ] seal

stranded : Term 1 1
stranded = ν[ ℕᵗ ] sealedTerm

stuckFun : Term 1 zero
stuckFun = stranded ↑[ zero ≔ zero ] unseal

stuck : Term 1 zero
stuck = stuckFun · $ (κℕ zero)

identity-typed : regionEnv ,end[ zero ] ∣ [] ⊢ identity ⦂ ℕ⇒ℕ
identity-typed = ⊢ƛ (⊢` Z)

sealed-typed : regionEnv ∣ [] ⊢ sealedTerm ⦂ ＇ zero
sealed-typed = ⊢conceal refl refl ⊢seal identity-typed

stranded-typed : crossedEnv ∣ [] ⊢ stranded ⦂ ＇ zero
stranded-typed = ⊢ν sealed-typed

stuckFun-typed : baseEnv ∣ [] ⊢ stuckFun ⦂ ℕ⇒ℕ
stuckFun-typed = ⊢reveal {fresh = no-live-anchor}
  (rep?-here {Ψ = baseEnv}) ⊢unseal stranded-typed

stuck-typed : baseEnv ∣ [] ⊢ stuck ⦂ ℕᵗ
stuck-typed = ⊢· stuckFun-typed (⊢$ (κℕ zero))

identity-value : Value (identity {Θ = 2})
identity-value = ƛ ℕᵗ ˙ ` zero

sealed-value : Value sealedTerm
sealed-value = identity-value ↓[ zero ≔ suc zero ] sealᵥ

sealed-result : Result sealedTerm
sealed-result = result-val sealed-value

stranded-result : Result stranded
stranded-result = result-ν sealed-result

after-reveal-float : Term 1 zero
after-reveal-float =
  (ν[ ℕᵗ ] (sealedTerm ↑[ zero ≔ suc zero ] unseal))
    · $ (κℕ zero)

after-cancel : Term 1 zero
after-cancel = (ν[ ℕᵗ ] identity) · $ (κℕ zero)

after-application-float : Term 1 zero
after-application-float =
  ν[ ℕᵗ ] (identity · $ (κℕ zero))

endpoint : Term 1 zero
endpoint = ν[ ℕᵗ ] ($ (κℕ zero))

stranded-reduction : baseEnv ⊢ stuck —↠ endpoint
stranded-reduction =
    stuck
  —→⟨ ξ-·₁ (float-reveal refl stranded-result) ⟩
    after-reveal-float
  —→⟨ ξ-·₁ (ξ-ν (conceal-reveal (result-val identity-value))) ⟩
    after-cancel
  —→⟨ float-·₁ (result-ν (result-val identity-value)) ⟩
    after-application-float
  —→⟨ ξ-ν (β ($ (κℕ zero))) ⟩
    endpoint
  ∎

stranded-progress : Progress baseEnv stuck
stranded-progress = step (ξ-·₁ (float-reveal refl stranded-result))

concealFloatSource : Term 1 1
concealFloatSource =
  (ν[ ℕᵗ ] $ (κℕ zero)) ↓[ zero ≔ zero ] id↓

concealFloatMiddle : Term 1 1
concealFloatMiddle =
  ν[ ℕᵗ ] (($ (κℕ zero)) ↓[ zero ≔ suc zero ] id↓)

concealFloatTarget : Term 1 1
concealFloatTarget = ν[ ℕᵗ ] $ (κℕ zero)

concealFloatSource-typed :
  crossedEnv ∣ [] ⊢ concealFloatSource ⦂ ℕᵗ
concealFloatSource-typed = ⊢conceal refl
  (rep?-bracket {Ψ = baseEnv} {Y = zero} {a = zero} {q = zero}
    no-live-anchor (rep?-here {Ψ = baseEnv} {A = ℕ⇒ℕ}))
  (⊢id↓ (‵ `ℕ)) (⊢ν (⊢$ (κℕ zero)))

conceal-float-reduction :
  crossedEnv ⊢ concealFloatSource —↠ concealFloatTarget
conceal-float-reduction =
    concealFloatSource
  —→⟨ float-conceal (result-ν (result-val ($ (κℕ zero)))) ⟩
    concealFloatMiddle
  —→⟨ ξ-ν (id-conceal {κ = κℕ zero}) ⟩
    concealFloatTarget
  ∎

concealFloatSource-progress : Progress crossedEnv concealFloatSource
concealFloatSource-progress =
  step (float-conceal (result-ν (result-val ($ (κℕ zero)))))

------------------------------------------------------------------------
-- Resolved gap: β-Λ accepts a ν-prefixed Result body
------------------------------------------------------------------------

regionLambdaEnv : TyEnv zero zero Vec.[]
regionLambdaEnv = ∅

regionLambdaBody : Term zero 1
regionLambdaBody = ν[ ℕᵗ ] $ (κℕ zero)

regionLambdaRedex : Term zero zero
regionLambdaRedex = (Λ regionLambdaBody) ⦂∀ ℕᵗ [ ℕᵗ ]

regionLambdaContractum : Term zero zero
regionLambdaContractum =
  ν[ ℕᵗ ]
    (shiftᶿ regionLambdaBody ↑[ zero ≔ zero ] id↑)

regionLambdaAfterFloat : Term zero zero
regionLambdaAfterFloat =
  ν[ ℕᵗ ]
    (ν[ ℕᵗ ] (($ (κℕ zero)) ↑[ zero ≔ suc zero ] id↑))

regionLambdaEndpoint : Term zero zero
regionLambdaEndpoint = ν[ ℕᵗ ] (ν[ ℕᵗ ] $ (κℕ zero))

regionLambdaBody-result : Result regionLambdaBody
regionLambdaBody-result = result-ν (result-val ($ (κℕ zero)))

regionLambdaShiftedBody-result : Result (shiftᶿ regionLambdaBody)
regionLambdaShiftedBody-result =
  result-ν (result-val ($ (κℕ zero)))

regionLambdaRedex-typed :
  regionLambdaEnv ∣ [] ⊢ regionLambdaRedex ⦂ ℕᵗ
regionLambdaRedex-typed =
  ⊢⦂∀
    (⊢Λ (body-ν (body-result (result-val ($ (κℕ zero)))))
      (⊢ν (⊢$ (κℕ zero))))

regionLambda-trace :
  regionLambdaEnv ⊢ regionLambdaRedex —↠ regionLambdaEndpoint
regionLambda-trace =
    regionLambdaRedex
  —→⟨ β-Λ regionLambdaBody-result ⟩
    regionLambdaContractum
  —→⟨ ξ-ν (float-reveal refl regionLambdaShiftedBody-result) ⟩
    regionLambdaAfterFloat
  —→⟨ ξ-ν (ξ-ν id-reveal) ⟩
    regionLambdaEndpoint
  ∎

regionLambdaEndpoint-result : Result regionLambdaEndpoint
regionLambdaEndpoint-result =
  result-ν (result-ν (result-val ($ (κℕ zero))))

regionLambdaRedex-progress : Progress regionLambdaEnv regionLambdaRedex
regionLambdaRedex-progress = step (β-Λ regionLambdaBody-result)

------------------------------------------------------------------------
-- Remaining gap 1: an unfloatable adapter at a base delimiter
------------------------------------------------------------------------

dependentRegionEnv : TyEnv 2 1 (just (suc zero) Vec.∷ Vec.[])
dependentRegionEnv = crossedEnv ,:= ＇ zero

baseRegionBody : Term 2 1
baseRegionBody = $ (κℕ zero)

baseRegion : Term 1 1
baseRegion = ν[ ＇ zero ] baseRegionBody

baseAdapter : Term 1 zero
baseAdapter = baseRegion ↑[ zero ≔ zero ] id↑

baseAdapterGap : Term 1 zero
baseAdapterGap = baseAdapter ⊕[ addℕ ] $ (κℕ zero)

baseRegionBody-typed : dependentRegionEnv ∣ [] ⊢ baseRegionBody ⦂ ℕᵗ
baseRegionBody-typed = ⊢$ (κℕ zero)

baseRegion-typed : crossedEnv ∣ [] ⊢ baseRegion ⦂ ℕᵗ
baseRegion-typed = ⊢ν baseRegionBody-typed

baseAdapter-typed : baseEnv ∣ [] ⊢ baseAdapter ⦂ ℕᵗ
baseAdapter-typed = ⊢reveal {fresh = no-live-anchor}
  (rep?-here {Ψ = baseEnv} {A = ℕ⇒ℕ})
  (⊢id↑ (‵ `ℕ)) baseRegion-typed

baseAdapterGap-typed : baseEnv ∣ [] ⊢ baseAdapterGap ⦂ ℕᵗ
baseAdapterGap-typed =
  ⊢⊕ addℕ baseAdapter-typed (⊢$ (κℕ zero))

baseRegionBody-value : Value baseRegionBody
baseRegionBody-value = $ (κℕ zero)

baseRegion-result : Result baseRegion
baseRegion-result = result-ν (result-val baseRegionBody-value)

baseAdapter-value : Value baseAdapter
baseAdapter-value = baseRegion-result ↑[ zero ≔ zero ]
  adapter-region (result-val baseRegionBody-value) var-∈

baseAdapter-no-step : ∀ {M′} → ¬ (baseEnv ⊢ baseAdapter —→ M′)
baseAdapter-no-step = value-no-step baseAdapter-value

baseAdapterGap-no-step : ∀ {M′}
  → ¬ (baseEnv ⊢ baseAdapterGap —→ M′)
baseAdapterGap-no-step (ξ-⊕₁ reduction) =
  baseAdapter-no-step reduction
baseAdapterGap-no-step (ξ-⊕₂ Vᵥ reduction) =
  value-no-step ($ (κℕ zero)) reduction

baseAdapterGap-not-result : ¬ Result baseAdapterGap
baseAdapterGap-not-result (result-val ())

baseAdapterGap-no-progress : ¬ Progress baseEnv baseAdapterGap
baseAdapterGap-no-progress (step reduction) =
  baseAdapterGap-no-step reduction
baseAdapterGap-no-progress (done result) =
  baseAdapterGap-not-result result

baseAdapter-gap-witness :
  (baseEnv ∣ [] ⊢ baseAdapterGap ⦂ ℕᵗ)
  × ¬ Progress baseEnv baseAdapterGap
baseAdapter-gap-witness =
  baseAdapterGap-typed , baseAdapterGap-no-progress

------------------------------------------------------------------------
-- Resolved gap: strengthenable injections commute out of identity reveal
------------------------------------------------------------------------

taggedInReveal : Term 1 1
taggedInReveal =
  ($ (κℕ zero)) ⟨ (id {μ = idᶜ} (‵ `ℕ)) ! ⟩

starReveal : Term 1 zero
starReveal = taggedInReveal ↑[ zero ≔ zero ] id↑

starRevealMerge : Term 1 zero
starRevealMerge = starReveal ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

taggedInReveal-typed : crossedEnv ∣ [] ⊢ taggedInReveal ⦂ ★
taggedInReveal-typed =
  ⊢⟨⟩ (⊢$ (κℕ zero)) ((id {μ = idᶜ} (‵ `ℕ)) !)

starReveal-typed : baseEnv ∣ [] ⊢ starReveal ⦂ ★
starReveal-typed = ⊢reveal {fresh = no-live-anchor}
  (rep?-here {Ψ = baseEnv} {A = ℕ⇒ℕ})
  (⊢id↑ ★) taggedInReveal-typed

starRevealMerge-typed : baseEnv ∣ [] ⊢ starRevealMerge ⦂ ℕᵗ
starRevealMerge-typed =
  ⊢⟨⟩ starReveal-typed (？ (id {μ = idᶜ} (‵ `ℕ)))

taggedInReveal-value : Value taggedInReveal
taggedInReveal-value = ($ (κℕ zero)) 《 inj 》

starRevealAfterInject : Term 1 zero
starRevealAfterInject =
  (($ (κℕ zero))
    ↑[ zero ≔ zero ] expand↑ (ℕᵗ {Δ = 1}) id↑)
    ⟨ strengthenInjection {Δ = zero} {Y = zero} {μ = idᶜ}
      (‵ `ℕ) ι∼★ refl ⟩

starRevealMergeAfterInject : Term 1 zero
starRevealMergeAfterInject =
  starRevealAfterInject ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

taggedOutsideReveal : Term 1 zero
taggedOutsideReveal =
  ($ (κℕ zero))
    ⟨ strengthenInjection {Δ = zero} {Y = zero} {μ = idᶜ}
      (‵ `ℕ) ι∼★ refl ⟩

starRevealMergeAfterReveal : Term 1 zero
starRevealMergeAfterReveal =
  taggedOutsideReveal ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

starRevealMerge-gap-witness :
  baseEnv ⊢ starRevealMerge —↠ $ (κℕ zero)
starRevealMerge-gap-witness =
    starRevealMerge
  —→⟨ ξ-⟨⟩ (inject-reveal refl ($ (κℕ zero))) ⟩
    starRevealMergeAfterInject
  —→⟨ ξ-⟨⟩ (ξ-⟨⟩ id-reveal) ⟩
    starRevealMergeAfterReveal
  —→⟨ tag-untag ($ (κℕ zero)) ⟩
    $ (κℕ zero)
  ∎

starRevealMerge-progress : Progress baseEnv starRevealMerge
starRevealMerge-progress =
  step (ξ-⟨⟩ (inject-reveal refl ($ (κℕ zero))))

------------------------------------------------------------------------
-- Resolved gap: injections commute outward through identity conceal
------------------------------------------------------------------------

taggedInConceal : Term 1 zero
taggedInConceal =
  ($ (κℕ zero)) ⟨ (id {μ = idᶜ} (‵ `ℕ)) ! ⟩

starConceal : Term 1 1
starConceal = taggedInConceal ↓[ zero ≔ zero ] id↓

starConcealMerge : Term 1 1
starConcealMerge = starConceal ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

taggedInConceal-typed :
  crossedEnv ,end[ zero ] ∣ [] ⊢ taggedInConceal ⦂ ★
taggedInConceal-typed =
  ⊢⟨⟩ (⊢$ (κℕ zero)) ((id {μ = idᶜ} (‵ `ℕ)) !)

ended-base-rep :
  rep? (crossedEnv ,end[ zero ]) zero ≡ just ℕ⇒ℕ
ended-base-rep = rep?-bracket {Ψ = baseEnv} {Y = zero} {a = zero}
  {q = zero}
  no-live-anchor (rep?-here {Ψ = baseEnv} {A = ℕ⇒ℕ})

starConceal-typed : crossedEnv ∣ [] ⊢ starConceal ⦂ ★
starConceal-typed = ⊢conceal refl ended-base-rep
  (⊢id↓ ★) taggedInConceal-typed

starConcealMerge-typed :
  crossedEnv ∣ [] ⊢ starConcealMerge ⦂ ℕᵗ
starConcealMerge-typed =
  ⊢⟨⟩ starConceal-typed (？ (id {μ = idᶜ} (‵ `ℕ)))

taggedInConceal-value : Value taggedInConceal
taggedInConceal-value = ($ (κℕ zero)) 《 inj 》

starConcealAfterInject : Term 1 1
starConcealAfterInject =
  (($ (κℕ zero))
    ↓[ zero ≔ zero ] expand↓ (wkᵗ (zero {n = zero}) ℕᵗ) id↓)
    ⟨ weakenInjection {μ = idᶜ} zero (‵ `ℕ) ι∼★ ⟩

starConcealMergeAfterInject : Term 1 1
starConcealMergeAfterInject =
  starConcealAfterInject ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

taggedOutsideConceal : Term 1 1
taggedOutsideConceal =
  ($ (κℕ zero))
    ⟨ weakenInjection {μ = idᶜ} zero (‵ `ℕ) ι∼★ ⟩

starConcealMergeAfterConceal : Term 1 1
starConcealMergeAfterConceal =
  taggedOutsideConceal ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

starConcealMerge-gap-witness :
  crossedEnv ⊢ starConcealMerge —↠ $ (κℕ zero)
starConcealMerge-gap-witness =
    starConcealMerge
  —→⟨ ξ-⟨⟩ (inject-conceal ($ (κℕ zero))) ⟩
    starConcealMergeAfterInject
  —→⟨ ξ-⟨⟩ (ξ-⟨⟩ id-conceal) ⟩
    starConcealMergeAfterConceal
  —→⟨ tag-untag ($ (κℕ zero)) ⟩
    $ (κℕ zero)
  ∎

starConcealMerge-progress : Progress crossedEnv starConcealMerge
starConcealMerge-progress =
  step (ξ-⟨⟩ (inject-conceal ($ (κℕ zero))))

varProjectionEnv : Env∼ 1
varProjectionEnv zero = ★∼X

starConcealVarMerge : Term 1 1
starConcealVarMerge =
  starConceal
    ⟨ ？ (id {μ = varProjectionEnv} (＇ zero)) ⟩

starConcealVarMerge-typed :
  crossedEnv ∣ [] ⊢ starConcealVarMerge ⦂ ＇ zero
starConcealVarMerge-typed =
  ⊢⟨⟩ starConceal-typed
    (？ (id {μ = varProjectionEnv} (＇ zero)))

starConcealVarMergeAfterInject : Term 1 1
starConcealVarMergeAfterInject =
  starConcealAfterInject
    ⟨ ？ (id {μ = varProjectionEnv} (＇ zero)) ⟩

starConcealVarMergeAfterConceal : Term 1 1
starConcealVarMergeAfterConceal =
  taggedOutsideConceal
    ⟨ ？ (id {μ = varProjectionEnv} (＇ zero)) ⟩

starConcealVarMerge-trace :
  crossedEnv ⊢ starConcealVarMerge —↠ blame
starConcealVarMerge-trace =
    starConcealVarMerge
  —→⟨ ξ-⟨⟩ (inject-conceal ($ (κℕ zero))) ⟩
    starConcealVarMergeAfterInject
  —→⟨ ξ-⟨⟩ (ξ-⟨⟩ id-conceal) ⟩
    starConcealVarMergeAfterConceal
  —→⟨ tag-untag-bad ($ (κℕ zero)) (λ ()) ⟩
    blame
  ∎

------------------------------------------------------------------------
-- Remaining gap 2: ∀ reveal cannot merge through an inert ∀ cast
------------------------------------------------------------------------

∀ℕ : ∀ {Δ} → Ty Δ
∀ℕ = `∀ (‵ `ℕ)

polyInReveal : Term 1 1
polyInReveal = Λ ($ (κℕ zero))

allCastInReveal : Term 1 1
allCastInReveal = polyInReveal
  ⟨ ∀ᶜ (id {μ = extᵐ idᶜ} (‵ `ℕ)) ⟩

allRevealGap : Term 1 zero
allRevealGap =
  allCastInReveal ↑[ zero ≔ zero ] `∀↑ id↑

polyInReveal-typed : crossedEnv ∣ [] ⊢ polyInReveal ⦂ ∀ℕ
polyInReveal-typed =
  ⊢Λ (body-result (result-val ($ (κℕ zero)))) (⊢$ (κℕ zero))

allCastInReveal-typed : crossedEnv ∣ [] ⊢ allCastInReveal ⦂ ∀ℕ
allCastInReveal-typed = ⊢⟨⟩ polyInReveal-typed
  (∀ᶜ (id {μ = extᵐ idᶜ} (‵ `ℕ)))

allRevealGap-typed : baseEnv ∣ [] ⊢ allRevealGap ⦂ ∀ℕ
allRevealGap-typed = ⊢reveal {fresh = no-live-anchor}
  (rep?-here {Ψ = baseEnv} {A = ℕ⇒ℕ})
  (⊢↑-∀ (⊢id↑ (‵ `ℕ))) allCastInReveal-typed

polyInReveal-value : Value polyInReveal
polyInReveal-value = Λ (result-val ($ (κℕ zero)))

allCastInReveal-value : Value allCastInReveal
allCastInReveal-value = polyInReveal-value 《 all 》

allRevealGap-not-result : ¬ Result allRevealGap
allRevealGap-not-result (result-val (_ ↑[ _ ≔ _ ] ()))

allRevealGap-no-step : ∀ {M′}
  → ¬ (baseEnv ⊢ allRevealGap —→ M′)
allRevealGap-no-step (ξ-reveal reduction) =
  value-no-step allCastInReveal-value reduction

allRevealGap-no-progress : ¬ Progress baseEnv allRevealGap
allRevealGap-no-progress (step reduction) =
  allRevealGap-no-step reduction
allRevealGap-no-progress (done result) =
  allRevealGap-not-result result

allReveal-gap-witness :
  (baseEnv ∣ [] ⊢ allRevealGap ⦂ ∀ℕ)
  × ¬ Progress baseEnv allRevealGap
allReveal-gap-witness =
  allRevealGap-typed , allRevealGap-no-progress

------------------------------------------------------------------------
-- Remaining gap 3: ∀ conceal cannot merge through an inert ∀ cast
------------------------------------------------------------------------

polyInConceal : Term 1 zero
polyInConceal = Λ ($ (κℕ zero))

allCastInConceal : Term 1 zero
allCastInConceal = polyInConceal
  ⟨ ∀ᶜ (id {μ = extᵐ idᶜ} (‵ `ℕ)) ⟩

allConcealGap : Term 1 1
allConcealGap =
  allCastInConceal ↓[ zero ≔ zero ] `∀↓ id↓

polyInConceal-typed :
  crossedEnv ,end[ zero ] ∣ [] ⊢ polyInConceal ⦂ ∀ℕ
polyInConceal-typed =
  ⊢Λ (body-result (result-val ($ (κℕ zero)))) (⊢$ (κℕ zero))

allCastInConceal-typed :
  crossedEnv ,end[ zero ] ∣ [] ⊢ allCastInConceal ⦂ ∀ℕ
allCastInConceal-typed = ⊢⟨⟩ polyInConceal-typed
  (∀ᶜ (id {μ = extᵐ idᶜ} (‵ `ℕ)))

allConcealGap-typed : crossedEnv ∣ [] ⊢ allConcealGap ⦂ ∀ℕ
allConcealGap-typed = ⊢conceal refl ended-base-rep
  (⊢↓-∀ (⊢id↓ (‵ `ℕ))) allCastInConceal-typed

polyInConceal-value : Value polyInConceal
polyInConceal-value = Λ (result-val ($ (κℕ zero)))

allCastInConceal-value : Value allCastInConceal
allCastInConceal-value = polyInConceal-value 《 all 》

allConcealGap-not-result : ¬ Result allConcealGap
allConcealGap-not-result (result-val (_ ↓[ _ ≔ _ ] ()))

allConcealGap-no-step : ∀ {M′}
  → ¬ (crossedEnv ⊢ allConcealGap —→ M′)
allConcealGap-no-step (ξ-conceal reduction) =
  value-no-step allCastInConceal-value reduction

allConcealGap-no-progress : ¬ Progress crossedEnv allConcealGap
allConcealGap-no-progress (step reduction) =
  allConcealGap-no-step reduction
allConcealGap-no-progress (done result) =
  allConcealGap-not-result result

allConceal-gap-witness :
  (crossedEnv ∣ [] ⊢ allConcealGap ⦂ ∀ℕ)
  × ¬ Progress crossedEnv allConcealGap
allConceal-gap-witness =
  allConcealGap-typed , allConcealGap-no-progress
