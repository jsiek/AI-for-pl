module alt.probes.ProgressGaps where

-- File Charter:
--   * Records the U46 progress frontier with checked typing and no-progress
--     witnesses: immobile ν heads, `Λ blame`, and the two ∀ boundary casts.
--   * The adapter-family witness is a ν seal sandwich exposed at a function
--     boundary.  `ChainNuReachability` separately proves that closed sources
--     now stop earlier at a ν-wrapped function reveal.
--   * Retains positive traces for the former region-Λ and injection gaps.

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
  (Progress; step; done; failed; BlockedElimination; adapter-·;
   ν-immobile; Λ-blame)

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

dependentRegionEnv : TyEnv 2 1 (just (suc zero) Vec.∷ Vec.[])
dependentRegionEnv = crossedEnv ,:= ＇ zero

identity : ∀ {Θ} → Term Θ zero
identity = ƛ ℕᵗ ˙ ` zero

sealedTerm : Term 2 1
sealedTerm = identity ↓[ zero ≔ suc zero ] seal

identity-value : Value (identity {Θ = 2})
identity-value = ƛ ℕᵗ ˙ ` zero

sealed-value : Value sealedTerm
sealed-value = seal-value identity-value

identity-typed :
  dependentRegionEnv ,end[ zero ] ∣ [] ⊢ identity ⦂ ℕ⇒ℕ
identity-typed = ⊢ƛ (⊢` Z)

sealed-typed : dependentRegionEnv ∣ [] ⊢ sealedTerm ⦂ ＇ zero
sealed-typed = ⊢conceal refl refl ⊢seal identity-typed

------------------------------------------------------------------------
-- Gap family 1a: an immobile ν seal sandwich
------------------------------------------------------------------------

stranded : Term 1 1
stranded = ν[ ＇ zero ] sealedTerm

stranded-typed : crossedEnv ∣ [] ⊢ stranded ⦂ ＇ zero
stranded-typed = ⊢ν sealed-typed

stranded-blocked : BlockedElimination crossedEnv stranded
stranded-blocked = ν-immobile sealed-value seal-head stranded-typed

stranded-no-step : ∀ {M′} → ¬ (crossedEnv ⊢ stranded —→ M′)
stranded-no-step (ξ-ν reduction) = value-no-step sealed-value reduction

stranded-not-value : ¬ Value stranded
stranded-not-value ()

stranded-no-progress : ¬ Progress crossedEnv stranded
stranded-no-progress (step reduction) = stranded-no-step reduction
stranded-no-progress (done value) = stranded-not-value value

stranded-gap-witness :
  (crossedEnv ∣ [] ⊢ stranded ⦂ ＇ zero)
  × ¬ Progress crossedEnv stranded
stranded-gap-witness = stranded-typed , stranded-no-progress

------------------------------------------------------------------------
-- Gap family 1b: the same sandwich at a function elimination
------------------------------------------------------------------------

sealAdapter : Term 1 zero
sealAdapter = stranded ↑[ zero ≔ zero ] unseal

sealApplication : Term 1 zero
sealApplication = sealAdapter · $ (κℕ zero)

sealAdapter-typed : baseEnv ∣ [] ⊢ sealAdapter ⦂ ℕ⇒ℕ
sealAdapter-typed =
  ⊢reveal {fresh = no-live-anchor} (rep?-here {Ψ = baseEnv})
    ⊢unseal stranded-typed

sealApplication-typed : baseEnv ∣ [] ⊢ sealApplication ⦂ ℕᵗ
sealApplication-typed = ⊢· sealAdapter-typed (⊢$ (κℕ zero))

sealAdapter-value : Value sealAdapter
sealAdapter-value = adapter-region sealed-value seal-head var-∈

sealApplication-blocked : BlockedElimination baseEnv sealApplication
sealApplication-blocked =
  adapter-· sealAdapter-value adapter-region-head ($ (κℕ zero))
    sealApplication-typed

sealApplication-no-step : ∀ {M′}
  → ¬ (baseEnv ⊢ sealApplication —→ M′)
sealApplication-no-step (ξ-·₁ reduction) =
  value-no-step sealAdapter-value reduction
sealApplication-no-step (ξ-·₂ value reduction) =
  value-no-step ($ (κℕ zero)) reduction

sealApplication-not-value : ¬ Value sealApplication
sealApplication-not-value ()

sealApplication-no-progress : ¬ Progress baseEnv sealApplication
sealApplication-no-progress (step reduction) =
  sealApplication-no-step reduction
sealApplication-no-progress (done value) =
  sealApplication-not-value value

baseAdapter-gap-witness :
  (baseEnv ∣ [] ⊢ sealApplication ⦂ ℕᵗ)
  × ¬ Progress baseEnv sealApplication
baseAdapter-gap-witness =
  sealApplication-typed , sealApplication-no-progress

------------------------------------------------------------------------
-- Gap family 1c: dropping ΛBody admits a stuck `Λ blame`
------------------------------------------------------------------------

lambdaBlameEnv : TyEnv zero zero Vec.[]
lambdaBlameEnv = ∅

lambdaBlame : Term zero zero
lambdaBlame = Λ blame

lambdaBlame-typed : lambdaBlameEnv ∣ [] ⊢ lambdaBlame ⦂ `∀ ℕᵗ
lambdaBlame-typed = ⊢Λ ⊢blame

lambdaBlame-blocked : BlockedElimination lambdaBlameEnv lambdaBlame
lambdaBlame-blocked = Λ-blame lambdaBlame-typed

lambdaBlame-no-step : ∀ {M′}
  → ¬ (lambdaBlameEnv ⊢ lambdaBlame —→ M′)
lambdaBlame-no-step (ξ-Λ ())

lambdaBlame-not-value : ¬ Value lambdaBlame
lambdaBlame-not-value (Λ ())

lambdaBlame-no-progress : ¬ Progress lambdaBlameEnv lambdaBlame
lambdaBlame-no-progress (step reduction) = lambdaBlame-no-step reduction
lambdaBlame-no-progress (done value) = lambdaBlame-not-value value

lambdaBlame-gap-witness :
  (lambdaBlameEnv ∣ [] ⊢ lambdaBlame ⦂ `∀ ℕᵗ)
  × ¬ Progress lambdaBlameEnv lambdaBlame
lambdaBlame-gap-witness = lambdaBlame-typed , lambdaBlame-no-progress

------------------------------------------------------------------------
-- Resolved former region-Λ obstruction
------------------------------------------------------------------------

regionLambdaBody : Term zero 1
regionLambdaBody = ν[ ℕᵗ ] $ (κℕ zero)

regionLambdaRedex : Term zero zero
regionLambdaRedex = (Λ regionLambdaBody) ⦂∀ ℕᵗ [ ℕᵗ ]

regionLambdaReady : Term zero zero
regionLambdaReady = (Λ ($ (κℕ zero))) ⦂∀ ℕᵗ [ ℕᵗ ]

regionLambdaContractum : Term zero zero
regionLambdaContractum =
  ν[ ℕᵗ ] (($ (κℕ zero)) ↑[ zero ≔ zero ] id↑)

regionLambdaAllocated : Term zero zero
regionLambdaAllocated = ν[ ℕᵗ ] $ (κℕ zero)

regionLambdaRedex-typed :
  lambdaBlameEnv ∣ [] ⊢ regionLambdaRedex ⦂ ℕᵗ
regionLambdaRedex-typed = ⊢⦂∀ (⊢Λ (⊢ν (⊢$ (κℕ zero))))

regionLambda-trace :
  lambdaBlameEnv ⊢ regionLambdaRedex —↠ $ (κℕ zero)
regionLambda-trace =
    regionLambdaRedex
  —→⟨ ξ-• (ξ-Λ const-ν) ⟩
    regionLambdaReady
  —→⟨ β-Λ ($ (κℕ zero)) ⟩
    regionLambdaContractum
  —→⟨ ξ-ν id-reveal ⟩
    regionLambdaAllocated
  —→⟨ const-ν ⟩
    $ (κℕ zero)
  ∎

------------------------------------------------------------------------
-- Resolved injection crossings
------------------------------------------------------------------------

taggedInReveal : Term 1 1
taggedInReveal =
  ($ (κℕ zero)) ⟨ (id {μ = idᶜ} (‵ `ℕ)) ! ⟩

starReveal : Term 1 zero
starReveal = taggedInReveal ↑[ zero ≔ zero ] id↑

starRevealMerge : Term 1 zero
starRevealMerge = starReveal ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

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

------------------------------------------------------------------------
-- Remaining gap 2: ∀ reveal through an inert ∀ cast
------------------------------------------------------------------------

∀ℕ : ∀ {Δ} → Ty Δ
∀ℕ = `∀ (‵ `ℕ)

polyInReveal : Term 1 1
polyInReveal = Λ ($ (κℕ zero))

allCastInReveal : Term 1 1
allCastInReveal = polyInReveal
  ⟨ ∀ᶜ (id {μ = extᵐ idᶜ} (‵ `ℕ)) ⟩

allRevealGap : Term 1 zero
allRevealGap = allCastInReveal ↑[ zero ≔ zero ] `∀↑ id↑

polyInReveal-typed : crossedEnv ∣ [] ⊢ polyInReveal ⦂ ∀ℕ
polyInReveal-typed = ⊢Λ (⊢$ (κℕ zero))

allCastInReveal-typed : crossedEnv ∣ [] ⊢ allCastInReveal ⦂ ∀ℕ
allCastInReveal-typed = ⊢⟨⟩ polyInReveal-typed
  (∀ᶜ (id {μ = extᵐ idᶜ} (‵ `ℕ)))

allRevealGap-typed : baseEnv ∣ [] ⊢ allRevealGap ⦂ ∀ℕ
allRevealGap-typed = ⊢reveal {fresh = no-live-anchor}
  (rep?-here {Ψ = baseEnv} {A = ℕ⇒ℕ}) (⊢↑-∀ (⊢id↑ (‵ `ℕ)))
  allCastInReveal-typed

polyInReveal-value : Value polyInReveal
polyInReveal-value = Λ ($ (κℕ zero))

allCastInReveal-value : Value allCastInReveal
allCastInReveal-value = polyInReveal-value 《 all 》

allRevealGap-no-step : ∀ {M′}
  → ¬ (baseEnv ⊢ allRevealGap —→ M′)
allRevealGap-no-step (ξ-reveal reduction) =
  value-no-step allCastInReveal-value reduction

allRevealGap-not-value : ¬ Value allRevealGap
allRevealGap-not-value ()

allRevealGap-no-progress : ¬ Progress baseEnv allRevealGap
allRevealGap-no-progress (step reduction) = allRevealGap-no-step reduction
allRevealGap-no-progress (done value) = allRevealGap-not-value value

allReveal-gap-witness :
  (baseEnv ∣ [] ⊢ allRevealGap ⦂ ∀ℕ)
  × ¬ Progress baseEnv allRevealGap
allReveal-gap-witness = allRevealGap-typed , allRevealGap-no-progress

------------------------------------------------------------------------
-- Remaining gap 3: ∀ conceal through an inert ∀ cast
------------------------------------------------------------------------

polyInConceal : Term 1 zero
polyInConceal = Λ ($ (κℕ zero))

allCastInConceal : Term 1 zero
allCastInConceal = polyInConceal
  ⟨ ∀ᶜ (id {μ = extᵐ idᶜ} (‵ `ℕ)) ⟩

allConcealGap : Term 1 1
allConcealGap = allCastInConceal ↓[ zero ≔ zero ] `∀↓ id↓

ended-base-rep :
  rep? (crossedEnv ,end[ zero ]) zero ≡ just ℕ⇒ℕ
ended-base-rep = rep?-bracket {Ψ = baseEnv} {Y = zero} {a = zero}
  {q = zero} no-live-anchor (rep?-here {Ψ = baseEnv} {A = ℕ⇒ℕ})

polyInConceal-typed :
  crossedEnv ,end[ zero ] ∣ [] ⊢ polyInConceal ⦂ ∀ℕ
polyInConceal-typed = ⊢Λ (⊢$ (κℕ zero))

allCastInConceal-typed :
  crossedEnv ,end[ zero ] ∣ [] ⊢ allCastInConceal ⦂ ∀ℕ
allCastInConceal-typed = ⊢⟨⟩ polyInConceal-typed
  (∀ᶜ (id {μ = extᵐ idᶜ} (‵ `ℕ)))

allConcealGap-typed : crossedEnv ∣ [] ⊢ allConcealGap ⦂ ∀ℕ
allConcealGap-typed = ⊢conceal refl ended-base-rep
  (⊢↓-∀ (⊢id↓ (‵ `ℕ))) allCastInConceal-typed

polyInConceal-value : Value polyInConceal
polyInConceal-value = Λ ($ (κℕ zero))

allCastInConceal-value : Value allCastInConceal
allCastInConceal-value = polyInConceal-value 《 all 》

allConcealGap-no-step : ∀ {M′}
  → ¬ (crossedEnv ⊢ allConcealGap —→ M′)
allConcealGap-no-step (ξ-conceal reduction) =
  value-no-step allCastInConceal-value reduction

allConcealGap-not-value : ¬ Value allConcealGap
allConcealGap-not-value ()

allConcealGap-no-progress : ¬ Progress crossedEnv allConcealGap
allConcealGap-no-progress (step reduction) = allConcealGap-no-step reduction
allConcealGap-no-progress (done value) = allConcealGap-not-value value

allConceal-gap-witness :
  (crossedEnv ∣ [] ⊢ allConcealGap ⦂ ∀ℕ)
  × ¬ Progress crossedEnv allConcealGap
allConceal-gap-witness = allConcealGap-typed , allConcealGap-no-progress
