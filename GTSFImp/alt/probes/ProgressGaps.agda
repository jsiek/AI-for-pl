module alt.probes.ProgressGaps where

-- File Charter:
--   * Checks the former stranded-ν gap as a positive reduction trace.
--   * The region first floats through reveal, strict conceal/reveal then fires,
--     and the persistent allocation remains around the final constant.
--   * Audits the indexed `BlockedElimination` frontier.  The application and
--     projection adapters have closed-source witnesses in
--     `ChainNuReachability`; this file supplies the type-application,
--     primitive, atomic-boundary, and nested-unseal witnesses.
--   * The atomic reveal/conceal families each include a checked stepping old
--     shape and a checked no-step value residue.  The primitive audit likewise
--     contrasts U42's stepping plain pair with its region-adapter residue.
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
open import Data.Sum using (inj₁)
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
open import alt.ThetaTermSubst using (⊢bracket; rep?-bracket; rep?-here)
open import alt.ThetaProgress using
  (CanonicalFun; Progress; step; done; failed; BlockedElimination;
   BoundaryValue; adapter-•; boundary-⊕; atomic-reveal; unseal-interior;
   atomic-conceal; bb-reveal; bv-reveal-adapter; bv-reveal-region;
   conceal-boundary)
import alt.probes.LooseIdCancelRecheck as U42

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

baseAdapterGap-blocked : BlockedElimination baseEnv baseAdapterGap
baseAdapterGap-blocked =
  boundary-⊕ baseAdapter-value ($ (κℕ zero))
    (inj₁
      (bb-reveal baseRegion-result
        (adapter-region (result-val baseRegionBody-value) var-∈)
      , baseAdapter-no-step))
    baseAdapterGap-typed

------------------------------------------------------------------------
-- U43 boundary audit: stepping plain pair and stuck region residue
------------------------------------------------------------------------

plainBasePrimitive : Term 3 2
plainBasePrimitive = U42.baseRedex ⊕[ addℕ ] $ (κℕ zero)

plainBasePrimitiveAfterConceal : Term 3 2
plainBasePrimitiveAfterConceal =
  U42.baseMiddle ⊕[ addℕ ] $ (κℕ zero)

plainBasePrimitiveReady : Term 3 2
plainBasePrimitiveReady = $ (κℕ zero) ⊕[ addℕ ] $ (κℕ zero)

plainBasePrimitive-typed :
  U42.baseEnv ∣ [] ⊢ plainBasePrimitive ⦂ ℕᵗ
plainBasePrimitive-typed =
  ⊢⊕ addℕ U42.baseRedex-typed (⊢$ (κℕ zero))

plainBasePrimitive-trace :
  U42.baseEnv ⊢ plainBasePrimitive —↠ $ (κℕ zero)
plainBasePrimitive-trace =
    plainBasePrimitive
  —→⟨ ξ-⊕₁ U42.base-current-first-step ⟩
    plainBasePrimitiveAfterConceal
  —→⟨ ξ-⊕₁ U42.base-current-second-step ⟩
    plainBasePrimitiveReady
  —→⟨ δ-⊕ δ-add ⟩
    $ (κℕ zero)
  ∎

------------------------------------------------------------------------
-- U43 adapter-• witness
------------------------------------------------------------------------

adapterAll : ∀ {Δ} → Ty Δ
adapterAll = `∀ (‵ `ℕ)

allRegionBody : Term 2 1
allRegionBody = Λ ($ (κℕ zero))

allRegion : Term 1 1
allRegion = ν[ ＇ zero ] allRegionBody

allAdapter : Term 1 zero
allAdapter = allRegion ↑[ zero ≔ zero ] `∀↑ id↑

allAdapterGap : Term 1 zero
allAdapterGap = allAdapter ⦂∀ (‵ `ℕ) [ ℕᵗ ]

allRegionBody-typed :
  dependentRegionEnv ∣ [] ⊢ allRegionBody ⦂ adapterAll
allRegionBody-typed =
  ⊢Λ (body-result (result-val ($ (κℕ zero)))) (⊢$ (κℕ zero))

allRegion-typed : crossedEnv ∣ [] ⊢ allRegion ⦂ adapterAll
allRegion-typed = ⊢ν allRegionBody-typed

allAdapter-typed : baseEnv ∣ [] ⊢ allAdapter ⦂ adapterAll
allAdapter-typed = ⊢reveal {fresh = no-live-anchor}
  (rep?-here {Ψ = baseEnv} {A = ℕ⇒ℕ})
  (⊢↑-∀ (⊢id↑ (‵ `ℕ))) allRegion-typed

allAdapterGap-typed : baseEnv ∣ [] ⊢ allAdapterGap ⦂ ℕᵗ
allAdapterGap-typed = ⊢⦂∀ allAdapter-typed

allRegionBody-result : Result allRegionBody
allRegionBody-result = result-val (Λ (result-val ($ (κℕ zero))))

allRegion-result : Result allRegion
allRegion-result = result-ν allRegionBody-result

allAdapter-value : Value allAdapter
allAdapter-value = allRegion-result ↑[ zero ≔ zero ]
  adapter-region allRegionBody-result var-∈

allAdapterGap-blocked : BlockedElimination baseEnv allAdapterGap
allAdapterGap-blocked =
  adapter-• allRegionBody-result var-∈ allAdapterGap-typed

allAdapterGap-no-step : ∀ {M′}
  → ¬ (baseEnv ⊢ allAdapterGap —→ M′)
allAdapterGap-no-step (ξ-• reduction) =
  value-no-step allAdapter-value reduction

------------------------------------------------------------------------
-- U43 bottom audit: stuck if inhabited; inhabitation remains open
------------------------------------------------------------------------

-- Unlike the store-indexed calculus, Theta's universal canonical view has an
-- adapter-region case.  Thus the old `no-bot-value` proof cannot simply be
-- imported.  This checked half of the audit isolates the remaining question:
-- any value-headed `bot-elim` cast is dynamically stuck, but no typed closed
-- inhabitant (or Theta-specific refutation of one) is currently known.
bottomCast-no-step : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ} {μ : Env∼ Δ} {M′ : Term Θ Δ}
  → Value V
  → ¬ (Ψ ⊢ V ⟨ bot-elim { μ = μ } ⟩ —→ M′)
bottomCast-no-step Vᵛ (ξ-⟨⟩ reduction) = value-no-step Vᵛ reduction

------------------------------------------------------------------------
-- U43 atomic-reveal: stepping old shape and narrowed stuck residue
------------------------------------------------------------------------

plainBoundary : BoundaryValue U42.baseRedex
plainBoundary =
  bv-reveal-adapter (result-val ($ (κℕ zero)))
    U42.variable-node-pair-mismatch

atomicRevealOuterEnv : TyEnv 3 1
  (just U42.beta Vec.∷ Vec.[])
atomicRevealOuterEnv =
  U42.rootEnv ,begin[ zero ≔ U42.beta ]⟨ U42.empty-fresh ⟩

atomicRevealStepping : Term 3 1
atomicRevealStepping =
  U42.baseRedex ↑[ suc zero ≔ U42.gamma ] id↑

atomicRevealStepping-typed :
  atomicRevealOuterEnv ∣ [] ⊢ atomicRevealStepping ⦂ ℕᵗ
atomicRevealStepping-typed =
  ⊢reveal {fresh = U42.second-fresh} refl (⊢id↑ (‵ `ℕ))
    U42.baseRedex-typed

atomicRevealStepping-step : ∀ {M′}
  → U42.baseEnv ⊢ U42.baseRedex —→ M′
  → atomicRevealOuterEnv ⊢ atomicRevealStepping —→
      M′ ↑[ suc zero ≔ U42.gamma ] id↑
atomicRevealStepping-step reduction =
  ξ-reveal {fresh = U42.second-fresh} reduction

alpha-after-gamma-fresh : U42.alpha ∉ᵛ
  (just U42.gamma Vec.∷ Vec.[])
alpha-after-gamma-fresh zero ()

beta-after-gamma-alpha-fresh : U42.beta ∉ᵛ
  (just U42.gamma Vec.∷ just U42.alpha Vec.∷ Vec.[])
beta-after-gamma-alpha-fresh zero ()
beta-after-gamma-alpha-fresh (suc zero) ()

gammaEnv : TyEnv 3 1 (just U42.gamma Vec.∷ Vec.[])
gammaEnv =
  U42.rootEnv ,begin[ zero ≔ U42.gamma ]⟨ U42.empty-fresh ⟩

gammaAlphaEnv : TyEnv 3 2
  (just U42.gamma Vec.∷ just U42.alpha Vec.∷ Vec.[])
gammaAlphaEnv =
  gammaEnv ,begin[ suc zero ≔ U42.alpha ]⟨ alpha-after-gamma-fresh ⟩

sensitiveOperand-typed :
  gammaAlphaEnv ∣ [] ⊢ U42.baseSensitiveOperand ⦂ ℕᵗ
sensitiveOperand-typed =
  ⊢reveal {fresh = beta-after-gamma-alpha-fresh} refl
    (⊢id↑ (‵ `ℕ)) (⊢ν (⊢$ (κℕ zero)))

sensitiveOperand-boundary : BoundaryValue U42.baseSensitiveOperand
sensitiveOperand-boundary =
  bv-reveal-region (result-val ($ (κℕ zero))) var-∈

atomicRevealStuck : Term 3 1
atomicRevealStuck =
  U42.baseSensitiveOperand ↑[ suc zero ≔ U42.alpha ] id↑

atomicRevealStuck-typed :
  gammaEnv ∣ [] ⊢ atomicRevealStuck ⦂ ℕᵗ
atomicRevealStuck-typed =
  ⊢reveal {fresh = alpha-after-gamma-fresh} refl
    (⊢id↑ (‵ `ℕ)) sensitiveOperand-typed

atomicRevealStuck-blocked :
  BlockedElimination gammaEnv atomicRevealStuck
atomicRevealStuck-blocked =
  atomic-reveal (‵ `ℕ) sensitiveOperand-boundary
    U42.baseSensitiveOperand-value atomicRevealStuck-typed

atomicRevealStuck-no-step : ∀ {M′}
  → ¬ (gammaEnv ⊢ atomicRevealStuck —→ M′)
atomicRevealStuck-no-step (ξ-reveal reduction) =
  value-no-step U42.baseSensitiveOperand-value reduction

------------------------------------------------------------------------
-- U43 atomic-conceal: stepping old shape and narrowed stuck residue
------------------------------------------------------------------------

plainConcealEnv : TyEnv 3 3
  (just U42.alpha Vec.∷ U42.baseΣ)
plainConcealEnv =
  U42.baseEnv ,begin[ zero ≔ U42.alpha ]⟨ U42.third-fresh ⟩

atomicConcealStepping : Term 3 3
atomicConcealStepping =
  U42.baseRedex ↓[ zero ≔ U42.alpha ] id↓

plainConcealEndedRep :
  rep? (plainConcealEnv ,end[ zero ]) U42.alpha ≡ just ℕᵗ
plainConcealEndedRep =
  rep?-bracket {Ψ = U42.baseEnv} {Y = zero} {a = U42.alpha}
    {q = U42.alpha} {A = ℕᵗ} U42.third-fresh refl

atomicConcealStepping-typed :
  plainConcealEnv ∣ [] ⊢ atomicConcealStepping ⦂ ℕᵗ
atomicConcealStepping-typed =
  ⊢conceal refl
    plainConcealEndedRep
    (⊢id↓ (‵ `ℕ))
    (⊢bracket U42.third-fresh U42.baseRedex-typed)

atomicConcealStepping-step :
  plainConcealEnv ⊢ atomicConcealStepping —→
    U42.baseMiddle ↓[ zero ≔ U42.alpha ] id↓
atomicConcealStepping-step =
  ξ-conceal
    (ξ-reveal {fresh = U42.third-fresh} id-conceal)

atomicConcealStuck-blocked :
  BlockedElimination U42.outerEnv U42.baseSensitiveInner
atomicConcealStuck-blocked =
  atomic-conceal
    (conceal-boundary sensitiveOperand-boundary
      U42.baseSensitiveOperand-value)
    U42.baseSensitiveInner-typed

atomicConcealStuck-no-step : ∀ {M′}
  → ¬ (U42.outerEnv ⊢ U42.baseSensitiveInner —→ M′)
atomicConcealStuck-no-step (ξ-conceal reduction) =
  value-no-step U42.baseSensitiveOperand-value reduction

------------------------------------------------------------------------
-- U43 unseal-interior narrowed to the delimited residue
------------------------------------------------------------------------

unsealRoot : TyEnv 2 zero Vec.[]
unsealRoot = ∅ ,:= ℕᵗ ,:= ℕᵗ

unsealOuterEnv : TyEnv 2 1 (just zero Vec.∷ Vec.[])
unsealOuterEnv =
  unsealRoot ,begin[ zero ≔ zero ]⟨ no-live-anchor ⟩

unsealInnerAnchor : TyVar 2
unsealInnerAnchor = suc zero

unsealInnerFresh : unsealInnerAnchor ∉ᵛ
  (just (zero {n = 1}) Vec.∷ Vec.[])
unsealInnerFresh zero ()

unsealInnerEnv : TyEnv 2 2
  (just zero Vec.∷ just (suc zero) Vec.∷ Vec.[])
unsealInnerEnv =
  unsealOuterEnv
    ,begin[ suc zero ≔ unsealInnerAnchor ]⟨ unsealInnerFresh ⟩

unsealSealed : Term 2 2
unsealSealed = ($ (κℕ zero)) ↓[ zero ≔ zero ] seal

unsealDelimited : Term 2 1
unsealDelimited =
  unsealSealed ↑[ suc zero ≔ unsealInnerAnchor ] id↑

unsealGap : Term 2 zero
unsealGap = unsealDelimited ↑[ zero ≔ zero ] unseal

unsealSealed-typed :
  unsealInnerEnv ∣ [] ⊢ unsealSealed ⦂ ＇ zero
unsealSealed-typed =
  ⊢conceal refl refl ⊢seal (⊢$ (κℕ zero))

unsealDelimited-typed :
  unsealOuterEnv ∣ [] ⊢ unsealDelimited ⦂ ＇ zero
unsealDelimited-typed =
  ⊢reveal {fresh = unsealInnerFresh} refl
    (⊢id↑ (＇ zero)) unsealSealed-typed

unsealGap-typed : unsealRoot ∣ [] ⊢ unsealGap ⦂ ℕᵗ
unsealGap-typed =
  ⊢reveal {fresh = no-live-anchor} refl ⊢unseal
    unsealDelimited-typed

unsealSealed-value : Value unsealSealed
unsealSealed-value = ($ (κℕ zero)) ↓[ zero ≔ zero ] sealᵥ

unsealSealed-canonical : CanonicalInterior unsealSealed
unsealSealed-canonical = sealed ($ (κℕ zero)) zero zero

unsealDelimited-value : Value unsealDelimited
unsealDelimited-value =
  result-val unsealSealed-value ↑[ suc zero ≔ unsealInnerAnchor ]
    delimiter unsealSealed-canonical

unsealGap-blocked : BlockedElimination unsealRoot unsealGap
unsealGap-blocked =
  unseal-interior unsealSealed-canonical unsealGap-typed

unsealGap-no-step : ∀ {M′}
  → ¬ (unsealRoot ⊢ unsealGap —→ M′)
unsealGap-no-step (ξ-reveal reduction) =
  value-no-step unsealDelimited-value reduction

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
