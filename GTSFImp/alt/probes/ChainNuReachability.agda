module alt.probes.ChainNuReachability where

-- File Charter:
--   * Asks whether a source-shaped type application can produce the
--     chain-ν adapter gaps at a region boundary.
--   * Answers yes: β-Λ at the live abstract type allocates `ν[ ＇ X ]`,
--     `float-·₁` carries it through the interior application, and evaluation
--     stops at checked `adapter-·` and `adapter-project` eliminations.
--   * Both sources are closed and contain no ν or mismatched adapter nodes;
--     their seal/unseal nodes and ground casts are compile-style conversions.

open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just)
import Data.Nat as Nat
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
open import alt.ThetaPreservation using (preserve)
open import alt.ThetaProgress using
  (BlockedElimination; Progress; adapter-·; adapter-project;
   step; done; failed)

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

identityBody : ∀ {Δ} → Ty (Nat.suc Δ)
identityBody = ＇ zero ⇒ ＇ zero

no-live-anchor : ∀ {Θ} {α : TyVar Θ} → α ∉ᵛ Vec.[]
no-live-anchor ()

allocated-anchor-fresh :
  zero {n = 1} ∉ᵛ (just (suc zero) Vec.∷ Vec.[])
allocated-anchor-fresh zero ()

polyBody : Term 1 2
polyBody = ƛ ＇ zero ˙ ` Nat.zero

polyIdentity : Term 1 1
polyIdentity = Λ polyBody

polyApplied : Term 1 1
polyApplied = polyIdentity
  ⦂∀ identityBody {Δ = Nat.suc Nat.zero} [ ＇ zero ]

polyBody-value : Value polyBody
polyBody-value = ƛ ＇ zero ˙ ` Nat.zero

polyIdentity-value : Value polyIdentity
polyIdentity-value = Λ (result-val polyBody-value)

polyIdentity-typed : ∀
    {σ : Vec.Vec (Maybe (TyVar (Nat.suc Nat.zero))) (Nat.suc Nat.zero)}
    {Ψ : TyEnv (Nat.suc Nat.zero) (Nat.suc Nat.zero) σ}
  → Ψ ∣ [] ⊢ polyIdentity
      ⦂ `∀ (identityBody {Δ = Nat.suc Nat.zero})
polyIdentity-typed =
  ⊢Λ (body-result (result-val polyBody-value)) (⊢ƛ (⊢` Z))

polyApplied-typed : ∀
    {σ : Vec.Vec (Maybe (TyVar (Nat.suc Nat.zero))) (Nat.suc Nat.zero)}
    {Ψ : TyEnv (Nat.suc Nat.zero) (Nat.suc Nat.zero) σ}
  → Ψ ∣ [] ⊢ polyApplied ⦂ ＇ zero ⇒ ＇ zero
polyApplied-typed = ⊢⦂∀ polyIdentity-typed

instantiationBody : Term 2 1
instantiationBody =
  shiftᶿ polyBody ↑[ zero ≔ zero ]
    〖 zero ↑ identityBody {Δ = Nat.suc Nat.zero} 〗

instantiationRegion : Term 1 1
instantiationRegion = ν[ ＇ zero ] instantiationBody

shiftedPolyBody-value : Value (shiftᶿ polyBody)
shiftedPolyBody-value = ƛ ＇ zero ˙ ` Nat.zero

instantiationBody-value : Value instantiationBody
instantiationBody-value =
  result-val shiftedPolyBody-value ↑[ zero ≔ zero ]
    fun shiftedPolyBody-value

instantiationRegion-result : Result instantiationRegion
instantiationRegion-result =
  result-ν (result-val instantiationBody-value)

emptyEnv : TyEnv 0 0 Vec.[]
emptyEnv = ∅

closedPolyBody : Term 0 2
closedPolyBody = ƛ ＇ zero ˙ ` Nat.zero

closedPolyIdentity : Term 0 1
closedPolyIdentity = Λ closedPolyBody

closedPolyApplied : Term 0 1
closedPolyApplied = closedPolyIdentity
  ⦂∀ identityBody {Δ = Nat.suc Nat.zero} [ ＇ zero ]

outerBody : Term 0 1
outerBody = ƛ ＇ zero ˙ (closedPolyApplied · ` Nat.zero)

outerPoly : Term 0 0
outerPoly = Λ outerBody

closedPolyBody-value : Value closedPolyBody
closedPolyBody-value = ƛ ＇ zero ˙ ` Nat.zero

closedPolyIdentity-typed :
  emptyEnv ,typ ∣ ＇ zero ∷ [] ⊢ closedPolyIdentity
    ⦂ `∀ (identityBody {Δ = Nat.suc Nat.zero})
closedPolyIdentity-typed =
  ⊢Λ (body-result (result-val closedPolyBody-value)) (⊢ƛ (⊢` Z))

outerBody-value : Value outerBody
outerBody-value = ƛ ＇ zero ˙ (closedPolyApplied · ` Nat.zero)

outerBody-typed :
  emptyEnv ,typ ∣ [] ⊢ outerBody ⦂ ＇ zero ⇒ ＇ zero
outerBody-typed =
  ⊢ƛ (⊢· (⊢⦂∀ closedPolyIdentity-typed) (⊢` Z))

outerPoly-typed :
  emptyEnv ∣ [] ⊢ outerPoly ⦂ `∀ identityBody
outerPoly-typed =
  ⊢Λ (body-result (result-val outerBody-value)) outerBody-typed

outerInstantiationBody : Term 1 0
outerInstantiationBody =
  shiftᶿ outerBody ↑[ zero ≔ zero ]
    〖 zero ↑ identityBody {Δ = Nat.zero} 〗

shiftedOuterBody-value : Value (shiftᶿ outerBody)
shiftedOuterBody-value =
  ƛ ＇ zero ˙ (polyApplied · ` Nat.zero)

outerInstantiationBody-value : Value outerInstantiationBody
outerInstantiationBody-value =
  result-val shiftedOuterBody-value ↑[ zero ≔ zero ]
    fun shiftedOuterBody-value

------------------------------------------------------------------------
-- Application outside a function-valued region boundary
------------------------------------------------------------------------

appBaseEnv : TyEnv 1 0 Vec.[]
appBaseEnv = ∅ ,:= ℕ⇒ℕ

appLiveEnv : TyEnv 1 1 (just zero Vec.∷ Vec.[])
appLiveEnv = appBaseEnv ,begin[ zero ≔ zero ]⟨ no-live-anchor ⟩

appEndedRep :
  rep? (appLiveEnv ,end[ zero ]) zero ≡ just ℕ⇒ℕ
appEndedRep = rep?-bracket {Ψ = appBaseEnv} {Y = zero}
  {a = zero} {q = zero} no-live-anchor
  (rep?-here {Ψ = appBaseEnv} {A = ℕ⇒ℕ})

appSeedOutside : Term 1 0
appSeedOutside = ƛ ℕᵗ ˙ ` Nat.zero

appSeedInside : Term 1 1
appSeedInside = appSeedOutside ↓[ zero ≔ zero ] seal

appSeedOutside-value : Value appSeedOutside
appSeedOutside-value = ƛ ℕᵗ ˙ ` Nat.zero

appSeedInside-value : Value appSeedInside
appSeedInside-value = appSeedOutside-value ↓[ zero ≔ zero ] sealᵥ

appSeedOutside-typed :
  appLiveEnv ,end[ zero ] ∣ [] ⊢ appSeedOutside ⦂ ℕ⇒ℕ
appSeedOutside-typed = ⊢ƛ (⊢` Z)

appSeedInside-typed : appLiveEnv ∣ [] ⊢ appSeedInside ⦂ ＇ zero
appSeedInside-typed =
  ⊢conceal refl appEndedRep ⊢seal appSeedOutside-typed

appSource : Term 1 0
appSource =
  ((polyApplied · appSeedInside) ↑[ zero ≔ zero ] unseal)
    · $ (κℕ Nat.zero)

appSource-typed : appBaseEnv ∣ [] ⊢ appSource ⦂ ℕᵗ
appSource-typed =
  ⊢·
    (⊢reveal {fresh = no-live-anchor}
      (rep?-here {Ψ = appBaseEnv}) ⊢unseal
      (⊢· polyApplied-typed appSeedInside-typed))
    (⊢$ (κℕ Nat.zero))

appAfterBeta : Term 1 0
appAfterBeta =
  ((instantiationRegion · appSeedInside) ↑[ zero ≔ zero ] unseal)
    · $ (κℕ Nat.zero)

appShiftedSeed : Term 2 1
appShiftedSeed = shiftᶿ appSeedInside

appShiftedSeed-value : Value appShiftedSeed
appShiftedSeed-value =
  (ƛ ℕᵗ ˙ ` Nat.zero) ↓[ zero ≔ suc zero ] sealᵥ

appAfterFloat : Term 1 0
appAfterFloat =
  ((ν[ ＇ zero ] (instantiationBody · appShiftedSeed))
    ↑[ zero ≔ zero ] unseal) · $ (κℕ Nat.zero)

appInnerConcealedSeed : Term 2 2
appInnerConcealedSeed =
  appShiftedSeed ↓[ zero ≔ zero ] seal

appInnerConcealedSeed-value : Value appInnerConcealedSeed
appInnerConcealedSeed-value =
  appShiftedSeed-value ↓[ zero ≔ zero ] sealᵥ

appAfterBoundaryBeta : Term 1 0
appAfterBoundaryBeta =
  ((ν[ ＇ zero ]
      ((shiftᶿ polyBody · appInnerConcealedSeed)
        ↑[ zero ≔ zero ] unseal))
    ↑[ zero ≔ zero ] unseal) · $ (κℕ Nat.zero)

appAfterLambdaBeta : Term 1 0
appAfterLambdaBeta =
  ((ν[ ＇ zero ]
      (appInnerConcealedSeed ↑[ zero ≔ zero ] unseal))
    ↑[ zero ≔ zero ] unseal) · $ (κℕ Nat.zero)

appFinalRegion : Term 1 1
appFinalRegion = ν[ ＇ zero ] appShiftedSeed

appAdapter : Term 1 0
appAdapter = appFinalRegion ↑[ zero ≔ zero ] unseal

appEndpoint : Term 1 0
appEndpoint = appAdapter · $ (κℕ Nat.zero)

app-step₁ : appBaseEnv ⊢ appSource —→ appAfterBeta
app-step₁ = ξ-·₁
  (ξ-reveal {fresh = no-live-anchor} (ξ-·₁ (β-Λ polyBody-value)))

app-step₂ : appBaseEnv ⊢ appAfterBeta —→ appAfterFloat
app-step₂ =
  ξ-·₁ (ξ-reveal {fresh = no-live-anchor}
    (float-·₁ instantiationRegion-result))

app-step₃ : appBaseEnv ⊢ appAfterFloat —→ appAfterBoundaryBeta
app-step₃ =
  ξ-·₁ (ξ-reveal {fresh = no-live-anchor} (ξ-ν
    (β-reveal-⇒ (result-val shiftedPolyBody-value)
      appShiftedSeed-value)))

app-step₄ : appBaseEnv ⊢ appAfterBoundaryBeta —→ appAfterLambdaBeta
app-step₄ =
  ξ-·₁ (ξ-reveal {fresh = no-live-anchor} (ξ-ν
    (ξ-reveal {fresh = allocated-anchor-fresh}
      (β appInnerConcealedSeed-value))))

app-step₅ : appBaseEnv ⊢ appAfterLambdaBeta —→ appEndpoint
app-step₅ =
  ξ-·₁ (ξ-reveal {fresh = no-live-anchor} (ξ-ν
    (conceal-reveal (result-val appShiftedSeed-value))))

app-trace : appBaseEnv ⊢ appSource —↠ appEndpoint
app-trace =
    appSource
  —→⟨ app-step₁ ⟩
    appAfterBeta
  —→⟨ app-step₂ ⟩
    appAfterFloat
  —→⟨ app-step₃ ⟩
    appAfterBoundaryBeta
  —→⟨ app-step₄ ⟩
    appAfterLambdaBeta
  —→⟨ app-step₅ ⟩
    appEndpoint
  ∎

appAfterBeta-typed : appBaseEnv ∣ [] ⊢ appAfterBeta ⦂ ℕᵗ
appAfterBeta-typed = preserve appSource-typed app-step₁

appAfterFloat-typed : appBaseEnv ∣ [] ⊢ appAfterFloat ⦂ ℕᵗ
appAfterFloat-typed = preserve appAfterBeta-typed app-step₂

appAfterBoundaryBeta-typed :
  appBaseEnv ∣ [] ⊢ appAfterBoundaryBeta ⦂ ℕᵗ
appAfterBoundaryBeta-typed = preserve appAfterFloat-typed app-step₃

appAfterLambdaBeta-typed :
  appBaseEnv ∣ [] ⊢ appAfterLambdaBeta ⦂ ℕᵗ
appAfterLambdaBeta-typed =
  preserve appAfterBoundaryBeta-typed app-step₄

appEndpoint-typed : appBaseEnv ∣ [] ⊢ appEndpoint ⦂ ℕᵗ
appEndpoint-typed = preserve appAfterLambdaBeta-typed app-step₅

appFinalRegion-result : Result appFinalRegion
appFinalRegion-result = result-ν (result-val appShiftedSeed-value)

appAdapter-value : Value appAdapter
appAdapter-value = appFinalRegion-result ↑[ zero ≔ zero ]
  adapter-region (result-val appShiftedSeed-value) var-∈

appEndpoint-blocked : BlockedElimination appBaseEnv appEndpoint
appEndpoint-blocked =
  adapter-· (result-val appShiftedSeed-value) var-∈
    ($ (κℕ Nat.zero)) appEndpoint-typed

appEndpoint-no-step : ∀ {M′} → ¬ (appBaseEnv ⊢ appEndpoint —→ M′)
appEndpoint-no-step (ξ-·₁ reduction) =
  value-no-step appAdapter-value reduction
appEndpoint-no-step (ξ-·₂ Vᵥ reduction) =
  value-no-step ($ (κℕ Nat.zero)) reduction

appEndpoint-not-result : ¬ Result appEndpoint
appEndpoint-not-result (result-val ())

appEndpoint-no-progress : ¬ Progress appBaseEnv appEndpoint
appEndpoint-no-progress (step reduction) =
  appEndpoint-no-step reduction
appEndpoint-no-progress (done result) =
  appEndpoint-not-result result

-- This wrapper starts in the empty world.  Its first β-Λ creates the outer
-- region whose internal reachability trace was checked above.

closedAppSeed : Term 0 0
closedAppSeed = ƛ ℕᵗ ˙ ` Nat.zero

closedAppSeed-value : Value closedAppSeed
closedAppSeed-value = ƛ ℕᵗ ˙ ` Nat.zero

shiftedClosedAppSeed-value : Value (shiftᶿ closedAppSeed)
shiftedClosedAppSeed-value = ƛ ℕᵗ ˙ ` Nat.zero

outerAppConcealedSeed : Term 1 1
outerAppConcealedSeed =
  shiftᶿ closedAppSeed ↓[ zero ≔ zero ] seal

outerAppConcealedSeed-value : Value outerAppConcealedSeed
outerAppConcealedSeed-value =
  shiftedClosedAppSeed-value ↓[ zero ≔ zero ] sealᵥ

closedAppSource : Term 0 0
closedAppSource =
  ((outerPoly ⦂∀ identityBody [ ℕ⇒ℕ ]) · closedAppSeed)
    · $ (κℕ Nat.zero)

closedAppSource-typed : emptyEnv ∣ [] ⊢ closedAppSource ⦂ ℕᵗ
closedAppSource-typed =
  ⊢· (⊢· (⊢⦂∀ outerPoly-typed) (⊢ƛ (⊢` Z)))
    (⊢$ (κℕ Nat.zero))

closedAppAfterOuterBeta : Term 0 0
closedAppAfterOuterBeta =
  ((ν[ ℕ⇒ℕ ] outerInstantiationBody) · closedAppSeed)
    · $ (κℕ Nat.zero)

closedAppAfterOuterFloat : Term 0 0
closedAppAfterOuterFloat =
  (ν[ ℕ⇒ℕ ]
    (outerInstantiationBody · shiftᶿ closedAppSeed))
    · $ (κℕ Nat.zero)

closedAppAfterOuterBoundary : Term 0 0
closedAppAfterOuterBoundary =
  (ν[ ℕ⇒ℕ ]
    ((shiftᶿ outerBody · outerAppConcealedSeed)
      ↑[ zero ≔ zero ] unseal)) · $ (κℕ Nat.zero)

closedAppAfterOuterLambda : Term 0 0
closedAppAfterOuterLambda =
  (ν[ ℕ⇒ℕ ]
    ((polyApplied · appSeedInside) ↑[ zero ≔ zero ] unseal))
    · $ (κℕ Nat.zero)

closedAppAfterInnerBeta : Term 0 0
closedAppAfterInnerBeta =
  (ν[ ℕ⇒ℕ ]
    ((instantiationRegion · appSeedInside)
      ↑[ zero ≔ zero ] unseal)) · $ (κℕ Nat.zero)

closedAppAfterInnerFloat : Term 0 0
closedAppAfterInnerFloat =
  (ν[ ℕ⇒ℕ ]
    ((ν[ ＇ zero ] (instantiationBody · appShiftedSeed))
      ↑[ zero ≔ zero ] unseal)) · $ (κℕ Nat.zero)

closedAppAfterInnerBoundary : Term 0 0
closedAppAfterInnerBoundary =
  (ν[ ℕ⇒ℕ ]
    ((ν[ ＇ zero ]
      ((shiftᶿ polyBody · appInnerConcealedSeed)
        ↑[ zero ≔ zero ] unseal)) ↑[ zero ≔ zero ] unseal))
    · $ (κℕ Nat.zero)

closedAppAfterInnerLambda : Term 0 0
closedAppAfterInnerLambda =
  (ν[ ℕ⇒ℕ ]
    ((ν[ ＇ zero ]
      (appInnerConcealedSeed ↑[ zero ≔ zero ] unseal))
      ↑[ zero ≔ zero ] unseal)) · $ (κℕ Nat.zero)

closedAppReady : Term 0 0
closedAppReady =
  (ν[ ℕ⇒ℕ ] appAdapter) · $ (κℕ Nat.zero)

closedAppEndpoint : Term 0 0
closedAppEndpoint = ν[ ℕ⇒ℕ ] appEndpoint

closed-app-step₁ :
  emptyEnv ⊢ closedAppSource —→ closedAppAfterOuterBeta
closed-app-step₁ = ξ-·₁ (ξ-·₁ (β-Λ outerBody-value))

closed-app-step₂ :
  emptyEnv ⊢ closedAppAfterOuterBeta —→ closedAppAfterOuterFloat
closed-app-step₂ = ξ-·₁
  (float-·₁ (result-ν (result-val outerInstantiationBody-value)))

closed-app-step₃ :
  emptyEnv ⊢ closedAppAfterOuterFloat —→ closedAppAfterOuterBoundary
closed-app-step₃ = ξ-·₁ (ξ-ν
  (β-reveal-⇒ (result-val shiftedOuterBody-value)
    shiftedClosedAppSeed-value))

closed-app-step₄ :
  emptyEnv ⊢ closedAppAfterOuterBoundary —→ closedAppAfterOuterLambda
closed-app-step₄ = ξ-·₁ (ξ-ν
  (ξ-reveal {fresh = no-live-anchor}
    (β outerAppConcealedSeed-value)))

closed-app-step₅ :
  emptyEnv ⊢ closedAppAfterOuterLambda —→ closedAppAfterInnerBeta
closed-app-step₅ = ξ-·₁ (ξ-ν
  (ξ-reveal {fresh = no-live-anchor}
    (ξ-·₁ (β-Λ polyBody-value))))

closed-app-step₆ :
  emptyEnv ⊢ closedAppAfterInnerBeta —→ closedAppAfterInnerFloat
closed-app-step₆ = ξ-·₁ (ξ-ν
  (ξ-reveal {fresh = no-live-anchor}
    (float-·₁ instantiationRegion-result)))

closed-app-step₇ :
  emptyEnv ⊢ closedAppAfterInnerFloat —→ closedAppAfterInnerBoundary
closed-app-step₇ = ξ-·₁ (ξ-ν
  (ξ-reveal {fresh = no-live-anchor} (ξ-ν
    (β-reveal-⇒ (result-val shiftedPolyBody-value)
      appShiftedSeed-value))))

closed-app-step₈ :
  emptyEnv ⊢ closedAppAfterInnerBoundary —→ closedAppAfterInnerLambda
closed-app-step₈ = ξ-·₁ (ξ-ν
  (ξ-reveal {fresh = no-live-anchor} (ξ-ν
    (ξ-reveal {fresh = allocated-anchor-fresh}
      (β appInnerConcealedSeed-value)))))

closed-app-step₉ :
  emptyEnv ⊢ closedAppAfterInnerLambda —→ closedAppReady
closed-app-step₉ = ξ-·₁ (ξ-ν
  (ξ-reveal {fresh = no-live-anchor} (ξ-ν
    (conceal-reveal (result-val appShiftedSeed-value)))))

closed-app-step₁₀ :
  emptyEnv ⊢ closedAppReady —→ closedAppEndpoint
closed-app-step₁₀ =
  float-·₁ (result-ν (result-val appAdapter-value))

closed-app-trace : emptyEnv ⊢ closedAppSource —↠ closedAppEndpoint
closed-app-trace =
    closedAppSource
  —→⟨ closed-app-step₁ ⟩
    closedAppAfterOuterBeta
  —→⟨ closed-app-step₂ ⟩
    closedAppAfterOuterFloat
  —→⟨ closed-app-step₃ ⟩
    closedAppAfterOuterBoundary
  —→⟨ closed-app-step₄ ⟩
    closedAppAfterOuterLambda
  —→⟨ closed-app-step₅ ⟩
    closedAppAfterInnerBeta
  —→⟨ closed-app-step₆ ⟩
    closedAppAfterInnerFloat
  —→⟨ closed-app-step₇ ⟩
    closedAppAfterInnerBoundary
  —→⟨ closed-app-step₈ ⟩
    closedAppAfterInnerLambda
  —→⟨ closed-app-step₉ ⟩
    closedAppReady
  —→⟨ closed-app-step₁₀ ⟩
    closedAppEndpoint
  ∎

closedAppEndpoint-typed :
  emptyEnv ∣ [] ⊢ closedAppEndpoint ⦂ ℕᵗ
closedAppEndpoint-typed =
  preserve
    (preserve
      (preserve
        (preserve
          (preserve
            (preserve
              (preserve
                (preserve
                  (preserve
                    (preserve closedAppSource-typed closed-app-step₁)
                    closed-app-step₂)
                  closed-app-step₃)
                closed-app-step₄)
              closed-app-step₅)
            closed-app-step₆)
          closed-app-step₇)
        closed-app-step₈)
      closed-app-step₉)
    closed-app-step₁₀

closedAppEndpoint-no-step : ∀ {M′}
  → ¬ (emptyEnv ⊢ closedAppEndpoint —→ M′)
closedAppEndpoint-no-step (ξ-ν reduction) =
  appEndpoint-no-step reduction

closedAppEndpoint-not-result : ¬ Result closedAppEndpoint
closedAppEndpoint-not-result (result-ν result) =
  appEndpoint-not-result result

closedAppEndpoint-no-progress :
  ¬ Progress emptyEnv closedAppEndpoint
closedAppEndpoint-no-progress (step reduction) =
  closedAppEndpoint-no-step reduction
closedAppEndpoint-no-progress (done result) =
  closedAppEndpoint-not-result result

------------------------------------------------------------------------
-- Ground projection outside a ★-valued region boundary
------------------------------------------------------------------------

starBaseEnv : TyEnv 1 0 Vec.[]
starBaseEnv = ∅ ,:= ★

starLiveEnv : TyEnv 1 1 (just zero Vec.∷ Vec.[])
starLiveEnv = starBaseEnv ,begin[ zero ≔ zero ]⟨ no-live-anchor ⟩

starEndedRep : rep? (starLiveEnv ,end[ zero ]) zero ≡ just ★
starEndedRep = rep?-bracket {Ψ = starBaseEnv} {Y = zero}
  {a = zero} {q = zero} no-live-anchor
  (rep?-here {Ψ = starBaseEnv} {A = ★})

starSeedOutside : Term 1 0
starSeedOutside =
  ($ (κℕ Nat.zero)) ⟨ (id {μ = idᶜ} (‵ `ℕ)) ! ⟩

starSeedInside : Term 1 1
starSeedInside = starSeedOutside ↓[ zero ≔ zero ] seal

starSeedOutside-value : Value starSeedOutside
starSeedOutside-value = ($ (κℕ Nat.zero)) 《 inj 》

starSeedInside-value : Value starSeedInside
starSeedInside-value = starSeedOutside-value ↓[ zero ≔ zero ] sealᵥ

starSeedOutside-typed :
  starLiveEnv ,end[ zero ] ∣ [] ⊢ starSeedOutside ⦂ ★
starSeedOutside-typed =
  ⊢⟨⟩ (⊢$ (κℕ Nat.zero)) ((id {μ = idᶜ} (‵ `ℕ)) !)

starSeedInside-typed : starLiveEnv ∣ [] ⊢ starSeedInside ⦂ ＇ zero
starSeedInside-typed =
  ⊢conceal refl starEndedRep ⊢seal starSeedOutside-typed

starSource : Term 1 0
starSource =
  ((polyApplied · starSeedInside) ↑[ zero ≔ zero ] unseal)
    ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

starSource-typed : starBaseEnv ∣ [] ⊢ starSource ⦂ ℕᵗ
starSource-typed =
  ⊢⟨⟩
    (⊢reveal {fresh = no-live-anchor}
      (rep?-here {Ψ = starBaseEnv}) ⊢unseal
      (⊢· polyApplied-typed starSeedInside-typed))
    (？ (id {μ = idᶜ} (‵ `ℕ)))

starAfterBeta : Term 1 0
starAfterBeta =
  ((instantiationRegion · starSeedInside) ↑[ zero ≔ zero ] unseal)
    ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

starShiftedSeed : Term 2 1
starShiftedSeed = shiftᶿ starSeedInside

starShiftedSeed-value : Value starShiftedSeed
starShiftedSeed-value =
  (($ (κℕ Nat.zero)) 《 inj 》) ↓[ zero ≔ suc zero ] sealᵥ

starAfterFloat : Term 1 0
starAfterFloat =
  ((ν[ ＇ zero ] (instantiationBody · starShiftedSeed))
    ↑[ zero ≔ zero ] unseal)
    ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

starInnerConcealedSeed : Term 2 2
starInnerConcealedSeed =
  starShiftedSeed ↓[ zero ≔ zero ] seal

starInnerConcealedSeed-value : Value starInnerConcealedSeed
starInnerConcealedSeed-value =
  starShiftedSeed-value ↓[ zero ≔ zero ] sealᵥ

starAfterBoundaryBeta : Term 1 0
starAfterBoundaryBeta =
  ((ν[ ＇ zero ]
      ((shiftᶿ polyBody · starInnerConcealedSeed)
        ↑[ zero ≔ zero ] unseal))
    ↑[ zero ≔ zero ] unseal)
    ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

starAfterLambdaBeta : Term 1 0
starAfterLambdaBeta =
  ((ν[ ＇ zero ]
      (starInnerConcealedSeed ↑[ zero ≔ zero ] unseal))
    ↑[ zero ≔ zero ] unseal)
    ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

starFinalRegion : Term 1 1
starFinalRegion = ν[ ＇ zero ] starShiftedSeed

starAdapter : Term 1 0
starAdapter = starFinalRegion ↑[ zero ≔ zero ] unseal

starEndpoint : Term 1 0
starEndpoint = starAdapter ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

star-step₁ : starBaseEnv ⊢ starSource —→ starAfterBeta
star-step₁ = ξ-⟨⟩
  (ξ-reveal {fresh = no-live-anchor} (ξ-·₁ (β-Λ polyBody-value)))

star-step₂ : starBaseEnv ⊢ starAfterBeta —→ starAfterFloat
star-step₂ =
  ξ-⟨⟩ (ξ-reveal {fresh = no-live-anchor}
    (float-·₁ instantiationRegion-result))

star-step₃ : starBaseEnv ⊢ starAfterFloat —→ starAfterBoundaryBeta
star-step₃ =
  ξ-⟨⟩ (ξ-reveal {fresh = no-live-anchor} (ξ-ν
    (β-reveal-⇒ (result-val shiftedPolyBody-value)
      starShiftedSeed-value)))

star-step₄ : starBaseEnv ⊢ starAfterBoundaryBeta —→ starAfterLambdaBeta
star-step₄ =
  ξ-⟨⟩ (ξ-reveal {fresh = no-live-anchor} (ξ-ν
    (ξ-reveal {fresh = allocated-anchor-fresh}
      (β starInnerConcealedSeed-value))))

star-step₅ : starBaseEnv ⊢ starAfterLambdaBeta —→ starEndpoint
star-step₅ =
  ξ-⟨⟩ (ξ-reveal {fresh = no-live-anchor} (ξ-ν
    (conceal-reveal (result-val starShiftedSeed-value))))

star-trace : starBaseEnv ⊢ starSource —↠ starEndpoint
star-trace =
    starSource
  —→⟨ star-step₁ ⟩
    starAfterBeta
  —→⟨ star-step₂ ⟩
    starAfterFloat
  —→⟨ star-step₃ ⟩
    starAfterBoundaryBeta
  —→⟨ star-step₄ ⟩
    starAfterLambdaBeta
  —→⟨ star-step₅ ⟩
    starEndpoint
  ∎

starAfterBeta-typed : starBaseEnv ∣ [] ⊢ starAfterBeta ⦂ ℕᵗ
starAfterBeta-typed = preserve starSource-typed star-step₁

starAfterFloat-typed : starBaseEnv ∣ [] ⊢ starAfterFloat ⦂ ℕᵗ
starAfterFloat-typed = preserve starAfterBeta-typed star-step₂

starAfterBoundaryBeta-typed :
  starBaseEnv ∣ [] ⊢ starAfterBoundaryBeta ⦂ ℕᵗ
starAfterBoundaryBeta-typed = preserve starAfterFloat-typed star-step₃

starAfterLambdaBeta-typed :
  starBaseEnv ∣ [] ⊢ starAfterLambdaBeta ⦂ ℕᵗ
starAfterLambdaBeta-typed =
  preserve starAfterBoundaryBeta-typed star-step₄

starEndpoint-typed : starBaseEnv ∣ [] ⊢ starEndpoint ⦂ ℕᵗ
starEndpoint-typed = preserve starAfterLambdaBeta-typed star-step₅

starFinalRegion-result : Result starFinalRegion
starFinalRegion-result = result-ν (result-val starShiftedSeed-value)

starAdapter-value : Value starAdapter
starAdapter-value = starFinalRegion-result ↑[ zero ≔ zero ]
  adapter-region (result-val starShiftedSeed-value) var-∈

starEndpoint-blocked : BlockedElimination starBaseEnv starEndpoint
starEndpoint-blocked =
  adapter-project (result-val starShiftedSeed-value) var-∈
    starEndpoint-typed

starEndpoint-no-step : ∀ {M′}
  → ¬ (starBaseEnv ⊢ starEndpoint —→ M′)
starEndpoint-no-step (expand Vᵥ G≢G) = G≢G refl
starEndpoint-no-step (ξ-⟨⟩ reduction) =
  value-no-step starAdapter-value reduction

starEndpoint-not-result : ¬ Result starEndpoint
starEndpoint-not-result (result-val (_ 《 () 》))

starEndpoint-no-progress : ¬ Progress starBaseEnv starEndpoint
starEndpoint-no-progress (step reduction) =
  starEndpoint-no-step reduction
starEndpoint-no-progress (done result) =
  starEndpoint-not-result result

closedStarSeed : Term 0 0
closedStarSeed =
  ($ (κℕ Nat.zero)) ⟨ (id {μ = idᶜ} (‵ `ℕ)) ! ⟩

closedStarSeed-value : Value closedStarSeed
closedStarSeed-value = ($ (κℕ Nat.zero)) 《 inj 》

shiftedClosedStarSeed-value : Value (shiftᶿ closedStarSeed)
shiftedClosedStarSeed-value = ($ (κℕ Nat.zero)) 《 inj 》

outerStarConcealedSeed : Term 1 1
outerStarConcealedSeed =
  shiftᶿ closedStarSeed ↓[ zero ≔ zero ] seal

outerStarConcealedSeed-value : Value outerStarConcealedSeed
outerStarConcealedSeed-value =
  shiftedClosedStarSeed-value ↓[ zero ≔ zero ] sealᵥ

closedStarSource : Term 0 0
closedStarSource =
  ((outerPoly ⦂∀ identityBody [ ★ ]) · closedStarSeed)
    ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

closedStarSource-typed : emptyEnv ∣ [] ⊢ closedStarSource ⦂ ℕᵗ
closedStarSource-typed =
  ⊢⟨⟩
    (⊢· (⊢⦂∀ outerPoly-typed)
      (⊢⟨⟩ (⊢$ (κℕ Nat.zero))
        ((id {μ = idᶜ} (‵ `ℕ)) !)))
    (？ (id {μ = idᶜ} (‵ `ℕ)))

closedStarAfterOuterBeta : Term 0 0
closedStarAfterOuterBeta =
  ((ν[ ★ ] outerInstantiationBody) · closedStarSeed)
    ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

closedStarAfterOuterFloat : Term 0 0
closedStarAfterOuterFloat =
  (ν[ ★ ]
    (outerInstantiationBody · shiftᶿ closedStarSeed))
    ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

closedStarAfterOuterBoundary : Term 0 0
closedStarAfterOuterBoundary =
  (ν[ ★ ]
    ((shiftᶿ outerBody · outerStarConcealedSeed)
      ↑[ zero ≔ zero ] unseal))
    ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

closedStarAfterOuterLambda : Term 0 0
closedStarAfterOuterLambda =
  (ν[ ★ ]
    ((polyApplied · starSeedInside) ↑[ zero ≔ zero ] unseal))
    ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

closedStarAfterInnerBeta : Term 0 0
closedStarAfterInnerBeta =
  (ν[ ★ ]
    ((instantiationRegion · starSeedInside)
      ↑[ zero ≔ zero ] unseal))
    ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

closedStarAfterInnerFloat : Term 0 0
closedStarAfterInnerFloat =
  (ν[ ★ ]
    ((ν[ ＇ zero ] (instantiationBody · starShiftedSeed))
      ↑[ zero ≔ zero ] unseal))
    ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

closedStarAfterInnerBoundary : Term 0 0
closedStarAfterInnerBoundary =
  (ν[ ★ ]
    ((ν[ ＇ zero ]
      ((shiftᶿ polyBody · starInnerConcealedSeed)
        ↑[ zero ≔ zero ] unseal)) ↑[ zero ≔ zero ] unseal))
    ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

closedStarAfterInnerLambda : Term 0 0
closedStarAfterInnerLambda =
  (ν[ ★ ]
    ((ν[ ＇ zero ]
      (starInnerConcealedSeed ↑[ zero ≔ zero ] unseal))
      ↑[ zero ≔ zero ] unseal))
    ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

closedStarReady : Term 0 0
closedStarReady =
  (ν[ ★ ] starAdapter) ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

closedStarEndpoint : Term 0 0
closedStarEndpoint = ν[ ★ ] starEndpoint

closed-star-step₁ :
  emptyEnv ⊢ closedStarSource —→ closedStarAfterOuterBeta
closed-star-step₁ = ξ-⟨⟩ (ξ-·₁ (β-Λ outerBody-value))

closed-star-step₂ :
  emptyEnv ⊢ closedStarAfterOuterBeta —→ closedStarAfterOuterFloat
closed-star-step₂ = ξ-⟨⟩
  (float-·₁ (result-ν (result-val outerInstantiationBody-value)))

closed-star-step₃ :
  emptyEnv ⊢ closedStarAfterOuterFloat —→ closedStarAfterOuterBoundary
closed-star-step₃ = ξ-⟨⟩ (ξ-ν
  (β-reveal-⇒ (result-val shiftedOuterBody-value)
    shiftedClosedStarSeed-value))

closed-star-step₄ :
  emptyEnv ⊢ closedStarAfterOuterBoundary —→ closedStarAfterOuterLambda
closed-star-step₄ = ξ-⟨⟩ (ξ-ν
  (ξ-reveal {fresh = no-live-anchor}
    (β outerStarConcealedSeed-value)))

closed-star-step₅ :
  emptyEnv ⊢ closedStarAfterOuterLambda —→ closedStarAfterInnerBeta
closed-star-step₅ = ξ-⟨⟩ (ξ-ν
  (ξ-reveal {fresh = no-live-anchor}
    (ξ-·₁ (β-Λ polyBody-value))))

closed-star-step₆ :
  emptyEnv ⊢ closedStarAfterInnerBeta —→ closedStarAfterInnerFloat
closed-star-step₆ = ξ-⟨⟩ (ξ-ν
  (ξ-reveal {fresh = no-live-anchor}
    (float-·₁ instantiationRegion-result)))

closed-star-step₇ :
  emptyEnv ⊢ closedStarAfterInnerFloat —→ closedStarAfterInnerBoundary
closed-star-step₇ = ξ-⟨⟩ (ξ-ν
  (ξ-reveal {fresh = no-live-anchor} (ξ-ν
    (β-reveal-⇒ (result-val shiftedPolyBody-value)
      starShiftedSeed-value))))

closed-star-step₈ :
  emptyEnv ⊢ closedStarAfterInnerBoundary —→ closedStarAfterInnerLambda
closed-star-step₈ = ξ-⟨⟩ (ξ-ν
  (ξ-reveal {fresh = no-live-anchor} (ξ-ν
    (ξ-reveal {fresh = allocated-anchor-fresh}
      (β starInnerConcealedSeed-value)))))

closed-star-step₉ :
  emptyEnv ⊢ closedStarAfterInnerLambda —→ closedStarReady
closed-star-step₉ = ξ-⟨⟩ (ξ-ν
  (ξ-reveal {fresh = no-live-anchor} (ξ-ν
    (conceal-reveal (result-val starShiftedSeed-value)))))

closed-star-step₁₀ :
  emptyEnv ⊢ closedStarReady —→ closedStarEndpoint
closed-star-step₁₀ =
  float-⟨⟩ (result-ν (result-val starAdapter-value))

closed-star-trace : emptyEnv ⊢ closedStarSource —↠ closedStarEndpoint
closed-star-trace =
    closedStarSource
  —→⟨ closed-star-step₁ ⟩
    closedStarAfterOuterBeta
  —→⟨ closed-star-step₂ ⟩
    closedStarAfterOuterFloat
  —→⟨ closed-star-step₃ ⟩
    closedStarAfterOuterBoundary
  —→⟨ closed-star-step₄ ⟩
    closedStarAfterOuterLambda
  —→⟨ closed-star-step₅ ⟩
    closedStarAfterInnerBeta
  —→⟨ closed-star-step₆ ⟩
    closedStarAfterInnerFloat
  —→⟨ closed-star-step₇ ⟩
    closedStarAfterInnerBoundary
  —→⟨ closed-star-step₈ ⟩
    closedStarAfterInnerLambda
  —→⟨ closed-star-step₉ ⟩
    closedStarReady
  —→⟨ closed-star-step₁₀ ⟩
    closedStarEndpoint
  ∎

closedStarEndpoint-typed :
  emptyEnv ∣ [] ⊢ closedStarEndpoint ⦂ ℕᵗ
closedStarEndpoint-typed =
  preserve
    (preserve
      (preserve
        (preserve
          (preserve
            (preserve
              (preserve
                (preserve
                  (preserve
                    (preserve closedStarSource-typed closed-star-step₁)
                    closed-star-step₂)
                  closed-star-step₃)
                closed-star-step₄)
              closed-star-step₅)
            closed-star-step₆)
          closed-star-step₇)
        closed-star-step₈)
      closed-star-step₉)
    closed-star-step₁₀

closedStarEndpoint-no-step : ∀ {M′}
  → ¬ (emptyEnv ⊢ closedStarEndpoint —→ M′)
closedStarEndpoint-no-step (ξ-ν reduction) =
  starEndpoint-no-step reduction

closedStarEndpoint-not-result : ¬ Result closedStarEndpoint
closedStarEndpoint-not-result (result-ν result) =
  starEndpoint-not-result result

closedStarEndpoint-no-progress :
  ¬ Progress emptyEnv closedStarEndpoint
closedStarEndpoint-no-progress (step reduction) =
  closedStarEndpoint-no-step reduction
closedStarEndpoint-no-progress (done result) =
  closedStarEndpoint-not-result result
