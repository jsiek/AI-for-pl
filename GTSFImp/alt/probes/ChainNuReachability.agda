module alt.probes.ChainNuReachability where

-- File Charter:
--   * Rechecks whether source-shaped type applications reach the old chain-ν
--     adapter gaps after the U46 immobile transition.
--   * U50 changes the answer: in both an application and a ★ projection, the
--     first β-Λ allocation reaches a reveal-headed lambda, and reveal-polarity
--     SCWRAP now steps inside the ν.  Both updated stepping traces are checked.
--   * Both sources are closed in the empty environment and contain no ν or
--     mismatched adapter syntax; all boundary nodes are compile-style.

open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)
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
open import alt.ThetaTermSubst using (rep?-here)
open import alt.ThetaPreservation using (preserve)
open import alt.ThetaProgress using (Progress; step; done; failed)

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

identityBody : ∀ {Δ} → Ty (suc Δ)
identityBody = ＇ zero ⇒ ＇ zero

emptyEnv : TyEnv 0 0 Vec.[]
emptyEnv = ∅

closedPolyBody : Term 0 2
closedPolyBody = ƛ ＇ zero ˙ ` zero

closedPolyIdentity : Term 0 1
closedPolyIdentity = Λ closedPolyBody

closedPolyApplied : Term 0 1
closedPolyApplied = closedPolyIdentity ⦂∀ identityBody [ ＇ zero ]

closedPolyBody-value : Value closedPolyBody
closedPolyBody-value = ƛ ＇ zero ˙ ` zero

closedPolyIdentity-typed :
  emptyEnv ,typ ∣
    ((＇ zero) at currentScope (emptyEnv ,typ)) ∷ []
    ⊢ closedPolyIdentity ⦂ `∀ identityBody
closedPolyIdentity-typed = ⊢Λ (⊢ƛ (⊢` Z))

outerBody : Term 0 1
outerBody = ƛ ＇ zero ˙ (closedPolyApplied · ` zero)

outerPoly : Term 0 0
outerPoly = Λ outerBody

outerBody-value : Value outerBody
outerBody-value = ƛ ＇ zero ˙ (closedPolyApplied · ` zero)

outerBody-typed : emptyEnv ,typ ∣ [] ⊢ outerBody ⦂ ＇ zero ⇒ ＇ zero
outerBody-typed =
  ⊢ƛ (⊢· (⊢⦂∀ closedPolyIdentity-typed) (⊢` Z))

outerPoly-typed : emptyEnv ∣ [] ⊢ outerPoly ⦂ `∀ identityBody
outerPoly-typed = ⊢Λ outerBody-typed

outerInstantiationBody : Term 1 0
outerInstantiationBody =
  shiftᶿ outerBody ↑[ zero ≔ zero ]
    〖 zero ↑ identityBody {Δ = zero} 〗

shiftedOuterBody-value : Value (shiftᶿ outerBody)
shiftedOuterBody-value =
  ƛ ＇ zero ˙
    ((Λ (ƛ ＇ zero ˙ ` zero)) ⦂∀ identityBody [ ＇ zero ]) · ` zero

outerInstantiationBody-not-value : ¬ Value outerInstantiationBody
outerInstantiationBody-not-value (reveal-fun Vᵛ nonλ) = nonλ refl

outerInstantiationContractum : Ty 0 → Term 1 0
outerInstantiationContractum A =
  ƛ A ˙
    (((((Λ (ƛ ＇ zero ˙ ` zero))
        ⦂∀ identityBody [ ＇ zero ]) · ` zero)
      [ (` zero) ↓[ zero ≔ zero ] seal ])
      ↑[ zero ≔ zero ] unseal)

outer-domain-computes : ∀ (A : Ty 0)
  → outsideDomain? (emptyEnv ,:= A) zero zero
      seal (＇ zero) ≡ just A
outer-domain-computes A
    rewrite rep?-here {Ψ = emptyEnv} {A = A} =
  strengthenᵗ?-wkᵗ zero A

outerRegion-step : ∀ {A : Ty 0}
  → emptyEnv ⊢ ν[ A ] outerInstantiationBody —→
      ν[ A ] outerInstantiationContractum A
outerRegion-step {A = A} = ξ-ν (SCWRAP (outer-domain-computes A))

------------------------------------------------------------------------
-- Application context
------------------------------------------------------------------------

closedAppSeed : Term 0 0
closedAppSeed = ƛ ℕᵗ ˙ ` zero

closedAppSeed-value : Value closedAppSeed
closedAppSeed-value = ƛ ℕᵗ ˙ ` zero

closedAppSource : Term 0 0
closedAppSource =
  ((outerPoly ⦂∀ identityBody [ ℕ⇒ℕ ]) · closedAppSeed)
    · $ (κℕ zero)

closedAppEndpoint : Term 0 0
closedAppEndpoint =
  ((ν[ ℕ⇒ℕ ] outerInstantiationBody) · closedAppSeed) · $ (κℕ zero)

closedAppSource-typed : emptyEnv ∣ [] ⊢ closedAppSource ⦂ ℕᵗ
closedAppSource-typed =
  ⊢· (⊢· (⊢⦂∀ outerPoly-typed) (⊢ƛ (⊢` Z))) (⊢$ (κℕ zero))

closed-app-step : emptyEnv ⊢ closedAppSource —→ closedAppEndpoint
closed-app-step = ξ-·₁ (ξ-·₁ (β-Λ outerBody-value))

closed-app-trace : emptyEnv ⊢ closedAppSource —↠ closedAppEndpoint
closed-app-trace =
    closedAppSource
  —→⟨ closed-app-step ⟩
    closedAppEndpoint
  ∎

closedAppEndpoint-typed : emptyEnv ∣ [] ⊢ closedAppEndpoint ⦂ ℕᵗ
closedAppEndpoint-typed = preserve closedAppSource-typed closed-app-step

closedAppAfterSCWrap : Term 0 0
closedAppAfterSCWrap =
  ((ν[ ℕ⇒ℕ ] outerInstantiationContractum ℕ⇒ℕ) · closedAppSeed)
    · $ (κℕ zero)

closed-app-scwrap-step :
  emptyEnv ⊢ closedAppEndpoint —→ closedAppAfterSCWrap
closed-app-scwrap-step = ξ-·₁ (ξ-·₁ outerRegion-step)

closed-app-scwrap-trace :
  emptyEnv ⊢ closedAppSource —↠ closedAppAfterSCWrap
closed-app-scwrap-trace =
    closedAppSource
  —→⟨ closed-app-step ⟩
    closedAppEndpoint
  —→⟨ closed-app-scwrap-step ⟩
    closedAppAfterSCWrap
  ∎

closedAppAfterSCWrap-typed :
  emptyEnv ∣ [] ⊢ closedAppAfterSCWrap ⦂ ℕᵗ
closedAppAfterSCWrap-typed =
  preserve closedAppEndpoint-typed closed-app-scwrap-step

------------------------------------------------------------------------
-- ★ projection context
------------------------------------------------------------------------

closedStarSeed : Term 0 0
closedStarSeed = ($ (κℕ zero)) ⟨ (id {μ = idᶜ} (‵ `ℕ)) ! ⟩

closedStarSeed-value : Value closedStarSeed
closedStarSeed-value = inject ($ (κℕ zero))

closedStarSource : Term 0 0
closedStarSource =
  ((outerPoly ⦂∀ identityBody [ ★ ]) · closedStarSeed)
    ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

closedStarEndpoint : Term 0 0
closedStarEndpoint =
  ((ν[ ★ ] outerInstantiationBody) · closedStarSeed)
    ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

closedStarSource-typed : emptyEnv ∣ [] ⊢ closedStarSource ⦂ ℕᵗ
closedStarSource-typed =
  ⊢⟨⟩ (⊢· (⊢⦂∀ outerPoly-typed)
    (⊢⟨⟩ (⊢$ (κℕ zero)) ((id {μ = idᶜ} (‵ `ℕ)) !)))
    (？ (id {μ = idᶜ} (‵ `ℕ)))

closed-star-step : emptyEnv ⊢ closedStarSource —→ closedStarEndpoint
closed-star-step = ξ-⟨⟩ (ξ-·₁ (β-Λ outerBody-value))

closed-star-trace : emptyEnv ⊢ closedStarSource —↠ closedStarEndpoint
closed-star-trace =
    closedStarSource
  —→⟨ closed-star-step ⟩
    closedStarEndpoint
  ∎

closedStarEndpoint-typed : emptyEnv ∣ [] ⊢ closedStarEndpoint ⦂ ℕᵗ
closedStarEndpoint-typed = preserve closedStarSource-typed closed-star-step

closedStarAfterSCWrap : Term 0 0
closedStarAfterSCWrap =
  ((ν[ ★ ] outerInstantiationContractum ★) · closedStarSeed)
    ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

closed-star-scwrap-step :
  emptyEnv ⊢ closedStarEndpoint —→ closedStarAfterSCWrap
closed-star-scwrap-step = ξ-⟨⟩ (ξ-·₁ outerRegion-step)

closed-star-scwrap-trace :
  emptyEnv ⊢ closedStarSource —↠ closedStarAfterSCWrap
closed-star-scwrap-trace =
    closedStarSource
  —→⟨ closed-star-step ⟩
    closedStarEndpoint
  —→⟨ closed-star-scwrap-step ⟩
    closedStarAfterSCWrap
  ∎

closedStarAfterSCWrap-typed :
  emptyEnv ∣ [] ⊢ closedStarAfterSCWrap ⦂ ℕᵗ
closedStarAfterSCWrap-typed =
  preserve closedStarEndpoint-typed closed-star-scwrap-step
