module alt.probes.RegionInterleavingReachable where

-- File Charter:
--   * Adapts the closed U40 nested-polymorphism source so the inner
--     polymorphic value closes over the outer term parameter.
--   * Checks the reduction prefix in which outer SCWRAP turns that capture
--     into a Y-conceal, then inner β-Λ and SCWRAP put the surviving conceal
--     beneath a fresh X-reveal.
--   * The endpoint has typing path
--     `begin Y ; ν X ; begin X ; end Y`, so region interleaving is reachable
--     from a closed source containing no ν/reveal/conceal syntax.

open import Data.Bool using (true)
open import Data.Fin using (zero; suc)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
import Data.Vec.Base as Vec

open import Types
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction
open import alt.ThetaTermSubst
open import alt.ThetaPreservation using (preserve)
open import alt.probes.AnchorAccessibility using (_∈acc_)
open import alt.probes.RegionBracketingAudit using (ruleMintedOnly)
import alt.probes.ChainNuReachability as U40
open U40 using (_⊢_—↠_; _∎; _—→⟨_⟩_)

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

ℕ⇒ℕ : ∀ {Δ} → Ty Δ
ℕ⇒ℕ = ℕᵗ ⇒ ℕᵗ

innerBodyTy : ∀ {Δ} → Ty (suc (suc Δ))
innerBodyTy = ＇ zero ⇒ ＇ suc zero

outerBodyTy : ∀ {Δ} → Ty (suc Δ)
outerBodyTy = ＇ zero ⇒ (＇ zero ⇒ ＇ zero)

emptyEnv : TyEnv 0 0 Vec.[]
emptyEnv = ∅

outer-fresh : zero {n = 0} ∉ᵛ Vec.[]
outer-fresh ()

capturingInnerBody : Term 0 2
capturingInnerBody = ƛ ＇ zero ˙ ` suc zero

capturingPoly : Term 0 1
capturingPoly = Λ capturingInnerBody

capturingApplied : Term 0 1
capturingApplied = capturingPoly ⦂∀ innerBodyTy [ ＇ zero ]

outerBody : Term 0 1
outerBody = ƛ ＇ zero ˙ capturingApplied

outerPoly : Term 0 0
outerPoly = Λ outerBody

source : Term 0 0
source = (outerPoly ⦂∀ outerBodyTy [ ℕᵗ ]) · $ (κℕ 7)

capturingPoly-typed :
  emptyEnv ,typ ∣ ((＇ zero) at currentScope (emptyEnv ,typ)) ∷ []
    ⊢ capturingPoly ⦂ `∀ innerBodyTy
capturingPoly-typed = ⊢Λ (⊢ƛ (⊢` (S Z)))

capturingApplied-typed :
  emptyEnv ,typ ∣ ((＇ zero) at currentScope (emptyEnv ,typ)) ∷ []
    ⊢ capturingApplied ⦂ ＇ zero ⇒ ＇ zero
capturingApplied-typed = ⊢⦂∀ capturingPoly-typed

outerBody-typed :
  emptyEnv ,typ ∣ [] ⊢ outerBody ⦂ outerBodyTy
outerBody-typed = ⊢ƛ capturingApplied-typed

outerPoly-typed : emptyEnv ∣ [] ⊢ outerPoly ⦂ `∀ outerBodyTy
outerPoly-typed = ⊢Λ outerBody-typed

source-typed : emptyEnv ∣ [] ⊢ source ⦂ ℕ⇒ℕ
source-typed = ⊢· (⊢⦂∀ outerPoly-typed) (⊢$ (κℕ 7))

source-closed-and-crossing-free : ruleMintedOnly source ≡ true
source-closed-and-crossing-free = refl

outerAllocated : Term 0 0
outerAllocated =
  (ν[ ℕᵗ ]
    (shiftᶿ outerBody
      ↑[ zero ≔ zero ] 〖 zero ↑ outerBodyTy {Δ = zero} 〗))
  · $ (κℕ 7)

outer-allocation-step : emptyEnv ⊢ source —→ outerAllocated
outer-allocation-step = ξ-·₁ (β-Λ outerBody-typed-value)
  where
  outerBody-typed-value : Value outerBody
  outerBody-typed-value = ƛ ＇ zero ˙ capturingApplied

outerInstantiationContractum : Term 1 0
outerInstantiationContractum =
  ƛ ℕᵗ ˙
    ((shiftᶿ capturingApplied
      [ (` zero) ↓[ zero ≔ zero ] seal ])
      ↑[ zero ≔ zero ] (seal ↦↑ unseal))

outerAfterSCWrap : Term 0 0
outerAfterSCWrap =
  (ν[ ℕᵗ ] outerInstantiationContractum) · $ (κℕ 7)

outer-domain-computes :
  outsideDomain? (emptyEnv ,:= ℕᵗ) zero zero
    seal (＇ zero) ≡ just ℕᵗ
outer-domain-computes = strengthenᵗ?-wkᵗ zero ℕᵗ

outer-scwrap-step : emptyEnv ⊢ outerAllocated —→ outerAfterSCWrap
outer-scwrap-step = ξ-·₁ (ξ-ν (SCWRAP outer-domain-computes))

outerAfterNuWrap : Term 0 0
outerAfterNuWrap =
  (ƛ ℕᵗ ˙ ν[ ℕᵗ ]
    ((shiftᶿ capturingApplied
      [ (` zero) ↓[ zero ≔ zero ] seal ])
      ↑[ zero ≔ zero ] (seal ↦↑ unseal)))
  · $ (κℕ 7)

outer-nuwrap-step : emptyEnv ⊢ outerAfterSCWrap —→ outerAfterNuWrap
outer-nuwrap-step = ξ-·₁ NUWRAP

outerWrapper : Term 1 1
outerWrapper = ($ (κℕ 7)) ↓[ zero ≔ zero ] seal

capturingAfterOuterBeta : Term 1 1
capturingAfterOuterBeta =
  (Λ (ƛ ＇ zero ˙
    (($ (κℕ 7)) ↓[ suc zero ≔ zero ] seal)))
    ⦂∀ innerBodyTy [ ＇ zero ]

outerAfterBeta : Term 0 0
outerAfterBeta =
  ν[ ℕᵗ ]
    (capturingAfterOuterBeta
      ↑[ zero ≔ zero ] (seal ↦↑ unseal))

outer-beta-step : emptyEnv ⊢ outerAfterNuWrap —→ outerAfterBeta
outer-beta-step = β ($ (κℕ 7))

innerAllocatedBody : Term 2 1
innerAllocatedBody =
  shiftᶿ (ƛ ＇ zero ˙
    (($ (κℕ 7)) ↓[ suc zero ≔ zero ] seal))
    ↑[ zero ≔ zero ] 〖 zero ↑ innerBodyTy {Δ = zero} 〗

innerAllocated : Term 1 1
innerAllocated = ν[ ＇ zero ] innerAllocatedBody

outerAfterInnerAllocation : Term 0 0
outerAfterInnerAllocation =
  ν[ ℕᵗ ]
    (innerAllocated
      ↑[ zero ≔ zero ] (seal ↦↑ unseal))

inner-body-value : Value {Θ = 1} {Δ = 2}
  (ƛ ＇ zero ˙ (($ (κℕ 7)) ↓[ suc zero ≔ zero ] seal))
inner-body-value =
  ƛ ＇ zero ˙ (($ (κℕ 7)) ↓[ suc zero ≔ zero ] seal)

inner-allocation-step :
  emptyEnv ⊢ outerAfterBeta —→ outerAfterInnerAllocation
inner-allocation-step =
  ξ-ν (ξ-reveal {fresh = outer-fresh} (β-Λ inner-body-value))

closed-source-to-first-interleaving :
  emptyEnv ⊢ source —↠ outerAfterInnerAllocation
closed-source-to-first-interleaving =
    source
  —→⟨ outer-allocation-step ⟩
    outerAllocated
  —→⟨ outer-scwrap-step ⟩
    outerAfterSCWrap
  —→⟨ outer-nuwrap-step ⟩
    outerAfterNuWrap
  —→⟨ outer-beta-step ⟩
    outerAfterBeta
  —→⟨ inner-allocation-step ⟩
    outerAfterInnerAllocation
  ∎

firstInterleaving-typed :
  emptyEnv ∣ [] ⊢ outerAfterInnerAllocation ⦂ ℕ⇒ℕ
firstInterleaving-typed =
  preserve
    (preserve
      (preserve
        (preserve
          (preserve source-typed outer-allocation-step)
          outer-scwrap-step)
        outer-nuwrap-step)
      outer-beta-step)
    inner-allocation-step

inner-fresh : zero {n = 1} ∉ᵛ (just (suc zero) Vec.∷ Vec.[])
inner-fresh zero ()

reachableOuterOpen : TyEnv 1 1 (just zero Vec.∷ Vec.[])
reachableOuterOpen =
  (emptyEnv ,:= ℕᵗ) ,begin[ zero ≔ zero ]⟨ outer-fresh ⟩

reachableInnerAllocation :
  TyEnv 2 1 (just (suc zero) Vec.∷ Vec.[])
reachableInnerAllocation = reachableOuterOpen ,:= ＇ zero

reachableInterleaved : TyEnv 2 2
    (just zero Vec.∷ just (suc zero) Vec.∷ Vec.[])
reachableInterleaved =
  reachableInnerAllocation ,begin[ zero ≔ zero ]⟨ inner-fresh ⟩

reachablePocket : TyEnv 2 1 (just zero Vec.∷ Vec.[])
reachablePocket = reachableInterleaved ,end[ suc zero ]

reachable-X-live :
  Vec.lookup {A = Maybe (TyVar 2)}
      (just (zero {n = 1}) Vec.∷ Vec.[]) (zero {n = 0})
    ≡ just (zero {n = 1})
reachable-X-live = refl

reachable-X-inaccessible : ¬ (zero ∈acc reachablePocket)
reachable-X-inaccessible ()

interleavedInnerBody : Term 2 1
interleavedInnerBody =
  ƛ (＇ zero) ˙
    ((($ (κℕ 7)) ↓[ suc zero ≔ suc zero ] seal)
      ↑[ zero ≔ zero ] id↑)

interleavedInner : Term 1 1
interleavedInner = ν[ ＇ zero ] interleavedInnerBody

interleavedEndpoint : Term 0 0
interleavedEndpoint =
  ν[ ℕᵗ ]
    (interleavedInner
      ↑[ zero ≔ zero ] (seal ↦↑ unseal))

inner-domain-computes :
  outsideDomain?
      ((emptyEnv ,:= ℕᵗ)
        ,begin[ zero ≔ zero ]⟨ (λ ()) ⟩
        ,:= ＇ zero)
      zero zero seal (＇ zero)
    ≡ just (＇ zero)
inner-domain-computes = strengthenᵗ?-wkᵗ zero (＇ zero)

inner-scwrap-step :
  emptyEnv ⊢ outerAfterInnerAllocation —→ interleavedEndpoint
inner-scwrap-step =
  ξ-ν
    (ξ-reveal {fresh = outer-fresh}
      (ξ-ν (SCWRAP inner-domain-computes)))

closed-source-to-interleaving :
  emptyEnv ⊢ source —↠ interleavedEndpoint
closed-source-to-interleaving =
    source
  —→⟨ outer-allocation-step ⟩
    outerAllocated
  —→⟨ outer-scwrap-step ⟩
    outerAfterSCWrap
  —→⟨ outer-nuwrap-step ⟩
    outerAfterNuWrap
  —→⟨ outer-beta-step ⟩
    outerAfterBeta
  —→⟨ inner-allocation-step ⟩
    outerAfterInnerAllocation
  —→⟨ inner-scwrap-step ⟩
    interleavedEndpoint
  ∎

interleavedEndpoint-typed :
  emptyEnv ∣ [] ⊢ interleavedEndpoint ⦂ ℕ⇒ℕ
interleavedEndpoint-typed =
  preserve firstInterleaving-typed inner-scwrap-step
