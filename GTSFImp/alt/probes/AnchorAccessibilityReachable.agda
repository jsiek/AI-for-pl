module alt.probes.AnchorAccessibilityReachable where

-- File Charter:
--   * Checks every crossing in both U40 source/endpoint traces and in every
--     intermediate of U44's escape and projection traces with
--     `AllAccessible`.
--   * Checks the escape/re-entry crossing spine isolated by
--     `EscapeReentryProbe.reentry-is-variable-tag-untag` using its Θ analogue:
--     outer reveal, exit conceal, sibling re-entry reveal, and inner conceal.
--   * At every conceal node in these configurations, the certificate carries
--     both `lookup σ Y ≡ just α` and `α ∈acc Ψ`; named instances below
--     expose the same liveness/accessibility pairs directly.

open import Data.Fin using (zero)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Vec.Base as Vec

open import Types
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.probes.AnchorAccessibility
import alt.probes.ChainNuReachability as U40
import alt.probes.EscapeLambdaBodyCounterexample as U44
import alt.probes.EscapeReentryProbe as Live
import proof.DGG.OneStep as Step

------------------------------------------------------------------------
-- U40: both one-step chain-ν reachability traces
------------------------------------------------------------------------

u40-no-live-anchor : ∀ {α : TyVar 1} → α ∉ᵛ Vec.[]
u40-no-live-anchor ()

u40-closed-poly-body-accessible :
  AllAccessible (U40.emptyEnv ,typ ,typ) U40.closedPolyBody
u40-closed-poly-body-accessible = acc-ƛ acc-`

u40-closed-poly-identity-accessible :
  AllAccessible (U40.emptyEnv ,typ) U40.closedPolyIdentity
u40-closed-poly-identity-accessible =
  acc-Λ u40-closed-poly-body-accessible

u40-closed-poly-applied-accessible :
  AllAccessible (U40.emptyEnv ,typ) U40.closedPolyApplied
u40-closed-poly-applied-accessible =
  acc-• u40-closed-poly-identity-accessible

u40-outer-body-accessible :
  AllAccessible (U40.emptyEnv ,typ) U40.outerBody
u40-outer-body-accessible =
  acc-ƛ (acc-· u40-closed-poly-applied-accessible acc-`)

u40-outer-poly-accessible :
  AllAccessible U40.emptyEnv U40.outerPoly
u40-outer-poly-accessible = acc-Λ u40-outer-body-accessible

u40-shifted-outer-body-accessible : ∀ (A : Ty 0)
  → AllAccessible
      ((U40.emptyEnv ,:= A)
        ,begin[ zero ≔ zero ]⟨ u40-no-live-anchor ⟩)
      (shiftᶿ U40.outerBody)
u40-shifted-outer-body-accessible A =
  acc-ƛ (acc-· (acc-• (acc-Λ (acc-ƛ acc-`))) acc-`)

u40-instantiation-body-accessible : ∀ (A : Ty 0)
  → AllAccessible (U40.emptyEnv ,:= A) U40.outerInstantiationBody
u40-instantiation-body-accessible A =
  acc-reveal {fresh = u40-no-live-anchor} refl
    (u40-shifted-outer-body-accessible A)

u40-closed-app-source-accessible :
  AllAccessible U40.emptyEnv U40.closedAppSource
u40-closed-app-source-accessible =
  acc-·
    (acc-· (acc-• u40-outer-poly-accessible) (acc-ƛ acc-`))
    acc-$

u40-closed-app-endpoint-accessible :
  AllAccessible U40.emptyEnv U40.closedAppEndpoint
u40-closed-app-endpoint-accessible =
  acc-·
    (acc-·
      (acc-ν (u40-instantiation-body-accessible U40.ℕ⇒ℕ))
      (acc-ƛ acc-`))
    acc-$

u40-app-trace-accessible :
  AllAccessible U40.emptyEnv U40.closedAppSource
  × AllAccessible U40.emptyEnv U40.closedAppEndpoint
u40-app-trace-accessible =
  u40-closed-app-source-accessible , u40-closed-app-endpoint-accessible

u40-closed-star-seed-accessible :
  AllAccessible U40.emptyEnv U40.closedStarSeed
u40-closed-star-seed-accessible = acc-⟨⟩ acc-$

u40-closed-star-source-accessible :
  AllAccessible U40.emptyEnv U40.closedStarSource
u40-closed-star-source-accessible =
  acc-⟨⟩
    (acc-· (acc-• u40-outer-poly-accessible)
      u40-closed-star-seed-accessible)

u40-closed-star-endpoint-accessible :
  AllAccessible U40.emptyEnv U40.closedStarEndpoint
u40-closed-star-endpoint-accessible =
  acc-⟨⟩
    (acc-· (acc-ν (u40-instantiation-body-accessible ★))
      u40-closed-star-seed-accessible)

u40-star-trace-accessible :
  AllAccessible U40.emptyEnv U40.closedStarSource
  × AllAccessible U40.emptyEnv U40.closedStarEndpoint
u40-star-trace-accessible =
  u40-closed-star-source-accessible , u40-closed-star-endpoint-accessible

------------------------------------------------------------------------
-- U44: escape values and every intermediate of both checked traces
------------------------------------------------------------------------

u44-public-payload-ended-accessible :
  AllAccessible (U44.regionEnv ,end[ zero ]) U44.publicPayload
u44-public-payload-ended-accessible = acc-⟨⟩ acc-$

u44-sealed-payload-accessible :
  AllAccessible U44.regionEnv U44.sealedPayload
u44-sealed-payload-accessible =
  acc-conceal refl refl u44-public-payload-ended-accessible

u44-tagged-payload-accessible :
  AllAccessible U44.regionEnv U44.taggedPayload
u44-tagged-payload-accessible = acc-⟨⟩ u44-sealed-payload-accessible

u44-source-body-accessible :
  AllAccessible U44.lambdaEnv U44.sourceBody
u44-source-body-accessible =
  acc-reveal {fresh = U44.no-live-anchor} refl
    u44-tagged-payload-accessible

u44-target-body-accessible :
  AllAccessible U44.lambdaEnv U44.targetBody
u44-target-body-accessible =
  acc-reveal {fresh = U44.no-live-anchor} refl
    u44-sealed-payload-accessible

u44-public-payload-accessible :
  AllAccessible U44.lambdaEnv U44.publicPayload
u44-public-payload-accessible = acc-⟨⟩ acc-$

u44-escape-trace-accessible :
  AllAccessible U44.lambdaEnv U44.sourceBody
  × (AllAccessible U44.lambdaEnv U44.targetBody
    × AllAccessible U44.lambdaEnv U44.publicPayload)
u44-escape-trace-accessible =
  u44-source-body-accessible ,
  u44-target-body-accessible ,
  u44-public-payload-accessible

u44-source-accessible : AllAccessible U44.baseEnv U44.source
u44-source-accessible = acc-Λ u44-source-body-accessible

u44-target-accessible : AllAccessible U44.baseEnv U44.target
u44-target-accessible = acc-Λ u44-target-body-accessible

u44-projection-source-accessible :
  AllAccessible U44.lambdaEnv U44.projectionSource
u44-projection-source-accessible = acc-⟨⟩ u44-source-body-accessible

u44-projection-after-resolve-accessible :
  AllAccessible U44.lambdaEnv U44.projectionAfterResolve
u44-projection-after-resolve-accessible =
  acc-⟨⟩ u44-target-body-accessible

u44-projection-ready-accessible :
  AllAccessible U44.lambdaEnv U44.projectionReady
u44-projection-ready-accessible = acc-⟨⟩ u44-public-payload-accessible

u44-projection-trace-accessible :
  AllAccessible U44.lambdaEnv U44.projectionSource
  × (AllAccessible U44.lambdaEnv U44.projectionAfterResolve
    × (AllAccessible U44.lambdaEnv U44.projectionReady
      × AllAccessible U44.lambdaEnv ($ (κℕ 7))))
u44-projection-trace-accessible =
  u44-projection-source-accessible ,
  u44-projection-after-resolve-accessible ,
  u44-projection-ready-accessible ,
  acc-$

------------------------------------------------------------------------
-- EscapeReentryProbe: the checked live spine and its Θ counterpart
------------------------------------------------------------------------

live-reentry-crossing-spine :
  Live.VariableTagUntagStep (Step.reduction Live.reentry-step)
live-reentry-crossing-spine = Live.reentry-is-variable-tag-untag

reentry-spine : Term 1 1
reentry-spine =
  (((($ (κℕ 9)) ↓[ zero ≔ zero ] seal)
      ↑[ zero ≔ zero ] unseal)
    ↓[ zero ≔ zero ] id↓)
  ↑[ zero ≔ zero ] id↑

reentry-spine-accessible :
  AllAccessible U44.lambdaEnv reentry-spine
reentry-spine-accessible =
  acc-reveal {fresh = U44.no-live-anchor} refl
    (acc-conceal refl refl
      (acc-reveal {fresh = U44.no-live-anchor} refl
        (acc-conceal refl refl acc-$)))

------------------------------------------------------------------------
-- Conceal liveness: live lookup and accessibility at each distinct node
------------------------------------------------------------------------

u44-conceal-live-accessible :
  Vec.lookup {A = Maybe (TyVar 1)}
      (just (zero {n = 0}) Vec.∷ nothing Vec.∷ Vec.[])
      (zero {n = 1})
    ≡ just (zero {n = 0})
  × (zero ∈acc U44.regionEnv)
u44-conceal-live-accessible = refl , refl

reentry-exited-anchor-accessible :
  zero ∈acc (U44.regionEnv ,end[ zero ])
reentry-exited-anchor-accessible = refl

reentry-inner-conceal-live-accessible :
  Vec.lookup {A = Maybe (TyVar 1)}
      (just (zero {n = 0}) Vec.∷ nothing Vec.∷ Vec.[])
      (zero {n = 1})
    ≡ just (zero {n = 0})
  × (zero ∈acc
      (U44.regionEnv ,end[ zero ]
        ,begin[ zero ≔ zero ]⟨ U44.no-live-anchor ⟩))
reentry-inner-conceal-live-accessible = refl , refl
