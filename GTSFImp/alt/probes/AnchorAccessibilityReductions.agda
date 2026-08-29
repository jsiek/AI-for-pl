module alt.probes.AnchorAccessibilityReductions where

-- File Charter:
--   * Checks accessibility across representative wrapper steps: both live
--     ScTyWrap polarities and both prospective eager SCWRAP function shapes.
--     The latter remain untypable for the independent term-context reason
--     recorded by U47b/U48, but their crossing anchors are accessible.
--   * Checks non-vacuous NUWRAP and NUTYWRAP instances whose bodies contain
--     crossings, plus the vacuous const-ν dissolution.
--   * Checks representative guarded `ν-push-conceal` and `ν-gc-conceal`
--     shapes from the conceal-meets-ν proposal.  The push guard is a computed
--     strengthening; the moved conceal anchor unshifts.  The gc instance
--     carries a whole-term unshift witness and removes the young ν.
--   * Every conceal certificate supplies its live lookup and its accessible
--     anchor, exposing the preservation obligations that an installation
--     would add for β-conceal-∀, NUTYWRAP, ν-push-conceal, and
--     ν-gc-conceal.

open import Data.Fin using (zero; suc)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Vec.Base as Vec

open import Types
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction
open import alt.probes.AnchorAccessibility
import alt.ThetaRegression as Regression
import alt.probes.ChainNuReachability as U40
import alt.probes.EagerSCWrapPreservationCounterexample as SCWRAP
import alt.probes.EscapeLambdaBodyCounterexample as U44

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

no-live-empty : ∀ {Θ} {α : TyVar Θ} → α ∉ᵛ Vec.[]
no-live-empty ()

no-live-one-lexical : ∀ {Θ} {α : TyVar Θ}
  → α ∉ᵛ (nothing Vec.∷ Vec.[])
no-live-one-lexical zero ()

no-live-two-lexical : ∀ {Θ} {α : TyVar Θ}
  → α ∉ᵛ (nothing Vec.∷ nothing Vec.∷ Vec.[])
no-live-two-lexical zero ()
no-live-two-lexical (suc zero) ()

------------------------------------------------------------------------
-- SCWRAP function shapes: accessibility is not their typing obstruction
------------------------------------------------------------------------

scwrap-reveal-redex-accessible :
  AllAccessible SCWRAP.baseEnv SCWRAP.revealRedex
scwrap-reveal-redex-accessible =
  acc-reveal {fresh = SCWRAP.no-live-anchor} refl (acc-ƛ acc-`)

scwrap-reveal-contractum-accessible :
  AllAccessible SCWRAP.baseEnv SCWRAP.revealContractum
scwrap-reveal-contractum-accessible =
  acc-ƛ
    (acc-reveal {fresh = SCWRAP.no-live-anchor} refl
      (acc-conceal refl refl acc-`))

scwrap-reveal-preserves-accessibility :
  AllAccessible SCWRAP.baseEnv SCWRAP.revealRedex
  → AllAccessible SCWRAP.baseEnv SCWRAP.revealContractum
scwrap-reveal-preserves-accessibility redex-accessible =
  scwrap-reveal-contractum-accessible

scwrap-conceal-redex-accessible :
  AllAccessible SCWRAP.crossedEnv SCWRAP.concealRedex
scwrap-conceal-redex-accessible =
  acc-conceal refl refl (acc-ƛ acc-`)

scwrap-conceal-contractum-accessible :
  AllAccessible SCWRAP.crossedEnv SCWRAP.concealContractum
scwrap-conceal-contractum-accessible =
  acc-ƛ
    (acc-conceal refl refl
      (acc-reveal {fresh = SCWRAP.no-live-anchor} refl acc-`))

scwrap-conceal-preserves-accessibility :
  AllAccessible SCWRAP.crossedEnv SCWRAP.concealRedex
  → AllAccessible SCWRAP.crossedEnv SCWRAP.concealContractum
scwrap-conceal-preserves-accessibility redex-accessible =
  scwrap-conceal-contractum-accessible

------------------------------------------------------------------------
-- Live ScTyWrap rules under Λ
------------------------------------------------------------------------

scTyWrap-reveal-redex-accessible :
  AllAccessible (Regression.βΛ-Ψ ,typ) Regression.βΛ-body
scTyWrap-reveal-redex-accessible =
  acc-reveal {fresh = Regression.nothing-fresh} refl (acc-Λ acc-$)

scTyWrap-reveal-contractum-accessible :
  AllAccessible (Regression.βΛ-Ψ ,typ) Regression.βΛ-body-pushed
scTyWrap-reveal-contractum-accessible =
  acc-Λ
    (acc-reveal {fresh = no-live-two-lexical} refl acc-$)

scTyWrap-reveal-step :
  Regression.βΛ-Ψ ,typ ⊢ Regression.βΛ-body —→
    Regression.βΛ-body-pushed
scTyWrap-reveal-step = Regression.βΛ-body-step₁

scTyWrap-reveal-preserves-accessibility :
  AllAccessible (Regression.βΛ-Ψ ,typ) Regression.βΛ-body
  → AllAccessible (Regression.βΛ-Ψ ,typ) Regression.βΛ-body-pushed
scTyWrap-reveal-preserves-accessibility redex-accessible =
  scTyWrap-reveal-contractum-accessible

scTyWrap-conceal-redex : Term 1 2
scTyWrap-conceal-redex =
  (Λ ($ (κℕ 7))) ↓[ zero ≔ zero ] `∀↓ id↓

scTyWrap-conceal-contractum : Term 1 2
scTyWrap-conceal-contractum =
  Λ (($ (κℕ 7)) ↓[ suc zero ≔ zero ] id↓)

scTyWrap-conceal-redex-accessible :
  AllAccessible U44.regionEnv scTyWrap-conceal-redex
scTyWrap-conceal-redex-accessible =
  acc-conceal refl refl (acc-Λ acc-$)

scTyWrap-conceal-contractum-accessible :
  AllAccessible U44.regionEnv scTyWrap-conceal-contractum
scTyWrap-conceal-contractum-accessible =
  acc-Λ (acc-conceal refl refl acc-$)

scTyWrap-conceal-step :
  U44.regionEnv ⊢ scTyWrap-conceal-redex —→
    scTyWrap-conceal-contractum
scTyWrap-conceal-step = β-conceal-∀ ($ (κℕ 7))

scTyWrap-conceal-preserves-accessibility :
  AllAccessible U44.regionEnv scTyWrap-conceal-redex
  → AllAccessible U44.regionEnv scTyWrap-conceal-contractum
scTyWrap-conceal-preserves-accessibility redex-accessible =
  scTyWrap-conceal-contractum-accessible

------------------------------------------------------------------------
-- ν dissolution: NUWRAP, NUTYWRAP, and const-ν
------------------------------------------------------------------------

nuWrap-body : Term 1 0
nuWrap-body = ($ (κℕ 1)) ↑[ zero ≔ zero ] id↑

nuWrap-redex : Term 0 0
nuWrap-redex = ν[ ℕᵗ ] (ƛ ℕᵗ ˙ nuWrap-body)

nuWrap-contractum : Term 0 0
nuWrap-contractum = ƛ ℕᵗ ˙ ν[ ℕᵗ ] nuWrap-body

nuWrap-redex-accessible : AllAccessible U40.emptyEnv nuWrap-redex
nuWrap-redex-accessible =
  acc-ν
    (acc-ƛ
      (acc-reveal {fresh = no-live-empty} refl acc-$))

nuWrap-contractum-accessible :
  AllAccessible U40.emptyEnv nuWrap-contractum
nuWrap-contractum-accessible =
  acc-ƛ
    (acc-ν
      (acc-reveal {fresh = no-live-empty} refl acc-$))

nuWrap-step : U40.emptyEnv ⊢ nuWrap-redex —→ nuWrap-contractum
nuWrap-step = NUWRAP

nuWrap-preserves-accessibility :
  AllAccessible U40.emptyEnv nuWrap-redex
  → AllAccessible U40.emptyEnv nuWrap-contractum
nuWrap-preserves-accessibility redex-accessible =
  nuWrap-contractum-accessible

nuTyWrap-body : Term 1 1
nuTyWrap-body = ($ (κℕ 2)) ↑[ zero ≔ zero ] id↑

nuTyWrap-redex : Term 0 0
nuTyWrap-redex = ν[ ℕᵗ ] (Λ nuTyWrap-body)

nuTyWrap-contractum : Term 0 0
nuTyWrap-contractum = Λ (ν[ ⇑ᵗ ℕᵗ ] nuTyWrap-body)

nuTyWrap-redex-accessible :
  AllAccessible U40.emptyEnv nuTyWrap-redex
nuTyWrap-redex-accessible =
  acc-ν
    (acc-Λ
      (acc-reveal {fresh = no-live-one-lexical} refl acc-$))

nuTyWrap-contractum-accessible :
  AllAccessible U40.emptyEnv nuTyWrap-contractum
nuTyWrap-contractum-accessible =
  acc-Λ
    (acc-ν
      (acc-reveal {fresh = no-live-one-lexical} refl acc-$))

nuTyWrap-step :
  U40.emptyEnv ⊢ nuTyWrap-redex —→ nuTyWrap-contractum
nuTyWrap-step = NUTYWRAP

nuTyWrap-preserves-accessibility :
  AllAccessible U40.emptyEnv nuTyWrap-redex
  → AllAccessible U40.emptyEnv nuTyWrap-contractum
nuTyWrap-preserves-accessibility redex-accessible =
  nuTyWrap-contractum-accessible

constNu-redex : Term 0 0
constNu-redex = ν[ ℕᵗ ] ($ (κℕ 3))

constNu-redex-accessible : AllAccessible U40.emptyEnv constNu-redex
constNu-redex-accessible = acc-ν acc-$

constNu-contractum-accessible :
  AllAccessible U40.emptyEnv ($ (κℕ 3))
constNu-contractum-accessible = acc-$

constNu-step : U40.emptyEnv ⊢ constNu-redex —→ $ (κℕ 3)
constNu-step = const-ν

constNu-preserves-accessibility :
  AllAccessible U40.emptyEnv constNu-redex
  → AllAccessible U40.emptyEnv ($ (κℕ 3))
constNu-preserves-accessibility redex-accessible =
  constNu-contractum-accessible

------------------------------------------------------------------------
-- Proposed guarded ν-push-conceal
------------------------------------------------------------------------

nuPush-body : Term 2 1
nuPush-body = ($ (κℕ 4)) ↑[ zero ≔ suc zero ] id↑

nuPush-redex : Term 1 2
nuPush-redex =
  ν[ ℕᵗ ] (nuPush-body ↓[ zero ≔ suc zero ] id↓)

nuPush-contractum : Term 1 2
nuPush-contractum =
  (ν[ ℕᵗ ] nuPush-body) ↓[ zero ≔ zero ] id↓

nuPush-entry-strengthens :
  strengthenᵗ? (zero {n = 1}) (ℕᵗ {Δ = 2})
    ≡ just (ℕᵗ {Δ = 1})
nuPush-entry-strengthens = refl

nuPush-redex-accessible :
  AllAccessible U44.regionEnv nuPush-redex
nuPush-redex-accessible =
  acc-ν
    (acc-conceal refl refl
      (acc-reveal {fresh = no-live-one-lexical} refl acc-$))

nuPush-contractum-accessible :
  AllAccessible U44.regionEnv nuPush-contractum
nuPush-contractum-accessible =
  acc-conceal refl refl
    (acc-ν
      (acc-reveal {fresh = no-live-one-lexical} refl acc-$))

nuPush-preserves-accessibility :
  AllAccessible U44.regionEnv nuPush-redex
  → AllAccessible U44.regionEnv nuPush-contractum
nuPush-preserves-accessibility redex-accessible =
  nuPush-contractum-accessible

------------------------------------------------------------------------
-- Proposed ν-gc-conceal: whole-term unshift removes the young ν
------------------------------------------------------------------------

data WholeUnshift : ∀ {Θ Δ}
    → Term (suc Θ) Δ → Term Θ Δ → Set where
  whole-shift : ∀ {Θ Δ} {M : Term Θ Δ}
      ---------------------------
    → WholeUnshift (shiftᶿ M) M

nuGc-body : Term 1 1
nuGc-body = ($ (κℕ 5)) ↑[ zero ≔ zero ] id↑

nuGc-redex : Term 1 2
nuGc-redex =
  ν[ ＇ zero ]
    ((shiftᶿ nuGc-body) ↓[ zero ≔ suc zero ] id↓)

nuGc-contractum : Term 1 2
nuGc-contractum = nuGc-body ↓[ zero ≔ zero ] id↓

nuGc-entry-not-strengthenable :
  strengthenᵗ? (zero {n = 1}) (＇ (zero {n = 1})) ≡ nothing
nuGc-entry-not-strengthenable = refl

nuGc-body-whole-unshift : WholeUnshift (shiftᶿ nuGc-body) nuGc-body
nuGc-body-whole-unshift = whole-shift

nuGc-redex-accessible : AllAccessible U44.regionEnv nuGc-redex
nuGc-redex-accessible =
  acc-ν
    (acc-conceal refl refl
      (acc-reveal {fresh = no-live-one-lexical} refl acc-$))

nuGc-contractum-accessible :
  AllAccessible U44.regionEnv nuGc-contractum
nuGc-contractum-accessible =
  acc-conceal refl refl
    (acc-reveal {fresh = no-live-one-lexical} refl acc-$)

nuGc-preserves-accessibility :
  AllAccessible U44.regionEnv nuGc-redex
  → AllAccessible U44.regionEnv nuGc-contractum
nuGc-preserves-accessibility redex-accessible =
  nuGc-contractum-accessible
