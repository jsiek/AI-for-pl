module alt.probes.EscapeLambdaBodyCounterexample where

-- File Charter:
--   * Retains the history of the U44 counterexample and records its U46
--     resolution.  At representation `C = ★`, smart injection is bare.
--   * With ΛBody removed from typing, `ξ-Λ` carries the escaping reduction and
--     preservation checks directly; no value-stability premise is required.
--   * The complete escape reaches the public value `7 ⟨ ℕ ! ⟩`; an outside
--     `？ℕ` observer then reaches `7`.  Public-on-exit is deliberate and keeps
--     parametricity scoped to the live region.
--
-- Historically the proposed contractum added `⟨ id ★ ⟩`.  That non-value cast
-- refuted ΛBody stability.  U44b removed the cast at ★, and U46 removed the
-- typing predicate whose stability had made the overlap load bearing.

open import Data.Fin using (zero)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)
import Data.Vec.Base as Vec

open import Types
open import TermCtx
open import Consistency
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction
open import alt.ThetaPreservation using (preserve)

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

ℕ! : ∀ {Δ} → _∼_ {Δ = Δ} ℕᵗ ★
ℕ! = id (‵ `ℕ) !

pivot! : _∼_ {Δ = 2} (＇ zero) ★
pivot! = _! ⦃ Gᵍ = ＇ zero ⦄ ⦃ G∼★ = X∼★ᶜ refl ⦄
  (id (＇ zero)) ⦃ nonstar-X ⦄

baseEnv : TyEnv 1 zero Vec.[]
baseEnv = ∅ ,:= ★

lambdaEnv : TyEnv 1 1 (nothing Vec.∷ Vec.[])
lambdaEnv = baseEnv ,typ

no-live-anchor : zero {n = zero} ∉ᵛ (nothing Vec.∷ Vec.[])
no-live-anchor zero ()

regionEnv : TyEnv 1 2
    (just zero Vec.∷ nothing Vec.∷ Vec.[])
regionEnv = lambdaEnv ,begin[ zero ≔ zero ]⟨ no-live-anchor ⟩

publicPayload : Term 1 1
publicPayload = ($ (κℕ 7)) ⟨ ℕ! ⟩

sealedPayload : Term 1 2
sealedPayload = publicPayload ↓[ zero ≔ zero ] seal

taggedPayload : Term 1 2
taggedPayload = sealedPayload ⟨ pivot! ⟩

sourceBody : Term 1 1
sourceBody = taggedPayload ↑[ zero ≔ zero ] id↑

targetBody : Term 1 1
targetBody = sealedPayload ↑[ zero ≔ zero ] unseal

publicPayload-value : Value publicPayload
publicPayload-value = inject ($ (κℕ 7))

sealedPayload-value : Value sealedPayload
sealedPayload-value = seal-value publicPayload-value

publicPayload-typed :
  regionEnv ,end[ zero ] ∣ [] ⊢ publicPayload ⦂ ★
publicPayload-typed = ⊢⟨⟩ (⊢$ (κℕ 7)) ℕ!

sealedPayload-typed : regionEnv ∣ [] ⊢ sealedPayload ⦂ ＇ zero
sealedPayload-typed =
  ⊢conceal refl refl ⊢seal publicPayload-typed

taggedPayload-typed : regionEnv ∣ [] ⊢ taggedPayload ⦂ ★
taggedPayload-typed = ⊢⟨⟩ sealedPayload-typed pivot!

sourceBody-typed : lambdaEnv ∣ [] ⊢ sourceBody ⦂ ★
sourceBody-typed =
  ⊢reveal {fresh = no-live-anchor} refl (⊢id↑ ★) taggedPayload-typed

targetBody-typed : lambdaEnv ∣ [] ⊢ targetBody ⦂ ★
targetBody-typed =
  ⊢reveal {fresh = no-live-anchor} refl ⊢unseal sealedPayload-typed

sourceBody-step : lambdaEnv ⊢ sourceBody —→ targetBody
sourceBody-step =
  inject-reveal-resolve {μ = idᶜ} refl sealedPayload-value

source : Term 1 zero
source = Λ sourceBody

target : Term 1 zero
target = Λ targetBody

source-typed : baseEnv ∣ [] ⊢ source ⦂ `∀ ★
source-typed = ⊢Λ sourceBody-typed

source-step : baseEnv ⊢ source —→ target
source-step = ξ-Λ sourceBody-step

target-typed : baseEnv ∣ [] ⊢ target ⦂ `∀ ★
target-typed = preserve source-typed source-step

bare-escape-preservation-record :
  (baseEnv ∣ [] ⊢ source ⦂ `∀ ★)
  × ((baseEnv ⊢ source —→ target)
    × (baseEnv ∣ [] ⊢ target ⦂ `∀ ★))
bare-escape-preservation-record = source-typed , source-step , target-typed

targetBody-step : lambdaEnv ⊢ targetBody —→ publicPayload
targetBody-step = conceal-reveal publicPayload-value

escape-trace : lambdaEnv ⊢ sourceBody —↠ publicPayload
escape-trace =
    sourceBody
  —→⟨ sourceBody-step ⟩
    targetBody
  —→⟨ targetBody-step ⟩
    publicPayload
  ∎

projectionSource : Term 1 1
projectionSource = sourceBody ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

projectionAfterResolve : Term 1 1
projectionAfterResolve = targetBody ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

projectionReady : Term 1 1
projectionReady = publicPayload ⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩

projection-trace : lambdaEnv ⊢ projectionSource —↠ $ (κℕ 7)
projection-trace =
    projectionSource
  —→⟨ ξ-⟨⟩ sourceBody-step ⟩
    projectionAfterResolve
  —→⟨ ξ-⟨⟩ targetBody-step ⟩
    projectionReady
  —→⟨ tag-untag ($ (κℕ 7)) ⟩
    $ (κℕ 7)
  ∎
