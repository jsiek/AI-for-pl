module alt.probes.ScTyWrapValueRestriction where

-- File Charter:
--   * Records the U46 replacement for the former ΛBody-stability probe.
--   * Typing admits a Λ whose body is reducible, while the λB value grammar
--     does not classify that Λ as a value until its body reaches a value.
--   * The historical const-ν overlap is now intentional transient behavior.

open import Data.Fin using (zero)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero)
open import Data.Product using (_×_; _,_)
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
open import alt.ThetaTermSubst using (rep?-here; rep?-typ)

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

ℕ! : ∀ {Δ} → _∼_ {Δ = Δ} ℕᵗ ★
ℕ! = id (‵ `ℕ) !

baseEnv : TyEnv 1 zero Vec.[]
baseEnv = ∅ ,:= ℕᵗ

lambdaEnv : TyEnv 1 1 (nothing Vec.∷ Vec.[])
lambdaEnv = baseEnv ,typ

no-live-anchor : zero {n = zero} ∉ᵛ (nothing Vec.∷ Vec.[])
no-live-anchor zero ()

regionEnv : TyEnv 1 2
    (just zero Vec.∷ nothing Vec.∷ Vec.[])
regionEnv = lambdaEnv ,begin[ zero ≔ zero ]⟨ no-live-anchor ⟩

region : Term 1 2
region = ν[ ＇ zero ] $ (κℕ zero)

region-typed : regionEnv ∣ [] ⊢ region ⦂ ℕᵗ
region-typed = ⊢ν (⊢$ (κℕ zero))

wrapped : Term 1 1
wrapped = region ↑[ zero ≔ zero ] id↑

wrapped-typed : lambdaEnv ∣ [] ⊢ wrapped ⦂ ℕᵗ
wrapped-typed = ⊢reveal
  (rep?-typ {Θ = 1} {Ψ = baseEnv} {α = zero} {A = ℕᵗ}
    (rep?-here {Θ = 0} {Ψ = ∅} {A = ℕᵗ}))
  (⊢id↑ (‵ `ℕ)) region-typed

sourceBody : Term 1 1
sourceBody = wrapped ⟨ ℕ! ⟩

middleBody : Term 1 1
middleBody = (($ (κℕ zero)) ↑[ zero ≔ zero ] id↑) ⟨ ℕ! ⟩

targetBody : Term 1 1
targetBody = ($ (κℕ zero)) ⟨ ℕ! ⟩

sourceBody-typed : lambdaEnv ∣ [] ⊢ sourceBody ⦂ ★
sourceBody-typed = ⊢⟨⟩ wrapped-typed ℕ!

sourceBody-step : lambdaEnv ⊢ sourceBody —→ middleBody
sourceBody-step = ξ-⟨⟩ (ξ-reveal {fresh = no-live-anchor} const-ν)

middleBody-step : lambdaEnv ⊢ middleBody —→ targetBody
middleBody-step = ξ-⟨⟩ id-reveal

targetBody-value : Value targetBody
targetBody-value = inject ($ (κℕ zero))

source : Term 1 zero
source = Λ sourceBody

target : Term 1 zero
target = Λ targetBody

source-typed : baseEnv ∣ [] ⊢ source ⦂ `∀ ★
source-typed = ⊢Λ sourceBody-typed

wrapped-not-value : ¬ Value wrapped
wrapped-not-value (adapter-region value () occurrence)

source-not-value : ¬ Value source
source-not-value (Λ (inject value)) = wrapped-not-value value
source-not-value (Λ (_ 《 () 》))

source-step : baseEnv ⊢ source —→ Λ middleBody
source-step = ξ-Λ sourceBody-step

target-value : Value target
target-value = Λ targetBody-value

value-grammar-record :
  (baseEnv ∣ [] ⊢ source ⦂ `∀ ★)
  × (¬ Value source × Value target)
value-grammar-record = source-typed , source-not-value , target-value
