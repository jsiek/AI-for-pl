module alt.probes.ScTyWrapValueRestriction where

-- File Charter:
--   * Checks that the restored Λ value restriction is stable under reduction.
--   * Records the former const-ν counterexample as a positive fixture: its
--     inert-cast body is a value, hence cannot step after const-ν is deleted.

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

anchor₀ : TyVar 1
anchor₀ = zero

no-live-anchor : anchor₀ ∉ᵛ (nothing Vec.∷ Vec.[])
no-live-anchor zero ()

regionEnv : TyEnv 1 2
    (just zero Vec.∷ nothing Vec.∷ Vec.[])
regionEnv = lambdaEnv ,begin[ zero ≔ zero ]⟨ no-live-anchor ⟩

region : Term 1 2
region = ν[ ℕᵗ ] ($ (κℕ zero))

region-result : Result region
region-result = result-ν (result-val ($ (κℕ zero)))

region-typed : regionEnv ∣ [] ⊢ region ⦂ ℕᵗ
region-typed = ⊢ν (⊢$ (κℕ zero))

wrapped : Term 1 1
wrapped = region ↑[ zero ≔ zero ] id↑

wrapped-typed : lambdaEnv ∣ [] ⊢ wrapped ⦂ ℕᵗ
wrapped-typed = ⊢reveal
  (rep?-typ {Θ = 1} {Ψ = baseEnv} {α = zero} {A = ℕᵗ}
    (rep?-here {Θ = 0} {Ψ = ∅} {A = ℕᵗ}))
  (⊢id↑ (‵ `ℕ)) region-typed

wrapped-value : Value wrapped
wrapped-value = region-result ↑[ zero ≔ zero ]
  adapter-region (result-val ($ (κℕ zero)))

sourceBody : Term 1 1
sourceBody = wrapped ⟨ ℕ! ⟩

sourceBody-typed : lambdaEnv ∣ [] ⊢ sourceBody ⦂ ★
sourceBody-typed = ⊢⟨⟩ wrapped-typed ℕ!

sourceBody-admissible : ΛBody sourceBody
sourceBody-admissible = body-result (result-val (wrapped-value 《 inj 》))

sourceBody-value : Value sourceBody
sourceBody-value = wrapped-value 《 inj 》

sourceBody-no-step : ∀ {M′}
  → ¬ (lambdaEnv ⊢ sourceBody —→ M′)
sourceBody-no-step = value-no-step sourceBody-value

sourceBody-stable : ∀ {M′}
  → lambdaEnv ⊢ sourceBody —→ M′
  → ΛBody M′
sourceBody-stable = ΛBody-stable sourceBody-admissible

source : Term 1 zero
source = Λ sourceBody

source-typed : baseEnv ∣ [] ⊢ source ⦂ `∀ ★
source-typed = ⊢Λ sourceBody-admissible sourceBody-typed

source-value : Value source
source-value = Λ (result-val sourceBody-value)

source-no-step : ∀ {M′}
  → ¬ (baseEnv ⊢ source —→ M′)
source-no-step = value-no-step source-value

stability-record :
  (lambdaEnv ∣ [] ⊢ sourceBody ⦂ ★)
  × (ΛBody sourceBody
    × (∀ {M′}
      → lambdaEnv ⊢ sourceBody —→ M′
      → ΛBody M′))
stability-record =
  sourceBody-typed , sourceBody-admissible , sourceBody-stable
