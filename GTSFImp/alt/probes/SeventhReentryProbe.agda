module alt.probes.SeventhReentryProbe where

-- U20's seventh preservation obstruction.
--
-- Statement: closed one-step preservation fails for the current β-Λ rule.
-- Counterexample: instantiate the polymorphic identity at noncanonical alias
-- `＇1`; the redex has type `＇1 ⇒ ＇1` and takes the checked step below.
-- Why: public lookup under the fresh ν canonicalizes its representation to
-- the same anchor's minimum live alias `＇0`, so conversion typing forces the
-- contractum through `＇0` and rules out its advertised `＇1 ⇒ ＇1` type.

open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)

open import Types
open import TermCtx
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction
open import alt.ThetaTermSubst

seventh-Ψ : TyEnv (suc zero) (suc (suc zero))
seventh-Ψ =
  ((∅ ,:= ‵ `ℕ) ,begin[ zero ≔ zero ]) ,begin[ zero ≔ zero ]

seventh-C : Ty (suc (suc zero))
seventh-C = ＇ suc zero

seventh-B : Ty (suc (suc (suc zero)))
seventh-B = ＇ zero ⇒ ＇ zero

seventh-V : Term (suc zero) (suc (suc (suc zero)))
seventh-V = ƛ ＇ zero ˙ ` zero

seventh-V-value : Value seventh-V
seventh-V-value = ƛ ＇ zero ˙ ` zero

seventh-redex : Term (suc zero) (suc (suc zero))
seventh-redex = (Λ seventh-V) ⦂∀ seventh-B [ seventh-C ]

seventh-redex-⊢ : seventh-Ψ ∣ [] ⊢ seventh-redex
  ⦂ seventh-C ⇒ seventh-C
seventh-redex-⊢ = ⊢⦂∀ (⊢Λ (⊢ƛ (⊢` Z)))

seventh-contractum : Term (suc zero) (suc (suc zero))
seventh-contractum =
  ν[ seventh-C ]
    (shiftᶿ seventh-V
      ↑[ zero ≔ zero ] 〖 zero ↑ seventh-B 〗)

seventh-step : seventh-Ψ ⊢ seventh-redex —→ seventh-contractum
seventh-step = β-Λ seventh-V-value

seventh-canonical-lookup : seventh-Ψ ,:= seventh-C
  ∋rep zero ≔ ＇ zero
seventh-canonical-lookup = ∋rep-here

seventh-conversion-representation : ∀ {C D : Ty (suc (suc zero))}
  → ⊢↑[ zero ⦂ wkᵗ zero C ] (seal ↦↑ unseal)
      ⦂ ＇ zero ⇒ ＇ zero ↝ wkᵗ zero (D ⇒ D)
  → C ≡ D
seventh-conversion-representation conversion =
  sym (wkᵗ-injective zero
    (ty-fun-left-injectiveᵗ (target-determinacy↑ conversion)))

seventh-aliases-distinct : seventh-C ≢ ＇ zero
seventh-aliases-distinct eq with ty-var-injectiveᵗ eq
seventh-aliases-distinct eq | ()

seventh-contractum-untypable :
  seventh-Ψ ∣ [] ⊢ seventh-contractum ⦂ seventh-C ⇒ seventh-C
  → ⊥
seventh-contractum-untypable
    (⊢ν (⊢reveal {C = C} lookup conversion (⊢ƛ (⊢` Z)))) =
  seventh-aliases-distinct
    (trans (sym (seventh-conversion-representation conversion))
      (∋rep-unique lookup seventh-canonical-lookup))
