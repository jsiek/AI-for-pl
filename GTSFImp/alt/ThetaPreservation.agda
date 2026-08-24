module alt.ThetaPreservation where

-- File Charter:
--   * Records the obstruction to one-step type preservation for the current
--     Θ-indexed alternative calculus.
--   * The loose `id-cancel` rule permits the following typed instance.  Its
--     inner node uses slot zero and anchor zero, while its outer node uses
--     slot two and anchor one:
--
--       (($ 7 ↓[ 0 ≔ 0 ] seal) ↓[ 0 ≔ 0 ] id↓)
--         ↑[ 2 ≔ 1 ] id↑  —→  ($ 7 ↓[ 0 ≔ 0 ] seal)
--
--     The redex has type `＇ 1`: both identity conversions see the same
--     foreign atom after their different slot insertions.  The reduct's
--     sealing node fixes its only possible type at `＇ 0`, however, so it
--     cannot have type `＇ 1`.
--   * Thus the requested total `preserve` statement is false.  The missing
--     fact in the `id-cancel` case is matching node data (in particular,
--     equality of its two slots; the instance also mismatches the anchors).
--     As pre-agreed, no partial theorem or postulate is introduced here.

open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.List using ([])
open import Data.Nat using (zero; suc)

open import Types
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction

bad-Ψ : TyEnv (suc (suc zero)) (suc (suc zero))
bad-Ψ =
  ∅ ,:= ‵ `ℕ ,:= ‵ `ℕ ,typ[ zero ] ,typ[ zero ]

bad-body-Ψ : TyEnv (suc (suc zero)) (suc (suc zero))
bad-body-Ψ =
  ∅ ,:= ‵ `ℕ ,:= ‵ `ℕ ,typ[ zero ] ,typ[ suc zero ]

bad-V : Term (suc (suc zero)) (suc (suc zero))
bad-V = ($ (κℕ 7)) ↓[ zero ≔ zero ] seal

bad-V-⊢ : bad-body-Ψ ∣ [] ⊢ bad-V ⦂ ＇ zero
bad-V-⊢ = ⊢conceal (skip-typ Z) ⊢seal (⊢$ (κℕ 7))

bad-inner : Term (suc (suc zero)) (suc (suc (suc zero)))
bad-inner = bad-V ↓[ zero ≔ zero ] id↓

bad-inner-⊢ :
  bad-Ψ ,typ[ suc (suc zero) ] ∣ [] ⊢ bad-inner ⦂ ＇ suc zero
bad-inner-⊢ =
  ⊢conceal (skip-typ (skip-typ Z)) (⊢id↓ (＇ suc zero)) bad-V-⊢

bad-redex : Term (suc (suc zero)) (suc (suc zero))
bad-redex = bad-inner ↑[ suc (suc zero) ≔ suc zero ] id↑

bad-redex-⊢ : bad-Ψ ∣ [] ⊢ bad-redex ⦂ ＇ suc zero
bad-redex-⊢ =
  ⊢reveal (skip-typ (skip-typ (S Z)))
    (⊢id↑ (＇ suc zero)) bad-inner-⊢

bad-V-canonical : CanonicalInterior bad-V
bad-V-canonical = sealed ($ (κℕ 7)) zero zero

bad-step : bad-Ψ ⊢ bad-redex —→ bad-V
bad-step = id-cancel bad-V-canonical

bad-reduct-untypable : bad-Ψ ∣ [] ⊢ bad-V ⦂ ＇ suc zero → ⊥
bad-reduct-untypable (⊢conceal α∈ () M⊢)

preserve-impossible :
  (∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ} {M M′ A}
    → Ψ ∣ Γ ⊢ M ⦂ A
    → Ψ ⊢ M —→ M′
    → Ψ ∣ Γ ⊢ M′ ⦂ A)
  → ⊥
preserve-impossible preserve =
  bad-reduct-untypable (preserve bad-redex-⊢ bad-step)
