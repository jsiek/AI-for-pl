module proof.DGG.Catchup.StructuralTargetPeelSupportProof where

-- File Charter:
--   * Provides local value/step impossibility lemmas used by target-trace
--     peel proofs.
--   * Does not change the reduction relation; it only inverts existing
--     value and store-step constructors.

open import Data.Empty using (⊥)
open import Data.Nat using (suc)

open import Types using (Ty)
open import CastTerms using
  (Term; Value; ƛ_; Λ_; $; _《_》; _↑_; _↓_; _⟨_⟩; _⦂∀_[_])
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef


no-value-type-app : ∀ {Δ} {M : Term Δ} {A : Ty (suc Δ)}
    {B : Ty Δ}
  → Value (M ⦂∀ A [ B ])
  → ⊥
no-value-type-app ()


no-value-apply-spine : ∀ {Δ} {M : Term Δ} {A B : Ty Δ}
    (spine : InstantiationSpine A B)
  → (Value M → ⊥)
  → Value (applyInstantiationSpine M spine)
  → ⊥
no-value-apply-spine []ⁱ noM vM = noM vM
no-value-apply-spine (type-transport-frame eq ▻ⁱ spine) noM v =
  no-value-apply-spine spine noM v
no-value-apply-spine (name-type-app-frame B X eqA eqC ▻ⁱ spine)
    noM v =
  no-value-apply-spine spine no-value-type-app v
no-value-apply-spine (cast-frame c ▻ⁱ spine) noM v =
  no-value-apply-spine spine noCast v
  where
  noCast : Value (_ ⟨ c ⟩) → ⊥
  noCast (vM 《 inert 》) = noM vM
no-value-apply-spine (reveal-frame c ▻ⁱ spine) noM v =
  no-value-apply-spine spine noReveal v
  where
  noReveal : Value (_ ↑ c) → ⊥
  noReveal (vM ↑ reveal-value) = noM vM
no-value-apply-spine (conceal-frame c ▻ⁱ spine) noM v =
  no-value-apply-spine spine noConceal v
  where
  noConceal : Value (_ ↓ c) → ⊥
  noConceal (vM ↓ conceal-value) = noM vM
