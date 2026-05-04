module proof.PreservationWkTerm where

-- File Charter:
--   * Seal-context and store weakening for PolyConvert term typing.
--   * Proves the `wk-term` preservation obligation independently by induction
--     on term typing derivations.
--   * Depends on the sibling weakening slices for imprecision and conversions.

open import Data.Nat using (_≤_)

open import Types
open import proof.TypeProperties using (WfTy-weakenˢ)
open import Store using (_⊆ˢ_)
open import Terms
open import proof.PreservationWkImp using (wk-⊑; wk-⊒)
open import proof.PreservationWkConv using (⟰ᵗ-⊆ˢ; wk-conv↑; wk-conv↓)

wk-term :
  ∀ {Δ Ψ Ψ′}{Σ Σ′ : Store}{Γ : Ctx}{M : Term}{A : Ty} →
  Ψ ≤ Ψ′ →
  Σ ⊆ˢ Σ′ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Ψ′ ∣ Σ′ ∣ Γ ⊢ M ⦂ A
wk-term Ψ≤Ψ′ wΣ (⊢` x) = ⊢` x
wk-term Ψ≤Ψ′ wΣ (⊢ƛ wfA M⊢) =
  ⊢ƛ (WfTy-weakenˢ wfA Ψ≤Ψ′) (wk-term Ψ≤Ψ′ wΣ M⊢)
wk-term Ψ≤Ψ′ wΣ (⊢· L⊢ M⊢) =
  ⊢· (wk-term Ψ≤Ψ′ wΣ L⊢) (wk-term Ψ≤Ψ′ wΣ M⊢)
wk-term Ψ≤Ψ′ wΣ (⊢Λ vM M⊢) =
  ⊢Λ vM (wk-term Ψ≤Ψ′ (⟰ᵗ-⊆ˢ wΣ) M⊢)
wk-term Ψ≤Ψ′ wΣ (⊢• M⊢ wfB wfT) =
  ⊢•
    (wk-term Ψ≤Ψ′ wΣ M⊢)
    (WfTy-weakenˢ wfB Ψ≤Ψ′)
    (WfTy-weakenˢ wfT Ψ≤Ψ′)
wk-term Ψ≤Ψ′ wΣ (⊢$ κ) = ⊢$ κ
wk-term Ψ≤Ψ′ wΣ (⊢⊕ L⊢ op M⊢) =
  ⊢⊕ (wk-term Ψ≤Ψ′ wΣ L⊢) op (wk-term Ψ≤Ψ′ wΣ M⊢)
wk-term Ψ≤Ψ′ wΣ (⊢up p⊢ M⊢) =
  ⊢up (wk-⊑ Ψ≤Ψ′ p⊢) (wk-term Ψ≤Ψ′ wΣ M⊢)
wk-term Ψ≤Ψ′ wΣ (⊢down p⊢ M⊢) =
  ⊢down (wk-⊒ Ψ≤Ψ′ p⊢) (wk-term Ψ≤Ψ′ wΣ M⊢)
wk-term Ψ≤Ψ′ wΣ (⊢reveal c⊢ M⊢) =
  ⊢reveal (wk-conv↑ Ψ≤Ψ′ wΣ c⊢) (wk-term Ψ≤Ψ′ wΣ M⊢)
wk-term Ψ≤Ψ′ wΣ (⊢conceal c⊢ M⊢) =
  ⊢conceal (wk-conv↓ Ψ≤Ψ′ wΣ c⊢) (wk-term Ψ≤Ψ′ wΣ M⊢)
wk-term Ψ≤Ψ′ wΣ (⊢blame ℓ) = ⊢blame ℓ
