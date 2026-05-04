module proof.PreservationWkConv where

-- File Charter:
--   * Seal-context and store weakening for PolyConvert conversion typing.
--   * Proves the `wk-conv↑` and `wk-conv↓` preservation obligations.
--   * Keeps conversion-specific weakening separate from the main preservation
--     proof script so it can be integrated once the parallel slices land.

open import Data.Nat using (_≤_; suc)

open import Types
open import proof.TypeProperties using (WfTy-weakenˢ)
open import Store
open import Conversion

⟰ᵗ-⊆ˢ :
  ∀ {Σ Σ′ : Store} →
  Σ ⊆ˢ Σ′ →
  ⟰ᵗ Σ ⊆ˢ ⟰ᵗ Σ′
⟰ᵗ-⊆ˢ done = done
⟰ᵗ-⊆ˢ (keep {α = α} {A = A} w) =
  keep {α = α} {A = renameᵗ suc A} (⟰ᵗ-⊆ˢ w)
⟰ᵗ-⊆ˢ (drop {α = α} {A = A} w) =
  drop {α = α} {A = renameᵗ suc A} (⟰ᵗ-⊆ˢ w)

mutual
  wk-conv↑ :
    ∀ {Δ Ψ Ψ′}{Σ Σ′ : Store}{c A B} →
    Ψ ≤ Ψ′ →
    Σ ⊆ˢ Σ′ →
    Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↑ˢ B →
    Δ ∣ Ψ′ ∣ Σ′ ⊢ c ⦂ A ↑ˢ B
  wk-conv↑ Ψ≤Ψ′ wΣ (⊢↑-unseal h) =
    ⊢↑-unseal (wkLookupˢ wΣ h)
  wk-conv↑ Ψ≤Ψ′ wΣ (⊢↑-⇒ p⊢ q⊢) =
    ⊢↑-⇒ (wk-conv↓ Ψ≤Ψ′ wΣ p⊢) (wk-conv↑ Ψ≤Ψ′ wΣ q⊢)
  wk-conv↑ Ψ≤Ψ′ wΣ (⊢↑-∀ c⊢) =
    ⊢↑-∀ (wk-conv↑ Ψ≤Ψ′ (⟰ᵗ-⊆ˢ wΣ) c⊢)
  wk-conv↑ Ψ≤Ψ′ wΣ (⊢↑-id wfA) =
    ⊢↑-id (WfTy-weakenˢ wfA Ψ≤Ψ′)

  wk-conv↓ :
    ∀ {Δ Ψ Ψ′}{Σ Σ′ : Store}{c A B} →
    Ψ ≤ Ψ′ →
    Σ ⊆ˢ Σ′ →
    Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↓ˢ B →
    Δ ∣ Ψ′ ∣ Σ′ ⊢ c ⦂ A ↓ˢ B
  wk-conv↓ Ψ≤Ψ′ wΣ (⊢↓-seal h) =
    ⊢↓-seal (wkLookupˢ wΣ h)
  wk-conv↓ Ψ≤Ψ′ wΣ (⊢↓-⇒ p⊢ q⊢) =
    ⊢↓-⇒ (wk-conv↑ Ψ≤Ψ′ wΣ p⊢) (wk-conv↓ Ψ≤Ψ′ wΣ q⊢)
  wk-conv↓ Ψ≤Ψ′ wΣ (⊢↓-∀ c⊢) =
    ⊢↓-∀ (wk-conv↓ Ψ≤Ψ′ (⟰ᵗ-⊆ˢ wΣ) c⊢)
  wk-conv↓ Ψ≤Ψ′ wΣ (⊢↓-id wfA) =
    ⊢↓-id (WfTy-weakenˢ wfA Ψ≤Ψ′)
