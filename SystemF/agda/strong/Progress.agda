module strong.Progress where

-- Strong System F v7 — public progress statement.

open import Data.List using ([])
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; Σ-syntax)

open import strong.Types using (Ty)
open import strong.Ctx using (Ctxᵗ; _ok)
open import strong.Terms using (Term; Value; _∣_⊢_⦂_)
open import strong.Reduction using (_⊢_-→_)
import strong.proof.Progress as Proof

progress : ∀ {Δ : Ctxᵗ} {M : Term} {A : Ty}
  → Δ ok
  → Δ ∣ [] ⊢ M ⦂ A
  → Value M ⊎ (Σ[ M′ ∈ Term ] (Δ ⊢ M -→ M′))
progress = Proof.progress
