module nu-cancel-id.Progress where

-- File Charter:
--   * THE PUBLIC PROGRESS THEOREM of νF₁ᶜ: a closed well-typed term is a
--     value or steps, at any context, with no premise beyond typing.
--     The proof is nu-cancel-id.proof.Progress.

open import Data.List using ([])
open import Data.Product using (Σ-syntax)
open import Data.Sum using (_⊎_)

open import nu-cancel-id.Types using (Ty)
open import nu-cancel-id.Ctx using (Ctx)
open import nu-cancel-id.Terms using (Term; _∣_⊢_⦂_)
open import nu-cancel-id.Reduction using (Value; Alloc; _⊢_⟶_∣_)
import nu-cancel-id.proof.Progress as P

progress : ∀ {Γ : Ctx} {M : Term} {R : Ty}
  → Γ ∣ [] ⊢ M ⦂ R
  → Value M ⊎ Σ[ N ∈ Term ] Σ[ a ∈ Alloc ] (Γ ⊢ M ⟶ N ∣ a)
progress = P.progress
