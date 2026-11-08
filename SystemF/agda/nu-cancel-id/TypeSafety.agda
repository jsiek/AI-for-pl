module nu-cancel-id.TypeSafety where

-- File Charter:
--   * TYPE SAFETY of νF₁ᶜ: a well-typed closed term never reaches a stuck
--     term.  Every term a run reaches is a value or steps.  From
--     nu-cancel-id.Progress and nu-cancel-id.Preservation.

open import Data.List using ([])
open import Data.Product using (Σ-syntax)
open import Data.Sum using (_⊎_)

open import nu-cancel-id.Types using (Ty)
open import nu-cancel-id.Ctx using (Ctx)
open import nu-cancel-id.Terms using (Term; _∣_⊢_⦂_)
open import nu-cancel-id.Reduction
  using (Value; Alloc; _⊢_⟶_∣_; _⊢_—↠_⊣_)
open import nu-cancel-id.Progress using (progress)
open import nu-cancel-id.Preservation using (preservation*)

type-safety : ∀ {Γ Γ′ : Ctx} {M N : Term} {A : Ty}
  → Γ ∣ [] ⊢ M ⦂ A
  → Γ ⊢ M —↠ N ⊣ Γ′
  → Value N ⊎ Σ[ N′ ∈ Term ] Σ[ a ∈ Alloc ] (Γ′ ⊢ N ⟶ N′ ∣ a)
type-safety ⊢M M↠N = progress (preservation* ⊢M M↠N)
