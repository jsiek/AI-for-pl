module nu-cancel-id.Determinism where

-- File Charter:
--   * THE PUBLIC DETERMINISM THEOREMS of νF₁ᶜ: a term has at most one
--     step, with a unique result and a unique allocation, and a value
--     has none.  Neither needs typing.
--     The proofs are nu-cancel-id.proof.Determinism.

open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import nu-cancel-id.Ctx using (Ctx)
open import nu-cancel-id.Terms using (Term)
open import nu-cancel-id.Reduction using (Value; Alloc; _⊢_⟶_∣_)
import nu-cancel-id.proof.Determinism as P

determinism : ∀ {Γ : Ctx} {M M₁ M₂ : Term} {a₁ a₂ : Alloc}
  → Γ ⊢ M ⟶ M₁ ∣ a₁
  → Γ ⊢ M ⟶ M₂ ∣ a₂
  → M₁ ≡ M₂ × a₁ ≡ a₂
determinism = P.det

value-irreducible : ∀ {Γ : Ctx} {V N : Term} {a : Alloc}
  → Value V
  → ¬ (Γ ⊢ V ⟶ N ∣ a)
value-irreducible = P.value-¬step
