module nu-cancel-id.Preservation where

-- File Charter:
--   * THE PUBLIC PRESERVATION THEOREMS of νF₁ᶜ, typed at named types: a
--     step at Γ that allocates `a` types its contractum at `a ⨾ Γ`, at
--     the same named type; so does a run, at the context it ends at.
--     The proofs are nu-cancel-id.proof.Preservation.

open import Data.List using ([])

open import nu-cancel-id.Types using (Ty)
open import nu-cancel-id.Ctx using (Ctx)
open import nu-cancel-id.Terms using (Term; _∣_⊢_⦂_)
open import nu-cancel-id.Reduction using (Alloc; _⨾_; _⊢_⟶_∣_; _⊢_—↠_⊣_)
import nu-cancel-id.proof.Preservation as P

preservation : ∀ {Γ : Ctx} {M N : Term} {A : Ty} {a : Alloc}
  → Γ ∣ [] ⊢ M ⦂ A
  → Γ ⊢ M ⟶ N ∣ a
  → a ⨾ Γ ∣ [] ⊢ N ⦂ A
preservation = P.preservation

preservation* : ∀ {Γ Γ′ : Ctx} {M N : Term} {A : Ty}
  → Γ ∣ [] ⊢ M ⦂ A
  → Γ ⊢ M —↠ N ⊣ Γ′
  → Γ′ ∣ [] ⊢ N ⦂ A
preservation* = P.preservation*
