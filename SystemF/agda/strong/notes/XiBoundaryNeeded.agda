module strong.notes.XiBoundaryNeeded where

-- Is `ξ-⟨⟩` needed?  (Jeremy, 2026-09-17.)
--
-- It is the ONLY reduction rule that changes the type context Δ — there
-- is no ξ-Λ (Λ bodies are values) and no ξ-ν (an allocation in
-- evaluation position discharges first).  So without it every step of a
-- closed program would happen at `[] ∥ []`, whose stack is empty, and
-- `notes/EmptyStackClosed.wf-empty-closed` would hand `⊢•[]`'s premise
-- `Δ ⊢ᵗ A` straight to `Closedᵗ A` — closing the `TyWrapOk` gap.
--
-- But `Wrap` mints a boundary around a REDEX:
--
--   ((ƛ A ∙ N) ⟨ c ⟩) · W  —→  ((ƛ A ∙ N) · (W ⟨ c₁ ⟩)) ⟨ c₂ ⟩
--
-- and the body of that boundary is an APPLICATION, which is never a
-- value — so `Merge` (which needs a boundary value inside) and `Const`
-- (which needs a literal) cannot fire, and ξ-⟨⟩ is the only rule left.

open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Maybe using (Maybe; just)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.Reduction

-- An application is never a value.
app-¬value : ∀ {A N M} → ¬ Value ((ƛ A ∙ N) · M)
app-¬value (Vs ())

-- So a `Wrap` contractum can step in exactly ONE way.
wrap-only-ξ : ∀ {Σ Σ′ Δ A N W c T}
  → Σ ∣ Δ ⊢ ((ƛ A ∙ N) · W) ⟨ c ⟩ —→ T ⊣ Σ′
  → Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ M′ ∈ Term ]
      ((interior c Δ ≡ just Δᵢ)
       × (Σ ∣ Δᵢ ⊢ ((ƛ A ∙ N) · W) —→ M′ ⊣ Σ′)
       × (T ≡ M′ ⟨ c ⟩))
wrap-only-ξ (Const () _)
wrap-only-ξ (ξ-⟨⟩ ieq st) = _ , _ , ieq , st , refl
