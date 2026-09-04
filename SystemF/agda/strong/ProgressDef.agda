module strong.ProgressDef where

-- Statements of the progress cases still open.  AFTER MERGE'S LANDING
-- (2026-09-04) there are TWO, not four, and strong.Progress.Impl takes
-- exactly those two:
--
--   Nested…     a WRAPPER-BODIED wrapper at a ∀ / ⇒ face — TyWrap and Wrap
--               are partial in their body (they consume a Λ / a ƛ), so a
--               wrapper body is a Merge redex (Decision 3).
--   RevealVar…  a wrapped VALUE whose boundary type is a REVEAL VARIABLE.
--               *** THESE TWO ARE NOW THEOREMS *** — strong.Progress's
--               rv-app / rv-tapp.  At a reveal-variable face the INTERNAL
--               face is that same variable (γᵇ-lo: a reveal passes through
--               unchanged), so the wrapped value has VARIABLE type and
--               strong.Canonical's canon-var makes it a wrapper: the redex
--               was a wrapper-bodied wrapper all along and the SAME Merge
--               frame reaches it.  The statements are kept here because
--               Progress still exports the two theorems at these types.
--
-- Each is stated over the KNOWLEDGE-INDEXED reduction relation: the redex
-- sits at the type context Δ that also types it.
--
-- WHAT IS LEFT IN THE Nested… PAIR, EXACTLY.  The step itself is settled —
-- it is `ξ-·-l (Merge v ok)` / `ξ-·[] (Merge v ok)` — and everything in
-- `ok : MergeOK Δ Θ₁ Θ₂ B₁ B₀₂` except its LAST component follows from the
-- redex's own typing (the frame arithmetic revs-⊕ / cmax-⊕ and the internal
-- face ⊕-γ are theorems).  The last component — the composite's EXTERNAL
-- face is the redex's own type — is a premise of Merge and NOT derivable:
-- notes/InstallGauntlet.agda §9d(i) is an ⇒-faced wrapper-bodied wrapper,
-- well typed, for which it FAILS (the composite would export ℕ⇒ℕ where the
-- redex has X⇒ℕ, dropping X's abstraction), and §9d exhibits the merged
-- boundary that DOES work there.  So these two parameters are not waiting
-- on a proof but on the B₂′ / ⊕ ruling recorded in notes.md §Merge.

open import Data.Nat using (ℕ; _<_)
open import Data.Product using (Σ)
open import Data.List using ([])
open import strong.Types
open import strong.Context using (TCtx)
open import strong.Boundary
open import strong.BReduction using (Value; _⊢_-→_)

-- (V ⟪ Θ , X ⟫) · W steps, when X is a reveal variable of Θ and both are values
RevealVarApp : Set
RevealVarApp = ∀ {Δ : TCtx} {V W : Term} {Θ : BCtx} {X : ℕ} {A B : Ty}
  → Value V → Value W → Δ ∣ [] ⊢ V ⟪ Θ , ` X ⟫ ⦂ (A ⇒ B) → X < revs Θ
  → Σ Term λ M′ → Δ ⊢ (V ⟪ Θ , ` X ⟫) · W -→ M′

-- (V ⟪ Θ , X ⟫) ·[ B , A ] steps, when X is a reveal variable of Θ
RevealVarTApp : Set
RevealVarTApp = ∀ {Δ : TCtx} {V : Term} {Θ : BCtx} {X : ℕ} {B A : Ty}
  → Value V → Δ ∣ [] ⊢ V ⟪ Θ , ` X ⟫ ⦂ `∀ B → X < revs Θ
  → Σ Term λ M′ → Δ ⊢ (V ⟪ Θ , ` X ⟫) ·[ B , A ] -→ M′

-- a wrapper-bodied wrapper at ⇒ face steps (Merge, Decision 3): Wrap
-- consumes the ƛ, so a wrapper body is not a Wrap redex
NestedApp : Set
NestedApp = ∀ {Δ : TCtx} {V W : Term} {Θ₁ Θ₂ : BCtx} {B₁ B₀₂ A B : Ty}
  → Value V → Value W
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₀₂ ⟫ ⦂ (A ⇒ B)
  → Σ Term λ M′ → Δ ⊢ ((V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₀₂ ⟫) · W -→ M′

-- a wrapper-bodied wrapper at ∀ face steps (Merge, Decision 3): TyWrap
-- consumes the Λ, so a wrapper body is not a TyWrap redex
NestedTApp : Set
NestedTApp = ∀ {Δ : TCtx} {V : Term} {Θ₁ Θ₂ : BCtx} {B₁ B₀₂ B A : Ty}
  → Value V
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₀₂ ⟫ ⦂ `∀ B
  → Σ Term λ M′ → Δ ⊢ ((V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₀₂ ⟫) ·[ B , A ] -→ M′
