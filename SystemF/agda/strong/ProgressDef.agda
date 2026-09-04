module strong.ProgressDef where

-- Statements of the two progress cases that still await the restored conceal
-- invariant (notes/DECISIONS.md, Decision 1) and Merge (Decision 3): a wrapped
-- VALUE whose boundary type is a REVEAL VARIABLE, sitting at an elimination
-- position.  strong.Progress is parameterised over these statements (the
-- repo's `…Def` convention) and is instantiated once they are proven.

open import Data.Nat using (ℕ; _<_)
open import Data.Product using (Σ)
open import Data.List using ([])
open import strong.Types
open import strong.Context using (TCtx)
open import strong.Boundary
open import strong.BReduction using (Value; _-→_)

-- (V ⟪ Θ , X ⟫) · W steps, when X is a reveal variable of Θ and both are values
RevealVarApp : Set
RevealVarApp = ∀ {Δ : TCtx} {V W : Term} {Θ : BCtx} {X : ℕ} {A B : Ty}
  → Value V → Value W → Δ ∣ [] ⊢ V ⟪ Θ , ` X ⟫ ⦂ (A ⇒ B) → X < revs Θ
  → Σ Term λ M′ → (V ⟪ Θ , ` X ⟫) · W -→ M′

-- (V ⟪ Θ , X ⟫) ·[ B , A ] steps, when X is a reveal variable of Θ
RevealVarTApp : Set
RevealVarTApp = ∀ {Δ : TCtx} {V : Term} {Θ : BCtx} {X : ℕ} {B A : Ty}
  → Value V → Δ ∣ [] ⊢ V ⟪ Θ , ` X ⟫ ⦂ `∀ B → X < revs Θ
  → Σ Term λ M′ → (V ⟪ Θ , ` X ⟫) ·[ B , A ] -→ M′
