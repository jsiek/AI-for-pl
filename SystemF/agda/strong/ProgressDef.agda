module strong.ProgressDef where

-- Statements of the four progress cases that still await the restored conceal
-- invariant (notes/DECISIONS.md, Decision 1) and Merge (Decision 3).  Two
-- families, one per elimination:
--
--   RevealVar…  a wrapped VALUE whose boundary type is a REVEAL VARIABLE —
--               neither TyWrap nor Wrap applies (Decision 1);
--   Nested…     a WRAPPER-BODIED wrapper at a ∀ / ⇒ face — TyWrap and Wrap
--               are partial in their body (they consume a Λ / a ƛ), so a
--               wrapper body is a Merge redex (Decision 3).
--
-- strong.Progress is parameterised over these statements (the repo's `…Def`
-- convention) and is instantiated once they are proven.  Merge discharges the
-- Nested… pair uniformly: the contractum is the merged wrapper back under the
-- same elimination frame (ξ-·-l / ξ-·[]), so nothing beyond the redex's own
-- typing is assumed here.

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

-- a wrapper-bodied wrapper at ⇒ face steps (Merge, Decision 3): Wrap
-- consumes the ƛ, so a wrapper body is not a Wrap redex
NestedApp : Set
NestedApp = ∀ {Δ : TCtx} {V W : Term} {Θ₁ Θ₂ : BCtx} {B₁ B₀₂ A B : Ty}
  → Value V → Value W
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₀₂ ⟫ ⦂ (A ⇒ B)
  → Σ Term λ M′ → ((V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₀₂ ⟫) · W -→ M′

-- a wrapper-bodied wrapper at ∀ face steps (Merge, Decision 3): TyWrap
-- consumes the Λ, so a wrapper body is not a TyWrap redex
NestedTApp : Set
NestedTApp = ∀ {Δ : TCtx} {V : Term} {Θ₁ Θ₂ : BCtx} {B₁ B₀₂ B A : Ty}
  → Value V
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₀₂ ⟫ ⦂ `∀ B
  → Σ Term λ M′ → ((V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₀₂ ⟫) ·[ B , A ] -→ M′
