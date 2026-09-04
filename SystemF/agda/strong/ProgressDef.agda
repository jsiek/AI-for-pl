module strong.ProgressDef where

-- Statements of the progress cases still open.  AFTER THE PEEL INSTALL
-- (2026-09-04) there are TWO, and they are NOT the two that were open
-- before: the roles have SWAPPED.
--
--   Nested… (a wrapper-bodied wrapper at a ⇒ / ∀ face) — *** DISCHARGED ***.
--       Peel fires at an ⇒ face on ANY value body and TyPeel at a ∀ face on
--       any WRAPPER body (TyWrap on a Λ body), so strong.Progress's app-⇒ /
--       tapp-∀ are now total, with no case analysis left over and no Merge
--       premise to supply.  This is what the peel design bought: the shapes
--       notes/InstallGauntlet §9d(i) and §9g proved UNMERGEABLE (§9g: under
--       ANY ⊕, face-directed or not) simply step.
--
--   RevealVar… — a wrapped VALUE whose BOUNDARY TYPE is one of the
--       boundary's own REVEAL VARIABLES ` X, eliminated.  These were
--       theorems at the Merge landing, but only BECAUSE they routed into
--       the Nested… parameters; they are now the residue, and they are the
--       ONE place where progress still needs Merge.  See the obstruction
--       below, and notes/InstallGauntlet §9i for the machine-checked,
--       REACHABLE witness.
--
-- THE OBSTRUCTION, precisely.  At a reveal-variable face the two faces are
--
--   internal:  substᵗ (γᵇ Θ) (` X) = ` X        (γᵇ-lo — a reveal variable
--                                                passes through unchanged)
--   external:  substᵗ (ρᵇ Θ) (` X) = repOf X Θ  (the reveal's rep, which
--                                                the elimination's typing
--                                                forces to be ⇒ / ∀-shaped)
--
-- so the wrapped value has ABSTRACT type ` X in the interior.  Peel and
-- TyPeel push the elimination INWARD, and an eliminationof a term of
-- VARIABLE type is not typable — so neither rule can fire here, whatever
-- its premises.  Re-spelling the boundary type as the rep is barred by the
-- same argument that kills flattening in §9g: the body is typed at ` X on
-- the nose and terms are never rewritten, so any B₀ ≠ ` X breaks the
-- INTERNAL face.  The only remaining move is to collapse the nesting —
-- `canon-var` says the body IS a wrapper — i.e. Merge.  Its MergeOK premise
-- is fully discharged on the reachable witness (§9i), but is not a theorem
-- in general, which is exactly what these two statements assume.
--
-- Each is stated over the KNOWLEDGE-INDEXED reduction relation: the redex
-- sits at the type context Δ that also types it.  The NESTED SHAPE is part
-- of the statement — strong.Canonical's canon-var derives it, so assuming
-- it makes the hypothesis STRICTLY WEAKER than the plain reveal-variable
-- form these two had before.

open import Data.Nat using (ℕ; _<_)
open import Data.Product using (Σ)
open import Data.List using ([])
open import strong.Types
open import strong.Context using (TCtx)
open import strong.Boundary
open import strong.BReduction using (Value; _⊢_-→_)

-- ((V ⟪ Θ₁ , Y ⟫) ⟪ Θ₂ , X ⟫) · W steps, when X is a reveal variable of Θ₂
RevealVarApp : Set
RevealVarApp = ∀ {Δ : TCtx} {V W : Term} {Θ₁ Θ₂ : BCtx} {X Y : ℕ} {A B : Ty}
  → Value V → Value W
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , ` Y ⟫) ⟪ Θ₂ , ` X ⟫ ⦂ (A ⇒ B) → X < revs Θ₂
  → Σ Term λ M′ → Δ ⊢ ((V ⟪ Θ₁ , ` Y ⟫) ⟪ Θ₂ , ` X ⟫) · W -→ M′

-- ((V ⟪ Θ₁ , Y ⟫) ⟪ Θ₂ , X ⟫) ·[ B , A ] steps, same side condition
RevealVarTApp : Set
RevealVarTApp = ∀ {Δ : TCtx} {V : Term} {Θ₁ Θ₂ : BCtx} {X Y : ℕ} {B A : Ty}
  → Value V
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , ` Y ⟫) ⟪ Θ₂ , ` X ⟫ ⦂ `∀ B → X < revs Θ₂
  → Σ Term λ M′ → Δ ⊢ ((V ⟪ Θ₁ , ` Y ⟫) ⟪ Θ₂ , ` X ⟫) ·[ B , A ] -→ M′
