module strong-rep-store.TypeSafety where

-- File Charter:
--   * THE WHOLE PUBLIC THEOREM SURFACE, STATED EXPLICITLY IN ONE PLACE.
--     `Progress`, `Preservation`, `PreservationWf`, `Preservation*` and
--     `TypeSafety` are written out here rather than re-exported, and
--     `TypeSafety` is the COMPOSITION of progress and preservation: from
--     `WfCtx Δ`, `Δ ∣ [] ⊢ M ⦂ A` and a run `r : Δ ⊢ M -→* N`, N is a
--     `Value` or N steps — at `runCtx r`, the context the run ENDS at.
--     `det` and `value-¬step` are re-stated here and delegate to
--     strong-rep-store.Reduction.
--   * NO PROOFS AND NO DEFINITIONS.  Every right-hand side is a
--     delegation: strong-rep-store.Preservation, strong-rep-store.Progress,
--     strong-rep-store.proof.TypeSafety and strong-rep-store.Reduction.
--     The refutations that shaped these statements are the wall modules
--     under notes/, and the dated record is notes/DECISIONS.md.
--   * A STEP RETURNS THE CHANGE IT MADE TO THE STORE.  `_⊢_-→_∣_` is
--     indexed by an `Alloc` — `none`, or `new R` when a ∀-elimination
--     allocated the cell for R — and the contractum lives at
--     `apply δ Δ` (experiment 2, notes/RepStoreSketch.md).  So
--     preservation MOVES the context, `PreservationWf` keeps it well
--     formed, and `det` concludes that the PAIR `(M′ , δ)` is unique.
--   * THE PREMISES ARE NOT UNIFORM, AND THAT IS THE POINT.
--     `preservation` (and everything built on it, `type-safety`
--     included) takes `WfCtx Δ`; the premise-free form is FALSE here,
--     because at a duplicate name map a TyBeta contractum must mint a
--     `BoundaryWf` that `Unique` refuses (notes/DECISIONS.md,
--     2026-09-18).  `progress` takes NO such premise — a boundary case
--     reads well-formedness off its own `env`.  `det` takes the
--     REDEX'S TYPING DERIVATION, from which it recovers the name-map
--     uniqueness the rules used to carry as premises (same entry).  The
--     reduction relation is indexed by the type context Δ only; the
--     term context is empty, as it must be.
--
-- THE WHOLE SURFACE HOLDS OUTRIGHT:
--
--   det            reduction is deterministic on well-typed terms —
--                  contractum AND store change
--   value-¬step    values do not step
--   preservation   a well-typed term stays well typed, at `apply δ Δ`
--   preservation-wf  and that context stays well formed
--   preservation*  and along a whole run, at `runCtx r`
--   progress       a well-typed closed term is a value or steps
--   type-safety    every state reached is a value or steps
--
-- PRESERVATION BECAME UNCONDITIONAL ON 2026-09-20, in three steps of the
-- same day: `RepWeakenTyping` was proved, making `PeelCase`
-- unconditional; `CrossΛTyping` was proved, making Beta unconditional;
-- and `AddLock0Typing`, which `notes/AddLock0Wall.agda` had REFUTED that
-- morning, was answered by the RULE repair Jeremy approved (the moved
-- conversion is NAMED and pinned by `SameConv`) and then PROVED on the
-- reshaped statement.  That was the second rule defect of the shape
-- `CancelRCase`'s had (refuted by `notes/CancelRShiftWall.agda`,
-- reached from source by `notes/CancelRReachabilityWitness.agda`,
-- repaired by Jeremy's repair (a) on 2026-09-19 and proved).  The final
-- progress obligation, `MergedReading`, was proved on 2026-09-21.
--
-- THE STORE EXPERIMENT (2026-09-22) kept every one of those statements
-- and retired one of the lemmas behind them: `Peel` no longer moves its
-- argument at all, so `RepWeakenTyping` is gone, replaced by the SIBLING
-- SHIFT `ShiftTyping` that the four congruences consume.

open import Data.List using ([])
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; Σ-syntax; _×_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong-rep-store.Types using (Ty)
open import strong-rep-store.Ctx using (Ctxᵗ; WfCtx; Alloc; apply)
open import strong-rep-store.Terms using (Term; Ctx; Value; _∣_⊢_⦂_)
open import strong-rep-store.Reduction
  using (_⊢_-→_∣_; _⊢_-→*_; runCtx)
import strong-rep-store.Reduction as R
import strong-rep-store.Progress as Pr
import strong-rep-store.Preservation as Pv
import strong-rep-store.proof.TypeSafety as TS

------------------------------------------------------------------------
-- The statements
------------------------------------------------------------------------

Progress : Set
Progress = ∀ {Δ : Ctxᵗ} {M : Term} {A : Ty}
  → Δ ∣ [] ⊢ M ⦂ A
    ---------------------------------------------
  → Value M ⊎ (Σ[ M′ ∈ Term ] Σ[ δ ∈ Alloc ] (Δ ⊢ M -→ M′ ∣ δ))

Preservation : Set
Preservation = ∀ {Δ : Ctxᵗ} {M M′ : Term} {A : Ty} {δ : Alloc}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→ M′ ∣ δ
    -----------------------
  → apply δ Δ ∣ [] ⊢ M′ ⦂ A

PreservationWf : Set
PreservationWf = ∀ {Δ : Ctxᵗ} {M M′ : Term} {A : Ty} {δ : Alloc}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→ M′ ∣ δ
    -----------------
  → WfCtx (apply δ Δ)

Preservation* : Set
Preservation* = ∀ {Δ : Ctxᵗ} {M M′ : Term} {A : Ty}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → (r : Δ ⊢ M -→* M′)
    ------------------------
  → runCtx r ∣ [] ⊢ M′ ⦂ A

TypeSafety : Set
TypeSafety = ∀ {Δ : Ctxᵗ} {M N : Term} {A : Ty}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → (r : Δ ⊢ M -→* N)
    ---------------------------------------------
  → Value N ⊎ (Σ[ N′ ∈ Term ] Σ[ δ ∈ Alloc ] (runCtx r ⊢ N -→ N′ ∣ δ))

------------------------------------------------------------------------
-- The theorems
------------------------------------------------------------------------

preservation : Preservation
preservation = Pv.preservation

preservation-wf : PreservationWf
preservation-wf = Pv.preservation-wf

preservation* : Preservation*
preservation* = Pv.preservation*

progress : Progress
progress = Pr.progress

type-safety : TypeSafety
type-safety = TS.type-safety

------------------------------------------------------------------------
-- Determinism, and values do not step — unconditional
------------------------------------------------------------------------

-- The contractum AND the store change are functions of the redex.
det : ∀ {Δ : Ctxᵗ} {Γ : Ctx} {M M₁ M₂ : Term} {A : Ty} {δ₁ δ₂ : Alloc}
  → Δ ∣ Γ ⊢ M ⦂ A
  → Δ ⊢ M -→ M₁ ∣ δ₁
  → Δ ⊢ M -→ M₂ ∣ δ₂
    -------------------------
  → (M₁ ≡ M₂) × (δ₁ ≡ δ₂)
det = R.det

value-¬step : ∀ {Δ : Ctxᵗ} {M M′ : Term} {δ : Alloc}
  → Value M
  → Δ ⊢ M -→ M′ ∣ δ
    -------------
  → ⊥
value-¬step = R.value-¬step
