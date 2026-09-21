module strong-rep-var.TypeSafety where

-- File Charter:
--   * THE WHOLE PUBLIC THEOREM SURFACE, STATED EXPLICITLY IN ONE PLACE.
--     `Progress`, `Preservation`, `Preservation*` and `TypeSafety` are
--     written out here rather than re-exported, and `TypeSafety` is the
--     COMPOSITION of the other two: from `WfCtx Δ`, `Δ ∣ [] ⊢ M ⦂ A`
--     and `Δ ⊢ M -→* N`, N is a `Value` or N steps.  `preservation`
--     and `preservation*` are unconditional (2026-09-20), and `progress`
--     and `type-safety` are unconditional (2026-09-21), after the last
--     merged-reading parameter was proved.  `det` and `value-¬step` are
--     re-stated here and delegate to strong-rep-var.Reduction.
--   * NO PROOFS AND NO DEFINITIONS.  Every right-hand side is a
--     delegation: strong-rep-var.Preservation, strong-rep-var.Progress,
--     strong-rep-var.proof.TypeSafety and strong-rep-var.Reduction.  The
-- refutations
--     that shaped these statements are the wall modules under notes/,
--     and the dated record is notes/DECISIONS.md.
--   * THE PREMISES ARE NOT UNIFORM, AND THAT IS THE POINT.
--     `preservation` (and everything built on it, `type-safety`
--     included) takes `WfCtx Δ`; the premise-free form is FALSE here,
--     because at a duplicate name map a TyBeta contractum must mint a
--     `MorphWf` that `Unique` refuses (notes/DECISIONS.md,
--     2026-09-18).  `progress` takes NO such premise — a boundary case
--     reads well-formedness off its own `env`.  `det` takes the
--     REDEX'S TYPING DERIVATION, from which it recovers the name-map
--     uniqueness the rules used to carry as premises (same entry).  The
--     reduction relation is indexed by the type context Δ only; the
--     term context is empty, as it must be.
--
-- THE WHOLE SURFACE HOLDS OUTRIGHT:
--
--   det            reduction is deterministic on well-typed terms
--   value-¬step    values do not step
--   preservation   a well-typed term stays well typed  (2026-09-20)
--   preservation*  and along a whole run                (2026-09-20)
--   progress        a well-typed closed term is a value or steps
--   type-safety     every state reached is a value or steps
--
-- PRESERVATION BECAME UNCONDITIONAL ON 2026-09-20, in three steps of the
-- same day.  `RepWeakenTyping` was proved
-- (`strong-rep-var.proof.RepWeaken.rep-weaken-⊢`), making `PeelCase`
-- unconditional; `CrossΛTyping` was proved
-- (`strong-rep-var.proof.RepWeaken.cross-Λ-⊢`), making Beta unconditional; and
-- `AddLock0Typing`, which `notes/AddLock0Wall.agda` had REFUTED that
-- morning — a closed, plain System F program losing its type three steps
-- in, at `TyPeelR-⟪⟫`, whose contractum re-spelled the moved boundary's
-- conversion with `renᶜ suc` in a name map where the new ordinary name is
-- not at position zero — was answered by the RULE repair Jeremy approved
-- (the moved conversion is NAMED and pinned by `SameConv`) and then PROVED
-- on the reshaped statement, `strong-rep-var.proof.AddLock0.addLock0-⊢`.
--
-- That was the second rule defect of the shape `CancelRCase`'s had
-- (refuted by `notes/CancelRShiftWall.agda`, reached from source by
-- `notes/CancelRReachabilityWitness.agda`, repaired by Jeremy's repair (a)
-- on 2026-09-19 and proved,
-- `strong-rep-var.proof.MoveScope.preserve-CancelR`).  The final progress
-- obligation, `MergedReading`, was proved on 2026-09-21 by lifting Θ₂'s
-- conversion reading, weakening Θ₁'s reading from the resulting larger
-- name map, and concatenating the two change runs.

open import Data.List using ([])
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; Σ-syntax)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong-rep-var.Types using (Ty)
open import strong-rep-var.Ctx using (Ctxᵗ; WfCtx)
open import strong-rep-var.Terms using (Term; Ctx; Value; _∣_⊢_⦂_)
open import strong-rep-var.Reduction using (_⊢_-→_; _⊢_-→*_)
import strong-rep-var.Reduction as R
import strong-rep-var.Progress as Pr
import strong-rep-var.Preservation as Pv
import strong-rep-var.proof.TypeSafety as TS

------------------------------------------------------------------------
-- The statements
------------------------------------------------------------------------

Progress : Set
Progress = ∀ {Δ : Ctxᵗ} {M : Term} {A : Ty}
  → Δ ∣ [] ⊢ M ⦂ A
    ---------------------------------------------
  → Value M ⊎ (Σ[ M′ ∈ Term ] (Δ ⊢ M -→ M′))

Preservation : Set
Preservation = ∀ {Δ : Ctxᵗ} {M M′ : Term} {A : Ty}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→ M′
    ----------------
  → Δ ∣ [] ⊢ M′ ⦂ A

Preservation* : Set
Preservation* = ∀ {Δ : Ctxᵗ} {M M′ : Term} {A : Ty}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→* M′
    ----------------
  → Δ ∣ [] ⊢ M′ ⦂ A

TypeSafety : Set
TypeSafety = ∀ {Δ : Ctxᵗ} {M N : Term} {A : Ty}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→* N
    ---------------------------------------------
  → Value N ⊎ (Σ[ N′ ∈ Term ] (Δ ⊢ N -→ N′))

------------------------------------------------------------------------
-- The theorems
------------------------------------------------------------------------

preservation : Preservation
preservation = Pv.preservation

preservation* : Preservation*
preservation* = Pv.preservation*

progress : Progress
progress = Pr.progress

type-safety : TypeSafety
type-safety = TS.type-safety

------------------------------------------------------------------------
-- Determinism, and values do not step — unconditional
------------------------------------------------------------------------

det : ∀ {Δ : Ctxᵗ} {Γ : Ctx} {M M₁ M₂ : Term} {A : Ty}
  → Δ ∣ Γ ⊢ M ⦂ A
  → Δ ⊢ M -→ M₁
  → Δ ⊢ M -→ M₂
    -------------
  → M₁ ≡ M₂
det = R.det

value-¬step : ∀ {Δ : Ctxᵗ} {M M′ : Term}
  → Value M
  → Δ ⊢ M -→ M′
    -------------
  → ⊥
value-¬step = R.value-¬step
