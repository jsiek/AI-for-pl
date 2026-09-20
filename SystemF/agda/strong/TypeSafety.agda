module strong.TypeSafety where

-- TYPE SAFETY for Strong System F (the two-universe design).
--
-- The public theorem surface.  FOUR theorems hold outright:
--
--   det            reduction is deterministic on well-typed terms
--   value-¬step    values do not step
--   preservation   a well-typed term stays well typed  (2026-09-20)
--   preservation*  and along a whole run                (2026-09-20)
--
-- The other two — progress and its composition with preservation,
-- type-safety — are STAGE-1 PARAMETERIZED by exactly ONE statement,
-- `MergedReading`, which is held for review rather than implemented.  It
-- is visible in the type of `Stage1`.
--
-- PRESERVATION BECAME UNCONDITIONAL ON 2026-09-20, in three steps of the
-- same day.  `RepWeakenTyping` was proved
-- (`strong.proof.RepWeaken.rep-weaken-⊢`), making `PeelCase`
-- unconditional; `CrossΛTyping` was proved
-- (`strong.proof.RepWeaken.cross-Λ-⊢`), making Beta unconditional; and
-- `AddLock0Typing`, which `notes/AddLock0Wall.agda` had REFUTED that
-- morning — a closed, plain System F program losing its type three steps
-- in, at `TyPeelR-⟪⟫`, whose contractum re-spelled the moved boundary's
-- conversion with `renᶜ suc` in a name map where the new ordinary name is
-- not at position zero — was answered by the RULE repair Jeremy approved
-- (the moved conversion is NAMED and pinned by `SameConv`) and then PROVED
-- on the reshaped statement, `strong.proof.AddLock0.addLock0-⊢`.
--
-- That was the second rule defect of the shape `CancelRCase`'s had
-- (refuted by `notes/CancelRShiftWall.agda`, reached from source by
-- `notes/CancelRReachabilityWitness.agda`, repaired by Jeremy's repair (a)
-- on 2026-09-19 and proved,
-- `strong.proof.MoveScope.preserve-CancelR`).  `MergedReading` remains the
-- one open, plausible obligation pending review.
--
-- Two statements CHANGED with the port, each against the old surface:
--
--   * `preservation` (and everything built on it) takes `WfCtx Δ`.  The
--     premise-free statement is FALSE here: at a duplicate name map a
--     TyBeta contractum must mint a `MorphWf` that `Unique` refuses
--     (notes/DECISIONS.md, 2026-09-18).  `progress` needs no such
--     premise — a boundary case reads well-formedness off its own `env`.
--
--   * `det` takes the redex's typing derivation, from which it recovers
--     the name-map uniqueness the rules used to carry as premises
--     (notes/DECISIONS.md, 2026-09-18).
--
-- The reduction relation is indexed by the type context Δ only; the term
-- context is empty, as it must be (see strong.Preservation).

open import Data.List using ([])
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; Σ-syntax)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong.Types using (Ty)
open import strong.Ctx using (Ctxᵗ; WfCtx)
open import strong.Terms using (Term; Ctx; Value; _∣_⊢_⦂_)
open import strong.Reduction using (_⊢_-→_; _⊢_-→*_)
import strong.Reduction as R
import strong.proof.Preserve as P
import strong.proof.Progress as PP
import strong.Progress as Pr
import strong.Preservation as Pv
import strong.proof.TypeSafety as TS

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
-- The stage-1 theorems, over the statements pending review
------------------------------------------------------------------------

preservation : Preservation
preservation = Pv.preservation

preservation* : Preservation*
preservation* = Pv.preservation*

module Stage1
  (merged-reading : PP.MergedReading)
  where

  private
    module Pr1 = Pr.Stage1 merged-reading
    module TS1 = TS.Stage1 merged-reading

  progress : Progress
  progress = Pr1.progress

  type-safety : TypeSafety
  type-safety = TS1.type-safety

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
