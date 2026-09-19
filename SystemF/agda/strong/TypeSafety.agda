module strong.TypeSafety where

-- TYPE SAFETY for Strong System F (the two-universe design).
--
-- The public theorem surface.  Two theorems hold outright:
--
--   det           reduction is deterministic on well-typed terms
--   value-¬step   values do not step
--
-- The other three — progress, preservation (and preservation* along a
-- run), and their composition type-safety — are STAGE-1 PARAMETERIZED:
-- the statements are final, and the proofs are complete modulo the
-- reviewed-before-implementation statements collected by `Stage1` below
-- (`MergedReading` for progress; `CrossΛTyping`, `AddLock0Typing` and
-- the three crossing cases for preservation).  No postulates: a missing
-- proof is a module parameter, visible in the type of `Stage1`.
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

module Stage1
  (merged-reading : PP.MergedReading)
  (crossΛ   : P.CrossΛTyping)
  (addLock0 : P.AddLock0Typing)
  (peel     : P.PeelCase)
  (cancel   : P.CancelRCase)
  (idpush   : P.IdPushCase)
  where

  private
    module Pr1 = Pr.Stage1 merged-reading
    module Pv1 = Pv.Stage1 crossΛ addLock0 peel cancel idpush
    module TS1 = TS.Stage1 merged-reading crossΛ addLock0
                           peel cancel idpush

  progress : Progress
  progress = Pr1.progress

  preservation : Preservation
  preservation = Pv1.preservation

  preservation* : Preservation*
  preservation* = Pv1.preservation*

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
