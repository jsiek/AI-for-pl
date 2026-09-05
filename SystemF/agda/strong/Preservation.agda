module strong.Preservation where

-- PRESERVATION for Strong System F (v2, the conversion-boundary calculus).
--
-- THE STATEMENT (and why it has the shape it has).
--
--   preservation : Δ ∣ [] ⊢ M ⦂ A → Δ ⊢ M -→ M′ → Δ ∣ [] ⊢ M′ ⦂ A
--
-- * NO CONTEXT WELL-FORMEDNESS PREMISE (`⊢ᶜ Δ`).  The v1 endgame note
--   expected the store-typing pattern, because `conv-unseal` hands back an
--   owner's rep with no `Δ ⊢ᵗ A` attached.  It is not needed here: every
--   site that reads a rep back also has the `env` node that put it there,
--   whose LAST PREMISE is `Δ ⊢ᵗ Bₑ`, and `⊢ᵗ-of` (proof/Preserve §1)
--   recovers the well-formedness of any typed term's type from the
--   derivation alone.  TyBeta — the one rule that MINTS a rep — gets it
--   from `⊢·[]`'s own premise.
--
-- * THE TERM CONTEXT IS EMPTY.  `_⊢_-→_` carries no term context, and
--   TyBeta's contractum is a WRAPPER, whose interior `env` types at
--   Γ = [].  At a non-empty Γ the theorem is already false: `Λ (ƛ `ℕ ∙ ` 1)`
--   is a value at Γ = `ℕ ∷ [], TyBeta fires, and the contractum's interior
--   would have to mention a term variable that a wrapper body may not have.
--
-- THE STATUS.  As the rules in strong.Reduction stand, preservation is
-- FALSE: four of the eight rules have machine-checked counterexamples
-- (proof/PreserveObstruct — a typed redex whose contractum is untypeable
-- at the redex's type), one per root cause:
--
--   CancelR  drops Θ₁'s frame
--   TyPeelR  reuses the exterior ∀-body as the pushed-in annotation
--   Peel     the dual re-blocks a no-op `unlock`
--   IdPush   pushes an owner's rep across a `lock`
--
-- What IS proven, unconditionally: TyBeta (the mint), Beta, Drop$ and all
-- five congruences — and preservation itself, over the four open cases as
-- premises (`module Conditional`).

open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (¬_)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; _[_]ᵗ)
open import strong.Ctx using (Ctxᵗ; Ent; abst; bind; blk; Base; _⊢ᵗ_)
open import strong.Conversion using (Conv; id)
open import strong.Terms
open import strong.TermSubst using (_[_]ᵐ; preserve-Beta)
open import strong.Reduction using (_⊢_-→_; _⊢_-→*_; unsealAt)

open import strong.proof.Preserve
  using (PeelCase; TyPeelRCase; CancelRCase; IdPushCase;
         preserve-TyBeta; preserve-Drop$; ⊢ᵗ-of; CtxWf-[])
import strong.proof.Preserve as P
open import strong.proof.PreserveObstruct using (¬preservation)

private
  variable
    Δ : Ctxᵗ
    A B C : Ty
    M M′ N : Term

------------------------------------------------------------------------
-- 1.  The statements
------------------------------------------------------------------------

Preservation : Set
Preservation = ∀ {Δ M M′ A}
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→ M′
    ----------------
  → Δ ∣ [] ⊢ M′ ⦂ A

Preservation* : Set
Preservation* = ∀ {Δ M M′ A}
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→* M′
    ----------------
  → Δ ∣ [] ⊢ M′ ⦂ A

------------------------------------------------------------------------
-- 2.  The status: FALSE for the rule set as it stands
------------------------------------------------------------------------

preservation-fails : ¬ Preservation
preservation-fails = ¬preservation

------------------------------------------------------------------------
-- 3.  CONDITIONAL preservation
------------------------------------------------------------------------

-- Every case is discharged except the four refuted ones, which are the
-- module's parameters.  Instantiating this module is exactly the work a
-- repair of those four rules would unlock.
module Conditional
  (peel   : PeelCase)
  (typeel : TyPeelRCase)
  (cancel : CancelRCase)
  (idpush : IdPushCase)
  where

  private
    module I = P.Impl peel typeel cancel idpush

  preservation : Preservation
  preservation = I.preserve

  preservation* : Preservation*
  preservation* = I.preserve*

------------------------------------------------------------------------
-- 4.  The rule cases that hold unconditionally
------------------------------------------------------------------------

-- TYBETA — the boundary is born, and its face is minted at the owner the
-- rule itself binds.
preservation-TyBeta : ∀ {A}
  → Δ ∣ [] ⊢ (Λ N) ·[ B , A ] ⦂ C
    ---------------------------------------------
  → Δ ∣ [] ⊢ N ⟪ bind A ∷ [] , unsealAt 0 B ⟫ ⦂ C
preservation-TyBeta = preserve-TyBeta

-- BETA — the ordinary β step, i.e. the substitution lemma.
preservation-Beta : ∀ {W}
  → Δ ∣ [] ⊢ (ƛ A ∙ N) · W ⦂ C
    --------------------------
  → Δ ∣ [] ⊢ N [ W ]ᵐ ⦂ C
preservation-Beta = preserve-Beta

-- DROP$ — a base-faced boundary over a numeral.
preservation-Drop$ : ∀ {n Θ}
  → Base A
  → Δ ∣ [] ⊢ ($ n) ⟪ Θ , id A ⟫ ⦂ C
    -------------------------------
  → Δ ∣ [] ⊢ $ n ⦂ C
preservation-Drop$ = preserve-Drop$

------------------------------------------------------------------------
-- 5.  A by-product worth naming: typed terms have well-formed types
------------------------------------------------------------------------

-- This is what stands in for `⊢ᶜ Δ`.
⊢ᵗ-of-closed : Δ ∣ [] ⊢ M ⦂ A → Δ ⊢ᵗ A
⊢ᵗ-of-closed = ⊢ᵗ-of CtxWf-[]
