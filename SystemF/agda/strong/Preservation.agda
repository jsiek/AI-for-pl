module strong.Preservation where

-- PRESERVATION for Strong System F (v2, the conversion-boundary calculus).
--
-- THE STATEMENT (and why it has the shape it has).
--
--   preservation : Δ ∣ [] ⊢ M ⦂ A → Δ ⊢ M -→ M′ → Δ ∣ [] ⊢ M′ ⦂ A
--
-- * NO CONTEXT WELL-FORMEDNESS PREMISE (`⊢ᶜ Δ`).  The v1 endgame note
--   expected the store-typing pattern, because `conv-unseal` hands back a
--   binder's rep with no `Δ ⊢ᵗ A` attached.  It is not needed here: every
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
-- THE STATUS (2026-09-06, after the SCOPE MOVE).  PRESERVATION HOLDS,
-- with no parameters and no invariant.
--
--   TYBETA    PROVEN (proof/Preserve.preserve-TyBeta) — the mint.
--   BETA      PROVEN (strong.TermSubst.preserve-Beta).
--   PEEL      PROVEN (proof/PeelDual.preserve-Peel), since `dualScope` drops
--             the `unlock` case.
--   TYPEELR   REPAIRED and PROVEN, at EVERY ∀ CONVERSION
--             (proof/Preserve.preserve-TyPeelR).  The rule pushes in the
--             premise-determined interior ∀-body, keeps the frame plain,
--             and mints the conversion `instReveal 0 s`.  Under the
--             retired POLARITY index this held only at a REVEALING
--             conversion, because the mint's inserted `seal 0` sat where
--             a global `p` refused it; per variable each leaf cites its
--             own binder, and `env`'s frame checks are what keep the two
--             apart.  Examples §13 runs both directions from closed
--             plain source.
--   DROP$     PROVEN (proof/Preserve.preserve-Drop$).
--   CANCELR   PROVEN (proof/MoveScope.preserve-CancelR).
--   IDPUSH    PROVEN (proof/MoveScope.preserve-IdPush).
--
-- WHAT CLOSED THE LAST TWO: THE SCOPE MOVE (Jeremy, 2026-09-06;
-- strong.Reduction §2b).  Both rules swap the two conversions, so the
-- inner boundary stops presenting the abstract name and starts presenting
-- the BINDER'S REP — and `env`'s last premise then asks for that rep to be
-- well formed INSIDE the outer frame, where its own `lock`s may have
-- blocked the slot the rep names.  That was the wall (the old
-- proof/PreserveObstruct §4 refutation; the search for an invariant to
-- ground the premise is recorded in notes/DECISIONS.md, 2026-09-06).
--
-- The repair is a FRAME MOVE, not a side condition: the outer frame keeps
-- only its binds and unmasks (`dropLocks Θ₂`) and its whole SCOPE travels
-- into the inner frame's tail (`Θ₁ ⋉ Θ₂`), where `scope` applies it first —
-- exactly where it applied before.  Then
-- `interior (dropLocks Θ₂) Δ ≡ convCtx Θ₂ Δ`, the rep is presented OUTSIDE the
-- locks, and the missing premise is `wf-shiftBy-pushBinds` on the redex's own
-- exterior type: the reveal's target IS that type, lifted.  Nothing is
-- assumed about the world, and the old counterexample now REDUCES to a
-- TYPED term (proof/PreserveObstruct §4, `⊢i-contractum`).

open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (¬_)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; _[_]ᵗ; renameᵗ; extᵗ)
open import strong.Ctx
  using (Ctxᵗ; Ent; abst; bind; masked; Base; _⊢ᵗ_; _∋_:=_; shiftBy)
open import strong.Conversion
  using (Conv; id; seal; unseal; _↦_; `∀; mkId; _⊢_∶_⇝_)
open import strong.Terms
open import strong.TermSubst using (_[_]ᵐ; wkᴹ; preserve-Beta)
open import strong.Reduction
  using (_⊢_-→_; _⊢_-→*_; reveal; instReveal)

open import strong.Reduction using (_⋉_; dropLocks)
open import strong.proof.Preserve
  using (preserve-TyBeta; preserve-Drop$; preserve-TyPeelR;
         ⊢ᵗ-of; CtxWf-[])
import strong.proof.Preserve as P
open import strong.proof.PeelDual using (preserve-Peel)
open import strong.proof.MoveScope using (preserve-CancelR; preserve-IdPush)

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
-- 2.  THE THEOREMS
------------------------------------------------------------------------

-- No parameters, no invariant, no side condition: every case of every
-- rule is discharged.  `P.Impl` is the induction, and its three
-- arguments are the three cases whose proofs live downstream of
-- proof/Preserve.
private
  module I = P.Impl preserve-Peel preserve-CancelR preserve-IdPush

preservation : Preservation
preservation = I.preserve

preservation* : Preservation*
preservation* = I.preserve*

------------------------------------------------------------------------
-- 4.  The rule cases that hold unconditionally
------------------------------------------------------------------------

-- TYBETA — the boundary is born, and its conversion is minted at the
-- binder the rule itself introduces.
preservation-TyBeta : ∀ {A}
  → Δ ∣ [] ⊢ (Λ N) ·[ B , A ] ⦂ C
    ---------------------------------------------
  → Δ ∣ [] ⊢ N ⟪ bind A ∷ [] , reveal 0 B ⟫ ⦂ C
preservation-TyBeta = preserve-TyBeta

-- BETA — the ordinary β step, i.e. the substitution lemma.
preservation-Beta : ∀ {W}
  → Δ ∣ [] ⊢ (ƛ A ∙ N) · W ⦂ C
    --------------------------
  → Δ ∣ [] ⊢ N [ W ]ᵐ ⦂ C
preservation-Beta = preserve-Beta

-- DROP$ — an identity boundary at a base type, over a numeral.
preservation-Drop$ : ∀ {n Θ}
  → Base A
  → Δ ∣ [] ⊢ ($ n) ⟪ Θ , id A ⟫ ⦂ C
    -------------------------------
  → Δ ∣ [] ⊢ $ n ⦂ C
preservation-Drop$ = preserve-Drop$

-- TYPEELR AT ANY ∀ CONVERSION — the repaired rule, unconditionally.  The
-- pushed-in annotation is the interior ∀-body the premise determines, and
-- the conversion is the mint at the binder the rule introduces.
preservation-TyPeelR : ∀ {V Θ s B Bᵢ Bₑ}
  → Value V
  → (abst ∷ convCtx Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ
  → Δ ∣ [] ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ] ⦂ C
    -----------------------------------------------------
  → Δ ∣ [] ⊢ (wkᴹ 1 V ·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ])
               ⟪ bind A ∷ Θ , instReveal 0 s ⟫ ⦂ C
preservation-TyPeelR = preserve-TyPeelR

-- CANCELR — at the moved scope, unconditionally.
preservation-CancelR : ∀ {V Θ₁ Θ₂ X Y}
  → Value V → convCtx Θ₂ Δ ∋ Y := A
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
    ---------------------------------------------------------------
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ ⋉ Θ₂ , mkId (shiftBy (numBinds Θ₁) A) ⟫)
               ⟪ dropLocks Θ₂ , mkId A ⟫ ⦂ C
preservation-CancelR = preserve-CancelR

-- IDPUSH — the case the wall used to block, likewise unconditional.
preservation-IdPush : ∀ {V Θ₁ Θ₂ X Y}
  → Value V → convCtx Θ₂ Δ ∋ Y := A
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
    ---------------------------------------------------------------
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ ⋉ Θ₂ , unseal X ⟫) ⟪ dropLocks Θ₂ , mkId A ⟫ ⦂ C
preservation-IdPush = preserve-IdPush

------------------------------------------------------------------------
-- 5.  A by-product worth naming: typed terms have well-formed types
------------------------------------------------------------------------

-- This is what stands in for `⊢ᶜ Δ`.
⊢ᵗ-of-closed : Δ ∣ [] ⊢ M ⦂ A → Δ ⊢ᵗ A
⊢ᵗ-of-closed = ⊢ᵗ-of CtxWf-[]
