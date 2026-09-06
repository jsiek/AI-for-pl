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
-- THE STATUS (2026-09-05, after the CancelR/TyPeelR rule repairs).
--
--   PEEL      PROVEN (proof/PeelDual.preserve-Peel), since `dualS` drops
--             the `unlock` case.
--   CANCELR   REPAIRED — both frames kept, both faces neutralised — and
--             DISCHARGED over ONE interface, `ScopedAtUnseal`
--             (proof/CancelFaces.preserve-CancelR).  Its old
--             counterexample now TYPES (proof/PreserveObstruct §1).
--   TYPEELR   REPAIRED — premise-determined annotation, plain frame,
--             minted face `unsealAtᶜ 0 s` — and PROVEN at an `↑ˢ`
--             (reveal) ∀-face (proof/Preserve.preserve-TyPeelR-↑).  At a
--             `↓ˢ` (conceal) ∀-face the contractum's face is
--             MIXED-POLARITY, which the conversion judgment forbids
--             outright: `¬TyPeelRCase` (proof/PreserveObstruct §2) is now
--             a statement about the POLARITY DISCIPLINE, not about the
--             rule.  Examples §13 reaches it from closed plain source.
--   IDPUSH    right as formulated; it needs only the grounded scoping
--             fact (proof/WallReach.idPush-RepWf).
--
-- What IS proven, unconditionally: TyBeta (the mint), Beta, Drop$, PEEL,
-- and all five congruences — and preservation itself, over the remaining
-- open cases as premises (`module Conditional`).

open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (¬_)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; _[_]ᵗ; renameᵗ; extᵗ)
open import strong.Ctx
  using (Ctxᵗ; Ent; abst; bind; blk; Base; _⊢ᵗ_; _∋_:=_; liftN)
open import strong.Conversion
  using (Conv; id; seal; unseal; _↦_; `∀; idc; _⊢_∶_⇝_∙_; Pol; ↑ˢ; ↓ˢ)
open import strong.Terms
open import strong.TermSubst using (_[_]ᵐ; wkᴹ; preserve-Beta)
open import strong.Reduction
  using (_⊢_-→_; _⊢_-→*_; unsealAt; unsealAtᶜ)

open import strong.proof.Preserve
  using (PeelCase; TyPeelRCase; TyPeelRCase↑; CancelRCase; IdPushCase;
         preserve-TyBeta; preserve-Drop$; preserve-TyPeelR-↑;
         ⊢ᵗ-of; CtxWf-[])
import strong.proof.Preserve as P
open import strong.proof.PeelDual using (preserve-Peel)
open import strong.proof.CancelFaces using (preserve-CancelR)
open import strong.proof.ScopedAtUnsealDef using (ScopedAtUnseal)
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

-- Every case is discharged except the ones still open, which are the
-- module's parameters.  Note what CancelR's parameter now is: NOT its
-- preservation case, but the SCOPING FACT `ScopedAtUnseal` — the rule's
-- case is derived from it (`preserve-CancelR`).  That is the whole of
-- CancelR's remaining debt, and it is the common wall, stated once.
module Conditional
  (typeel : TyPeelRCase)
  (scoped : ScopedAtUnseal)
  (idpush : IdPushCase)
  where

  private
    module I = P.Impl preserve-Peel typeel (preserve-CancelR scoped) idpush

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

-- TYPEELR AT AN `↑ˢ` ∀-FACE — the repaired rule, unconditionally.  The
-- pushed-in annotation is the interior ∀-body the premise determines, and
-- the face is the mint at the owner the rule binds.
preservation-TyPeelR-↑ : ∀ {V Θ s B Bᵢ Bₑ}
  → Value V
  → (abst ∷ fceC Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ ∙ ↑ˢ
  → Δ ∣ [] ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ] ⦂ C
    -----------------------------------------------------
  → Δ ∣ [] ⊢ (wkᴹ 1 V ·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ])
               ⟪ bind A ∷ Θ , unsealAtᶜ 0 s ⟫ ⦂ C
preservation-TyPeelR-↑ = preserve-TyPeelR-↑

-- CANCELR — over the ONE scoping interface.
preservation-CancelR : ∀ {V Θ₁ Θ₂ X Y}
  → ScopedAtUnseal
  → Value V → fceC Θ₂ Δ ∋ Y := A
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
    ---------------------------------------------------------------
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , idc (liftN (nbind Θ₁) A) ⟫) ⟪ Θ₂ , idc A ⟫ ⦂ C
preservation-CancelR sc = preserve-CancelR sc

------------------------------------------------------------------------
-- 5.  A by-product worth naming: typed terms have well-formed types
------------------------------------------------------------------------

-- This is what stands in for `⊢ᶜ Δ`.
⊢ᵗ-of-closed : Δ ∣ [] ⊢ M ⦂ A → Δ ⊢ᵗ A
⊢ᵗ-of-closed = ⊢ᵗ-of CtxWf-[]
