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
-- THE STATUS (2026-09-06, after the polarity index was retired).
--
--   PEEL      PROVEN (proof/PeelDual.preserve-Peel), since `dualS` drops
--             the `unlock` case.
--   CANCELR   REPAIRED — both frames kept, both faces neutralised — and
--             DISCHARGED over ONE interface, `ScopedAtUnseal`
--             (proof/CancelFaces.preserve-CancelR).  Its old
--             counterexample now TYPES (proof/PreserveObstruct §1).
--   TYPEELR   REPAIRED and PROVEN, at EVERY ∀-face
--             (proof/Preserve.preserve-TyPeelR).  The rule pushes in the
--             premise-determined interior ∀-body, keeps the frame plain,
--             and mints the face `unsealAtᶜ 0 s`.  Under the retired
--             POLARITY index this held only at a reveal face, because the
--             mint's inserted `seal 0` sat where a global `p` refused it;
--             per variable each leaf cites its own owner, and `env`'s
--             frame checks are what keep the two apart.  Examples §13
--             runs both faces from closed plain source.
--   IDPUSH    the one case still open; it needs the grounded scoping fact
--             (proof/WallReach.idPush-RepWf).
--
-- What IS proven, unconditionally: TyBeta (the mint), Beta, Drop$, PEEL,
-- TYPEELR, and all five congruences — and preservation itself, over the
-- remaining open cases as premises (`module Conditional`).
--
-- WHERE IDPUSH'S MISSING PREMISE CAN LIVE.  proof/WallReach shows the
-- missing premise is `RepWf (intC Θ₂ Δ)` and proof/IdPushReach proves the
-- case from it (`idPush⁺`, with the mask-only step `maskOnly` now PROVEN).
-- proof/WallGrounding settles where that premise can be GROUNDED: NOT in
-- `Bwf`, because the `¬IdPushCase` witness and a REACHABLE wrapper of
-- Examples §12 have the SAME `Δ` and the SAME `Θ` and differ only in
-- their FACE — so a `Bwf`-level wall would make `preserve-TyBeta` false.
-- The candidate that followed — a FACE-CONDITIONED `env` premise, asked
-- at reveal faces only — switched on the polarity index and is retired
-- with it; its witness survives as `Ξ★`/`Θ★₁` (proof/ChainScoped §3),
-- which shows the obstruction MOVES to the inner, id-faced layer.
-- proof/ChainScoped runs the next two: POINTWISE `RepWf` at every
-- name-faced boundary, killed by a closed program (`¬NameFacedRepWf`),
-- and the REP CHAIN of the face's own name, which gets IdPush and
-- CancelR right but is broken by TyBeta's retag (`¬ChainFaced`) — a
-- chain STOPS at a Λ-bound slot, and TyBeta gives that slot a rep.

open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (¬_)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; _[_]ᵗ; renameᵗ; extᵗ)
open import strong.Ctx
  using (Ctxᵗ; Ent; abst; bind; blk; Base; _⊢ᵗ_; _∋_:=_; liftN)
open import strong.Conversion
  using (Conv; id; seal; unseal; _↦_; `∀; idc; _⊢_∶_⇝_)
open import strong.Terms
open import strong.TermSubst using (_[_]ᵐ; wkᴹ; preserve-Beta)
open import strong.Reduction
  using (_⊢_-→_; _⊢_-→*_; unsealAt; unsealAtᶜ)

open import strong.proof.Preserve
  using (IdPushCase; preserve-TyBeta; preserve-Drop$; preserve-TyPeelR;
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
-- module's TWO parameters (TyPeelR left the list when the polarity index
-- did).  Note what CancelR's parameter is: NOT its preservation case, but
-- the SCOPING FACT `ScopedAtUnseal` — the rule's case is derived from it
-- (`preserve-CancelR`).  That is the whole of CancelR's remaining debt,
-- and it is the common wall, stated once.
module Conditional
  (scoped : ScopedAtUnseal)
  (idpush : IdPushCase)
  where

  private
    module I = P.Impl preserve-Peel (preserve-CancelR scoped) idpush

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

-- TYPEELR AT ANY ∀-FACE — the repaired rule, unconditionally.  The
-- pushed-in annotation is the interior ∀-body the premise determines, and
-- the face is the mint at the owner the rule binds.
preservation-TyPeelR : ∀ {V Θ s B Bᵢ Bₑ}
  → Value V
  → (abst ∷ fceC Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ
  → Δ ∣ [] ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ] ⦂ C
    -----------------------------------------------------
  → Δ ∣ [] ⊢ (wkᴹ 1 V ·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ])
               ⟪ bind A ∷ Θ , unsealAtᶜ 0 s ⟫ ⦂ C
preservation-TyPeelR = preserve-TyPeelR

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
