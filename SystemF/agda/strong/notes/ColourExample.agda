module strong.notes.ColourExample where

-- COLOUR PRESERVATION, ON ONE CONCRETE PROGRAM  (2026-09-11).
--
-- The program is the smallest one that has a colour to preserve:
--
--     (ΛX. λy:X. y) • (X→X) [ ℕ ]
--
-- §1 writes it with its colour annotations and TYPES it (every source node
-- discharges `χ ≡ scopeᵗ Δ`).  §2 takes the TyBeta step and shows the
-- reduct contains the SAME annotated subterm, with the same colour set
-- still correct at its new frame.  §3 is the ⊢reveal hole the repair
-- closed, as a refutation and its positive counterpart.  §4 exhibits the
-- one place a colour set legitimately changes (AppBnd's rebuilt node) and
-- checks `scopeᵇ`'s law there.
--
-- No postulates, no holes.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ; _×_; _,_; ∃-syntax)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction

------------------------------------------------------------------------
-- 1.  THE SOURCE PROGRAM, ANNOTATED AND TYPED
------------------------------------------------------------------------

-- The two frames the program has.  Outside, nothing is in scope; inside
-- the Λ, exactly the Λ-bound colour (slot 0) is.
Δ₀ : Ctxᵗ
Δ₀ = []

Δ₁ : Ctxᵗ
Δ₁ = unmasked abst ∷ []

colours-outside : scopeᵗ Δ₀ ≡ []
colours-outside = refl

colours-inside : scopeᵗ Δ₁ ≡ 0 ∷ []
colours-inside = refl

-- λy:X. y  — the ƛ node and the variable node both carry {X} = {0}.
idX : Term
idX = ƛ (` 0) ∙ (` 0 ⟪ 0 ∷ [] ⟫) ⟪ 0 ∷ [] ⟫

-- ΛX. λy:X. y  — the Λ node itself carries the EXTERIOR set, which is ∅.
polyId : Term
polyId = Λ idX ⟪ [] ⟫

-- (ΛX. λy:X. y) • (X→X) [ ℕ ]
prog : Term
prog = polyId • (` 0 ⇒ ` 0) [ `ℕ ]⟪ [] ⟫

-- THE DERIVATION.  Every `refl` below is one discharged colour equation:
-- the variable's, the ƛ's, the Λ's and the •'s.
⊢prog : Δ₀ ∣ [] ⊢ prog ⦂ (`ℕ ⇒ `ℕ)
⊢prog = ⊢•[] (⊢Λ (⊢ƛ (wf-var (unmasked abst , ez , nameable))
                     (⊢` here refl)
                     refl)
                 refl)
             wf-ℕ
             refl

------------------------------------------------------------------------
-- 2.  THE STEP, AND THE COLOUR THAT SURVIVES IT
------------------------------------------------------------------------

-- TyBeta:  (ΛX.V) • B [ A ]  -→  ⁺ˣ⁼ᴬ[ V⟨+X(B)⟩ ].
--
-- READ THE TYPE OF `step`: the reduct mentions `idX` ITSELF — the same
-- term, not a renamed or re-annotated copy.  Nothing in the colour
-- annotations moved.
step : Δ₀ ⊢ prog -→ ν intro `ℕ [ idX ⟨ revTy 0 (` 0 ⇒ ` 0) ⟩ ]
step = TyBeta (simple→value Sƛ)

-- And the annotation is still CORRECT at the new frame.  idX was born at
-- Δ₁ = `unmasked abst ∷ []` (a Λ-bound slot) and now sits at Δ₂ =
-- `unmasked (bind ℕ) ∷ []` (an instantiated binder).  The BINDING layer
-- changed — abst became a binder with representation ℕ — but the LOCK
-- layer did not, and only the lock layer is visible to scopeᵗ.
Δ₂ : Ctxᵗ
Δ₂ = unmasked (bind `ℕ) ∷ []

colour-preserved : scopeᵗ Δ₂ ≡ scopeᵗ Δ₁
colour-preserved = refl

-- so the annotation idX carries is the right one on both sides:
colour-still-right : scopeᵗ Δ₂ ≡ 0 ∷ []
colour-still-right = refl

------------------------------------------------------------------------
-- 3.  THE ⊢reveal HOLE, AND WHAT THE NEW PREMISE REFUSES
------------------------------------------------------------------------

-- Take the SAME Δ₂ — slot 0 is a binder and it is NAMEABLE.  A boundary
-- `ν reveal {0} [ M ]` there unlocks nothing.  AppBnd sends the argument
-- across the DUAL, `ν conceal {0} [ W ]`, and W comes back with slot 0
-- LOCKED: any `` ` 0 `` in W is no longer nameable, so the reduct is
-- ill-typed.  Preservation was FALSE, with no annotation involved.
vacuous-reveal : lockχ (0 ∷ []) (unlockχ (0 ∷ []) Δ₂) ≡ masked (bind `ℕ) ∷ []
vacuous-reveal = refl

round-trip-fails : ¬ (lockχ (0 ∷ []) (unlockχ (0 ∷ []) Δ₂) ≡ Δ₂)
round-trip-fails ()

-- The repair refuses exactly this boundary: ⊢reveal now demands every
-- slot of the tag be LOCKED, and slot 0 of Δ₂ is not.
no-vacuous-reveal : ¬ (Δ₂ ∋lks (0 ∷ []))
no-vacuous-reveal (lks∷ (_ , ez , ()) _)

-- Where the tag DOES tell the truth, the round trip is exact — and it is
-- `lock-unlock` that says so, not a fresh computation.
Δ₃ : Ctxᵗ
Δ₃ = masked (bind `ℕ) ∷ []

locked-tag : Δ₃ ∋lks (0 ∷ [])
locked-tag = lks∷ (masked (bind `ℕ) , ez , locked) lks[]

round-trip-exact : lockχ (0 ∷ []) (unlockχ (0 ∷ []) Δ₃) ≡ Δ₃
round-trip-exact = lock-unlock locked-tag

------------------------------------------------------------------------
-- 4.  THE ONE PLACE A COLOUR SET LEGITIMATELY CHANGES
------------------------------------------------------------------------

-- At Δ₃ the colour set is EMPTY: slot 0 is concealed.
colours-at-Δ₃ : scopeᵗ Δ₃ ≡ []
colours-at-Δ₃ = refl

-- A boundary `ν reveal {0} [ M ]` at Δ₃ unlocks it, so M's frame has
-- colour set {0}.  AppBnd pushes the application node inside, and REBUILDS
-- it with `scopeᵇ (reveal {0})` applied to the node's own old set.
interior-colours : scopeᵇ (reveal (0 ∷ [])) (scopeᵗ Δ₃) ≡ 0 ∷ []
interior-colours = refl

-- scopeᵇ's law, at this boundary: the computed set IS the interior's.
scopeᵇ-law-reveal :
  scopeᵇ (reveal (0 ∷ [])) (scopeᵗ Δ₃) ≡ scopeᵗ (unlockχ (0 ∷ []) Δ₃)
scopeᵇ-law-reveal = refl

-- …and at an `intro`, where the interior gains the fresh binder's colour
-- and keeps the old ones shifted.
scopeᵇ-law-intro :
  scopeᵇ (intro `ℕ) (scopeᵗ Δ₂) ≡ scopeᵗ (applyᵇ (intro `ℕ) Δ₂)
scopeᵇ-law-intro = refl
