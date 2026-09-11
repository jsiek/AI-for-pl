module strong.notes.TyPosExample where

-- WHAT TyPos'S RENAMING DOES TO M, AND WHY THE CONCEAL MUST NAME Y
-- (2026-09-11).
--
-- TyPos wedges a fresh binder Y BELOW b's own binders:
--
--   ᵇ[M] •B[A]  -→  ⁺ʸ⁼ᴬ[ ᵇ′[ ⁻ʸ[M′] •B′[Y] ] ]
--
-- so M's references to Δ move up by one while M's OWN binders stay put.
-- That is exactly `renᴹ (extN (numBindsᵇ b) suc)`.  Its partner, the
-- conceal that hides Y from M, must therefore name slot `numBindsᵇ b` —
-- 0 for a `reveal` (binds nothing), 1 for an `intro`.
--
-- Everything here is refl.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.Ctx
open import strong.CtxMorph
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction

------------------------------------------------------------------------
-- 1.  THE INTRO TAG — where 0 and `numBindsᵇ b` differ
------------------------------------------------------------------------

-- Δ has one Λ-bound slot Z; b = intro ℕ, so M lives under its own binder
-- X′=ℕ; we instantiate at A = 𝔹, so the fresh Y has rep 𝔹.
Δ : Ctxᵗ
Δ = unmasked abst ∷ []

old-frame : applyᵇ (intro `ℕ) Δ ≡ unmasked (bind `ℕ) ∷ unmasked abst ∷ []
old-frame = refl

old-colours : scopeᵗ (applyᵇ (intro `ℕ) Δ) ≡ 0 ∷ 1 ∷ []
old-colours = refl

-- WHAT THE RENAMING DOES: M's own binder stays at 0, Δ's slots move up.
renamed-colours : map (extN (numBindsᵇ (intro `ℕ)) suc) (0 ∷ 1 ∷ []) ≡ 0 ∷ 2 ∷ []
renamed-colours = refl

-- The frame M lands in, with the conceal naming Y = slot numBindsᵇ b = 1.
new-frame : lockχ (numBindsᵇ (intro `ℕ) ∷ [])
                  (applyᵇ (renBnd suc (intro `ℕ)) (unmasked (bind `𝔹) ∷ Δ))
  ≡ unmasked (bind `ℕ) ∷ masked (bind `𝔹) ∷ unmasked abst ∷ []
new-frame = refl

-- FRAME-EXACT: the renamed colours ARE the new frame's colours.
frame-exact :
  map (extN (numBindsᵇ (intro `ℕ)) suc) (scopeᵗ (applyᵇ (intro `ℕ) Δ))
  ≡ scopeᵗ (lockχ (numBindsᵇ (intro `ℕ) ∷ [])
                  (applyᵇ (renBnd suc (intro `ℕ)) (unmasked (bind `𝔹) ∷ Δ)))
frame-exact = refl

------------------------------------------------------------------------
-- 2.  THE COUNTERFACTUAL — what concealing slot 0 would have done
------------------------------------------------------------------------

-- It hides M'S OWN BINDER and leaves Y visible: the exact opposite of the
-- notes' ⁻ʸ[V⁺].  The colour sets then disagree by one at the head.
wrong-frame : lockχ (0 ∷ []) (applyᵇ (renBnd suc (intro `ℕ)) (unmasked (bind `𝔹) ∷ Δ))
  ≡ masked (bind `ℕ) ∷ unmasked (bind `𝔹) ∷ unmasked abst ∷ []
wrong-frame = refl

wrong-colours :
  scopeᵗ (lockχ (0 ∷ []) (applyᵇ (renBnd suc (intro `ℕ)) (unmasked (bind `𝔹) ∷ Δ)))
  ≡ 1 ∷ 2 ∷ []
wrong-colours = refl

colours-disagree : ¬ ((0 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ []))
colours-disagree ()

------------------------------------------------------------------------
-- 3.  THE REVEAL TAG — unaffected, since it binds nothing
------------------------------------------------------------------------

reveal-binds-nothing : numBindsᵇ (reveal (0 ∷ [])) ≡ 0
reveal-binds-nothing = refl

-- Δᵣ has one CONCEALED slot for the reveal tag to unlock.
Δᵣ : Ctxᵗ
Δᵣ = masked abst ∷ []

reveal-frame-exact :
  map (extN (numBindsᵇ (reveal (0 ∷ []))) suc) (scopeᵗ (applyᵇ (reveal (0 ∷ [])) Δᵣ))
  ≡ scopeᵗ (lockχ (numBindsᵇ (reveal (0 ∷ [])) ∷ [])
                  (applyᵇ (renBnd suc (reveal (0 ∷ []))) (unmasked (bind `𝔹) ∷ Δᵣ)))
reveal-frame-exact = refl

------------------------------------------------------------------------
-- 4.  STILL OPEN — the missing conversion
------------------------------------------------------------------------

-- TyBeta mints `V ⟨ revTy 0 B ⟩` to reconcile the interior's view (which
-- names the fresh binder) with the exterior's (which names its rep).
-- TyPos mints nothing, so its interior type mentions Y where ⊢intro
-- demands A.  With the ∀-body B = ` 0 (i.e. ∀Z. Z) and A = ℕ:
produced : (renameᵗ (extᵗ suc) (` 0)) [ ` 0 ]ᵗ ≡ ` 0      -- the • node's type
produced = refl

demanded : ⇑ᵗ ((` 0) [ `ℕ ]ᵗ) ≡ `ℕ                        -- what ⊢intro wants
demanded = refl

type-mismatch : ¬ (_≡_ {A = Ty} (` 0) `ℕ)
type-mismatch ()

-- A SECOND ITEM IN THE SAME FAMILY.  `renameᵗ (extᵗ suc) B` is ONE shift.
-- For b = reveal that is right (⊢reveal gives the interior the exterior's
-- type unchanged).  For b = intro, ⊢intro ALREADY shifted M's type by ⇑ᵗ,
-- so M′'s ∀-body carries two shifts and the rule names only one.  Both
-- belong with the conversion decision, which is Jeremy's.

-- AND THE GENERAL FRAME LAW the rule now owes, of which §1 and §3 are
-- instances (not refl in general — it needs map-fusion and, on the reveal
-- side, the ⊢reveal premise):
--
--   map (extN (numBindsᵇ b) suc) (scopeᵗ (applyᵇ b Δ))
--     ≡ scopeᵗ (lockχ (numBindsᵇ b ∷ [])
--                     (applyᵇ (renBnd suc b) (unmasked (bind A) ∷ Δ)))
