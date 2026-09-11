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
open import strong.Conversion
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
-- 4.  THE MISSING CONVERSION — the gap, and the fix
------------------------------------------------------------------------

-- THE EXAMPLE.  V : ∀Z. Z→Z behind a positive boundary, instantiated at
-- ℕ.  So the ∀-body is B = ` 0 ⇒ ` 0 and A = ℕ, and the answer must have
-- the type the redex had.
B A : Ty
B = ` 0 ⇒ ` 0
A = `ℕ

redex-type : B [ A ]ᵗ ≡ (`ℕ ⇒ `ℕ)
redex-type = refl

-- Δ₁ is the intro's interior: Y at slot 0, with representation ℕ.
Δ₁ : Ctxᵗ
Δ₁ = unmasked (bind `ℕ) ∷ []

-- WHAT THE REBUILT `•` NODE PRODUCES: B with Z := Y.  In de Bruijn the
-- lift-then-substitute-slot-0 composite is the IDENTITY, so it is
-- literally B again — read at Δ₁, where slot 0 is Y.
produced : (renameᵗ (extᵗ suc) B) [ ` 0 ]ᵗ ≡ B
produced = refl

-- WITHOUT A CONVERSION that is what the ⁺ʸ⁼ᴬ boundary would have to
-- accept, and ⊢intro demands ⇑ᵗ of the exterior type instead.
demanded : ⇑ᵗ (B [ A ]ᵗ) ≡ (`ℕ ⇒ `ℕ)
demanded = refl

without-conversion : ¬ (B ≡ (`ℕ ⇒ `ℕ))
without-conversion ()

-- THE FIX, INSTALLED.  `revTy 0 B` is exactly TyBeta's conversion, and it
-- has precisely the type the gap needs:  B[Z:=Y] ⇝ B[Z:=ℕ].
Y∋ℕ : Δ₁ ∋ 0 := `ℕ
Y∋ℕ = ez

the-conversion : revTy 0 B ≡ (seal 0 ↦ unseal 0)
the-conversion = refl

conversion-types : Δ₁ ⊢ revTy 0 B ∶ B ⇝ (B [ A ]ᵗ)
conversion-types = conv-fun (conv-seal Y∋ℕ) (conv-unseal Y∋ℕ)

-- NOTE THE CONTRAVARIANT FLIP: the DOMAIN gets a seal (conceal), the
-- CODOMAIN an unseal (reveal).  The Agda's revTy does this; notes-v3 said
--   +X(A → B) = +X(A) → +X(B)
-- and defined no -X(A) at all.  Corrected there on 2026-09-11.

------------------------------------------------------------------------
-- 5.  B'S SHIFT IS TAG-DEPENDENT
------------------------------------------------------------------------

-- M's type already carries `numBindsᵇ b` shifts (⊢intro hands its body
-- ⇑ᵗ of the exterior type; ⊢reveal hands it the type unchanged), and the
-- rule adds ONE more for Y.  Hence `wkN (suc (numBindsᵇ b))`.

-- At a reveal that is DEFINITIONALLY the old one-shift form, since
-- wkN 1 X = suc X — so nothing that worked before moved.
reveal-shift-unchanged : ∀ {χ}
  → renameᵗ (extᵗ (wkN (suc (numBindsᵇ (reveal χ))))) B ≡ renameᵗ (extᵗ suc) B
reveal-shift-unchanged = refl

-- At an intro it is genuinely two shifts, and they differ.
intro-shift : renameᵗ (extᵗ (wkN (suc (numBindsᵇ (intro `ℕ))))) (` 0 ⇒ ` 1)
  ≡ (` 0 ⇒ ` 3)
intro-shift = refl

shifts-differ : ¬ (_≡_ {A = Ty} (` 0 ⇒ ` 3) (` 0 ⇒ ` 2))
shifts-differ ()

-- AND THE GENERAL FRAME LAW the rule owes, of which §1 and §3 are
-- instances (not refl in general — it needs map-fusion and, on the reveal
-- side, the ⊢reveal premise):
--
--   map (extN (numBindsᵇ b) suc) (scopeᵗ (applyᵇ b Δ))
--     ≡ scopeᵗ (lockχ (numBindsᵇ b ∷ [])
--                     (applyᵇ (renBnd suc b) (unmasked (bind A) ∷ Δ)))
