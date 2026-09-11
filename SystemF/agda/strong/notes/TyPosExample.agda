module strong.notes.TyPosExample where

-- TyPos, AND WHY THE FRESH BINDER Y GOES INSIDE b  (2026-09-11).
--
--   Δ ⊢ ⁺ᵖ[V⁺] •B[A]  -→  ⁺ᵖ[ ⁺ʸ⁼ᴬ[ (⁻ʸ[V⁺] •B[Y])⟨+Y(B[Y])⟩ ] ]
--
-- §1 checks the rule is FRAME-EXACT: M's renaming and the frame it lands
-- in agree on the colours.  §2 checks the hidden set is a PREFIX of the
-- context — the property the old Γ↓X design needs.  §3 is the earlier
-- shape, with Y OUTSIDE b, which was well typed under lock/unlock but
-- whose mask was NOT a prefix.  §4 is the conversion.  §5 is B's shifts.
-- §6 is TyConceal and the audit of every rule that mints an `intro`.
--
-- Everything is refl or a short proof; no postulates, no holes.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import strong.Types
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction

------------------------------------------------------------------------
-- 1.  THE FRAME M LANDS IN, AND THE RENAMING THAT PUTS IT THERE
------------------------------------------------------------------------

-- Δ has one Λ-bound slot Z; b = intro ℕ, so M already lives under its own
-- binder X′=ℕ; we instantiate at A = 𝔹, so the fresh Y has rep 𝔹.
Δ : Ctxᵗ
Δ = unmasked abst ∷ []

old-frame : applyᵇ (intro `ℕ) Δ ≡ unmasked (bind `ℕ) ∷ unmasked abst ∷ []
old-frame = refl

old-colours : scopeᵗ (applyᵇ (intro `ℕ) Δ) ≡ 0 ∷ 1 ∷ []
old-colours = refl

-- Y is the INNERMOST binder, so M gains ONE slot at the bottom and the
-- renaming is plain `suc` — every index moves up by one.
renamed-colours : map suc (0 ∷ 1 ∷ []) ≡ 1 ∷ 2 ∷ []
renamed-colours = refl

-- The frame: Y's slot, MASKED, pushed onto b's interior.
new-frame : lockχ (0 ∷ [])
              (unmasked (bind (shiftBy (numBindsᵇ (intro `ℕ)) `𝔹))
                 ∷ applyᵇ (intro `ℕ) Δ)
  ≡ masked (bind `𝔹) ∷ unmasked (bind `ℕ) ∷ unmasked abst ∷ []
new-frame = refl

-- FRAME-EXACT: the renamed colours ARE the new frame's colours.
frame-exact :
  map suc (scopeᵗ (applyᵇ (intro `ℕ) Δ))
  ≡ scopeᵗ (lockχ (0 ∷ [])
              (unmasked (bind (shiftBy (numBindsᵇ (intro `ℕ)) `𝔹))
                 ∷ applyᵇ (intro `ℕ) Δ))
frame-exact = refl

------------------------------------------------------------------------
-- 2.  THE HIDDEN SET IS A PREFIX
------------------------------------------------------------------------

-- Slot 0 masked, everything below it visible.  A mask that is a PREFIX of
-- the context is exactly what the old `Γ↓X` design expresses: Γ↓Y is the
-- rest of the context, and nothing M needs is dropped.
prefix-mask : lockχ (0 ∷ [])
                (unmasked (bind `𝔹) ∷ applyᵇ (intro `ℕ) Δ)
  ≡ masked (bind `𝔹) ∷ unmasked (bind `ℕ) ∷ unmasked abst ∷ []
prefix-mask = refl

------------------------------------------------------------------------
-- 3.  THE EARLIER SHAPE — Y OUTSIDE b — AND WHY IT MOVED
------------------------------------------------------------------------

-- With Y outside b the stack is Δ, Y=𝔹, b, so M's own binder X′ is slot 0
-- and Y is slot 1.  The conceal then had to name slot 1 (naming 0 was a
-- BUG: it hid M's own binder and left Y visible, and the colour
-- annotations caught it — M's renamed set started 0 ∷ …, the frame's
-- 1 ∷ …).  Correct under lock/unlock:
outside-frame : lockχ (1 ∷ [])
                  (applyᵇ (renBnd suc (intro `ℕ)) (unmasked (bind `𝔹) ∷ Δ))
  ≡ unmasked (bind `ℕ) ∷ masked (bind `𝔹) ∷ unmasked abst ∷ []
outside-frame = refl

-- …but the hidden set {1} leaves slot 0 VISIBLE BELOW IT, so it is not a
-- prefix, and no `Γ↓·` denotes it.  That is what moved Y inside b.
--
-- The concrete run: V₀ = ΛX. ΛZ. λw:X. w, instantiate X at ℕ (TyBeta) and
-- then Z at 𝔹 (TyPos).  With Y outside, ⁻ʸ[Vᶜ] sits at Γ, Y=𝔹, X=ℕ and
-- Vᶜ names X — which Γ↓Y drops, X having been bound after Y.
outside-is-not-a-prefix : ¬ (scopeᵗ (lockχ (1 ∷ [])
                               (applyᵇ (renBnd suc (intro `ℕ))
                                       (unmasked (bind `𝔹) ∷ Δ)))
                             ≡ scopeᵗ (lockχ (0 ∷ 1 ∷ [])
                                 (applyᵇ (renBnd suc (intro `ℕ))
                                         (unmasked (bind `𝔹) ∷ Δ))))
outside-is-not-a-prefix ()

------------------------------------------------------------------------
-- 4.  THE REVEAL TAG — unaffected, since it binds nothing
------------------------------------------------------------------------

reveal-binds-nothing : numBindsᵇ (reveal (0 ∷ [])) ≡ 0
reveal-binds-nothing = refl

-- Δᵣ has one CONCEALED slot for the reveal tag to unlock.
Δᵣ : Ctxᵗ
Δᵣ = masked abst ∷ []

reveal-frame-exact :
  map suc (scopeᵗ (applyᵇ (reveal (0 ∷ [])) Δᵣ))
  ≡ scopeᵗ (lockχ (0 ∷ [])
              (unmasked (bind (shiftBy (numBindsᵇ (reveal (0 ∷ []))) `𝔹))
                 ∷ applyᵇ (reveal (0 ∷ [])) Δᵣ))
reveal-frame-exact = refl

------------------------------------------------------------------------
-- 5.  THE CONVERSION — the gap, and the fix
------------------------------------------------------------------------

-- V : ∀Z. Z→Z, so the ∀-body is B = ` 0 ⇒ ` 0; we instantiate at ℕ.
B A : Ty
B = ` 0 ⇒ ` 0
A = `ℕ

redex-type : B [ A ]ᵗ ≡ (`ℕ ⇒ `ℕ)
redex-type = refl

Δ₁ : Ctxᵗ
Δ₁ = unmasked (bind `ℕ) ∷ []

-- WHAT THE `•` NODE PRODUCES at a reveal tag: B with Z := Y.  In de Bruijn
-- the lift-then-substitute-slot-0 composite is the IDENTITY, so it is
-- literally B again — read where slot 0 is Y.
produced : (renameᵗ (extᵗ suc) B) [ ` 0 ]ᵗ ≡ B
produced = refl

-- WITHOUT A CONVERSION that is what the ⁺ʸ⁼ᴬ boundary would have to
-- accept, and ⊢intro demands ⇑ᵗ of the exterior type instead.
demanded : ⇑ᵗ (B [ A ]ᵗ) ≡ (`ℕ ⇒ `ℕ)
demanded = refl

without-conversion : ¬ (B ≡ (`ℕ ⇒ `ℕ))
without-conversion ()

-- THE FIX, INSTALLED: TyBeta's own conversion, with exactly the type the
-- gap needs — B[Z:=Y] ⇝ B[Z:=ℕ].
Y∋ℕ : Δ₁ ∋ 0 := `ℕ
Y∋ℕ = ez

the-conversion : revTy 0 B ≡ (seal 0 ↦ unseal 0)
the-conversion = refl

conversion-types : Δ₁ ⊢ revTy 0 B ∶ B ⇝ (B [ A ]ᵗ)
conversion-types = conv-fun (conv-seal Y∋ℕ) (conv-unseal Y∋ℕ)

-- NOTE THE CONTRAVARIANT FLIP: the DOMAIN gets a seal (conceal), the
-- CODOMAIN an unseal (reveal).  notes-v3 said +X(A → B) = +X(A) → +X(B)
-- and defined no -X(A) at all; corrected there on 2026-09-11.

------------------------------------------------------------------------
-- 6.  B'S SHIFTS ARE TAG-DEPENDENT
------------------------------------------------------------------------

-- M's type already carries `numBindsᵇ b` shifts (⊢intro hands its body ⇑ᵗ
-- of the exterior type; ⊢reveal hands it the type unchanged), and `renᴹ
-- suc` adds one more for Y.  At a reveal both wkN expressions collapse to
-- the untagged form, since wkN 1 X = suc X and wkN 0 X = X.
reveal-shift-collapses : ∀ {χ}
  → renameᵗ (extᵗ (wkN (suc (numBindsᵇ (reveal χ))))) B ≡ renameᵗ (extᵗ suc) B
reveal-shift-collapses = refl

reveal-conv-collapses : ∀ {χ}
  → revTy 0 (renameᵗ (extᵗ (wkN (numBindsᵇ (reveal χ)))) B) ≡ revTy 0 B
reveal-conv-collapses = refl

-- At an intro it is genuinely one more, and they differ.
intro-shift : renameᵗ (extᵗ (wkN (suc (numBindsᵇ (intro `ℕ))))) (` 0 ⇒ ` 1)
  ≡ (` 0 ⇒ ` 3)
intro-shift = refl

shifts-differ : ¬ (_≡_ {A = Ty} (` 0 ⇒ ` 3) (` 0 ⇒ ` 2))
shifts-differ ()

------------------------------------------------------------------------
-- 7.  TyConceal HAD THE SAME GAP — and there the placement is FORCED
------------------------------------------------------------------------

-- `⁻χ[ΛY.V] •B[A] -→ ⁺ʸ⁼ᴬ[⁻χ[V]]` is TyBeta with a conceal boundary
-- wedged in, and it dropped TyBeta's conversion on the way: V : B at
-- `abst ∷ lockχ χ Δ`, so `ν conceal (map suc χ) [ V ] : B` — which NAMES
-- the new binder — where ⊢intro demands ⇑ᵗ of the exterior type.  Same B
-- and A as §5, so the same numbers, and `revTy 0 B` closes it.
--
-- WHAT IS DIFFERENT HERE: the placement is not merely preferred, it is
-- FORCED.  Outside the conceal, the conceal's body keeps type B and needs
-- `map suc χ ∉FVs B` — EXACTLY the redex's own `χ ∉FVs (`∀ B)`:
∉FVs-∀ : ∀ {χ′ B′} → χ′ ∉FVs (`∀ B′) → map suc χ′ ∉FVs B′
∉FVs-∀ ∉[]               = ∉[]
∉FVs-∀ (∉∷ (∉-∀ x) rest) = ∉∷ x (∉FVs-∀ rest)

-- INSIDE the conceal, the body's type would be B[Y:=A] and ⊢conceal would
-- need `χ ∉FVs A`.  Nothing provides it: ⊢conceal's premise is `Δ ∋tvs χ`
-- — every slot of χ is NAMEABLE in Δ — and A is a type over Δ, so A may
-- name them.  Here is such an A: at Δ𝒜 = [Z], slot 0 of χ = {0} is
-- nameable, and A = ` 0 names it.
Δ𝒜 : Ctxᵗ
Δ𝒜 = unmasked abst ∷ []

χ-nameable : Δ𝒜 ∋tvs (0 ∷ [])
χ-nameable = tvs∷ (unmasked abst , ez , nameable) tvs[]

A-names-χ : (0 ∷ []) ∉FVs (` 0) → ⊥
A-names-χ (∉∷ (∉-var X≢X) _) = X≢X refl

-- AUDIT of every rule that mints an `intro`:
--   TyBeta     ✓ always had `revTy 0 B`
--   TyPos      ✓ installed 2026-09-11
--   TyConceal  ✓ installed 2026-09-11
--   PushIntro  ✓ none needed — it mints NO binder; the intro already
--              existed, and both sides type M at the same frame:
PushIntro-same-frame : ∀ {A′ χ′ Δ′}
  → lockχ (map suc χ′) (unmasked (bind A′) ∷ Δ′)
  ≡ unmasked (bind A′) ∷ lockχ χ′ Δ′
PushIntro-same-frame {χ′ = []}     = refl
PushIntro-same-frame {χ′ = X ∷ χ′} =
  cong (mask (suc X)) (PushIntro-same-frame {χ′ = χ′})
