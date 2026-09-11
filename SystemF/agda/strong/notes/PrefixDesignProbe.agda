module strong.notes.PrefixDesignProbe where

-- CAN THE OLD `Γ↓X` PREFIX DESIGN COME BACK?   (2026-09-11)
--
-- The prefix design types a conceal body at `Γ↓X` — the part of Γ strictly
-- DEEPER than X — so concealing X also drops everything bound AFTER it.
-- It is therefore expressible exactly when NO conceal body ever needs to
-- name a slot SHALLOWER than what its boundary conceals.
--
-- Example 8 (notes/old/notes-v1.md) killed it once, via TyWrapCncl pushing
-- a type argument into a sealed body.  No v3 rule does that any more, so
-- that route is closed.  This probe asks the question afresh, rule by
-- rule, of the CURRENT v3 rule set.
--
-- VERDICT: AppBnd is clean, and so are crossΛ and TyPos.  PushIntro and
-- TyConceal are not, and cannot be repaired the way TyPos was.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.Ctx
open import strong.CtxMorph
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction

Δ : Ctxᵗ
Δ = unmasked abst ∷ []

------------------------------------------------------------------------
-- 1.  AppBnd IS CLEAN — all three tags
------------------------------------------------------------------------

-- b = intro A.  The argument enters under `conceal {0}` SHIFTED by ⇑ᴹ, so
-- it names only slots ≥ 1 — nothing is shallower than the concealed slot,
-- because the concealed slot IS the shallowest.
intro-frame : lockχ (0 ∷ []) (applyᵇ (intro `ℕ) Δ)
  ≡ masked (bind `ℕ) ∷ unmasked abst ∷ []
intro-frame = refl

-- b = reveal χ.  THIS IS THE CASE I HAD FLAGGED AS SUSPECT, AND IT IS NOT.
-- The dual crossing lands the argument back at its OWN frame, exactly —
-- and `lock-unlock` is the reason.  So AppBnd hides nothing from W that Δ
-- did not already hide; it introduces no new shallower-naming at all.
Δ𝓁 : Ctxᵗ
Δ𝓁 = masked abst ∷ []

reveal-round-trip : lockχ (0 ∷ []) (unlockχ (0 ∷ []) Δ𝓁) ≡ Δ𝓁
reveal-round-trip = lock-unlock (lks∷ (masked abst , ez , locked) lks[])

-- b = conceal χ.  The dual is a REVEAL, so no conceal is created at all,
-- and `unlock-lock` again returns the argument to its own frame.
conceal-round-trip : unlockχ (0 ∷ []) (lockχ (0 ∷ []) Δ) ≡ Δ
conceal-round-trip = unlock-lock (tvs∷ (unmasked abst , ez , nameable) tvs[])

------------------------------------------------------------------------
-- 2.  crossΛ AND TyPos ARE CLEAN TOO
------------------------------------------------------------------------

-- crossΛ conceals slot 0 and shifts the body past it, so the body names
-- only deeper slots.  Same shape as AppBnd's intro case.
crossΛ-frame : lockχ (0 ∷ []) (unmasked abst ∷ Δ)
  ≡ masked abst ∷ unmasked abst ∷ []
crossΛ-frame = refl

-- TyPos, since Y moved INSIDE b, likewise conceals slot 0 with the body
-- shifted by plain `suc` (notes/TyPosExample.agda §1–§2).
typos-frame : lockχ (0 ∷ []) (unmasked (bind `𝔹) ∷ applyᵇ (intro `ℕ) Δ)
  ≡ masked (bind `𝔹) ∷ unmasked (bind `ℕ) ∷ unmasked abst ∷ []
typos-frame = refl

------------------------------------------------------------------------
-- 3.  PushIntro AND TyConceal ARE NOT — and this one is structural
------------------------------------------------------------------------

-- Both have the shape `⁺ʸ⁼ᴬ[ ⁻^(map suc χ)[ M ] ]`: an intro moves OUT
-- past a conceal, so inside, Y is slot 0 and UNMASKED while the concealed
-- slots are all ≥ 1.  The body sits under a conceal yet may name a slot
-- SHALLOWER than everything that conceal hides.
pushintro-frame : lockχ (map suc (0 ∷ [])) (applyᵇ (intro `ℕ) Δ)
  ≡ unmasked (bind `ℕ) ∷ masked abst ∷ []
pushintro-frame = refl

-- Slot 0 really is nameable there, so the body may use it:
Y-is-nameable : (unmasked (bind `ℕ) ∷ masked abst ∷ []) ∋tv 0
Y-is-nameable = unmasked (bind `ℕ) , ez , nameable

-- …and the concealed slot is DEEPER than it:
Z-is-concealed : (unmasked (bind `ℕ) ∷ masked abst ∷ []) ∋lk 1
Z-is-concealed = masked abst , es ez , locked

-- FOR TyConceal THE BODY NAMES IT BY CONSTRUCTION.  Its redex is
-- `⁻χ[ΛY.V] •B[A]`, so V is the Λ's own body — a term whose whole point is
-- to use Y.  Take V = λw:Y. w:
V : Term
V = ƛ (` 0) ∙ (` 0 ⟪ 0 ∷ [] ⟫) ⟪ 0 ∷ [] ⟫

-- and it is well typed exactly where the rule puts it, at the frame above,
-- naming slot 0 — the slot `Γ↓(concealed)` would drop.
⊢V : (unmasked (bind `ℕ) ∷ masked abst ∷ []) ∣ [] ⊢ V ⦂ (` 0 ⇒ ` 0)
⊢V = ⊢ƛ (wf-var Y-is-nameable) (⊢` here refl) refl

------------------------------------------------------------------------
-- 4.  WHY TyConceal CANNOT BE REORDERED THE WAY TyPos WAS
------------------------------------------------------------------------

-- TyPos was repaired by moving its fresh binder INSIDE the tag.  The same
-- move on TyConceal would give `⁻χ[⁺ʸ⁼ᴬ[…]]`, whose conceal body then has
-- type B[Y:=A] — so ⊢conceal would need `χ ∉FVs A`.  Nothing provides it:
-- ⊢conceal's premise is `Δ ∋tvs χ` (every slot of χ is NAMEABLE in Δ) and
-- A is a type over Δ, so A may name them.  See notes/TyPosExample.agda §7
-- (`χ-nameable`, `A-names-χ`).
--
-- CONCLUSION.  The prefix design is not blocked by AppBnd, and no longer
-- by Example 8's mechanism.  It is blocked by the CONCEAL-COMMUTES-PAST-
-- AN-INTRO family — PushIntro and TyConceal — where the intro necessarily
-- ends up visible beneath a conceal.  That shape is what `Γ↓X` cannot
-- denote, and it is forced by those rules rather than incidental to them.
