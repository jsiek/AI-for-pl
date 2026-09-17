module strong.notes.TyConcealExample where

-- TyConceal, ON A COMPLETE RUN  (2026-09-11).
--
--     (λg:(∀Y.Y→Y). ΛZ. g •(Y→Y)[Z]) · (ΛY. λw:Y. w)
--
-- Beta substitutes the polymorphic identity for g ACROSS the ΛZ, so crossΛ
-- wraps it in a conceal of Z; the next step is then a TyConceal, because
-- the operator is a conceal boundary around a Λ and it is instantiated AT
-- THE CONCEALED VARIABLE Z itself.
--
-- This is the shape that the old `Γ↓X` prefix design cannot express.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_,_)
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
-- 1.  THE RUN
------------------------------------------------------------------------

Δ₀ : Ctxᵗ                       -- outside
Δ₀ = []

Δ₁ : Ctxᵗ                       -- under the ΛZ: Z in scope
Δ₁ = unmasked abst ∷ []

-- ΛY. λw:Y. w                  : ∀Y. Y→Y
polyId : Term
polyId = Λ (ƛ (` 0) ∙ (` 0 ⟪ 0 ∷ [] ⟫) ⟪ 0 ∷ [] ⟫) ⟪ [] ⟫

-- ΛZ. g •(Y→Y)[Z]   —  g is term variable 0; it is INSTANTIATED AT Z.
bodyΛ : Term
bodyΛ = Λ ((` 0 ⟪ 0 ∷ [] ⟫) • (` 0 ⇒ ` 0) [ ` 0 ]⟪ 0 ∷ [] ⟫) ⟪ [] ⟫

prog : Term
prog = (ƛ (`∀ (` 0 ⇒ ` 0)) ∙ bodyΛ ⟪ [] ⟫) · polyId ⟪ [] ⟫

-- STEP 1 — Beta.  The image crosses the ΛZ, so crossΛ conceals Z from it.
after₁ : Term
after₁ = Λ ((ν conceal (0 ∷ []) [ polyId ])
              • (` 0 ⇒ ` 0) [ ` 0 ]⟪ 0 ∷ [] ⟫) ⟪ [] ⟫

step₁ : Δ₀ ⊢ prog -→ after₁
step₁ = Beta (simple→value (SΛ (simple→value Sƛ)))

-- STEP 2 — TyConceal.  A conceal boundary around a Λ, instantiated at Z.
-- A FRESH Y IS MINTED WITH THE CONCEALED Z AS ITS REPRESENTATION.
V : Term                        -- λw:Y. w, the Λ's own body
V = ƛ (` 0) ∙ (` 0 ⟪ 0 ∷ [] ⟫) ⟪ 0 ∷ [] ⟫

after₂ : Term
after₂ = Λ (ν intro (` 0)
              [ (ν conceal (1 ∷ []) [ V ]) ⟨ revTy 0 (` 0 ⇒ ` 0) ⟩ ]) ⟪ [] ⟫

step₂ : Δ₀ ⊢ after₁ -→ after₂
step₂ = ξ-Λ (TyConceal ne (simple→value Sƛ))

run : Δ₀ ⊢ prog -→* after₂
run = step₁ then step₂ then done

------------------------------------------------------------------------
-- 2.  THE FRAME AT THE CONCEAL
------------------------------------------------------------------------

-- Reading outward-in: Δ₁ = Z, then the intro adds Y=Z, then the conceal
-- hides Z.  So Y is slot 0 and VISIBLE; Z is slot 1 and MASKED.
frame : lockχ (1 ∷ []) (applyᵇ (intro (` 0)) Δ₁)
  ≡ unmasked (bind (` 0)) ∷ masked abst ∷ []
frame = refl

-- (lookup returns the entry SHIFTED into the ambient context, so Y's
-- stored rep ` 0 reads as ` 1 — which is Z)
Y-visible : (unmasked (bind (` 0)) ∷ masked abst ∷ []) ∋tv 0
Y-visible = unmasked (bind (` 1)) , ez , nameable

Z-hidden : (unmasked (bind (` 0)) ∷ masked abst ∷ []) ∋lk 1
Z-hidden = masked abst , es ez , locked

-- THE BODY NAMES Y — it is the Λ's own body, so of course it does.
⊢V : (unmasked (bind (` 0)) ∷ masked abst ∷ []) ∣ [] ⊢ V ⦂ (` 0 ⇒ ` 0)
⊢V = ⊢ƛ (wf-var Y-visible) (⊢` here refl) refl

-- AND Y'S REPRESENTATION IS THE HIDDEN Z.  That is the whole point: the
-- body may NAME Y but cannot UNFOLD it, because unfolding needs Z.
Y-rep-is-Z : (unmasked (bind (` 0)) ∷ masked abst ∷ []) ∋ 0 := (` 1)
Y-rep-is-Z = ez

------------------------------------------------------------------------
-- 3.  WHY Γ↓X CANNOT DENOTE THIS FRAME
------------------------------------------------------------------------

-- Under lock/unlock the frame above is fine: hide slot 1, keep slot 0.
--
-- `Γ↓X` can only drop a SUFFIX — X and everything bound AFTER it.  Here
-- the hidden variable Z is bound BEFORE the visible one Y, so dropping Z
-- drops Y as well, and ⊢V fails.  And the order is forced: Y is minted BY
-- THIS STEP, so it is necessarily newer than Z, and it exists precisely to
-- stand for Z — it must be visible exactly where Z is not.
--
-- Machine-readably: the colour set keeps slot 0 while dropping slot 1,
-- which no prefix truncation of [Y=Z, Z] produces.
colours : scopeᵗ (lockχ (1 ∷ []) (applyᵇ (intro (` 0)) Δ₁)) ≡ 0 ∷ []
colours = refl

prefix-would-drop-both : scopeᵗ (lockχ (0 ∷ 1 ∷ []) (applyᵇ (intro (` 0)) Δ₁)) ≡ []
prefix-would-drop-both = refl

not-a-prefix : ¬ ((0 ∷ []) ≡ ([] {A = ℕ}))
not-a-prefix ()

------------------------------------------------------------------------
-- 4.  WHY THE TyPos REPAIR DOES NOT TRANSFER
------------------------------------------------------------------------

-- TyPos was repaired by minting its fresh binder INSIDE the tag, which
-- made the binder the newest slot and its conceal a prefix.  The same move
-- here gives `⁻χ[⁺ʸ⁼ᶻ[…]]` — the intro minted where Z is ALREADY
-- concealed.  But ⊢intro requires the new binder's REPRESENTATION to be
-- well formed, and that representation is Z itself:
Z-not-wf-inside : ¬ (lockχ (0 ∷ []) Δ₁ ⊢ᵗ (` 0))
Z-not-wf-inside (wf-var (_ , ez , ()))

-- So the reordering is not merely awkward here, it is unstateable: the
-- alias must be minted WHERE ITS REPRESENTATION IS STILL VISIBLE, i.e.
-- outside the conceal — and that is exactly what puts a newer visible slot
-- above an older hidden one.
