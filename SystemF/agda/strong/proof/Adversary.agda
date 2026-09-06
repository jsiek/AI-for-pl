module strong.proof.Adversary where

-- THE SOUNDNESS GATE, and the adversaries of the previous design, refuted.
--
-- A CONCEAL MUST CITE A LIVE BINDER.  That is the whole gate, and it is a
-- one-line inversion: `conv-seal` has no other premise.  Under the previous
-- design the same fact needed mwf↓ + Reversal≈, or mwf↓x + starOnly +
-- SkelEq, and the adversary passed ≡, ≈Δ̄ and SkelEq (only `starOnly`
-- refused it).

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms

------------------------------------------------------------------------
-- 1.  The gate
------------------------------------------------------------------------

seal-cites-binder : ∀ {Δ X A B c}
  → Δ ⊢ c ∶ A ⇝ B → c ≡ seal X → Δ ∋ X := A
seal-cites-binder (conv-seal d) refl = d

-- `unlock` claims NO KNOWLEDGE: it is a NAME with no rep, so it cannot
-- assert what a slot stands for.  What it now does claim is that the
-- slot is LOCKED (`scope Θ Δ ∋lk X`) — a statement about MASKING, in
-- which no type occurs, and which is what makes the dual's restoring
-- `lock` sound (proof/DualTightness).  A VACUOUS unlock, at a slot the
-- frame leaves nameable, is REFUSED.
unlock-claims-a-lock : ∀ {Δ X Θ} → scope Θ Δ ∋lk X → Δ ⊢ᵐ Θ
  → Δ ⊢ᵐ (unlock X ∷ Θ)
unlock-claims-a-lock = mw-u

-- The claim mentions no representation: all it hands back is a
-- NAMEABLE entry under one mask, and `Nameable` is `abst` or `bind`
-- without reading the bind's type.
unlock-mentions-no-rep : ∀ {Δ X} → Δ ∋lk X → ∃[ E ] Nameable E
unlock-mentions-no-rep (masked E , _ , locked v) = E , v

------------------------------------------------------------------------
-- 2.  THE ADVERSARY (the old ⊢3n-adv): a conceal asserting false knowledge
------------------------------------------------------------------------

-- At a type context where slot 0 is ABSTRACT (Λ-bound — no binder) the
-- adversary exported `7 : ℕ` at the abstract type.  Here the boundary is
-- unmintable, because `seal 0` demands `Δ ∋ 0 := `ℕ` and an `abst` slot
-- has no rep to cite.  Unmasking cannot manufacture one either
-- (`unlock-claims-a-lock`).

Δadv : Ctxᵗ
Δadv = abst ∷ []

¬know-adv : ∀ {A} → Δadv ∋ 0 := A → ⊥
¬know-adv ()

¬seal-adv : ∀ {A B} → Δadv ⊢ seal 0 ∶ A ⇝ B → ⊥
¬seal-adv (conv-seal d) = ¬know-adv d

¬⊢adv : ∀ {Γ} → Δadv ∣ Γ ⊢ ($ 7) ⟪ lock 0 ∷ [] , seal 0 ⟫ ⦂ ` 0 → ⊥
¬⊢adv (env mw ⊢M ⊢c wE) = ¬seal-adv ⊢c

------------------------------------------------------------------------
-- 3.  `bad`: two spellings of one fact — inexpressible
------------------------------------------------------------------------

-- An inner conceal at rep ℕ under a binder whose rep is ∀Z.Z→Z.  The two
-- spellings cannot disagree, because there is only ONE: `seal 0` reads the
-- binder, so the source type IS the binder's rep.

∀ZZ : Ty
∀ZZ = `∀ (` 0 ⇒ ` 0)

Δbad : Ctxᵗ
Δbad = bind ∀ZZ ∷ []

seal-bad-conv : ∀ {A B} → Δbad ⊢ seal 0 ∶ A ⇝ B → A ≡ ⇑ᵗ ∀ZZ
seal-bad-conv (conv-seal ez) = refl

¬⊢bad : ∀ {Γ} → Δbad ∣ Γ ⊢ ($ 7) ⟪ lock 0 ∷ [] , seal 0 ⟫ ⦂ ` 0 → ⊥
¬⊢bad (env mw ⊢$ ⊢c wE) with seal-bad-conv ⊢c
... | ()

------------------------------------------------------------------------
-- 4.  CANCEL'S TYPE EQUATION, DEFINITIONAL
------------------------------------------------------------------------

-- At a cancel the inner conceal's SOURCE type and the outer reveal's
-- TARGET type are the SAME lookup on the SAME type context, hence
-- literally equal.  This one lemma replaces cancel-agree + Reversal≈ +
-- SkelEq + xrep-stored + MergeOK's two type equations.
cancel-types-agree : ∀ {Δ X A B A′ B′}
  → Δ ⊢ seal X ∶ A ⇝ B       -- the inner conceal
  → Δ ⊢ unseal X ∶ A′ ⇝ B′   -- the binder it names
    ---------------------------
  → A ≡ B′
cancel-types-agree cs cu =
  ∋:=-det (seal-source-is-rep cs)
          (unseal-target-is-rep cu)
