module strong.proof.Adversary where

-- THE SOUNDNESS GATE, and the adversaries of the previous design, refuted.
--
-- A CONCEAL MUST CITE A LIVE OWNER.  That is the whole gate, and it is a
-- one-line inversion: `conv-seal` has no other premise.  Under the previous
-- design the same fact needed bwf↓ + Reversal≈, or bwf↓x + starOnly +
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

seal-cites-owner : ∀ {Δ X A B p c}
  → Δ ⊢ c ∶ A ⇝ B ∙ p → c ≡ seal X → Δ ∋ X := A
seal-cites-owner (conv-seal d) refl = d

-- `ali` claims nothing: it is a NAME with no rep, so it cannot assert
-- knowledge.  The boundary skeleton carries no type at an alias, and Bwf's
-- alias premise is `Δ ∋e X , E` — pure existence.
ali-claims-nothing : ∀ {Δ X E Θ} → Δ ∋e X , E → Bwf Δ Θ → Bwf Δ (ali X ∷ Θ)
ali-claims-nothing = bw-a

------------------------------------------------------------------------
-- 2.  THE ADVERSARY (the old ⊢3n-adv): a conceal asserting false knowledge
------------------------------------------------------------------------

-- At a type context where slot 0 is ABSTRACT (Λ-bound — no owner) the adversary
-- exported `7 : ℕ` at the abstract type.  Here the boundary is unmintable,
-- because `seal 0` demands `Δ ∋ 0 := `ℕ` and an `abst` slot has no rep to
-- cite.  Unmasking cannot manufacture one either (`ali-claims-nothing`).

Δadv : Ctxᵗ
Δadv = abst ∷ []

¬know-adv : ∀ {A} → Δadv ∋ 0 := A → ⊥
¬know-adv ()

¬seal-adv : ∀ {A B p} → Δadv ⊢ seal 0 ∶ A ⇝ B ∙ p → ⊥
¬seal-adv (conv-seal d) = ¬know-adv d

¬⊢adv : ∀ {Γ} → Δadv ∣ Γ ⊢ ($ 7) ⟪ cnc 0 ∷ [] , seal 0 ⟫ ⦂ ` 0 → ⊥
¬⊢adv (env bw ⊢M ⊢c wE) = ¬seal-adv ⊢c

------------------------------------------------------------------------
-- 3.  `bad`: two spellings of one fact — inexpressible
------------------------------------------------------------------------

-- An inner conceal at rep ℕ under an owner whose rep is ∀Z.Z→Z.  The two
-- spellings cannot disagree, because there is only ONE: `seal 0` reads the
-- owner, so the interior face IS the owner's rep.

∀ZZ : Ty
∀ZZ = `∀ (` 0 ⇒ ` 0)

Δbad : Ctxᵗ
Δbad = own ∀ZZ ∷ []

seal-bad-face : ∀ {A B p} → Δbad ⊢ seal 0 ∶ A ⇝ B ∙ p → A ≡ ⇑ᵗ ∀ZZ
seal-bad-face (conv-seal ez) = refl

¬⊢bad : ∀ {Γ} → Δbad ∣ Γ ⊢ ($ 7) ⟪ cnc 0 ∷ [] , seal 0 ⟫ ⦂ ` 0 → ⊥
¬⊢bad (env bw ⊢$ ⊢c wE) with seal-bad-face ⊢c
... | ()

------------------------------------------------------------------------
-- 4.  CANCEL'S FACE EQUATION, DEFINITIONAL
------------------------------------------------------------------------

-- At a cancel the inner conceal's interior face and the outer reveal's
-- exterior face are the SAME lookup on the SAME type context, hence literally
-- equal.  This one lemma replaces cancel-agree + Reversal≈ + SkelEq +
-- xrep-stored + MergeOK's two face equations.
cancel-faces-agree : ∀ {Δ X A B A′ B′ p q}
  → Δ ⊢ seal X ∶ A ⇝ B ∙ p       -- the inner conceal
  → Δ ⊢ unseal X ∶ A′ ⇝ B′ ∙ q   -- the owner it names
    ---------------------------
  → A ≡ B′
cancel-faces-agree cs cu =
  ∋:=-det (seal-face-is-the-owners-rep cs)
          (unseal-face-is-the-owners-rep cu)
