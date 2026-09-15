module strong.proof.Preservation where

-- Strong System F v8 — type preservation.
--
-- The step relation is indexed by the context it reduces in, and the
-- only rule that changes that context is `ξ-⟨⟩`, which walks into a
-- boundary's INTERIOR.  So the theorem carries the three facts the
-- per-rule lemmas need about that context, and each is preserved by
-- the walk:
--
--   `StoreOk`  the store is well formed — `Beta`'s substitution needs
--              stored representations to be base-closed, and `Alloc`
--              extends the store;
--   `Flat`     no binder assignment, empty base (proof.Flat): true of
--              every reduction context, and what lets `Alloc` store
--              its representation;
--   `NameFn`   names are unique, which makes the read-back
--              single-valued (`Merge`, `Wrap`, `TyWrap`).
--
-- The term context is `[]` throughout: no ξ-rule descends under a
-- binder, `Λ` bodies being values and `λ` bodies never reduced.
--
-- A step only ever EXTENDS the store (`step-⊑`), which is what lets a
-- ξ-rule retype the sibling it did not reduce.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion
open import strong.ConversionReduction
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction

open import strong.proof.Flat using (Flat; conv-flat)
open import strong.proof.Interior using (conv-interior)
open import strong.proof.CompositionTyping using (conv-namefn)
open import strong.proof.PreserveMerge using (preserve-Merge)
open import strong.proof.PreserveConst using (preserve-Const)
open import strong.proof.PreserveWrap using (preserve-Wrap)
open import strong.proof.StoreWeaken using (⊢-snoc; conv-snoc)
open import strong.proof.TermSubstitution using (module Proof)
open Proof using (preserve-Beta)
open import strong.proof.PreserveTyDef

------------------------------------------------------------------------
-- A step only extends the store
------------------------------------------------------------------------

infix 4 _⊑ˢ_
data _⊑ˢ_ : Store → Store → Set where
  ⊑-refl : ∀ {Sg} → Sg ⊑ˢ Sg
  ⊑-snoc : ∀ {Sg Sg′ R} → Sg ⊑ˢ Sg′ → Sg ⊑ˢ (Sg′ ∷ʳ R)

⊢-mono : ∀ {Sg Sg′ Δ Γ M A} → Sg ⊑ˢ Sg′
  → Sg ∣ Δ ∣ Γ ⊢ M ⦂ A → Sg′ ∣ Δ ∣ Γ ⊢ M ⦂ A
⊢-mono ⊑-refl ⊢M = ⊢M
⊢-mono (⊑-snoc le) ⊢M = ⊢-snoc (⊢-mono le ⊢M)

conv-mono : ∀ {Sg Sg′ Δᵢ Δ c A B} → Sg ⊑ˢ Sg′
  → Sg ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ → Sg′ ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ
conv-mono ⊑-refl ⊢c = ⊢c
conv-mono (⊑-snoc le) ⊢c = conv-snoc (conv-mono le ⊢c)

step-⊑ : ∀ {Sg Sg′ Δ M M′} → Sg ∣ Δ ⊢ M —→ M′ ⊣ Sg′ → Sg ⊑ˢ Sg′
step-⊑ (Beta v) = ⊑-refl
step-⊑ PrimBeta = ⊑-refl
step-⊑ (TyBeta v q) = ⊑-refl
step-⊑ Alloc = ⊑-snoc ⊑-refl
step-⊑ (Wrap v w eq) = ⊑-refl
step-⊑ (TyWrap v eq q) = ⊑-refl
step-⊑ (Merge v) = ⊑-refl
step-⊑ (Const lit eq) = ⊑-refl
step-⊑ (ξ-⊕-l st) = step-⊑ st
step-⊑ (ξ-⊕-r v st) = step-⊑ st
step-⊑ (ξ-·-l st) = step-⊑ st
step-⊑ (ξ-·-r v st) = step-⊑ st
step-⊑ (ξ-•[] st) = step-⊑ st
step-⊑ (ξ-⟨⟩ ieq st) = step-⊑ st

------------------------------------------------------------------------
-- Preservation
------------------------------------------------------------------------

module Main (tyBeta : TyBetaOk) (tyWrap : TyWrapOk) (alloc : AllocOk)
  where

  preserve : ∀ {Sg Sg′ Δ M M′ A}
    → StoreOk Sg → Flat Δ → NameFn Δ
    → Sg ∣ Δ ∣ [] ⊢ M ⦂ A
    → Sg ∣ Δ ⊢ M —→ M′ ⊣ Sg′
    → StoreOk Sg′ × (Sg′ ∣ Δ ∣ [] ⊢ M′ ⦂ A)

  -- the redexes
  preserve sok fl nf ⊢M (Beta v) = sok , preserve-Beta sok ⊢M
  preserve sok fl nf (⊢⊕ m n) PrimBeta = sok , ⊢$
  preserve sok fl nf ⊢M (TyBeta v q) = sok , tyBeta sok fl nf q ⊢M
  preserve sok fl nf ⊢M Alloc = alloc sok fl ⊢M
  preserve sok fl nf ⊢M (Wrap v w eq) = sok , preserve-Wrap nf eq ⊢M
  preserve sok fl nf ⊢M (TyWrap v eq q) = sok , tyWrap sok fl nf eq q ⊢M
  preserve sok fl nf ⊢M (Merge v) = sok , preserve-Merge nf ⊢M
  preserve sok fl nf ⊢M (Const lit eq) = sok , preserve-Const lit eq ⊢M

  -- the congruences: the sibling is retyped over the extended store
  preserve sok fl nf (⊢⊕ l m) (ξ-⊕-l st) with preserve sok fl nf l st
  preserve sok fl nf (⊢⊕ l m) (ξ-⊕-l st) | sok′ , l′ =
    sok′ , ⊢⊕ l′ (⊢-mono (step-⊑ st) m)
  preserve sok fl nf (⊢⊕ l m) (ξ-⊕-r v st) with preserve sok fl nf m st
  preserve sok fl nf (⊢⊕ l m) (ξ-⊕-r v st) | sok′ , m′ =
    sok′ , ⊢⊕ (⊢-mono (step-⊑ st) l) m′
  preserve sok fl nf (⊢· l m) (ξ-·-l st) with preserve sok fl nf l st
  preserve sok fl nf (⊢· l m) (ξ-·-l st) | sok′ , l′ =
    sok′ , ⊢· l′ (⊢-mono (step-⊑ st) m)
  preserve sok fl nf (⊢· l m) (ξ-·-r v st) with preserve sok fl nf m st
  preserve sok fl nf (⊢· l m) (ξ-·-r v st) | sok′ , m′ =
    sok′ , ⊢· (⊢-mono (step-⊑ st) l) m′
  preserve sok fl nf (⊢•[] l wf) (ξ-•[] st) with preserve sok fl nf l st
  preserve sok fl nf (⊢•[] l wf) (ξ-•[] st) | sok′ , l′ =
    sok′ , ⊢•[] l′ wf

  -- the boundary: the conversion's typing names the interior, and the
  -- given equation pins it to the one the step walked into
  preserve sok fl nf (⊢⟨⟩ nfc ⊢M conv) (ξ-⟨⟩ ieq st)
    with trans (sym (conv-interior conv)) ieq
  preserve sok fl nf (⊢⟨⟩ nfc ⊢M conv) (ξ-⟨⟩ ieq st) | refl
    with preserve sok (conv-flat conv fl) (conv-namefn conv nf) ⊢M st
  preserve sok fl nf (⊢⟨⟩ nfc ⊢M conv) (ξ-⟨⟩ ieq st) | refl | sok′ , ⊢M′ =
    sok′ , ⊢⟨⟩ nfc ⊢M′ (conv-mono (step-⊑ st) conv)

  -- and along a whole reduction sequence
  preserve-many : ∀ {Sg Sg′ Δ M M′ A}
    → StoreOk Sg → Flat Δ → NameFn Δ
    → Sg ∣ Δ ∣ [] ⊢ M ⦂ A
    → Sg ∣ Δ ⊢ M —↠ M′ ⊣ Sg′
    → StoreOk Sg′ × (Sg′ ∣ Δ ∣ [] ⊢ M′ ⦂ A)
  preserve-many sok fl nf ⊢M done = sok , ⊢M
  preserve-many sok fl nf ⊢M (st then rest) with preserve sok fl nf ⊢M st
  preserve-many sok fl nf ⊢M (st then rest) | sok′ , ⊢M′ =
    preserve-many sok′ fl nf ⊢M′ rest
