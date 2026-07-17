module ImprecisionWf where

-- File Charter:
--   * Context-indexed variant of GTSF type imprecision.
--   * Reuses the assumptions from `Imprecision`, but indexes
--     derivations by separate source and target type contexts so each
--     derivation determines well-formed endpoints.
--   * Exposes endpoint well-formedness theorems for the indexed judgment
--     `Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ`.
--   * Re-exports the crossed two-allocation context from `Imprecision`.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_<_; zero; suc)
open import Data.Product using (_×_; _,_)

open import Types
open import Imprecision public using
  ( ImpAssm
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ImpCtx
  ; ⇑ᵢₐ
  ; ⇑ᴸᵢₐ
  ; ⇑ᴿᵢₐ
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; ⇑ᴿᵢ
  ; swapRight∀∀ᵢ
  )

------------------------------------------------------------------------
-- Type imprecision with well-formed endpoints
------------------------------------------------------------------------

infix 4 _∣_⊢_⊑_⊣_
data _∣_⊢_⊑_⊣_ (Φ : ImpCtx) (Δᴸ : TyCtx) :
  Ty → Ty → TyCtx → Set where
  id★ : ∀ {Δᴿ}
    -----------------------------
    → Φ ∣ Δᴸ ⊢ ★ ⊑ ★ ⊣ Δᴿ

  idˣ : ∀ {X Y Δᴿ}
    → (X ˣ⊑ˣ Y) ∈ Φ
    → X < Δᴸ
    → Y < Δᴿ
    -----------------------------
    → Φ ∣ Δᴸ ⊢ ＇ X ⊑ ＇ Y ⊣ Δᴿ

  idι : ∀ {ι Δᴿ}
    -----------------------------
    → Φ ∣ Δᴸ ⊢ ‵ ι ⊑ ‵ ι ⊣ Δᴿ

  _↦_ : ∀ {A A′ B B′ Δᴿ}
    → Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ
    → Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ
    -------------------------------------
    → Φ ∣ Δᴸ ⊢ (A ⇒ B) ⊑ (A′ ⇒ B′) ⊣ Δᴿ

  ∀ⁱ_ : ∀ {A B Δᴿ}
    → ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ
    ------------------------------------------------
    → Φ ∣ Δᴸ ⊢ (`∀ A) ⊑ (`∀ B) ⊣ Δᴿ

  tag_ : ∀ {Δᴿ} (ι : Base)
    -----------------------------
    → Φ ∣ Δᴸ ⊢ ‵ ι ⊑ ★ ⊣ Δᴿ

  tag_⇛_ : ∀ {A₁ A₂ Δᴿ}
    → Φ ∣ Δᴸ ⊢ A₁ ⊑ ★ ⊣ Δᴿ
    → Φ ∣ Δᴸ ⊢ A₂ ⊑ ★ ⊣ Δᴿ
    --------------------------------
    → Φ ∣ Δᴸ ⊢ A₁ ⇒ A₂ ⊑ ★ ⊣ Δᴿ

  tagˣ : ∀ {X Δᴿ}
    → X ˣ⊑★ ∈ Φ
    → X < Δᴸ
    -----------------------------
    → Φ ∣ Δᴸ ⊢ ＇ X ⊑ ★ ⊣ Δᴿ

  ν : ∀ {A B Δᴿ}
    → occurs zero A ≡ true
    → (((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ)
    ------------------------------------------------
    → Φ ∣ Δᴸ ⊢ (`∀ A) ⊑ B ⊣ Δᴿ

------------------------------------------------------------------------
-- Endpoint well-formedness
------------------------------------------------------------------------

mutual
  ⊑-src-wf :
    ∀ {Δᴸ Δᴿ Φ A B} →
    Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
    WfTy Δᴸ A

  ⊑-tgt-wf :
    ∀ {Δᴸ Δᴿ Φ A B} →
    Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
    WfTy Δᴿ B

  ⊑-src-wf id★ = wf★
  ⊑-src-wf (idˣ _ X<Δᴸ _) = wfVar X<Δᴸ
  ⊑-src-wf idι = wfBase
  ⊑-src-wf (p ↦ q) = wf⇒ (⊑-src-wf p) (⊑-src-wf q)
  ⊑-src-wf (∀ⁱ p) = wf∀ (⊑-src-wf p)
  ⊑-src-wf (tag ι) = wfBase
  ⊑-src-wf (tag_⇛_ p q) = wf⇒ (⊑-src-wf p) (⊑-src-wf q)
  ⊑-src-wf (tagˣ _ X<Δᴸ) = wfVar X<Δᴸ
  ⊑-src-wf (ν occA p) = wf∀ (⊑-src-wf p)

  ⊑-tgt-wf id★ = wf★
  ⊑-tgt-wf (idˣ _ _ Y<Δᴿ) = wfVar Y<Δᴿ
  ⊑-tgt-wf idι = wfBase
  ⊑-tgt-wf (p ↦ q) = wf⇒ (⊑-tgt-wf p) (⊑-tgt-wf q)
  ⊑-tgt-wf (∀ⁱ p) = wf∀ (⊑-tgt-wf p)
  ⊑-tgt-wf (tag ι) = wf★
  ⊑-tgt-wf (tag_⇛_ p q) = wf★
  ⊑-tgt-wf (tagˣ _ _) = wf★
  ⊑-tgt-wf (ν occA p) = ⊑-tgt-wf p

⊑-wf :
  ∀ {Δᴸ Δᴿ Φ A B} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  WfTy Δᴸ A × WfTy Δᴿ B
⊑-wf p = ⊑-src-wf p , ⊑-tgt-wf p
