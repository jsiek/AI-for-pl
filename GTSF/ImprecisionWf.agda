module ImprecisionWf where

-- File Charter:
--   * Context-indexed variant of GTSF type imprecision.
--   * Reuses the assumptions from `Imprecision`, but indexes
--     derivations by separate source and target type contexts so each
--     derivation determines well-formed endpoints.
--   * Exposes erasure back to raw imprecision and endpoint well-formedness
--     theorems for the indexed judgment.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_<_; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)

open import Types
import Imprecision as Raw
open import Imprecision public using
  ( ImpAssm
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ImpCtx
  ; ⇑ᵢₐ
  ; ⇑ᴸᵢₐ
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; idᵢ
  )
open import proof.ImprecisionProperties using
  (WfImpCtx²; ∀ᵢ-wf²; νᵢ-wf²)
open import proof.TypeProperties using (WfTy-un⇑ᵗ)

------------------------------------------------------------------------
-- Type imprecision with well-formed endpoints
------------------------------------------------------------------------

infix 4 _∣_∣_⊢_⊑_
data _∣_∣_⊢_⊑_ (Δᴸ Δᴿ : TyCtx) (Φ : ImpCtx) :
  Ty → Ty → Set where
  id★ :
    -----------------------------
    Δᴸ ∣ Δᴿ ∣ Φ ⊢ ★ ⊑ ★

  idˣ : ∀ {X Y}
    → (X ˣ⊑ˣ Y) ∈ Φ
    → X < Δᴸ
    → Y < Δᴿ
    -----------------------------
    → Δᴸ ∣ Δᴿ ∣ Φ ⊢ ＇ X ⊑ ＇ Y

  idι : ∀ {ι}
    -----------------------------
    → Δᴸ ∣ Δᴿ ∣ Φ ⊢ ‵ ι ⊑ ‵ ι

  _↦_ : ∀ {A A′ B B′}
    → Δᴸ ∣ Δᴿ ∣ Φ ⊢ A ⊑ A′
    → Δᴸ ∣ Δᴿ ∣ Φ ⊢ B ⊑ B′
    -------------------------------------
    → Δᴸ ∣ Δᴿ ∣ Φ ⊢ (A ⇒ B) ⊑ (A′ ⇒ B′)

  ∀ⁱ_ : ∀ {A B}
    → suc Δᴸ ∣ suc Δᴿ ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ ⊢ A ⊑ B
    ------------------------------------------------
    → Δᴸ ∣ Δᴿ ∣ Φ ⊢ (`∀ A) ⊑ (`∀ B)

  tag_ : ∀ (ι : Base)
    -----------------------------
    → Δᴸ ∣ Δᴿ ∣ Φ ⊢ ‵ ι ⊑ ★

  tag_⇒_ : ∀ {A₁ A₂}
    → Δᴸ ∣ Δᴿ ∣ Φ ⊢ A₁ ⊑ ★
    → Δᴸ ∣ Δᴿ ∣ Φ ⊢ A₂ ⊑ ★
    --------------------------------
    → Δᴸ ∣ Δᴿ ∣ Φ ⊢ A₁ ⇒ A₂ ⊑ ★

  tagˣ : ∀ {X}
    → X ˣ⊑★ ∈ Φ
    → X < Δᴸ
    -----------------------------
    → Δᴸ ∣ Δᴿ ∣ Φ ⊢ ＇ X ⊑ ★

  ν : ∀ {A B}
    → occurs zero A ≡ true
    → (suc Δᴸ ∣ suc Δᴿ ∣ (0 ˣ⊑★) ∷ ⇑ᵢ Φ
        ⊢ A ⊑ ⇑ᵗ B)
    ------------------------------------------------
    → Δᴸ ∣ Δᴿ ∣ Φ ⊢ (`∀ A) ⊑ B

------------------------------------------------------------------------
-- Erasure to raw imprecision
------------------------------------------------------------------------

erase⊑ :
  ∀ {Δᴸ Δᴿ Φ A B} →
  Δᴸ ∣ Δᴿ ∣ Φ ⊢ A ⊑ B →
  Raw._⊢_⊑_ Φ A B
erase⊑ id★ = Raw.id★
erase⊑ (idˣ X⊑Y∈ _ _) = Raw.idˣ X⊑Y∈
erase⊑ idι = Raw.idι
erase⊑ (p ↦ q) = Raw._↦_ (erase⊑ p) (erase⊑ q)
erase⊑ (∀ⁱ p) = Raw.∀ⁱ (erase⊑ p)
erase⊑ (tag ι) = Raw.tag ι
erase⊑ (tag_⇒_ p q) = Raw.tag_⇒_ (erase⊑ p) (erase⊑ q)
erase⊑ (tagˣ X⊑★∈ _) = Raw.tagˣ X⊑★∈
erase⊑ (ν occA p) = Raw.ν occA (erase⊑ p)

raw→wf :
  ∀ {Δᴸ Δᴿ Φ A B} →
  WfImpCtx² Δᴸ Δᴿ Φ →
  Raw._⊢_⊑_ Φ A B →
  Δᴸ ∣ Δᴿ ∣ Φ ⊢ A ⊑ B
raw→wf hΦ Raw.id★ = id★
raw→wf hΦ (Raw.idˣ X⊑Y∈) =
  idˣ X⊑Y∈ (proj₁ (hΦ X⊑Y∈)) (proj₂ (hΦ X⊑Y∈))
raw→wf hΦ Raw.idι = idι
raw→wf hΦ (p Raw.↦ q) = raw→wf hΦ p ↦ raw→wf hΦ q
raw→wf hΦ (Raw.∀ⁱ p) = ∀ⁱ (raw→wf (∀ᵢ-wf² hΦ) p)
raw→wf hΦ (Raw.tag ι) = tag ι
raw→wf hΦ (Raw.tag_⇒_ p q) = tag_⇒_ (raw→wf hΦ p) (raw→wf hΦ q)
raw→wf hΦ (Raw.tagˣ X⊑★∈) = tagˣ X⊑★∈ (hΦ X⊑★∈)
raw→wf hΦ (Raw.ν occA p) = ν occA (raw→wf (νᵢ-wf² hΦ) p)

------------------------------------------------------------------------
-- Endpoint well-formedness
------------------------------------------------------------------------

mutual
  ⊑-src-wf :
    ∀ {Δᴸ Δᴿ Φ A B} →
    Δᴸ ∣ Δᴿ ∣ Φ ⊢ A ⊑ B →
    WfTy Δᴸ A

  ⊑-tgt-wf :
    ∀ {Δᴸ Δᴿ Φ A B} →
    Δᴸ ∣ Δᴿ ∣ Φ ⊢ A ⊑ B →
    WfTy Δᴿ B

  ⊑-src-wf id★ = wf★
  ⊑-src-wf (idˣ _ X<Δᴸ _) = wfVar X<Δᴸ
  ⊑-src-wf idι = wfBase
  ⊑-src-wf (p ↦ q) = wf⇒ (⊑-src-wf p) (⊑-src-wf q)
  ⊑-src-wf (∀ⁱ p) = wf∀ (⊑-src-wf p)
  ⊑-src-wf (tag ι) = wfBase
  ⊑-src-wf (tag_⇒_ p q) = wf⇒ (⊑-src-wf p) (⊑-src-wf q)
  ⊑-src-wf (tagˣ _ X<Δᴸ) = wfVar X<Δᴸ
  ⊑-src-wf (ν occA p) = wf∀ (⊑-src-wf p)

  ⊑-tgt-wf id★ = wf★
  ⊑-tgt-wf (idˣ _ _ Y<Δᴿ) = wfVar Y<Δᴿ
  ⊑-tgt-wf idι = wfBase
  ⊑-tgt-wf (p ↦ q) = wf⇒ (⊑-tgt-wf p) (⊑-tgt-wf q)
  ⊑-tgt-wf (∀ⁱ p) = wf∀ (⊑-tgt-wf p)
  ⊑-tgt-wf (tag ι) = wf★
  ⊑-tgt-wf (tag_⇒_ p q) = wf★
  ⊑-tgt-wf (tagˣ _ _) = wf★
  ⊑-tgt-wf (ν occA p) = WfTy-un⇑ᵗ (⊑-tgt-wf p)

⊑-wf :
  ∀ {Δᴸ Δᴿ Φ A B} →
  Δᴸ ∣ Δᴿ ∣ Φ ⊢ A ⊑ B →
  WfTy Δᴸ A × WfTy Δᴿ B
⊑-wf p = ⊑-src-wf p , ⊑-tgt-wf p

