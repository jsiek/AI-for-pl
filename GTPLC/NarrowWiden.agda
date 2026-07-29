module NarrowWiden where

-- File Charter:
--   * Defines context-indexed narrowing and widening for GTPLC.
--   * Indexes each judgment directly by its coercion.
--   * Uses endpoint type equality, rather than a separate non-identity
--     grammar, to choose between collapsed and sequenced coercions.
--   * Exposes smart wrappers and endpoint well-formedness.

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_<_; zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no)

open import Types
open import Coercions

------------------------------------------------------------------------
-- Type-imprecision assumptions
------------------------------------------------------------------------

data ImpAssm : Set where
  _ˣ⊑★ : TyVar → ImpAssm
  _ˣ⊑ˣ_ : TyVar → TyVar → ImpAssm

ImpCtx : Set
ImpCtx = List ImpAssm

⇑ᵢₐ : ImpAssm → ImpAssm
⇑ᵢₐ (X ˣ⊑★) = suc X ˣ⊑★
⇑ᵢₐ (X ˣ⊑ˣ Y) = suc X ˣ⊑ˣ suc Y

⇑ᴸᵢₐ : ImpAssm → ImpAssm
⇑ᴸᵢₐ (X ˣ⊑★) = suc X ˣ⊑★
⇑ᴸᵢₐ (X ˣ⊑ˣ Y) = suc X ˣ⊑ˣ Y

⇑ᴿᵢₐ : ImpAssm → ImpAssm
⇑ᴿᵢₐ (X ˣ⊑★) = X ˣ⊑★
⇑ᴿᵢₐ (X ˣ⊑ˣ Y) = X ˣ⊑ˣ suc Y

⇑ᵢ : ImpCtx → ImpCtx
⇑ᵢ [] = []
⇑ᵢ (a ∷ Φ) = ⇑ᵢₐ a ∷ ⇑ᵢ Φ

⇑ᴸᵢ : ImpCtx → ImpCtx
⇑ᴸᵢ [] = []
⇑ᴸᵢ (a ∷ Φ) = ⇑ᴸᵢₐ a ∷ ⇑ᴸᵢ Φ

⇑ᴿᵢ : ImpCtx → ImpCtx
⇑ᴿᵢ [] = []
⇑ᴿᵢ (a ∷ Φ) = ⇑ᴿᵢₐ a ∷ ⇑ᴿᵢ Φ

swapRight∀∀ᵢ : ImpCtx → ImpCtx
swapRight∀∀ᵢ Φ =
  (zero ˣ⊑ˣ suc zero) ∷
  (suc zero ˣ⊑ˣ zero) ∷
  ⇑ᵢ (⇑ᵢ Φ)

idᵢ : TyCtx → ImpCtx
idᵢ zero = []
idᵢ (suc Δ) = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ (idᵢ Δ)

------------------------------------------------------------------------
-- Atomic widening and narrowing
------------------------------------------------------------------------

infix 4 _⊢_⊑ᵃ_
infix 4 _⊢_⊒ᵃ_

_⊢_⊑ᵃ_ : ∀ {A B} → ImpCtx → Atom A → Atom B → Set
Φ ⊢ (＇ X) ⊑ᵃ (＇ Y) = (X ˣ⊑ˣ Y) ∈ Φ
Φ ⊢ (＇ X) ⊑ᵃ (‵ ι) = ⊥
Φ ⊢ (＇ X) ⊑ᵃ ★ = ⊥
Φ ⊢ (‵ ι) ⊑ᵃ (＇ Y) = ⊥
Φ ⊢ (‵ ι) ⊑ᵃ (‵ κ) = ι ≡ κ
Φ ⊢ (‵ ι) ⊑ᵃ ★ = ⊥
Φ ⊢ ★ ⊑ᵃ (＇ Y) = ⊥
Φ ⊢ ★ ⊑ᵃ (‵ ι) = ⊥
Φ ⊢ ★ ⊑ᵃ ★ = ⊤

_⊢_⊒ᵃ_ : ∀ {A B} → ImpCtx → Atom A → Atom B → Set
Φ ⊢ a ⊒ᵃ b = Φ ⊢ b ⊑ᵃ a

renameᵃ : ∀ {A} (ρ : Renameᵗ)
  → Atom A
  → Atom (renameᵗ ρ A)
renameᵃ ρ (＇ X) = ＇ (ρ X)
renameᵃ ρ (‵ ι) = ‵ ι
renameᵃ ρ ★ = ★

------------------------------------------------------------------------
-- Coercion-indexed widening and narrowing
------------------------------------------------------------------------

infix 4 _∣_⊢_⦂_⊑_⊣_
infix 4 _∣_⊢_⦂_⊒_⊣_

mutual

  data _∣_⊢_⦂_⊑_⊣_ (Φ : ImpCtx) (Δᴸ : TyCtx) :
    Coercion → Ty → Ty → TyCtx → Set where

    idᵃ : ∀ {A B Δᴿ} (a : Atom A) (b : Atom B)
      → WfTy Δᴸ A
      → WfTy Δᴿ B
      → Φ ⊢ a ⊑ᵃ b
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ id ⦂ A ⊑ B ⊣ Δᴿ

    _↦_ : ∀ {c d A A′ B B′ Δᴿ}
      → Φ ∣ Δᴿ ⊢ c ⦂ A′ ⊒ A ⊣ Δᴸ
      → Φ ∣ Δᴸ ⊢ d ⦂ B ⊑ B′ ⊣ Δᴿ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ c ↦ d ⦂ (A ⇒ B) ⊑ (A′ ⇒ B′) ⊣ Δᴿ

    ∀ⁱ_ : ∀ {c A B Δᴿ}
      → ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ c ⦂ A ⊑ B ⊣ suc Δᴿ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ `∀ c ⦂ (`∀ A) ⊑ (`∀ B) ⊣ Δᴿ

    tag_ : ∀ {Δᴿ} (ι : Base)
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ (‵ ι) ! ⦂ ‵ ι ⊑ ★ ⊣ Δᴿ

    tag⇒ : ∀ {Δᴿ}
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ ★⇒★ ! ⦂ (★ ⇒ ★) ⊑ ★ ⊣ Δᴿ

    _︔tag⇒[_] : ∀ {c A Δᴿ}
      → Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ (★ ⇒ ★) ⊣ Δᴿ
      → A ≢ (★ ⇒ ★)
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ (c ︔ (★⇒★ !)) ⦂ A ⊑ ★ ⊣ Δᴿ

    tagˣ : ∀ {X Δᴿ}
      → X ˣ⊑★ ∈ Φ
      → X < Δᴸ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ unseal X ⦂ ＇ X ⊑ ★ ⊣ Δᴿ

    inst : ∀ {c A B Δᴿ}
      → NonVar A
      → zero ∈ᵗ A
      → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ c ⦂ A ⊑ B ⊣ Δᴿ
      → B ≢ ★
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ inst c ⦂ (`∀ A) ⊑ B ⊣ Δᴿ

  data _∣_⊢_⦂_⊒_⊣_ (Φ : ImpCtx) (Δᴸ : TyCtx) :
    Coercion → Ty → Ty → TyCtx → Set where

    idᵃ : ∀ {A B Δᴿ} (a : Atom A) (b : Atom B)
      → WfTy Δᴸ A
      → WfTy Δᴿ B
      → Φ ⊢ a ⊒ᵃ b
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ id ⦂ A ⊒ B ⊣ Δᴿ

    _↦_ : ∀ {c d A A′ B B′ Δᴿ}
      → Φ ∣ Δᴿ ⊢ c ⦂ A′ ⊑ A ⊣ Δᴸ
      → Φ ∣ Δᴸ ⊢ d ⦂ B ⊒ B′ ⊣ Δᴿ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ c ↦ d ⦂ (A ⇒ B) ⊒ (A′ ⇒ B′) ⊣ Δᴿ

    ∀ⁱ_ : ∀ {c A B Δᴿ}
      → ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ c ⦂ A ⊒ B ⊣ suc Δᴿ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ `∀ c ⦂ (`∀ A) ⊒ (`∀ B) ⊣ Δᴿ

    untag_ : ∀ {Δᴿ} (ι : Base)
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ (‵ ι) ？ ⦂ ★ ⊒ ‵ ι ⊣ Δᴿ

    untag⇒ : ∀ {Δᴿ}
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ ★⇒★ ？ ⦂ ★ ⊒ (★ ⇒ ★) ⊣ Δᴿ

    untag⇒︔_[_] : ∀ {c B Δᴿ}
      → Φ ∣ Δᴸ ⊢ c ⦂ (★ ⇒ ★) ⊒ B ⊣ Δᴿ
      → (★ ⇒ ★) ≢ B
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ ((★⇒★ ？) ︔ c) ⦂ ★ ⊒ B ⊣ Δᴿ

    untagˣ : ∀ {X Δᴿ}
      → X ˣ⊑★ ∈ Φ
      → X < Δᴿ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ seal X ⦂ ★ ⊒ ＇ X ⊣ Δᴿ

    gen : ∀ {c A B Δᴿ}
      → NonVar A
      → zero ∈ᵗ A
      → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ Δᴸ ⊢ c ⦂ B ⊒ A ⊣ suc Δᴿ
      → B ≢ ★
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ gen c ⦂ B ⊒ (`∀ A) ⊣ Δᴿ

------------------------------------------------------------------------
-- Smart function-tag wrappers
------------------------------------------------------------------------

wrap-tag⇒ : ∀ {c Φ Δᴸ Δᴿ A}
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ (★ ⇒ ★) ⊣ Δᴿ
  → ∃[ d ] Φ ∣ Δᴸ ⊢ d ⦂ A ⊑ ★ ⊣ Δᴿ
wrap-tag⇒ {A = A} p with A ≟Ty (★ ⇒ ★)
wrap-tag⇒ {A = .(★ ⇒ ★)} p | yes refl = (★⇒★ !) , tag⇒
wrap-tag⇒ {c = c} p | no A≢★⇒★ =
  (c ︔ (★⇒★ !)) , p ︔tag⇒[ A≢★⇒★ ]

wrap-untag⇒ : ∀ {c Φ Δᴸ Δᴿ B}
  → Φ ∣ Δᴸ ⊢ c ⦂ (★ ⇒ ★) ⊒ B ⊣ Δᴿ
  → ∃[ d ] Φ ∣ Δᴸ ⊢ d ⦂ ★ ⊒ B ⊣ Δᴿ
wrap-untag⇒ {B = B} p with (★ ⇒ ★) ≟Ty B
wrap-untag⇒ {B = .(★ ⇒ ★)} p | yes refl = (★⇒★ ？) , untag⇒
wrap-untag⇒ {c = c} p | no ★⇒★≢B =
  ((★⇒★ ？) ︔ c) , untag⇒︔ p [ ★⇒★≢B ]

------------------------------------------------------------------------
-- Endpoint well-formedness
------------------------------------------------------------------------

mutual

  ⊑-src-wf : ∀ {c Δᴸ Δᴿ Φ A B}
    → Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ B ⊣ Δᴿ
    → WfTy Δᴸ A

  ⊑-tgt-wf : ∀ {c Δᴸ Δᴿ Φ A B}
    → Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ B ⊣ Δᴿ
    → WfTy Δᴿ B

  ⊒-src-wf : ∀ {c Δᴸ Δᴿ Φ A B}
    → Φ ∣ Δᴸ ⊢ c ⦂ A ⊒ B ⊣ Δᴿ
    → WfTy Δᴸ A

  ⊒-tgt-wf : ∀ {c Δᴸ Δᴿ Φ A B}
    → Φ ∣ Δᴸ ⊢ c ⦂ A ⊒ B ⊣ Δᴿ
    → WfTy Δᴿ B

  ⊑-src-wf (idᵃ _ _ hA _ _) = hA
  ⊑-src-wf (p ↦ q) = wf⇒ (⊒-tgt-wf p) (⊑-src-wf q)
  ⊑-src-wf (∀ⁱ p) = wf∀ (⊑-src-wf p)
  ⊑-src-wf (tag ι) = wfBase
  ⊑-src-wf tag⇒ = wf⇒ wf★ wf★
  ⊑-src-wf (p ︔tag⇒[ _ ]) = ⊑-src-wf p
  ⊑-src-wf (tagˣ _ X<Δᴸ) = wfVar X<Δᴸ
  ⊑-src-wf (inst _ _ p _) = wf∀ (⊑-src-wf p)

  ⊑-tgt-wf (idᵃ _ _ _ hB _) = hB
  ⊑-tgt-wf (p ↦ q) = wf⇒ (⊒-src-wf p) (⊑-tgt-wf q)
  ⊑-tgt-wf (∀ⁱ p) = wf∀ (⊑-tgt-wf p)
  ⊑-tgt-wf (tag ι) = wf★
  ⊑-tgt-wf tag⇒ = wf★
  ⊑-tgt-wf (_ ︔tag⇒[ _ ]) = wf★
  ⊑-tgt-wf (tagˣ _ _) = wf★
  ⊑-tgt-wf (inst _ _ p _) = ⊑-tgt-wf p

  ⊒-src-wf (idᵃ _ _ hA _ _) = hA
  ⊒-src-wf (p ↦ q) = wf⇒ (⊑-tgt-wf p) (⊒-src-wf q)
  ⊒-src-wf (∀ⁱ p) = wf∀ (⊒-src-wf p)
  ⊒-src-wf (untag ι) = wf★
  ⊒-src-wf untag⇒ = wf★
  ⊒-src-wf (untag⇒︔ _ [ _ ]) = wf★
  ⊒-src-wf (untagˣ _ _) = wf★
  ⊒-src-wf (gen _ _ p _) = ⊒-src-wf p

  ⊒-tgt-wf (idᵃ _ _ _ hB _) = hB
  ⊒-tgt-wf (p ↦ q) = wf⇒ (⊑-src-wf p) (⊒-tgt-wf q)
  ⊒-tgt-wf (∀ⁱ p) = wf∀ (⊒-tgt-wf p)
  ⊒-tgt-wf (untag ι) = wfBase
  ⊒-tgt-wf untag⇒ = wf⇒ wf★ wf★
  ⊒-tgt-wf (untag⇒︔ p [ _ ]) = ⊒-tgt-wf p
  ⊒-tgt-wf (untagˣ _ X<Δᴿ) = wfVar X<Δᴿ
  ⊒-tgt-wf (gen _ _ p _) = wf∀ (⊒-tgt-wf p)

⊑-wf : ∀ {c Δᴸ Δᴿ Φ A B}
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ B ⊣ Δᴿ
  → WfTy Δᴸ A × WfTy Δᴿ B
⊑-wf p = ⊑-src-wf p , ⊑-tgt-wf p

⊒-wf : ∀ {c Δᴸ Δᴿ Φ A B}
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⊒ B ⊣ Δᴿ
  → WfTy Δᴸ A × WfTy Δᴿ B
⊒-wf p = ⊒-src-wf p , ⊒-tgt-wf p
