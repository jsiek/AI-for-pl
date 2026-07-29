module Imprecision where

-- File Charter:
--   * Defines context-indexed type imprecision for GTPLC.
--   * Indexes imprecision derivations by widening coercions and the converse
--     judgment by narrowing coercions.
--   * Defines the assumption contexts used to relate type variables.
--   * Exposes well-formedness of both endpoints of each judgment.

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_<_; zero; suc)
open import Data.Product using (_×_; _,_)

open import Types
open import NarrowWiden

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
-- Indexed widening and narrowing
------------------------------------------------------------------------

infix 4 _∣_⊢_⦂_⊑_⊣_
infix 4 _∣_⊢_⦂_⊒_⊣_

mutual

  data _∣_⊢_⦂_⊑_⊣_ (Φ : ImpCtx) (Δᴸ : TyCtx) :
    ∀ {c} → Widening c → Ty → Ty → TyCtx → Set where

    id★ : ∀ {Δᴿ}
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ id ⦂ ★ ⊑ ★ ⊣ Δᴿ

    idˣ : ∀ {X Y Δᴿ}
      → (X ˣ⊑ˣ Y) ∈ Φ
      → X < Δᴸ
      → Y < Δᴿ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ id ⦂ ＇ X ⊑ ＇ Y ⊣ Δᴿ

    idι : ∀ {ι Δᴿ}
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ id ⦂ ‵ ι ⊑ ‵ ι ⊣ Δᴿ

    _↦_ : ∀ {c d A A′ B B′ Δᴿ}
      {n : Narrowing c} {w : Widening d}
      → Φ ∣ Δᴿ ⊢ n ⦂ A′ ⊒ A ⊣ Δᴸ
      → Φ ∣ Δᴸ ⊢ w ⦂ B ⊑ B′ ⊣ Δᴿ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ cross (n ↦ w) ⦂
          (A ⇒ B) ⊑ (A′ ⇒ B′) ⊣ Δᴿ

    ∀ⁱ_ : ∀ {c A B Δᴿ} {w : Widening c}
      → ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ w ⦂ A ⊑ B ⊣ suc Δᴿ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ cross (`∀ w) ⦂ (`∀ A) ⊑ (`∀ B) ⊣ Δᴿ

    tag_ : ∀ {Δᴿ} (ι : Base)
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ (‵ ι) ! ⦂ ‵ ι ⊑ ★ ⊣ Δᴿ

    tag⇒ : ∀ {Δᴿ}
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ ★⇒★ ! ⦂ (★ ⇒ ★) ⊑ ★ ⊣ Δᴿ

    tag_↦ˡ_ : ∀ {c d A B Δᴿ}
      {n : NonIdⁿ c} {w : Widening d}
      → Φ ∣ Δᴿ ⊢ nonIdⁿ→narrowing n ⦂ ★ ⊒ A ⊣ Δᴸ
      → Φ ∣ Δᴸ ⊢ w ⦂ B ⊑ ★ ⊣ Δᴿ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ (n ↦ˡ w) ︔ ★⇒★ ! ⦂
          (A ⇒ B) ⊑ ★ ⊣ Δᴿ

    tag_↦ʳ_ : ∀ {c d A B Δᴿ}
      {n : Narrowing c} {w : NonIdʷ d}
      → Φ ∣ Δᴿ ⊢ n ⦂ ★ ⊒ A ⊣ Δᴸ
      → Φ ∣ Δᴸ ⊢ nonIdʷ→widening w ⦂ B ⊑ ★ ⊣ Δᴿ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ (n ↦ʳ w) ︔ ★⇒★ ! ⦂
          (A ⇒ B) ⊑ ★ ⊣ Δᴿ

    tagˣ : ∀ {X Δᴿ}
      → X ˣ⊑★ ∈ Φ
      → X < Δᴸ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ unseal X ⦂ ＇ X ⊑ ★ ⊣ Δᴿ

    inst : ∀ {c A B Δᴿ} {safe : InstSafe c}
      → NonVar A
      → zero ∈ᵗ A
      → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ
          ⊢ instSafe→widening safe ⦂ A ⊑ B
          ⊣ Δᴿ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ inst safe ⦂ (`∀ A) ⊑ B ⊣ Δᴿ

    inst-tag : ∀ {c A Δᴿ} {safe : InstSafe c}
      → NonVar A
      → zero ∈ᵗ A
      → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ
          ⊢ instSafe→widening safe ⦂ A ⊑ (★ ⇒ ★)
          ⊣ Δᴿ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ inst safe ︔★⇒★! ⦂
          (`∀ A) ⊑ ★ ⊣ Δᴿ

  data _∣_⊢_⦂_⊒_⊣_ (Φ : ImpCtx) (Δᴸ : TyCtx) :
    ∀ {c} → Narrowing c → Ty → Ty → TyCtx → Set where

    id★ : ∀ {Δᴿ}
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ id ⦂ ★ ⊒ ★ ⊣ Δᴿ

    idˣ : ∀ {X Y Δᴿ}
      → (Y ˣ⊑ˣ X) ∈ Φ
      → X < Δᴸ
      → Y < Δᴿ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ id ⦂ ＇ X ⊒ ＇ Y ⊣ Δᴿ

    idι : ∀ {ι Δᴿ}
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ id ⦂ ‵ ι ⊒ ‵ ι ⊣ Δᴿ

    _↦_ : ∀ {c d A A′ B B′ Δᴿ}
      {w : Widening c} {n : Narrowing d}
      → Φ ∣ Δᴿ ⊢ w ⦂ A′ ⊑ A ⊣ Δᴸ
      → Φ ∣ Δᴸ ⊢ n ⦂ B ⊒ B′ ⊣ Δᴿ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ cross (w ↦ n) ⦂
          (A ⇒ B) ⊒ (A′ ⇒ B′) ⊣ Δᴿ

    ∀ⁱ_ : ∀ {c A B Δᴿ} {n : Narrowing c}
      → ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ n ⦂ A ⊒ B ⊣ suc Δᴿ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ cross (`∀ n) ⦂ (`∀ A) ⊒ (`∀ B) ⊣ Δᴿ

    untag_ : ∀ {Δᴿ} (ι : Base)
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ (‵ ι) ？ ⦂ ★ ⊒ ‵ ι ⊣ Δᴿ

    untag⇒ : ∀ {Δᴿ}
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ ★⇒★ ？ ⦂ ★ ⊒ (★ ⇒ ★) ⊣ Δᴿ

    untag_↦ˡ_ : ∀ {c d A B Δᴿ}
      {w : NonIdʷ c} {n : Narrowing d}
      → Φ ∣ Δᴿ ⊢ nonIdʷ→widening w ⦂ A ⊑ ★ ⊣ Δᴸ
      → Φ ∣ Δᴸ ⊢ n ⦂ ★ ⊒ B ⊣ Δᴿ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ ★⇒★ ？︔ (w ↦ˡ n) ⦂
          ★ ⊒ (A ⇒ B) ⊣ Δᴿ

    untag_↦ʳ_ : ∀ {c d A B Δᴿ}
      {w : Widening c} {n : NonIdⁿ d}
      → Φ ∣ Δᴿ ⊢ w ⦂ A ⊑ ★ ⊣ Δᴸ
      → Φ ∣ Δᴸ ⊢ nonIdⁿ→narrowing n ⦂ ★ ⊒ B ⊣ Δᴿ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ ★⇒★ ？︔ (w ↦ʳ n) ⦂
          ★ ⊒ (A ⇒ B) ⊣ Δᴿ

    untagˣ : ∀ {X Δᴿ}
      → X ˣ⊑★ ∈ Φ
      → X < Δᴿ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ seal X ⦂ ★ ⊒ ＇ X ⊣ Δᴿ

    gen : ∀ {c A B Δᴿ} {safe : GenSafe c}
      → NonVar A
      → zero ∈ᵗ A
      → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ Δᴸ
          ⊢ genSafe→narrowing safe ⦂ B ⊒ A
          ⊣ suc Δᴿ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ gen safe ⦂ B ⊒ (`∀ A) ⊣ Δᴿ

    gen-untag : ∀ {c A Δᴿ} {safe : GenSafe c}
      → NonVar A
      → zero ∈ᵗ A
      → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ Δᴸ
          ⊢ genSafe→narrowing safe ⦂ (★ ⇒ ★) ⊒ A
          ⊣ suc Δᴿ
       --------------------------------------------------
      → Φ ∣ Δᴸ ⊢ fun-？︔gen safe ⦂ ★ ⊒ (`∀ A) ⊣ Δᴿ

------------------------------------------------------------------------
-- Endpoint well-formedness
------------------------------------------------------------------------

mutual

  ⊑-src-wf : ∀ {c Δᴸ Δᴿ Φ A B} {w : Widening c}
    → Φ ∣ Δᴸ ⊢ w ⦂ A ⊑ B ⊣ Δᴿ
    → WfTy Δᴸ A

  ⊑-tgt-wf : ∀ {c Δᴸ Δᴿ Φ A B} {w : Widening c}
    → Φ ∣ Δᴸ ⊢ w ⦂ A ⊑ B ⊣ Δᴿ
    → WfTy Δᴿ B

  ⊒-src-wf : ∀ {c Δᴸ Δᴿ Φ A B} {n : Narrowing c}
    → Φ ∣ Δᴸ ⊢ n ⦂ A ⊒ B ⊣ Δᴿ
    → WfTy Δᴸ A

  ⊒-tgt-wf : ∀ {c Δᴸ Δᴿ Φ A B} {n : Narrowing c}
    → Φ ∣ Δᴸ ⊢ n ⦂ A ⊒ B ⊣ Δᴿ
    → WfTy Δᴿ B

  ⊑-src-wf id★ = wf★
  ⊑-src-wf (idˣ _ X<Δᴸ _) = wfVar X<Δᴸ
  ⊑-src-wf idι = wfBase
  ⊑-src-wf (p ↦ q) = wf⇒ (⊒-tgt-wf p) (⊑-src-wf q)
  ⊑-src-wf (∀ⁱ p) = wf∀ (⊑-src-wf p)
  ⊑-src-wf (tag ι) = wfBase
  ⊑-src-wf tag⇒ = wf⇒ wf★ wf★
  ⊑-src-wf (tag p ↦ˡ q) = wf⇒ (⊒-tgt-wf p) (⊑-src-wf q)
  ⊑-src-wf (tag p ↦ʳ q) = wf⇒ (⊒-tgt-wf p) (⊑-src-wf q)
  ⊑-src-wf (tagˣ _ X<Δᴸ) = wfVar X<Δᴸ
  ⊑-src-wf (inst _ _ p) = wf∀ (⊑-src-wf p)
  ⊑-src-wf (inst-tag _ _ p) = wf∀ (⊑-src-wf p)

  ⊑-tgt-wf id★ = wf★
  ⊑-tgt-wf (idˣ _ _ Y<Δᴿ) = wfVar Y<Δᴿ
  ⊑-tgt-wf idι = wfBase
  ⊑-tgt-wf (p ↦ q) = wf⇒ (⊒-src-wf p) (⊑-tgt-wf q)
  ⊑-tgt-wf (∀ⁱ p) = wf∀ (⊑-tgt-wf p)
  ⊑-tgt-wf (tag ι) = wf★
  ⊑-tgt-wf tag⇒ = wf★
  ⊑-tgt-wf (tag p ↦ˡ q) = wf★
  ⊑-tgt-wf (tag p ↦ʳ q) = wf★
  ⊑-tgt-wf (tagˣ _ _) = wf★
  ⊑-tgt-wf (inst _ _ p) = ⊑-tgt-wf p
  ⊑-tgt-wf (inst-tag _ _ p) = wf★

  ⊒-src-wf id★ = wf★
  ⊒-src-wf (idˣ _ X<Δᴸ _) = wfVar X<Δᴸ
  ⊒-src-wf idι = wfBase
  ⊒-src-wf (p ↦ q) = wf⇒ (⊑-tgt-wf p) (⊒-src-wf q)
  ⊒-src-wf (∀ⁱ p) = wf∀ (⊒-src-wf p)
  ⊒-src-wf (untag ι) = wf★
  ⊒-src-wf untag⇒ = wf★
  ⊒-src-wf (untag p ↦ˡ q) = wf★
  ⊒-src-wf (untag p ↦ʳ q) = wf★
  ⊒-src-wf (untagˣ _ _) = wf★
  ⊒-src-wf (gen _ _ p) = ⊒-src-wf p
  ⊒-src-wf (gen-untag _ _ p) = wf★

  ⊒-tgt-wf id★ = wf★
  ⊒-tgt-wf (idˣ _ _ Y<Δᴿ) = wfVar Y<Δᴿ
  ⊒-tgt-wf idι = wfBase
  ⊒-tgt-wf (p ↦ q) = wf⇒ (⊑-src-wf p) (⊒-tgt-wf q)
  ⊒-tgt-wf (∀ⁱ p) = wf∀ (⊒-tgt-wf p)
  ⊒-tgt-wf (untag ι) = wfBase
  ⊒-tgt-wf untag⇒ = wf⇒ wf★ wf★
  ⊒-tgt-wf (untag p ↦ˡ q) =
    wf⇒ (⊑-src-wf p) (⊒-tgt-wf q)
  ⊒-tgt-wf (untag p ↦ʳ q) =
    wf⇒ (⊑-src-wf p) (⊒-tgt-wf q)
  ⊒-tgt-wf (untagˣ _ X<Δᴿ) = wfVar X<Δᴿ
  ⊒-tgt-wf (gen _ _ p) = wf∀ (⊒-tgt-wf p)
  ⊒-tgt-wf (gen-untag _ _ p) = wf∀ (⊒-tgt-wf p)

⊑-wf : ∀ {c Δᴸ Δᴿ Φ A B} {w : Widening c}
  → Φ ∣ Δᴸ ⊢ w ⦂ A ⊑ B ⊣ Δᴿ
  → WfTy Δᴸ A × WfTy Δᴿ B
⊑-wf p = ⊑-src-wf p , ⊑-tgt-wf p

⊒-wf : ∀ {c Δᴸ Δᴿ Φ A B} {n : Narrowing c}
  → Φ ∣ Δᴸ ⊢ n ⦂ A ⊒ B ⊣ Δᴿ
  → WfTy Δᴸ A × WfTy Δᴿ B
⊒-wf p = ⊒-src-wf p , ⊒-tgt-wf p
