module GradualTermImprecision where

-- File Charter:
--   * Term imprecision for gradual terms.

open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc)

open import Types
open import Imprecision
open import Primitives using (Const; Prim; constTy; κℕ)
open import GradualTerms

------------------------------------------------------------------------
-- Gradual-term imprecision
------------------------------------------------------------------------

infix 4 _∣_∣_⊢ᴳ_⊑_⦂_
data _∣_∣_⊢ᴳ_⊑_⦂_ (Δ : TyCtx) (Φ : VarPrecCtx) (Π : List Imp) : GTerm → GTerm → Imp → Set₁ where

  x⊑x : ∀ {x}{A A′ : Ty}{p : Imp}
    → Π ∋ x ⦂ p
    ------------------------------
    → Δ ∣ Φ ∣ Π ⊢ᴳ (` x) ⊑ (` x) ⦂ p

  ƛ⊑ƛ : ∀ {A A′ : Ty}{M M′ : GTerm}{pA pB : Imp}
    → Δ ∣ Φ ⊢ pA ⦂ A ⊑ A′
    → Δ ∣ Φ ∣ Π ⊢ᴳ M ⊑ M′ ⦂ pB
    ----------------------------------------------------------
    → Δ ∣ Φ ∣ Π ⊢ᴳ (ƛ A ⇒ M) ⊑ (ƛ A′ ⇒ M′) ⦂ A⇒B-⊑-A′⇒B′ pA pB

  ·⊑· : ∀ {L L′ M M′}{pA pB pA′ : Imp}
    → Δ ∣ Φ ∣ Π ⊢ᴳ L ⊑ L′ ⦂ A⇒B-⊑-A′⇒B′ pA pB
    → Δ ∣ Φ ∣ Π ⊢ᴳ M ⊑ M′ ⦂ pA′
    ---------------------------------------
    → Δ ∣ Φ ∣ Π ⊢ᴳ (L · M) ⊑ (L′ · M′) ⦂ pB

  Λ⊑Λ : ∀ {M M′}{pA : Imp}
    → Value M
    → Value M′
    → suc Δ ∣ X⊑X ∷ Φ ∣ map ⇑⊑ Π ⊢ᴳ M ⊑ M′ ⦂ pA
    -------------------------------------------
    → Δ ∣ Φ ∣ Π ⊢ᴳ (Λ M) ⊑ (Λ M′) ⦂ ∀A-⊑-∀B pA

  Λ⊑ : ∀ {M M′}{pA : Imp}
    → Value M 
    → suc Δ ∣ X⊑★ ∷ Φ  ∣ Π ⊢ᴳ M ⊑ ⇑ᵗᴳ M′ ⦂ pA 
    -----------------------------------------
    → Δ ∣ Φ ∣ Π ⊢ᴳ (Λ M) ⊑ M′ ⦂ ∀A-⊑-B pA

  []⊑[] : ∀ {M M′ T T′}{pA pT : Imp} 
    → Δ ∣ Φ ∣ Π ⊢ᴳ M ⊑ M′ ⦂ ∀A-⊑-∀B pA
    → Δ ∣ Φ ⊢ pT ⦂ T ⊑ T′ 
    ------------------------------------------------------
    → Δ ∣ Φ ∣ Π ⊢ᴳ (M `[ T ]) ⊑ (M′ `[ T′ ]) ⦂ pA [ pT ]⊑ᵢ

  []⊑ : ∀ {M M′ T}{pA pT : Imp} 
    → Δ ∣ Φ ∣ Π ⊢ᴳ M ⊑ M′ ⦂ ∀A-⊑-B pA 
    → Δ ∣ Φ ⊢ pT ⦂ T ⊑ ★ 
    --------------------------------------------
    → Δ ∣ Φ ∣ Π ⊢ᴳ (M `[ T ]) ⊑ M′ ⦂ pA [ pT ]⊑ᵢ

  $⊑$ : ∀ {n}
    --------------------------------------------------
    → Δ ∣ Φ ∣ Π ⊢ᴳ ($ (κℕ n)) ⊑ ($ (κℕ n)) ⦂ ι-⊑-ι `ℕ

  ⊕⊑⊕ : ∀ {L L′ M M′ op} {pAB pA}
    → Δ ∣ Φ ∣ Π ⊢ᴳ L ⊑ L′ ⦂ pAB
    → Δ ∣ Φ ∣ Π ⊢ᴳ M ⊑ M′ ⦂ pA
    ---------------------------------------------------------
    → Δ ∣ Φ ∣ Π ⊢ᴳ (L ⊕[ op ] M) ⊑ (L′ ⊕[ op ] M′) ⦂ ι-⊑-ι `ℕ
