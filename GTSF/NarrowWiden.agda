-- This is based on the cambridge22 notes.

module NarrowWiden where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map)
open import Data.Nat using (ℕ; _<_; zero; suc; z<s; s<s)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import Coercions

------------------------------------------------------------------------
-- Narrowing and Widening
------------------------------------------------------------------------

infix 4 _∣_⊢_∶_⊒_
infix 4 _∣_⊢_∶_⊑_

mutual
  data _∣_⊢_∶_⊒_ : TyCtx → Store → Coercion → Ty → Ty → Set where

    nrw-id : ∀{Δ : TyCtx}{Σ : Store}{A : Ty}
      → WfTy Δ A
      → Atom A
       ---------------------
      → Δ ∣ Σ ⊢ id A ∶ A ⊒ A

    nrw-fun : ∀{Δ : TyCtx}{Σ : Store}{A A′ B B′ : Ty}{s t : Coercion}
      → Δ ∣ Σ ⊢ s ∶ A′ ⊑ A
      → Δ ∣ Σ ⊢ t ∶ B ⊒ B′
       ---------------------------------------
      → Δ ∣ Σ ⊢ (s ↦ t) ∶ (A ⇒ B) ⊒ (A′ ⇒ B′)

    nrw-all : ∀{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
      → suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ A ⊒ B
       ----------------------------------
      → Δ ∣ Σ ⊢ (`∀ s) ∶ (`∀ A) ⊒ (`∀ B)

    -- ν
    nrw-gen : ∀{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
      → WfTy Δ A
      → suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ ⇑ᵗ A ⊒ B
       ----------------------------------
      → Δ ∣ Σ ⊢ (gen A s) ∶ A ⊒ (`∀ B)

    nrw-untag : ∀{Δ : TyCtx}{Σ : Store}{G B : Ty}{ℓ : Label}{g}
      → WfTy Δ G
      → Ground G
      → Δ ∣ Σ ⊢ g ∶ G ⊒ B
       -----------------------------
      → Δ ∣ Σ ⊢ ((G ？ ℓ) ︔ g) ∶ ★ ⊒ B

    nrw-seal : ∀{Δ : TyCtx}{Σ : Store}{α : TyVar}{A A′ : Ty}{s}
      → WfTy Δ A′
      → (α , A′) ∈ Σ
      → Δ ∣ Σ ⊢ s ∶ A ⊒ A′
       ------------------------------------
      → Δ ∣ Σ ⊢ (s ︔ seal A′ α) ∶ A ⊒ (＇ α)



  data _∣_⊢_∶_⊑_ : TyCtx → Store → Coercion → Ty → Ty → Set where

    wid-id : ∀{Δ : TyCtx}{Σ : Store}{A : Ty}
      → WfTy Δ A
      → Atom A
       ---------------------
      → Δ ∣ Σ ⊢ id A ∶ A ⊑ A

    wid-fun : ∀{Δ : TyCtx}{Σ : Store}{A A′ B B′ : Ty}{s t : Coercion}
      → Δ ∣ Σ ⊢ s ∶ A′ ⊒ A
      → Δ ∣ Σ ⊢ t ∶ B ⊑ B′
       ---------------------------------------
      → Δ ∣ Σ ⊢ (s ↦ t) ∶ (A ⇒ B) ⊑ (A′ ⇒ B′)

    wid-all : ∀{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
      → suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ A ⊑ B
       ----------------------------------
      → Δ ∣ Σ ⊢ (`∀ s) ∶ (`∀ A) ⊑ (`∀ B)

    -- ν̅ 
    wid-inst : ∀{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
      → WfTy Δ B
      → suc Δ ∣ (0 , ★) ∷ ⟰ᵗ Σ ⊢ s ∶ A ⊑ ⇑ᵗ B
       ----------------------------------------
      → Δ ∣ Σ ⊢ (inst B s) ∶ (`∀ A) ⊑ B

    wid-tag : ∀{Δ : TyCtx}{Σ : Store}{A G : Ty}{g : Coercion}
      → WfTy Δ G
      → Ground G
      → Δ ∣ Σ ⊢ g ∶ A ⊑ G
       ----------------------------
      → Δ ∣ Σ ⊢ (g ︔ (G !)) ∶ A ⊑ ★

    wid-unseal : ∀{Δ : TyCtx}{Σ : Store}{α : TyVar}{A′ B : Ty}{s : Coercion}
      → WfTy Δ A′
      → (α , A′) ∈ Σ
      → Δ ∣ Σ ⊢ s ∶ A′ ⊑ B
       ---------------------------------------
      → Δ ∣ Σ ⊢ (unseal α A′ ︔ s) ∶ (＇ α) ⊑ B

