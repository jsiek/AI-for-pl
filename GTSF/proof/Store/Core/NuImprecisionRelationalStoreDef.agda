module proof.Store.Core.NuImprecisionRelationalStoreDef where

-- File Charter:
--   * Defines the relational runtime store used by ν-imprecision.
--   * Defines matched, one-sided, and correspondence-only entries together
--     with matched and one-sided binder lifts.
--   * Excludes crossed-allocation fixtures, term contexts, term imprecision,
--     simulation, and proof assembly.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong)

open import ImprecisionComposition using (⌊_⌋)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Types using
  (Store; Ty; TyCtx; TyVar; WfTy; ⇑ᵗ; ⟰ᵗ)


variable
  Φ Ψ : ImpCtx
  Δᴸ Δᴿ : TyCtx


data StoreImpEntry (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) : Set where
  store-matched :
    (α : TyVar) → (A : Ty) → (β : TyVar) → (B : Ty) →
    Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
    StoreImpEntry Φ Δᴸ Δᴿ

  store-left :
    (α : TyVar) → (A : Ty) →
    WfTy Δᴸ A →
    StoreImpEntry Φ Δᴸ Δᴿ

  store-right :
    (β : TyVar) → (B : Ty) →
    WfTy Δᴿ B →
    StoreImpEntry Φ Δᴸ Δᴿ

  store-link :
    (α : TyVar) → (A : Ty) → (β : TyVar) → (B : Ty) →
    Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
    StoreImpEntry Φ Δᴸ Δᴿ


StoreImp : ImpCtx → TyCtx → TyCtx → Set
StoreImp Φ Δᴸ Δᴿ = List (StoreImpEntry Φ Δᴸ Δᴿ)


leftStoreEntryⁱ : StoreImpEntry Φ Δᴸ Δᴿ → Store → Store
leftStoreEntryⁱ (store-matched α A β B p) Σ = (α , A) ∷ Σ
leftStoreEntryⁱ (store-left α A hA) Σ = (α , A) ∷ Σ
leftStoreEntryⁱ (store-right β B hB) Σ = Σ
leftStoreEntryⁱ (store-link α A β B p) Σ = Σ


rightStoreEntryⁱ : StoreImpEntry Φ Δᴸ Δᴿ → Store → Store
rightStoreEntryⁱ (store-matched α A β B p) Σ = (β , B) ∷ Σ
rightStoreEntryⁱ (store-left α A hA) Σ = Σ
rightStoreEntryⁱ (store-right β B hB) Σ = (β , B) ∷ Σ
rightStoreEntryⁱ (store-link α A β B p) Σ = Σ


leftStoreⁱ : StoreImp Φ Δᴸ Δᴿ → Store
leftStoreⁱ [] = []
leftStoreⁱ (entry ∷ ρ) = leftStoreEntryⁱ entry (leftStoreⁱ ρ)


rightStoreⁱ : StoreImp Φ Δᴸ Δᴿ → Store
rightStoreⁱ [] = []
rightStoreⁱ (entry ∷ ρ) = rightStoreEntryⁱ entry (rightStoreⁱ ρ)


data StoreCorresponds
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    (ρ : StoreImp Φ Δᴸ Δᴿ)
    (α : TyVar) (A : Ty) (β : TyVar) (B : Ty)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) : Set where
  correspondence-stored :
    store-matched α A β B p ∈ ρ →
    StoreCorresponds ρ α A β B p

  correspondence-linked :
    store-link α A β B p ∈ ρ →
    StoreCorresponds ρ α A β B p


data LiftStoreⁱ {Φ Δᴸ Δᴿ} (Ψ : ImpCtx) :
    StoreImp Φ Δᴸ Δᴿ → StoreImp Ψ (suc Δᴸ) (suc Δᴿ) → Set where
  lift-store-[] :
    LiftStoreⁱ Ψ [] []

  lift-store-∷ : ∀ {ρ ρ′ α β A B p p′}
    → ⌊ p′ ⌋ ≡ ⌊ p ⌋
    → LiftStoreⁱ Ψ ρ ρ′
      --------------------------------------------------------------
    → LiftStoreⁱ Ψ
        (store-matched α A β B p ∷ ρ)
        (store-matched (suc α) (⇑ᵗ A) (suc β) (⇑ᵗ B) p′ ∷ ρ′)

  lift-store-left : ∀ {ρ ρ′ α A hA hA′}
    → LiftStoreⁱ Ψ ρ ρ′
      --------------------------------------------------------------
    → LiftStoreⁱ Ψ
        (store-left α A hA ∷ ρ)
        (store-left (suc α) (⇑ᵗ A) hA′ ∷ ρ′)

  lift-store-right : ∀ {ρ ρ′ β B hB hB′}
    → LiftStoreⁱ Ψ ρ ρ′
      --------------------------------------------------------------
    → LiftStoreⁱ Ψ
        (store-right β B hB ∷ ρ)
        (store-right (suc β) (⇑ᵗ B) hB′ ∷ ρ′)

  lift-store-link : ∀ {ρ ρ′ α β A B p p′}
    → ⌊ p′ ⌋ ≡ ⌊ p ⌋
    → LiftStoreⁱ Ψ ρ ρ′
      --------------------------------------------------------------
    → LiftStoreⁱ Ψ
        (store-link α A β B p ∷ ρ)
        (store-link (suc α) (⇑ᵗ A) (suc β) (⇑ᵗ B) p′ ∷ ρ′)


leftStoreⁱ-lift :
  ∀ {Φ Δᴸ Δᴿ Ψ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ (suc Δᴸ) (suc Δᴿ)} →
  LiftStoreⁱ Ψ ρ ρ′ →
  leftStoreⁱ ρ′ ≡ ⟰ᵗ (leftStoreⁱ ρ)
leftStoreⁱ-lift lift-store-[] = refl
leftStoreⁱ-lift (lift-store-∷ _ liftρ) =
  cong ((_,_ _ _) ∷_) (leftStoreⁱ-lift liftρ)
leftStoreⁱ-lift (lift-store-left liftρ) =
  cong ((_,_ _ _) ∷_) (leftStoreⁱ-lift liftρ)
leftStoreⁱ-lift (lift-store-right liftρ) =
  leftStoreⁱ-lift liftρ
leftStoreⁱ-lift (lift-store-link _ liftρ) =
  leftStoreⁱ-lift liftρ


rightStoreⁱ-lift :
  ∀ {Φ Δᴸ Δᴿ Ψ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ (suc Δᴸ) (suc Δᴿ)} →
  LiftStoreⁱ Ψ ρ ρ′ →
  rightStoreⁱ ρ′ ≡ ⟰ᵗ (rightStoreⁱ ρ)
rightStoreⁱ-lift lift-store-[] = refl
rightStoreⁱ-lift (lift-store-∷ _ liftρ) =
  cong ((_,_ _ _) ∷_) (rightStoreⁱ-lift liftρ)
rightStoreⁱ-lift (lift-store-left liftρ) =
  rightStoreⁱ-lift liftρ
rightStoreⁱ-lift (lift-store-right liftρ) =
  cong ((_,_ _ _) ∷_) (rightStoreⁱ-lift liftρ)
rightStoreⁱ-lift (lift-store-link _ liftρ) =
  rightStoreⁱ-lift liftρ


data LiftLeftStoreⁱ {Φ Δᴸ Δᴿ} (Ψ : ImpCtx) :
    StoreImp Φ Δᴸ Δᴿ → StoreImp Ψ (suc Δᴸ) Δᴿ → Set where
  lift-left-store-[] :
    LiftLeftStoreⁱ Ψ [] []

  lift-left-store-∷ : ∀ {ρ ρ′ α β A B p p′}
    → ⌊ p′ ⌋ ≡ ⌊ p ⌋
    → LiftLeftStoreⁱ Ψ ρ ρ′
      --------------------------------------------------------------
    → LiftLeftStoreⁱ Ψ
        (store-matched α A β B p ∷ ρ)
        (store-matched (suc α) (⇑ᵗ A) β B p′ ∷ ρ′)

  lift-left-store-left : ∀ {ρ ρ′ α A hA hA′}
    → LiftLeftStoreⁱ Ψ ρ ρ′
      --------------------------------------------------------------
    → LiftLeftStoreⁱ Ψ
        (store-left α A hA ∷ ρ)
        (store-left (suc α) (⇑ᵗ A) hA′ ∷ ρ′)

  lift-left-store-right : ∀ {ρ ρ′ β B hB hB′}
    → LiftLeftStoreⁱ Ψ ρ ρ′
      --------------------------------------------------------------
    → LiftLeftStoreⁱ Ψ
        (store-right β B hB ∷ ρ)
        (store-right β B hB′ ∷ ρ′)

  lift-left-store-link : ∀ {ρ ρ′ α β A B p p′}
    → ⌊ p′ ⌋ ≡ ⌊ p ⌋
    → LiftLeftStoreⁱ Ψ ρ ρ′
      --------------------------------------------------------------
    → LiftLeftStoreⁱ Ψ
        (store-link α A β B p ∷ ρ)
        (store-link (suc α) (⇑ᵗ A) β B p′ ∷ ρ′)


leftStoreⁱ-lift-left :
  ∀ {Φ Δᴸ Δᴿ Ψ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ Ψ ρ ρ′ →
  leftStoreⁱ ρ′ ≡ ⟰ᵗ (leftStoreⁱ ρ)
leftStoreⁱ-lift-left lift-left-store-[] = refl
leftStoreⁱ-lift-left (lift-left-store-∷ _ liftρ) =
  cong ((_,_ _ _) ∷_) (leftStoreⁱ-lift-left liftρ)
leftStoreⁱ-lift-left (lift-left-store-left liftρ) =
  cong ((_,_ _ _) ∷_) (leftStoreⁱ-lift-left liftρ)
leftStoreⁱ-lift-left (lift-left-store-right liftρ) =
  leftStoreⁱ-lift-left liftρ
leftStoreⁱ-lift-left (lift-left-store-link _ liftρ) =
  leftStoreⁱ-lift-left liftρ


rightStoreⁱ-lift-left :
  ∀ {Φ Δᴸ Δᴿ Ψ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ Ψ ρ ρ′ →
  rightStoreⁱ ρ′ ≡ rightStoreⁱ ρ
rightStoreⁱ-lift-left lift-left-store-[] = refl
rightStoreⁱ-lift-left (lift-left-store-∷ _ liftρ) =
  cong ((_,_ _ _) ∷_) (rightStoreⁱ-lift-left liftρ)
rightStoreⁱ-lift-left (lift-left-store-left liftρ) =
  rightStoreⁱ-lift-left liftρ
rightStoreⁱ-lift-left (lift-left-store-right liftρ) =
  cong ((_,_ _ _) ∷_) (rightStoreⁱ-lift-left liftρ)
rightStoreⁱ-lift-left (lift-left-store-link _ liftρ) =
  rightStoreⁱ-lift-left liftρ


data LiftRightStoreⁱ {Φ Δᴸ Δᴿ} (Ψ : ImpCtx) :
    StoreImp Φ Δᴸ Δᴿ → StoreImp Ψ Δᴸ (suc Δᴿ) → Set where
  lift-right-store-[] :
    LiftRightStoreⁱ Ψ [] []

  lift-right-store-∷ : ∀ {ρ ρ′ α β A B p p′}
    → ⌊ p′ ⌋ ≡ ⌊ p ⌋
    → LiftRightStoreⁱ Ψ ρ ρ′
      --------------------------------------------------------------
    → LiftRightStoreⁱ Ψ
        (store-matched α A β B p ∷ ρ)
        (store-matched α A (suc β) (⇑ᵗ B) p′ ∷ ρ′)

  lift-right-store-left : ∀ {ρ ρ′ α A hA hA′}
    → LiftRightStoreⁱ Ψ ρ ρ′
      --------------------------------------------------------------
    → LiftRightStoreⁱ Ψ
        (store-left α A hA ∷ ρ)
        (store-left α A hA′ ∷ ρ′)

  lift-right-store-right : ∀ {ρ ρ′ β B hB hB′}
    → LiftRightStoreⁱ Ψ ρ ρ′
      --------------------------------------------------------------
    → LiftRightStoreⁱ Ψ
        (store-right β B hB ∷ ρ)
        (store-right (suc β) (⇑ᵗ B) hB′ ∷ ρ′)

  lift-right-store-link : ∀ {ρ ρ′ α β A B p p′}
    → ⌊ p′ ⌋ ≡ ⌊ p ⌋
    → LiftRightStoreⁱ Ψ ρ ρ′
      --------------------------------------------------------------
    → LiftRightStoreⁱ Ψ
        (store-link α A β B p ∷ ρ)
        (store-link α A (suc β) (⇑ᵗ B) p′ ∷ ρ′)


leftStoreⁱ-lift-right :
  ∀ {Φ Δᴸ Δᴿ Ψ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ Δᴸ (suc Δᴿ)} →
  LiftRightStoreⁱ Ψ ρ ρ′ →
  leftStoreⁱ ρ′ ≡ leftStoreⁱ ρ
leftStoreⁱ-lift-right lift-right-store-[] = refl
leftStoreⁱ-lift-right (lift-right-store-∷ _ liftρ) =
  cong ((_,_ _ _) ∷_) (leftStoreⁱ-lift-right liftρ)
leftStoreⁱ-lift-right (lift-right-store-left liftρ) =
  cong ((_,_ _ _) ∷_) (leftStoreⁱ-lift-right liftρ)
leftStoreⁱ-lift-right (lift-right-store-right liftρ) =
  leftStoreⁱ-lift-right liftρ
leftStoreⁱ-lift-right (lift-right-store-link _ liftρ) =
  leftStoreⁱ-lift-right liftρ


rightStoreⁱ-lift-right :
  ∀ {Φ Δᴸ Δᴿ Ψ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ Δᴸ (suc Δᴿ)} →
  LiftRightStoreⁱ Ψ ρ ρ′ →
  rightStoreⁱ ρ′ ≡ ⟰ᵗ (rightStoreⁱ ρ)
rightStoreⁱ-lift-right lift-right-store-[] = refl
rightStoreⁱ-lift-right (lift-right-store-∷ _ liftρ) =
  cong ((_,_ _ _) ∷_) (rightStoreⁱ-lift-right liftρ)
rightStoreⁱ-lift-right (lift-right-store-left liftρ) =
  rightStoreⁱ-lift-right liftρ
rightStoreⁱ-lift-right (lift-right-store-right liftρ) =
  cong ((_,_ _ _) ∷_) (rightStoreⁱ-lift-right liftρ)
rightStoreⁱ-lift-right (lift-right-store-link _ liftρ) =
  rightStoreⁱ-lift-right liftρ
