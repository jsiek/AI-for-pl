module NuTermImprecision where

-- File Charter:
--   * First draft of Nu-term imprecision for the DGG path.
--   * Indexes terms by `ImprecisionWf` witnesses rather than coercions.
--   * Relates independent left/right runtime stores with explicit matched,
--     left-only, and right-only allocation entries, so ν-step simulation cases
--     have a visible place to extend the store relation.
--   * Carries enough side conditions for the relation to project to ordinary
--     `NuTerms` typing derivations for both related terms.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import Types
open import Ctx using (⤊ᵗ)
open import Coercions
open import Conversion using (_∣_∣_⊢_∶_↑ˢ_; _∣_∣_⊢_∶_↓ˢ_)
open import ImprecisionWf
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuTerms using
  ( Term
  ; Value
  ; No•
  ; ⇑ᵗᵐ
  ; `_
  ; ƛ_
  ; _·_
  ; Λ_
  ; _•
  ; ν
  ; $
  ; _⊕[_]_
  ; _⟨_⟩
  ; blame
  )
open import Primitives
open import StoreCorrespondence using
  ( leftStore-⇑ᶜorr
  ; leftStore-⇑ʳᶜorr
  ; rightStore-⇑ᶜorr
  ; rightStore-⇑ʳᶜorr
  )
open import proof.CastImprecision using
  ( LeftCastCtxCompatible
  ; RightCastCtxCompatible
  ; narrowing⇒⊑ᵢ
  ; widening⇒⊑ᵢ
  ; ⊑-transˡ-castᵢ
  ; ⊑-transʳ-castᵢ
  )
open import proof.NarrowWidenProperties using (StoreDetWf)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; _∣_∣_⊢_⦂_
  ; ⊢`
  ; ⊢ƛ
  ; ⊢·
  ; ⊢Λ
  ; ⊢•
  ; ⊢ν↑
  ; ⊢ν⊑
  ; ⊢$
  ; ⊢⊕
  ; ⊢⟨⟩↑
  ; ⊢⟨⟩↓
  ; ⊢⟨⟩⊒
  ; ⊢⟨⟩⊑
  ; ⊢blame
  )

variable
  Φ Ψ : ImpCtx
  Δᴸ Δᴿ : TyCtx
  A A′ B B′ C C′ D D′ : Ty
  M M′ N N′ L L′ V V′ : Term
  x : Var
  κ : Const
  op : Prim
  c c′ d d′ s s′ : Coercion
  μ μ′ : ModeEnv

------------------------------------------------------------------------
-- Store imprecision
------------------------------------------------------------------------

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

StoreImp : ImpCtx → TyCtx → TyCtx → Set
StoreImp Φ Δᴸ Δᴿ = List (StoreImpEntry Φ Δᴸ Δᴿ)

leftStoreEntryⁱ : StoreImpEntry Φ Δᴸ Δᴿ → Store → Store
leftStoreEntryⁱ (store-matched α A β B p) Σ = (α , A) ∷ Σ
leftStoreEntryⁱ (store-left α A hA) Σ = (α , A) ∷ Σ
leftStoreEntryⁱ (store-right β B hB) Σ = Σ

rightStoreEntryⁱ : StoreImpEntry Φ Δᴸ Δᴿ → Store → Store
rightStoreEntryⁱ (store-matched α A β B p) Σ = (β , B) ∷ Σ
rightStoreEntryⁱ (store-left α A hA) Σ = Σ
rightStoreEntryⁱ (store-right β B hB) Σ = (β , B) ∷ Σ

leftStoreⁱ : StoreImp Φ Δᴸ Δᴿ → Store
leftStoreⁱ [] = []
leftStoreⁱ (entry ∷ ρ) = leftStoreEntryⁱ entry (leftStoreⁱ ρ)

rightStoreⁱ : StoreImp Φ Δᴸ Δᴿ → Store
rightStoreⁱ [] = []
rightStoreⁱ (entry ∷ ρ) = rightStoreEntryⁱ entry (rightStoreⁱ ρ)

data LiftStoreⁱ {Φ Δᴸ Δᴿ} (Ψ : ImpCtx) :
    StoreImp Φ Δᴸ Δᴿ → StoreImp Ψ (suc Δᴸ) (suc Δᴿ) → Set where
  lift-store-[] :
    LiftStoreⁱ Ψ [] []

  lift-store-∷ : ∀ {ρ ρ′ α β A B p p′}
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

leftStoreⁱ-lift :
  ∀ {Φ Δᴸ Δᴿ Ψ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ (suc Δᴸ) (suc Δᴿ)} →
  LiftStoreⁱ Ψ ρ ρ′ →
  leftStoreⁱ ρ′ ≡ ⟰ᵗ (leftStoreⁱ ρ)
leftStoreⁱ-lift lift-store-[] = refl
leftStoreⁱ-lift (lift-store-∷ liftρ) =
  cong ((_,_ _ _) ∷_) (leftStoreⁱ-lift liftρ)
leftStoreⁱ-lift (lift-store-left liftρ) =
  cong ((_,_ _ _) ∷_) (leftStoreⁱ-lift liftρ)
leftStoreⁱ-lift (lift-store-right liftρ) =
  leftStoreⁱ-lift liftρ

rightStoreⁱ-lift :
  ∀ {Φ Δᴸ Δᴿ Ψ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ (suc Δᴸ) (suc Δᴿ)} →
  LiftStoreⁱ Ψ ρ ρ′ →
  rightStoreⁱ ρ′ ≡ ⟰ᵗ (rightStoreⁱ ρ)
rightStoreⁱ-lift lift-store-[] = refl
rightStoreⁱ-lift (lift-store-∷ liftρ) =
  cong ((_,_ _ _) ∷_) (rightStoreⁱ-lift liftρ)
rightStoreⁱ-lift (lift-store-left liftρ) =
  rightStoreⁱ-lift liftρ
rightStoreⁱ-lift (lift-store-right liftρ) =
  cong ((_,_ _ _) ∷_) (rightStoreⁱ-lift liftρ)

data LiftLeftStoreⁱ {Φ Δᴸ Δᴿ} (Ψ : ImpCtx) :
    StoreImp Φ Δᴸ Δᴿ → StoreImp Ψ (suc Δᴸ) Δᴿ → Set where
  lift-left-store-[] :
    LiftLeftStoreⁱ Ψ [] []

  lift-left-store-∷ : ∀ {ρ ρ′ α β A B p p′}
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

leftStoreⁱ-lift-left :
  ∀ {Φ Δᴸ Δᴿ Ψ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ Ψ ρ ρ′ →
  leftStoreⁱ ρ′ ≡ ⟰ᵗ (leftStoreⁱ ρ)
leftStoreⁱ-lift-left lift-left-store-[] = refl
leftStoreⁱ-lift-left (lift-left-store-∷ liftρ) =
  cong ((_,_ _ _) ∷_) (leftStoreⁱ-lift-left liftρ)
leftStoreⁱ-lift-left (lift-left-store-left liftρ) =
  cong ((_,_ _ _) ∷_) (leftStoreⁱ-lift-left liftρ)
leftStoreⁱ-lift-left (lift-left-store-right liftρ) =
  leftStoreⁱ-lift-left liftρ

rightStoreⁱ-lift-left :
  ∀ {Φ Δᴸ Δᴿ Ψ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ Ψ ρ ρ′ →
  rightStoreⁱ ρ′ ≡ rightStoreⁱ ρ
rightStoreⁱ-lift-left lift-left-store-[] = refl
rightStoreⁱ-lift-left (lift-left-store-∷ liftρ) =
  cong ((_,_ _ _) ∷_) (rightStoreⁱ-lift-left liftρ)
rightStoreⁱ-lift-left (lift-left-store-left liftρ) =
  rightStoreⁱ-lift-left liftρ
rightStoreⁱ-lift-left (lift-left-store-right liftρ) =
  cong ((_,_ _ _) ∷_) (rightStoreⁱ-lift-left liftρ)

data LiftRightStoreⁱ {Φ Δᴸ Δᴿ} (Ψ : ImpCtx) :
    StoreImp Φ Δᴸ Δᴿ → StoreImp Ψ Δᴸ (suc Δᴿ) → Set where
  lift-right-store-[] :
    LiftRightStoreⁱ Ψ [] []

  lift-right-store-∷ : ∀ {ρ ρ′ α β A B p p′}
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

leftStoreⁱ-lift-right :
  ∀ {Φ Δᴸ Δᴿ Ψ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ Δᴸ (suc Δᴿ)} →
  LiftRightStoreⁱ Ψ ρ ρ′ →
  leftStoreⁱ ρ′ ≡ leftStoreⁱ ρ
leftStoreⁱ-lift-right lift-right-store-[] = refl
leftStoreⁱ-lift-right (lift-right-store-∷ liftρ) =
  cong ((_,_ _ _) ∷_) (leftStoreⁱ-lift-right liftρ)
leftStoreⁱ-lift-right (lift-right-store-left liftρ) =
  cong ((_,_ _ _) ∷_) (leftStoreⁱ-lift-right liftρ)
leftStoreⁱ-lift-right (lift-right-store-right liftρ) =
  leftStoreⁱ-lift-right liftρ

rightStoreⁱ-lift-right :
  ∀ {Φ Δᴸ Δᴿ Ψ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ Δᴸ (suc Δᴿ)} →
  LiftRightStoreⁱ Ψ ρ ρ′ →
  rightStoreⁱ ρ′ ≡ ⟰ᵗ (rightStoreⁱ ρ)
rightStoreⁱ-lift-right lift-right-store-[] = refl
rightStoreⁱ-lift-right (lift-right-store-∷ liftρ) =
  cong ((_,_ _ _) ∷_) (rightStoreⁱ-lift-right liftρ)
rightStoreⁱ-lift-right (lift-right-store-left liftρ) =
  rightStoreⁱ-lift-right liftρ
rightStoreⁱ-lift-right (lift-right-store-right liftρ) =
  cong ((_,_ _ _) ∷_) (rightStoreⁱ-lift-right liftρ)

------------------------------------------------------------------------
-- Term-context imprecision
------------------------------------------------------------------------

record CtxImpEntry (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) : Set where
  constructor ctx-imp
  field
    srcTyⁱ : Ty
    tgtTyⁱ : Ty
    impTyⁱ : Φ ∣ Δᴸ ⊢ srcTyⁱ ⊑ tgtTyⁱ ⊣ Δᴿ

open CtxImpEntry public

CtxImp : ImpCtx → TyCtx → TyCtx → Set
CtxImp Φ Δᴸ Δᴿ = List (CtxImpEntry Φ Δᴸ Δᴿ)

leftCtxⁱ : CtxImp Φ Δᴸ Δᴿ → Ctx
leftCtxⁱ = map srcTyⁱ

rightCtxⁱ : CtxImp Φ Δᴸ Δᴿ → Ctx
rightCtxⁱ = map tgtTyⁱ

data LiftCtxⁱ {Φ Δᴸ Δᴿ} (Ψ : ImpCtx) :
    CtxImp Φ Δᴸ Δᴿ → CtxImp Ψ (suc Δᴸ) (suc Δᴿ) → Set where
  lift-ctx-[] :
    LiftCtxⁱ Ψ [] []

  lift-ctx-∷ : ∀ {γ γ′ A B p p′}
    → LiftCtxⁱ Ψ γ γ′
      --------------------------------------------------------------
    → LiftCtxⁱ Ψ (ctx-imp A B p ∷ γ) (ctx-imp (⇑ᵗ A) (⇑ᵗ B) p′ ∷ γ′)

leftCtxⁱ-lift :
  ∀ {Φ Δᴸ Δᴿ Ψ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ′ : CtxImp Ψ (suc Δᴸ) (suc Δᴿ)} →
  LiftCtxⁱ Ψ γ γ′ →
  leftCtxⁱ γ′ ≡ ⤊ᵗ (leftCtxⁱ γ)
leftCtxⁱ-lift lift-ctx-[] = refl
leftCtxⁱ-lift (lift-ctx-∷ liftγ) =
  cong (_ ∷_) (leftCtxⁱ-lift liftγ)

rightCtxⁱ-lift :
  ∀ {Φ Δᴸ Δᴿ Ψ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ′ : CtxImp Ψ (suc Δᴸ) (suc Δᴿ)} →
  LiftCtxⁱ Ψ γ γ′ →
  rightCtxⁱ γ′ ≡ ⤊ᵗ (rightCtxⁱ γ)
rightCtxⁱ-lift lift-ctx-[] = refl
rightCtxⁱ-lift (lift-ctx-∷ liftγ) =
  cong (_ ∷_) (rightCtxⁱ-lift liftγ)

data LiftLeftCtxⁱ {Φ Δᴸ Δᴿ} (Ψ : ImpCtx) :
    CtxImp Φ Δᴸ Δᴿ → CtxImp Ψ (suc Δᴸ) Δᴿ → Set where
  lift-left-ctx-[] :
    LiftLeftCtxⁱ Ψ [] []

  lift-left-ctx-∷ : ∀ {γ γ′ A B p p′}
    → LiftLeftCtxⁱ Ψ γ γ′
      --------------------------------------------------------------
    → LiftLeftCtxⁱ Ψ (ctx-imp A B p ∷ γ) (ctx-imp (⇑ᵗ A) B p′ ∷ γ′)

leftCtxⁱ-lift-left :
  ∀ {Φ Δᴸ Δᴿ Ψ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ′ : CtxImp Ψ (suc Δᴸ) Δᴿ} →
  LiftLeftCtxⁱ Ψ γ γ′ →
  leftCtxⁱ γ′ ≡ ⤊ᵗ (leftCtxⁱ γ)
leftCtxⁱ-lift-left lift-left-ctx-[] = refl
leftCtxⁱ-lift-left (lift-left-ctx-∷ liftγ) =
  cong (_ ∷_) (leftCtxⁱ-lift-left liftγ)

rightCtxⁱ-lift-left :
  ∀ {Φ Δᴸ Δᴿ Ψ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ′ : CtxImp Ψ (suc Δᴸ) Δᴿ} →
  LiftLeftCtxⁱ Ψ γ γ′ →
  rightCtxⁱ γ′ ≡ rightCtxⁱ γ
rightCtxⁱ-lift-left lift-left-ctx-[] = refl
rightCtxⁱ-lift-left (lift-left-ctx-∷ liftγ) =
  cong (_ ∷_) (rightCtxⁱ-lift-left liftγ)

data LiftRightCtxⁱ {Φ Δᴸ Δᴿ} (Ψ : ImpCtx) :
    CtxImp Φ Δᴸ Δᴿ → CtxImp Ψ Δᴸ (suc Δᴿ) → Set where
  lift-right-ctx-[] :
    LiftRightCtxⁱ Ψ [] []

  lift-right-ctx-∷ : ∀ {γ γ′ A B p p′}
    → LiftRightCtxⁱ Ψ γ γ′
      --------------------------------------------------------------
    → LiftRightCtxⁱ Ψ (ctx-imp A B p ∷ γ) (ctx-imp A (⇑ᵗ B) p′ ∷ γ′)

leftCtxⁱ-lift-right :
  ∀ {Φ Δᴸ Δᴿ Ψ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ (suc Δᴿ)} →
  LiftRightCtxⁱ Ψ γ γ′ →
  leftCtxⁱ γ′ ≡ leftCtxⁱ γ
leftCtxⁱ-lift-right lift-right-ctx-[] = refl
leftCtxⁱ-lift-right (lift-right-ctx-∷ liftγ) =
  cong (_ ∷_) (leftCtxⁱ-lift-right liftγ)

rightCtxⁱ-lift-right :
  ∀ {Φ Δᴸ Δᴿ Ψ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ (suc Δᴿ)} →
  LiftRightCtxⁱ Ψ γ γ′ →
  rightCtxⁱ γ′ ≡ ⤊ᵗ (rightCtxⁱ γ)
rightCtxⁱ-lift-right lift-right-ctx-[] = refl
rightCtxⁱ-lift-right (lift-right-ctx-∷ liftγ) =
  cong (_ ∷_) (rightCtxⁱ-lift-right liftγ)

leftCtxⁱ-∋ :
  ∀ {Φ Δᴸ Δᴿ γ x A B p} →
  γ ∋ x ⦂ ctx-imp A B p →
  leftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} γ ∋ x ⦂ A
leftCtxⁱ-∋ Z = Z
leftCtxⁱ-∋ (S x∈) = S (leftCtxⁱ-∋ x∈)

rightCtxⁱ-∋ :
  ∀ {Φ Δᴸ Δᴿ γ x A B p} →
  γ ∋ x ⦂ ctx-imp A B p →
  rightCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} γ ∋ x ⦂ B
rightCtxⁱ-∋ Z = Z
rightCtxⁱ-∋ (S x∈) = S (rightCtxⁱ-∋ x∈)

variable
  ρ : StoreImp Φ Δᴸ Δᴿ
  γ : CtxImp Φ Δᴸ Δᴿ

------------------------------------------------------------------------
-- Typed/well-indexed Nu-term imprecision
------------------------------------------------------------------------

infix 4 _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_

data _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_ :
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) →
    StoreImp Φ Δᴸ Δᴿ → CtxImp Φ Δᴸ Δᴿ →
    Term → Term → (A B : Ty) →
    Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ → Set₁ where

  blame⊑ᵀ : ∀ {M A B p}
    → Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M ⦂ B
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ blame ⊑ M ⦂ A ⊑ B ∶ p

  x⊑xᵀ : ∀ {x A B p}
    → γ ∋ x ⦂ ctx-imp A B p
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ ` x ⊑ ` x ⦂ A ⊑ B ∶ p

  ƛ⊑ƛᵀ : ∀ {N N′ A A′ B B′ pA pB}
    → WfTy Δᴸ A
    → WfTy Δᴿ A′
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ ctx-imp A A′ pA ∷ γ
        ⊢ᴺ N ⊑ N′ ⦂ B ⊑ B′ ∶ pB
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺ ƛ N ⊑ ƛ N′ ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB

  ·⊑·ᵀ : ∀ {L L′ M M′ A A′ B B′ pA pB}
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ L ⊑ L′
        ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ pA
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ L · M ⊑ L′ · M′ ⦂ B ⊑ B′ ∶ pB

  Λ⊑Λᵀ : ∀ {ρ′ γ′ V V′ A B p}
    → LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′
    → LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ′
    → Value V
    → Value V′
    → ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ′ ∣ γ′
        ⊢ᴺ V ⊑ V′ ⦂ A ⊑ B ∶ p
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ Λ V ⊑ Λ V′ ⦂ `∀ A ⊑ `∀ B ∶ ∀ⁱ p

  α⊑αᵀ : ∀ {ρ′ γ′ L L′ A B C D p}
    → Value L
    → No• L
    → Value L′
    → No• L′
    → (A⇑⊑B⇑ :
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ B ⊣ suc Δᴿ)
    → LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ L ⊑ L′ ⦂ `∀ C ⊑ `∀ D ∶ ∀ⁱ p
    → suc Δᴸ ∣ leftStoreⁱ (store-matched zero (⇑ᵗ A) zero (⇑ᵗ B) A⇑⊑B⇑ ∷ ρ′)
        ∣ leftCtxⁱ γ′ ⊢ (⇑ᵗᵐ L) • ⦂ C
    → suc Δᴿ ∣ rightStoreⁱ (store-matched zero (⇑ᵗ A) zero (⇑ᵗ B) A⇑⊑B⇑ ∷ ρ′)
        ∣ rightCtxⁱ γ′ ⊢ (⇑ᵗᵐ L′) • ⦂ D
      ------------------------------------------------------------
    → ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ ∣ suc Δᴿ ∣
        store-matched zero (⇑ᵗ A) zero (⇑ᵗ B) A⇑⊑B⇑ ∷ ρ′ ∣ γ′
        ⊢ᴺ (⇑ᵗᵐ L) • ⊑ (⇑ᵗᵐ L′) • ⦂ C ⊑ D ∶ p

  ν⊑νᵀ : ∀ {ρ′ γ′ A A′ B B′ C C′ N N′ p q s s′ μ μ′}
    → WfTy Δᴸ A
    → WfTy Δᴿ A′
    → μ ∣ suc Δᴸ ∣ (zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ)
        ⊢ s ∶ C ↑ˢ ⇑ᵗ B
    → μ′ ∣ suc Δᴿ ∣ (zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ)
        ⊢ s′ ∶ C′ ↑ˢ ⇑ᵗ B′
    → Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ
    → (A⇑⊑A′⇑ :
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ)
    → LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′
    → LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ′
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ N ⊑ N′
        ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺ ν A N s ⊑ ν A′ N′ s′ ⦂ B ⊑ B′ ∶ p

  ν⊑ᵀ : ∀ {ρ′ γ′ A B B′ C N N′ p q s μ}
    → WfTy Δᴸ A
    → (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A))
    → μ ∣ suc Δᴸ ∣ (zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ)
        ⊢ s ∶ C ↑ˢ ⇑ᵗ B
    → LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′
    → LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ′
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ B′ ∶ q
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ ν A N s ⊑ N′ ⦂ B ⊑ B′ ∶ p

  ⊑νᵀ : ∀ {ρ′ γ′ A B B′ C′ N N′ p q s μ}
    → WfTy Δᴿ A
    → (h⇑A : WfTy (suc Δᴿ) (⇑ᵗ A))
    → μ ∣ suc Δᴿ ∣ (zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ)
        ⊢ s ∶ C′ ↑ˢ ⇑ᵗ B′
    → LiftRightStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′
    → LiftRightCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ′
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ N ⊑ N′ ⦂ B ⊑ `∀ C′ ∶ q
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ N ⊑ ν A N′ s ⦂ B ⊑ B′ ∶ p

  νcast⊑νcastᵀ :
      ∀ {ρ′ γ′ B B′ C C′ N N′ p q s s′ μ μ′}
    → CastMode μ
    → SealModeStore★ (instᵈ μ) ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    → CastMode μ′
    → SealModeStore★ (instᵈ μ′) ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    → instᵈ μ ∣ suc Δᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
        ⊢ s ∶ C ⊑ ⇑ᵗ B
    → instᵈ μ′ ∣ suc Δᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
        ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′
    → LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′
    → LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ′
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ N ⊑ N′
        ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺ ν ★ N s ⊑ ν ★ N′ s′ ⦂ B ⊑ B′ ∶ p

  νcast⊑ᵀ : ∀ {ρ′ γ′ B B′ C N N′ p q s μ}
    → CastMode μ
    → SealModeStore★ (instᵈ μ) ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    → instᵈ μ ∣ suc Δᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
        ⊢ s ∶ C ⊑ ⇑ᵗ B
    → LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′
    → LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ′
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ B′ ∶ q
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ ν ★ N s ⊑ N′ ⦂ B ⊑ B′ ∶ p

  ⊑νcastᵀ : ∀ {ρ′ γ′ B B′ C′ N N′ p q s μ}
    → CastMode μ
    → SealModeStore★ (instᵈ μ) ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    → instᵈ μ ∣ suc Δᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
        ⊢ s ∶ C′ ⊑ ⇑ᵗ B′
    → LiftRightStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′
    → LiftRightCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ′
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ N ⊑ N′ ⦂ B ⊑ `∀ C′ ∶ q
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ N ⊑ ν ★ N′ s ⦂ B ⊑ B′ ∶ p

  κ⊑κᵀ : ∀ {n}
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺ $ (κℕ n) ⊑ $ (κℕ n) ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι

  ⊕⊑⊕ᵀ : ∀ {L L′ M M′}
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺ L ⊑ L′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺ L ⊕[ addℕ ] M ⊑ L′ ⊕[ addℕ ] M′
        ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι

  cast⊒⊑ᵀ : ∀ {M M′ A B B′ p c μ}
    → CastMode μ
    → (wfΣ : StoreDetWf Δᴸ (leftStoreⁱ ρ))
    → (seal★ : SealModeStore★ μ (leftStoreⁱ ρ))
    → (okΦ : LeftCastCtxCompatible μ Δᴸ Φ)
    → (c⊒ : μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B)
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B′ ∶ p
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⦂ B ⊑ B′
        ∶ ⊑-transˡ-castᵢ okΦ (narrowing⇒⊑ᵢ wfΣ seal★ c⊒) p

  cast⊑⊑ᵀ : ∀ {M M′ A B B′ p c μ}
    → CastMode μ
    → SealModeStore★ μ (leftStoreⁱ ρ)
    → μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B′ ∶ p
    → (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ)
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⦂ B ⊑ B′ ∶ q

  ⊑cast⊒ᵀ : ∀ {M M′ A A′ B′ p c′ μ′}
    → CastMode μ′
    → SealModeStore★ μ′ (rightStoreⁱ ρ)
    → μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p
    → (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ)
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⟨ c′ ⟩ ⦂ A ⊑ B′ ∶ q

  ⊑cast⊑ᵀ : ∀ {M M′ A A′ B′ p c′ μ′}
    → CastMode μ′
    → (wfΣ′ : StoreDetWf Δᴿ (rightStoreⁱ ρ))
    → (seal★′ : SealModeStore★ μ′ (rightStoreⁱ ρ))
    → (okΦ : RightCastCtxCompatible μ′ Δᴿ Φ)
    → (c′⊑ : μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′)
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⟨ c′ ⟩ ⦂ A ⊑ B′
        ∶ ⊑-transʳ-castᵢ okΦ p (widening⇒⊑ᵢ wfΣ′ seal★′ c′⊑)

  conv↑⊑ᵀ : ∀ {M M′ A B B′ p c μ}
    → μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ↑ˢ B
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B′ ∶ p
    → (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ)
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⦂ B ⊑ B′ ∶ q

  conv↓⊑ᵀ : ∀ {M M′ A B B′ p c μ}
    → μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ↓ˢ B
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B′ ∶ p
    → (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ)
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⦂ B ⊑ B′ ∶ q

  ⊑conv↑ᵀ : ∀ {M M′ A A′ B′ p c′ μ′}
    → μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ↑ˢ B′
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p
    → (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ)
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⟨ c′ ⟩ ⦂ A ⊑ B′ ∶ q

  ⊑conv↓ᵀ : ∀ {M M′ A A′ B′ p c′ μ′}
    → μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ↓ˢ B′
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p
    → (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ)
      ------------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⟨ c′ ⟩ ⦂ A ⊑ B′ ∶ q

------------------------------------------------------------------------
-- Derived two-sided cast rules
------------------------------------------------------------------------

cast⊒⊑cast⊒ᵀ :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A A′ B B′ p c c′ μ μ′} →
  CastMode μ →
  StoreDetWf Δᴸ (leftStoreⁱ ρ) →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  LeftCastCtxCompatible μ Δᴸ Φ →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⦂ B ⊑ B′ ∶ q
cast⊒⊑cast⊒ᵀ mode wfΣ seal★ okΦ c⊒ mode′ seal★′ c′⊒
    M⊑M′ q =
  ⊑cast⊒ᵀ mode′ seal★′ c′⊒
    (cast⊒⊑ᵀ mode wfΣ seal★ okΦ c⊒ M⊑M′) q

cast⊒⊑cast⊑ᵀ :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A A′ B B′ p c c′ μ μ′} →
  CastMode μ →
  (wfΣ : StoreDetWf Δᴸ (leftStoreⁱ ρ)) →
  (seal★ : SealModeStore★ μ (leftStoreⁱ ρ)) →
  (okΦ : LeftCastCtxCompatible μ Δᴸ Φ) →
  (c⊒ : μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B) →
  CastMode μ′ →
  (wfΣ′ : StoreDetWf Δᴿ (rightStoreⁱ ρ)) →
  (seal★′ : SealModeStore★ μ′ (rightStoreⁱ ρ)) →
  (okΦ′ : RightCastCtxCompatible μ′ Δᴿ Φ) →
  (c′⊑ : μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⦂ B ⊑ B′
    ∶ ⊑-transʳ-castᵢ okΦ′
        (⊑-transˡ-castᵢ okΦ (narrowing⇒⊑ᵢ wfΣ seal★ c⊒) p)
        (widening⇒⊑ᵢ wfΣ′ seal★′ c′⊑)
cast⊒⊑cast⊑ᵀ mode wfΣ seal★ okΦ c⊒ mode′ wfΣ′ seal★′ okΦ′
    c′⊑ M⊑M′ =
  ⊑cast⊑ᵀ mode′ wfΣ′ seal★′ okΦ′ c′⊑
    (cast⊒⊑ᵀ mode wfΣ seal★ okΦ c⊒ M⊑M′)

cast⊑⊑cast⊒ᵀ :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A A′ B B′ p c c′ μ μ′} →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  (r : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ) →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⦂ B ⊑ B′ ∶ q
cast⊑⊑cast⊒ᵀ mode seal★ c⊑ mode′ seal★′ c′⊒ M⊑M′ r q =
  ⊑cast⊒ᵀ mode′ seal★′ c′⊒
    (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ r) q

cast⊑⊑cast⊑ᵀ :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A A′ B B′ p c c′ μ μ′} →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  CastMode μ′ →
  (wfΣ′ : StoreDetWf Δᴿ (rightStoreⁱ ρ)) →
  (seal★′ : SealModeStore★ μ′ (rightStoreⁱ ρ)) →
  (okΦ′ : RightCastCtxCompatible μ′ Δᴿ Φ) →
  (c′⊑ : μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  (r : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⦂ B ⊑ B′
    ∶ ⊑-transʳ-castᵢ okΦ′ r (widening⇒⊑ᵢ wfΣ′ seal★′ c′⊑)
cast⊑⊑cast⊑ᵀ mode seal★ c⊑ mode′ wfΣ′ seal★′ okΦ′ c′⊑
    M⊑M′ r =
  ⊑cast⊑ᵀ mode′ wfΣ′ seal★′ okΦ′ c′⊑
    (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ r)

conv↑⊑conv↑ᵀ :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A A′ B B′ p c c′ μ μ′} →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ↑ˢ B →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ↑ˢ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  (r : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ) →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⦂ B ⊑ B′ ∶ q
conv↑⊑conv↑ᵀ c↑ c′↑ M⊑M′ r q =
  ⊑conv↑ᵀ c′↑ (conv↑⊑ᵀ c↑ M⊑M′ r) q

conv↑⊑conv↓ᵀ :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A A′ B B′ p c c′ μ μ′} →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ↑ˢ B →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ↓ˢ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  (r : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ) →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⦂ B ⊑ B′ ∶ q
conv↑⊑conv↓ᵀ c↑ c′↓ M⊑M′ r q =
  ⊑conv↓ᵀ c′↓ (conv↑⊑ᵀ c↑ M⊑M′ r) q

conv↓⊑conv↑ᵀ :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A A′ B B′ p c c′ μ μ′} →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ↓ˢ B →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ↑ˢ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  (r : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ) →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⦂ B ⊑ B′ ∶ q
conv↓⊑conv↑ᵀ c↓ c′↑ M⊑M′ r q =
  ⊑conv↑ᵀ c′↑ (conv↓⊑ᵀ c↓ M⊑M′ r) q

conv↓⊑conv↓ᵀ :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A A′ B B′ p c c′ μ μ′} →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ↓ˢ B →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ↓ˢ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  (r : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ) →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⦂ B ⊑ B′ ∶ q
conv↓⊑conv↓ᵀ c↓ c′↓ M⊑M′ r q =
  ⊑conv↓ᵀ c′↓ (conv↓⊑ᵀ c↓ M⊑M′ r) q

------------------------------------------------------------------------
-- Typing projections
------------------------------------------------------------------------

mutual
  nu-term-imprecision-source-typing :
    ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Δᴸ ∣ leftStoreⁱ ρ ∣ leftCtxⁱ γ ⊢ M ⦂ A

  nu-term-imprecision-target-typing :
    ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M′ ⦂ B

  nu-term-imprecision-source-typing (blame⊑ᵀ {p = p} M′⊢) =
    ⊢blame (⊑-src-wf p)
  nu-term-imprecision-source-typing (x⊑xᵀ x∈) =
    ⊢` (leftCtxⁱ-∋ x∈)
  nu-term-imprecision-source-typing (ƛ⊑ƛᵀ hA hA′ N⊑N′) =
    ⊢ƛ hA (nu-term-imprecision-source-typing N⊑N′)
  nu-term-imprecision-source-typing (·⊑·ᵀ L⊑L′ M⊑M′) =
    ⊢·
      (nu-term-imprecision-source-typing L⊑L′)
      (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (Λ⊑Λᵀ {ρ = ρ} {γ = γ} liftρ liftγ vV vV′ V⊑V′) =
    ⊢Λ vV
      (subst
        (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
        (leftCtxⁱ-lift liftγ)
        (subst
          (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
          (leftStoreⁱ-lift liftρ)
          (nu-term-imprecision-source-typing V⊑V′)))
  nu-term-imprecision-source-typing
      (α⊑αᵀ vL noL vL′ noL′ A⇑⊑B⇑ liftρ L⊑L′ L•⊢ L′•⊢) =
    L•⊢
  nu-term-imprecision-source-typing
      (ν⊑νᵀ hA hA′ s⊢ s′⊢ A⊑A′ A⇑⊑A′⇑ liftρ liftγ
        N⊑N′) =
    ⊢ν↑ hA (nu-term-imprecision-source-typing N⊑N′) s⊢
  nu-term-imprecision-source-typing
      (ν⊑ᵀ hA h⇑A s⊢ liftρ liftγ N⊑N′) =
    ⊢ν↑ hA (nu-term-imprecision-source-typing N⊑N′) s⊢
  nu-term-imprecision-source-typing
      (⊑νᵀ hA h⇑A s⊢ liftρ liftγ N⊑N′) =
    nu-term-imprecision-source-typing N⊑N′
  nu-term-imprecision-source-typing
      (νcast⊑νcastᵀ mode seal★ mode′ seal★′ s⊢ s′⊢ liftρ liftγ
        N⊑N′) =
    ⊢ν⊑ mode seal★ (nu-term-imprecision-source-typing N⊑N′) s⊢
  nu-term-imprecision-source-typing
      (νcast⊑ᵀ mode seal★ s⊢ liftρ liftγ N⊑N′) =
    ⊢ν⊑ mode seal★ (nu-term-imprecision-source-typing N⊑N′) s⊢
  nu-term-imprecision-source-typing
      (⊑νcastᵀ mode seal★ s⊢ liftρ liftγ N⊑N′) =
    nu-term-imprecision-source-typing N⊑N′
  nu-term-imprecision-source-typing κ⊑κᵀ =
    ⊢$ (κℕ _)
  nu-term-imprecision-source-typing (⊕⊑⊕ᵀ L⊑L′ M⊑M′) =
    ⊢⊕
      (nu-term-imprecision-source-typing L⊑L′)
      addℕ
      (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (cast⊒⊑ᵀ mode wfΣ seal★ okΦ c⊒ M⊑M′) =
    ⊢⟨⟩⊒ mode seal★ c⊒ (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ q) =
    ⊢⟨⟩⊑ mode seal★ c⊑ (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing (⊑cast⊒ᵀ mode′ seal★′ c′⊒ M⊑M′ q) =
    nu-term-imprecision-source-typing M⊑M′
  nu-term-imprecision-source-typing
      (⊑cast⊑ᵀ mode′ wfΣ′ seal★′ okΦ′ c′⊑ M⊑M′) =
    nu-term-imprecision-source-typing M⊑M′
  nu-term-imprecision-source-typing (conv↑⊑ᵀ c↑ M⊑M′ q) =
    ⊢⟨⟩↑ c↑ (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing (conv↓⊑ᵀ c↓ M⊑M′ q) =
    ⊢⟨⟩↓ c↓ (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing (⊑conv↑ᵀ c′↑ M⊑M′ q) =
    nu-term-imprecision-source-typing M⊑M′
  nu-term-imprecision-source-typing (⊑conv↓ᵀ c′↓ M⊑M′ q) =
    nu-term-imprecision-source-typing M⊑M′

  nu-term-imprecision-target-typing (blame⊑ᵀ M′⊢) =
    M′⊢
  nu-term-imprecision-target-typing (x⊑xᵀ x∈) =
    ⊢` (rightCtxⁱ-∋ x∈)
  nu-term-imprecision-target-typing (ƛ⊑ƛᵀ hA hA′ N⊑N′) =
    ⊢ƛ hA′ (nu-term-imprecision-target-typing N⊑N′)
  nu-term-imprecision-target-typing (·⊑·ᵀ L⊑L′ M⊑M′) =
    ⊢·
      (nu-term-imprecision-target-typing L⊑L′)
      (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing
      (Λ⊑Λᵀ {ρ = ρ} {γ = γ} liftρ liftγ vV vV′ V⊑V′) =
    ⊢Λ vV′
      (subst
        (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
        (rightCtxⁱ-lift liftγ)
        (subst
          (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
          (rightStoreⁱ-lift liftρ)
          (nu-term-imprecision-target-typing V⊑V′)))
  nu-term-imprecision-target-typing
      (α⊑αᵀ vL noL vL′ noL′ A⇑⊑B⇑ liftρ L⊑L′ L•⊢ L′•⊢) =
    L′•⊢
  nu-term-imprecision-target-typing
      (ν⊑νᵀ hA hA′ s⊢ s′⊢ A⊑A′ A⇑⊑A′⇑ liftρ liftγ
        N⊑N′) =
    ⊢ν↑ hA′ (nu-term-imprecision-target-typing N⊑N′) s′⊢
  nu-term-imprecision-target-typing
      (ν⊑ᵀ hA h⇑A s⊢ liftρ liftγ N⊑N′) =
    nu-term-imprecision-target-typing N⊑N′
  nu-term-imprecision-target-typing
      (⊑νᵀ hA h⇑A s⊢ liftρ liftγ N⊑N′) =
    ⊢ν↑ hA (nu-term-imprecision-target-typing N⊑N′) s⊢
  nu-term-imprecision-target-typing
      (νcast⊑νcastᵀ mode seal★ mode′ seal★′ s⊢ s′⊢ liftρ liftγ
        N⊑N′) =
    ⊢ν⊑ mode′ seal★′ (nu-term-imprecision-target-typing N⊑N′) s′⊢
  nu-term-imprecision-target-typing
      (νcast⊑ᵀ mode seal★ s⊢ liftρ liftγ N⊑N′) =
    nu-term-imprecision-target-typing N⊑N′
  nu-term-imprecision-target-typing
      (⊑νcastᵀ mode seal★ s⊢ liftρ liftγ N⊑N′) =
    ⊢ν⊑ mode seal★ (nu-term-imprecision-target-typing N⊑N′) s⊢
  nu-term-imprecision-target-typing κ⊑κᵀ =
    ⊢$ (κℕ _)
  nu-term-imprecision-target-typing (⊕⊑⊕ᵀ L⊑L′ M⊑M′) =
    ⊢⊕
      (nu-term-imprecision-target-typing L⊑L′)
      addℕ
      (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing
      (cast⊒⊑ᵀ mode wfΣ seal★ okΦ c⊒ M⊑M′) =
    nu-term-imprecision-target-typing M⊑M′
  nu-term-imprecision-target-typing (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ q) =
    nu-term-imprecision-target-typing M⊑M′
  nu-term-imprecision-target-typing
      (⊑cast⊒ᵀ mode′ seal★′ c′⊒ M⊑M′ q) =
    ⊢⟨⟩⊒ mode′ seal★′ c′⊒ (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing
      (⊑cast⊑ᵀ mode′ wfΣ′ seal★′ okΦ′ c′⊑ M⊑M′) =
    ⊢⟨⟩⊑ mode′ seal★′ c′⊑ (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing (conv↑⊑ᵀ c↑ M⊑M′ q) =
    nu-term-imprecision-target-typing M⊑M′
  nu-term-imprecision-target-typing (conv↓⊑ᵀ c↓ M⊑M′ q) =
    nu-term-imprecision-target-typing M⊑M′
  nu-term-imprecision-target-typing (⊑conv↑ᵀ c′↑ M⊑M′ q) =
    ⊢⟨⟩↑ c′↑ (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing (⊑conv↓ᵀ c′↓ M⊑M′ q) =
    ⊢⟨⟩↓ c′↓ (nu-term-imprecision-target-typing M⊑M′)

nu-term-imprecision-typing :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  (Δᴸ ∣ leftStoreⁱ ρ ∣ leftCtxⁱ γ ⊢ M ⦂ A) ×
  (Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M′ ⦂ B)
nu-term-imprecision-typing M⊑M′ =
  nu-term-imprecision-source-typing M⊑M′ ,
  nu-term-imprecision-target-typing M⊑M′
