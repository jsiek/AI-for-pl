module proof.NuImprecisionPairedLambdaTargetClosingFrameViewDef where

-- File Charter:
--   * Defines a proof-relevant, world-changing frame spine for the paired
--     lambda target-closing proof.
--   * Keeps paired and quotiented frames atomic, so no unsound one-sided
--     intermediate type-imprecision index is exposed.
--   * Keeps source-only generic closing terminal while representing the
--     outer-`∀ⁱ` generic case as a recursive source frame.
--   * Uses only constructor-form term indices; plugging and frame composition
--     are deliberately absent from the data indices.
--   * Contains no classifier implementation, postulate, or permissive option.

open import Agda.Builtin.Equality using (_≡_)
import Coercions as C
open import Coercions using
  ( Coercion
  ; Inert
  ; ModeEnv
  ; genᵈ
  ; id-onlyᵈ
  ; tag-or-idᵈ
  ; _∣_∣_⊢_∶_=⇒_
  )
open import Conversion using (ConcealConversion; RevealConversion)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  ; ν
  )
import NarrowWiden as NW
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuTermImprecision using
  ( CtxImp
  ; LiftCtxⁱ
  ; LiftLeftCtxⁱ
  ; LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; Λ_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( PairedCast
  ; QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; _∣_∣_⊢_⦂_
  )
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; `∀
  ; occurs
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.NuProgress using (AllView)


data PairedLambdaTargetClosingLeaf
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} :
    ( ρ : StoreImp Φ Δᴸ Δᴿ) →
    (L L′ : Term) → (A A′ : Ty) →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) → Set₁ where

  leaf-ΛΛ :
      ∀ {ρ ρ′ γ′ V V′ A B p} →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
    LiftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) [] γ′ →
    Value V → No• V →
    Value V′ → No• V′ →
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ′ ∣ γ′
      ⊢ᴺ V ⊑ V′ ⦂ A ⊑ B ∶ p →
    PairedLambdaTargetClosingLeaf ρ
      (Λ V) (Λ V′) (`∀ A) (`∀ B) (∀ⁱ p)

  leaf-Λ :
      ∀ {ρ ρ′ γ′ V N′ A B p} →
    (occ : occurs zero A ≡ true) →
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
    LiftLeftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) [] γ′ →
    Value V → No• V →
    Value N′ → No• N′ →
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ γ′
      ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B ∶ p →
    PairedLambdaTargetClosingLeaf ρ
      (Λ V) N′ (`∀ A) B (ν _ occ p)

  leaf-gen-ν :
      ∀ {ρ V N′ A B B′ q c μ} →
    Value V → No• V →
    Value N′ → No• N′ →
    CastMode μ →
    SealModeStore★ μ (leftStoreⁱ ρ) →
    (hA : WfTy Δᴸ A) →
    (occ : occurs zero B ≡ true) →
    genᵈ μ ∣ suc Δᴸ ∣ ⟰ᵗ (leftStoreⁱ ρ)
      ⊢ c ∶ ⇑ᵗ A =⇒ B →
    (cⁿ : NW.Narrowing c) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B′ ∶ q →
    (occ-r : occurs zero B ≡ true) →
    (r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
    PairedLambdaTargetClosingLeaf ρ
      (V ⟨ C.gen A c ⟩) N′ (`∀ B) B′ (ν _ occ-r r)

  leaf-up-gen :
      ∀ {ρ M M′ X C′ D D′ B B′ pC
        d d′ u u′} →
    Value M → No• M →
    Value M′ → No• M′ →
    Inert d′ → Inert u′ →
    genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ
      ⊢ C.gen X d ∶ X ⊒ `∀ D →
    genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
      ⊢ d′ ∶ C′ ⊒ D′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ X ⊑ C′ ∶ pC →
    (qD : Φ ∣ Δᴸ ⊢ `∀ D ⊑ᵖ D′ ⊣ Δᴿ) →
    QuotientWideningPair Δᴸ Δᴿ ρ
      (C.`∀ u) u′ (`∀ D) D′ (`∀ B) B′ →
    (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ) →
    PairedLambdaTargetClosingLeaf ρ
      ((M ⟨ C.gen X d ⟩) ⟨ C.`∀ u ⟩)
      ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩)
      (`∀ B) B′ q


data PairedLambdaTargetClosingFrames
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    (ρ₀ : StoreImp Φ Δᴸ Δᴿ)
    (L L′ : Term) (A A′ : Ty)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) :
    ( ρ : StoreImp Φ Δᴸ Δᴿ) →
    (W W′ : Term) → (B B′ : Ty) →
    (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) → Set₁ where

  frame-refl :
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ₀ L L′ A A′ p

  frame-prefix :
      ∀ {ρ₁ ρ₂ W W′ B B′ q} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ₁ W W′ B B′ q →
    StoreImpPrefix ρ₁ ρ₂ →
    Δᴸ ∣ leftStoreⁱ ρ₂ ∣ [] ⊢ W ⦂ B →
    Δᴿ ∣ rightStoreⁱ ρ₂ ∣ [] ⊢ W′ ⦂ B′ →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ₂ W W′ B B′ q

  frame-cast⊒⊑ :
      ∀ {ρ W W′ B C B′ q c μ} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ (`∀ B) B′ q →
    CastMode μ →
    SealModeStore★ μ (leftStoreⁱ ρ) →
    μ ∣ Δᴸ ∣ leftStoreⁱ ρ
      ⊢ C.`∀ c ∶ `∀ B ⊒ `∀ C →
    (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ (W ⟨ C.`∀ c ⟩) W′ (`∀ C) B′ r

  frame-cast⊑⊑ :
      ∀ {ρ W W′ B C B′ q c μ} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ (`∀ B) B′ q →
    CastMode μ →
    SealModeStore★ μ (leftStoreⁱ ρ) →
    μ ∣ Δᴸ ∣ leftStoreⁱ ρ
      ⊢ C.`∀ c ∶ `∀ B ⊑ `∀ C →
    (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ (W ⟨ C.`∀ c ⟩) W′ (`∀ C) B′ r

  frame-conv↑⊑ :
      ∀ {ρ W W′ B C B′ q c μ α X} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ (`∀ B) B′ q →
    RevealConversion μ Δᴸ (leftStoreⁱ ρ)
      α X (C.`∀ c) (`∀ B) (`∀ C) →
    (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ (W ⟨ C.`∀ c ⟩) W′ (`∀ C) B′ r

  frame-conv↓⊑ :
      ∀ {ρ W W′ B C B′ q c μ α X} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ (`∀ B) B′ q →
    ConcealConversion μ Δᴸ (leftStoreⁱ ρ)
      α X (C.`∀ c) (`∀ B) (`∀ C) →
    (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ (W ⟨ C.`∀ c ⟩) W′ (`∀ C) B′ r

  frame-gen-all :
      ∀ {ρ V N′ F B B′ q c μ} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ V N′ (`∀ F) (`∀ B′) q →
    CastMode μ →
    SealModeStore★ μ (leftStoreⁱ ρ) →
    (hA : WfTy Δᴸ (`∀ F)) →
    (occ : occurs zero B ≡ true) →
    genᵈ μ ∣ suc Δᴸ ∣ ⟰ᵗ (leftStoreⁱ ρ)
      ⊢ c ∶ ⇑ᵗ (`∀ F) =⇒ B →
    NW.Narrowing c →
    (r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ) →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ (V ⟨ C.gen (`∀ F) c ⟩) N′
      (`∀ B) (`∀ B′) (∀ⁱ r)

  frame-⊑cast⊒ :
      ∀ {ρ W W′ B B′ C′ q c′ μ′} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ B B′ q →
    Inert c′ →
    CastMode μ′ →
    SealModeStore★ μ′ (rightStoreⁱ ρ) →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ B′ ⊒ C′ →
    (r : Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ Δᴿ) →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W (W′ ⟨ c′ ⟩) B C′ r

  frame-⊑cast⊑ :
      ∀ {ρ W W′ B B′ C′ q c′ μ′} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ B B′ q →
    Inert c′ →
    CastMode μ′ →
    SealModeStore★ μ′ (rightStoreⁱ ρ) →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ B′ ⊑ C′ →
    (r : Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ Δᴿ) →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W (W′ ⟨ c′ ⟩) B C′ r

  frame-⊑cast⊑id :
      ∀ {ρ W W′ B B′ C′ q c′} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ B B′ q →
    Inert c′ →
    SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) →
    id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
      ⊢ c′ ∶ B′ ⊑ C′ →
    (r : Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ Δᴿ) →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W (W′ ⟨ c′ ⟩) B C′ r

  frame-⊑conv↑ :
      ∀ {ρ W W′ B B′ C′ q c′ μ′ β X′} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ B B′ q →
    Inert c′ →
    RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
      β X′ c′ B′ C′ →
    (r : Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ Δᴿ) →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W (W′ ⟨ c′ ⟩) B C′ r

  frame-⊑conv↓ :
      ∀ {ρ W W′ B B′ C′ q c′ μ′ β X′} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ B B′ q →
    Inert c′ →
    ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
      β X′ c′ B′ C′ →
    (r : Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ Δᴿ) →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W (W′ ⟨ c′ ⟩) B C′ r

  frame-conv⊑conv :
      ∀ {ρ W W′ B C B′ C′ q r c c′} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ (`∀ B) B′ q →
    Inert c′ →
    PairedCast Φ Δᴸ Δᴿ ρ (C.`∀ c) c′ q r →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ (W ⟨ C.`∀ c ⟩) (W′ ⟨ c′ ⟩) (`∀ C) C′ r

  frame-up-id :
      ∀ {ρ M M′ C C′ D D′ B B′ pC d d′ u u′} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ M M′ (`∀ C) C′ pC →
    Inert d′ → Inert u′ →
    id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ
      ⊢ C.`∀ d ∶ `∀ C ⊒ `∀ D →
    id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ d′ ∶ C′ ⊒ D′ →
    (qD : Φ ∣ Δᴸ ⊢ `∀ D ⊑ᵖ D′ ⊣ Δᴿ) →
    QuotientWideningPair Δᴸ Δᴿ ρ
      (C.`∀ u) u′ (`∀ D) D′ (`∀ B) B′ →
    (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ) →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p ρ
      ((M ⟨ C.`∀ d ⟩) ⟨ C.`∀ u ⟩)
      ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) (`∀ B) B′ q

  frame-up-gen-all :
      ∀ {ρ M M′ C C′ D D′ B B′ pC d d′ u u′} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ M M′ (`∀ C) C′ pC →
    Inert d′ → Inert u′ →
    genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ
      ⊢ C.`∀ d ∶ `∀ C ⊒ `∀ D →
    genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
      ⊢ d′ ∶ C′ ⊒ D′ →
    (qD : Φ ∣ Δᴸ ⊢ `∀ D ⊑ᵖ D′ ⊣ Δᴿ) →
    QuotientWideningPair Δᴸ Δᴿ ρ
      (C.`∀ u) u′ (`∀ D) D′ (`∀ B) B′ →
    (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ) →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p ρ
      ((M ⟨ C.`∀ d ⟩) ⟨ C.`∀ u ⟩)
      ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) (`∀ B) B′ q


data PairedLambdaTargetClosingFrameView
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} :
    ( ρ : StoreImp Φ Δᴸ Δᴿ) →
    (W W′ : Term) → (B B′ : Ty) →
    (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) → Set₁ where

  closing-frame-view :
      ∀ {ρ₀ L L′ A A′ p ρ W W′ B B′ q} →
    PairedLambdaTargetClosingLeaf ρ₀ L L′ A A′ p →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ B B′ q →
    PairedLambdaTargetClosingFrameView ρ W W′ B B′ q


PairedLambdaTargetClosingFrameViewᵀ : Set₁
PairedLambdaTargetClosingFrameViewᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Value W →
  No• W →
  Value W′ →
  No• W′ →
  AllView W →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ A ⊑ B ∶ p →
  PairedLambdaTargetClosingFrameView ρ W W′ A B p
