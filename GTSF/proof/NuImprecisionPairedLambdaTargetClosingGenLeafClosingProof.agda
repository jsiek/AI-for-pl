module proof.NuImprecisionPairedLambdaTargetClosingGenLeafClosingProof where

-- File Charter:
--   * Assembles the complete generic-narrowing terminal handler from its two
--     genuine outer-index branch capabilities.
--   * Delegates the structural-all branch unchanged, and adds the final
--     source reveal after the `ν` branch's paired-conversion rotation.
--   * Contains no implementation of either missing branch theorem, broad
--     simulation import, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (_≡_)
import Coercions as C
open import Coercions using
  ( Coercion
  ; ModeEnv
  ; genᵈ
  ; _∣_∣_⊢_∶_=⇒_
  )
open import Conversion using (RevealConversion; reveal-all)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
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
open import NuTermImprecision using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; store-left
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( PairedConversion
  ; StoreImpPrefix
  ; conv↑⊑ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  )
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; `∀
  ; extᵗ
  ; occurs
  ; renameᵗ
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.MaximalLowerBoundsWf using (⊑-source-liftνᵢ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingGenLeafAllIndexClosingDef
  using (PairedLambdaTargetClosingGenLeafAllIndexClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingGenLeafNuConversionRotationDef
  using (PairedLambdaTargetClosingGenLeafNuConversionRotationᵀ)


paired-lambda-target-closing-gen-leaf-closing-proofᵀ :
  PairedLambdaTargetClosingGenLeafNuConversionRotationᵀ →
  PairedLambdaTargetClosingGenLeafAllIndexClosingᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {V N′ : Term} {A B B′ : Ty}
    {q₀ : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {g : Coercion} {μ₀ : ModeEnv} →
  Value V → No• V →
  Value N′ → No• N′ →
  CastMode μ₀ →
  SealModeStore★ μ₀ (leftStoreⁱ ρ₀) →
  (hA : WfTy Δᴸ A) →
  (occ : occurs zero B ≡ true) →
  genᵈ μ₀ ∣ suc Δᴸ ∣ ⟰ᵗ (leftStoreⁱ ρ₀)
    ⊢ g ∶ ⇑ᵗ A =⇒ B →
  NW.Narrowing g →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B′ ∶ q₀ →
  (r : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ) →
  ∀ {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {Aν C′ D E : Ty} {c c′ t : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C′ ⊣ Δᴿ}
    {s : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C′ ⊣ suc Δᴿ} →
  StoreImpPrefix ρ₀ ρ →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  RevealConversion (C.extᵈ μ) (suc (suc Δᴸ))
    (⟰ᵗ (leftStoreⁱ
      (store-left zero (⇑ᵗ Aν) h⇑A ∷ ρν)))
    (suc zero) (⇑ᵗ (⇑ᵗ Aν)) t E
    (renameᵗ (extᵗ suc) D) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′
    {`∀ B} {B′} {`∀ (`∀ E)} {`∀ C′} r (∀ⁱ s) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣
      store-left zero (⇑ᵗ Aν) h⇑A ∷ ρν ∣ []
    ⊢ᴺ (((⇑ᵗᵐ (V ⟨ C.gen A g ⟩)) •) ⟨ c ⟩) ⟨ C.`∀ t ⟩
      ⊑ N′ ⟨ c′ ⟩
      ⦂ ⇑ᵗ (`∀ D) ⊑ `∀ C′ ∶ ⊑-source-liftνᵢ p
paired-lambda-target-closing-gen-leaf-closing-proofᵀ
    rotation all-closing vV noV vN′ noN′ mode seal★ hA occ-g
    g⊒ gⁿ V⊑N′ (∀ⁱ r)
    prefix h⇑A reveal liftν lift∀ conversion =
  all-closing vV noV vN′ noN′ mode seal★ hA occ-g
    g⊒ gⁿ V⊑N′ r prefix h⇑A reveal liftν lift∀ conversion
paired-lambda-target-closing-gen-leaf-closing-proofᵀ
    rotation all-closing vV noV vN′ noN′ mode seal★ hA occ-g
    g⊒ gⁿ V⊑N′ (ν occ-r r)
    {p = p}
    prefix h⇑A reveal liftν lift∀ conversion
    with rotation prefix vV noV vN′ noN′ mode seal★ hA occ-g
      g⊒ gⁿ V⊑N′ occ-r r h⇑A liftν lift∀ conversion
paired-lambda-target-closing-gen-leaf-closing-proofᵀ
    rotation all-closing vV noV vN′ noN′ mode seal★ hA occ-g
    g⊒ gⁿ V⊑N′ (ν occ-r r)
    {p = p}
    prefix h⇑A reveal liftν lift∀ conversion
    | u , rotated =
  conv↑⊑ᵀ (reveal-all reveal) rotated (⊑-source-liftνᵢ p)
