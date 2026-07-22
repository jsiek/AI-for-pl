module
  proof.NuImprecisionPairedLambdaTargetClosingGenLeafNuClosingProof
  where

-- File Charter:
--   * Implements the `ν`-indexed generic-narrowing terminal closing handler.
--   * Uses the pre-final-reveal conversion rotation, then adds the final
--     structural source reveal at the source-lifted requested index.
--   * Contains no paired-index generic leaf, postulate, hole, permissive
--     option, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_)
import Coercions as C
open import Coercions using
  ( Coercion
  ; ModeEnv
  ; genᵈ
  ; _∣_∣_⊢_∶_=⇒_
  )
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import Conversion using (reveal-all)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ν
  )
import NarrowWiden as NW
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (No•; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( conv↑⊑ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (CastMode; SealModeStore★)
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; `∀
  ; occurs
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.MaximalLowerBoundsWf using (⊑-source-liftνᵢ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)
open import
  proof.NuImprecisionPairedLambdaTargetClosingGenLeafNuConversionRotationDef
  using (PairedLambdaTargetClosingGenLeafNuConversionRotationᵀ)


paired-lambda-target-closing-gen-leaf-ν-closing-proofᵀ :
  PairedLambdaTargetClosingGenLeafNuConversionRotationᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V N′ : Term} {A B B′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {c : Coercion} {μ : ModeEnv} →
  Value V → No• V →
  Value N′ → No• N′ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  (hA : WfTy Δᴸ A) →
  (occ : occurs zero B ≡ true) →
  genᵈ μ ∣ suc Δᴸ ∣ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ c ∶ ⇑ᵗ A =⇒ B →
  NW.Narrowing c →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B′ ∶ q →
  (occ-r : occurs zero B ≡ true) →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    (V ⟨ C.gen A c ⟩) N′ B B′ (ν _ occ-r r)
paired-lambda-target-closing-gen-leaf-ν-closing-proofᵀ
    rotation {r = r} vV noV vN′ noN′ mode seal★ hA occ-g
    g⊢ gⁿ V⊑N′ occ-r
    prefix coherent exclusive wfL h⇑A reveal liftν lift∀ conversion
    with rotation prefix vV noV vN′ noN′ mode seal★ hA occ-g
      g⊢ gⁿ V⊑N′ occ-r r h⇑A liftν lift∀ conversion
paired-lambda-target-closing-gen-leaf-ν-closing-proofᵀ
    rotation {r = r} vV noV vN′ noN′ mode seal★ hA occ-g
    g⊢ gⁿ V⊑N′ occ-r
    prefix coherent exclusive wfL h⇑A reveal liftν lift∀ conversion
    | u , rotated =
  conv↑⊑ᵀ (reveal-all reveal) rotated (⊑-source-liftνᵢ _)
