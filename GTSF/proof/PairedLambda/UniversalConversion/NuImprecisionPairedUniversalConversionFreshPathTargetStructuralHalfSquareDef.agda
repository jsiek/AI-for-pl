module
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathTargetStructuralHalfSquareDef
  where

-- File Charter:
--   * Defines the structural target/imprecision half-square after inversion
--     of an outer universal target conversion and an outer source path.
--   * Exposes the binder history honestly: the distinguished source
--     occurrence is now variable one inside the source universal body, and
--     the target conversion has been lifted under its universal binder.
--   * Retains the proof-relevant source path aligned with the target path;
--     boolean source occurrence alone is insufficient for this descent.
--   * Separates reveal and conceal because their structural conversion
--     evidence remains polarity-specific.
--   * Contains no implementation, postulate, hole, permissive option,
--     paired-conversion dispatcher, handler import, or simulation import.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; ModeEnv; extᵈ)
open import Conversion using (ConcealConversion; RevealConversion)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreCorresponds
  ; StoreImp
  ; rightStoreⁱ
  )
open import Types using (Ty; TyCtx; TyVar; ⇑ᵗ; ⟰ᵗ; `∀; occurs)
open import proof.Source.FreshTypePath.NuImprecisionFreshTypePath using
  ( TypePath
  ; VarAtPath
  ; body
  )


PairedUniversalConversionFreshPathTargetStructuralRevealHalfSquareᵀ :
  Set
PairedUniversalConversionFreshPathTargetStructuralRevealHalfSquareᵀ =
  ∀ {p : TypePath} {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {B D E C′ X X′ : Ty} {d′ : Coercion}
    {η′ : ModeEnv} {α β : TyVar}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ `∀ D ⊣ Δᴿ}
    {s : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C′ ⊣ suc Δᴿ} →
  StoreCorresponds ρ α X β X′ pX →
  RevealConversion (extᵈ η′) (suc Δᴿ) (⟰ᵗ (rightStoreⁱ ρ))
    (suc β) (⇑ᵗ X′) d′ D C′ →
  occurs zero B ≡ true →
  VarAtPath zero (body p) B →
  VarAtPath (suc zero) p E →
  VarAtPath (suc zero) (body p) E


PairedUniversalConversionFreshPathTargetStructuralConcealHalfSquareᵀ :
  Set
PairedUniversalConversionFreshPathTargetStructuralConcealHalfSquareᵀ =
  ∀ {p : TypePath} {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {B D E C′ X X′ : Ty} {d′ : Coercion}
    {η′ : ModeEnv} {α β : TyVar}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ `∀ D ⊣ Δᴿ}
    {s : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C′ ⊣ suc Δᴿ} →
  StoreCorresponds ρ α X β X′ pX →
  ConcealConversion (extᵈ η′) (suc Δᴿ) (⟰ᵗ (rightStoreⁱ ρ))
    (suc β) (⇑ᵗ X′) d′ D C′ →
  occurs zero B ≡ true →
  VarAtPath zero (body p) B →
  VarAtPath (suc zero) p E →
  VarAtPath (suc zero) (body p) E
