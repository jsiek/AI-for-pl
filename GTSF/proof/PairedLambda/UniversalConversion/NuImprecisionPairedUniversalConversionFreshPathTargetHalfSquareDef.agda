module
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathTargetHalfSquareDef
  where

-- File Charter:
--   * Defines the target/imprecision half of fresh-path transport around a
--     source-only-to-paired universal-conversion square.
--   * Retains the exact TypePath prefix so structural descent cannot forget
--     which source and target branches contain the fresh source variable.
--   * Separates reveal and conceal because their target conversion proofs
--     have different active terminal cases.
--   * Contains no implementation, postulate, hole, permissive option,
--     paired-conversion dispatcher, handler import, or broad simulation
--     import.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; ModeEnv)
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
open import Types using (Ty; TyCtx; TyVar; `∀; occurs)
open import proof.Source.FreshTypePath.NuImprecisionFreshTypePath using
  ( TypePath
  ; VarAtPath
  ; body
  )


PairedUniversalConversionFreshPathTargetRevealHalfSquareᵀ : Set
PairedUniversalConversionFreshPathTargetRevealHalfSquareᵀ =
  ∀ {p : TypePath} {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {B B′ E C′ X X′ : Ty} {c′ : Coercion}
    {η′ : ModeEnv} {α β : TyVar}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {s : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C′ ⊣ suc Δᴿ} →
  StoreCorresponds ρ α X β X′ pX →
  RevealConversion η′ Δᴿ (rightStoreⁱ ρ) β X′ c′
    B′ (`∀ C′) →
  occurs zero B ≡ true →
  VarAtPath zero p B →
  VarAtPath zero p (`∀ E) →
  VarAtPath zero (body p) (`∀ E)


PairedUniversalConversionFreshPathTargetConcealHalfSquareᵀ : Set
PairedUniversalConversionFreshPathTargetConcealHalfSquareᵀ =
  ∀ {p : TypePath} {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {B B′ E C′ X X′ : Ty} {c′ : Coercion}
    {η′ : ModeEnv} {α β : TyVar}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {s : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C′ ⊣ suc Δᴿ} →
  StoreCorresponds ρ α X β X′ pX →
  ConcealConversion η′ Δᴿ (rightStoreⁱ ρ) β X′ c′
    B′ (`∀ C′) →
  occurs zero B ≡ true →
  VarAtPath zero p B →
  VarAtPath zero p (`∀ E) →
  VarAtPath zero (body p) (`∀ E)
