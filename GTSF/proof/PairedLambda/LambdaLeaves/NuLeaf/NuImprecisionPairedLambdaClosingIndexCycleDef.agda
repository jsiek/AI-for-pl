module proof.PairedLambda.LambdaLeaves.NuLeaf.NuImprecisionPairedLambdaClosingIndexCycleDef where

-- File Charter:
--   * Defines the pure type-index cycle exposed by matched-`Lambda` target
--     closing after the final fresh reveal identifies its two source bodies.
--   * States that an ambient extra target universal and its one-binder matched
--     view cannot coexist for the same finite source body.
--   * Contains no implementation, conversion, store, term relation,
--     simulation, postulate, hole, permissive option, or broad proof import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; _∣_⊢_⊑_⊣_
  )
open import Types using (Ty; TyCtx; `∀; extᵗ; renameᵗ; ⇑ᵗ)


PairedLambdaClosingIndexCycleᵀ : Set
PairedLambdaClosingIndexCycleᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} {F D X′ : Ty} →
  F ≡ D →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ
    ⊢ `∀ (renameᵗ (extᵗ suc) F) ⊑ ⇑ᵗ X′
    ⊣ suc Δᴿ →
  Φ ∣ Δᴸ
    ⊢ `∀ D ⊑ `∀ (⇑ᵗ X′)
    ⊣ Δᴿ →
  ⊥
