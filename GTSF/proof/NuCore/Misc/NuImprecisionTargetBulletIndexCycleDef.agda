module proof.NuCore.Misc.NuImprecisionTargetBulletIndexCycleDef where

-- File Charter:
--   * Defines the type-only obstruction carried by a target runtime bullet.
--   * States that a type cannot lie below both a target body and the
--     uniformly raised universal over that body.
--   * Contains no implementation, store, term relation, simulation,
--     postulate, hole, permissive option, or broad proof import.

open import Data.Empty using (⊥)
open import Data.Nat using (suc)

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_; ⇑ᴿᵢ)
open import Types using (Ty; TyCtx; `∀)


TargetBulletIndexCycleᵀ : Set
TargetBulletIndexCycleᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} {B C′ : Ty} →
  Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ →
  ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ →
  ⊥
