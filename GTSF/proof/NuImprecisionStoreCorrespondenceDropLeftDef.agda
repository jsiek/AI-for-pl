module
  proof.NuImprecisionStoreCorrespondenceDropLeftDef
  where

-- File Charter:
--   * Defines exact removal of a source-only store lift from a stored or
--     linked correspondence.
--   * Preserves both endpoint types rather than returning only the origin
--     name, as required by inverse world-coherence transport.
--   * Contains no implementation, term relation, postulate, hole,
--     permissive option, or broad simulation import.

open import Data.Product using (∃-syntax)
open import Data.Nat using (suc)
open import ImprecisionWf using (ImpCtx)
open import NuTermImprecision using
  (LiftLeftStoreⁱ; StoreCorresponds; StoreImp)
open import Types using (Ty; TyCtx; TyVar; ⇑ᵗ)


StoreCorrespondenceDropLeftᵀ : Set
StoreCorrespondenceDropLeftᵀ =
  ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴸ : StoreImp Ψ (suc Δᴸ) Δᴿ}
    {α β : TyVar} {A B : Ty} {pᴸ} →
  LiftLeftStoreⁱ Ψ ρ ρᴸ →
  StoreCorresponds ρᴸ
    (suc α) (⇑ᵗ A) β B pᴸ →
  ∃[ p ] StoreCorresponds ρ α A β B p
