module proof.Core.Properties.NuConversionTransport where

-- File Charter:
--   * Transports reveal and conceal conversions through runtime store changes.
--   * Preserves the exact transported name, type, coercion, and endpoints.
--   * Contains no term-imprecision, simulation-result, or world dependency.

open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; rename-conceal-conversion
  ; rename-reveal-conversion
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; ∃-syntax)
open import NuReduction using
  (StoreChanges; applyStores; applyTyCtxs; applyTys; bind; keep)
open import Store using (StoreIncl-drop)
open import TermTyping using (weakenCastᵈ)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; applyTyVars)
open import proof.Core.Properties.TypePreservation using
  (modeRename-suc-weakenCast)
open import proof.Core.Properties.TypeProperties using
  (TyRenameWf-suc)


apply-reveal-conversions-exact :
  ∀ {χs : StoreChanges} {μ Δ Σ α X c A B} →
  RevealConversion μ Δ Σ α X c A B →
  ∃[ μ′ ]
    RevealConversion μ′
      (applyTyCtxs χs Δ)
      (applyStores χs Σ)
      (applyTyVars χs α)
      (applyTys χs X)
      (applyCoercions χs c)
      (applyTys χs A)
      (applyTys χs B)
apply-reveal-conversions-exact {χs = []} {μ = μ} c↑ =
  μ , c↑
apply-reveal-conversions-exact {χs = keep ∷ χs} c↑ =
  apply-reveal-conversions-exact {χs = χs} c↑
apply-reveal-conversions-exact
    {χs = bind Aχ ∷ χs} {μ = μ} c↑ =
  apply-reveal-conversions-exact
    {χs = χs} {μ = weakenCastᵈ μ}
    (weaken-reveal-conversion StoreIncl-drop
      (rename-reveal-conversion
        {ν = weakenCastᵈ μ}
        TyRenameWf-suc modeRename-suc-weakenCast c↑))


apply-conceal-conversions-exact :
  ∀ {χs : StoreChanges} {μ Δ Σ α X c A B} →
  ConcealConversion μ Δ Σ α X c A B →
  ∃[ μ′ ]
    ConcealConversion μ′
      (applyTyCtxs χs Δ)
      (applyStores χs Σ)
      (applyTyVars χs α)
      (applyTys χs X)
      (applyCoercions χs c)
      (applyTys χs A)
      (applyTys χs B)
apply-conceal-conversions-exact {χs = []} {μ = μ} c↓ =
  μ , c↓
apply-conceal-conversions-exact {χs = keep ∷ χs} c↓ =
  apply-conceal-conversions-exact {χs = χs} c↓
apply-conceal-conversions-exact
    {χs = bind Aχ ∷ χs} {μ = μ} c↓ =
  apply-conceal-conversions-exact
    {χs = χs} {μ = weakenCastᵈ μ}
    (weaken-conceal-conversion StoreIncl-drop
      (rename-conceal-conversion
        {ν = weakenCastᵈ μ}
        TyRenameWf-suc modeRename-suc-weakenCast c↓))
