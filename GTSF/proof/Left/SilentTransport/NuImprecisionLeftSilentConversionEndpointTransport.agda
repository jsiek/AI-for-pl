module
  proof.Left.SilentTransport.NuImprecisionLeftSilentConversionEndpointTransport
  where

-- File Charter:
--   * Transports source reveal and conceal conversion endpoints through a
--     completed weak one-step result and an ambient store prefix.
--   * Restores the result context and store indices exactly.
--   * Contains no paired-conversion aggregate or term-imprecision constructor.

open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import Data.Product using (_,_; proj₁; proj₂; ∃-syntax)
open import NuReduction using
  (StoreChange; applyTyCtxs; applyTys)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using (Term)
open import QuotientedTermImprecision using
  (StoreImpPrefix)
open import Relation.Binary.PropositionalEquality using
  (subst; sym)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepResult
  ; resultLeftCtx
  ; resultStore
  ; sourceChanges
  ; sourceCtxResult
  ; sourceStoreResult
  )
open import proof.Core.Properties.NuConversionTransport using
  (apply-conceal-conversions-exact; apply-reveal-conversions-exact)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; applyTyVars)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion)


result-source-reveal :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ μ α X c A B}
    {χ : StoreChange}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ χ) →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
  ∃[ μ′ ]
    RevealConversion μ′
      (resultLeftCtx inner)
      (leftStoreⁱ (resultStore inner))
      (applyTyVars (sourceChanges inner) α)
      (applyTys (sourceChanges inner) X)
      (applyCoercions (sourceChanges inner) c)
      (applyTys (sourceChanges inner) A)
      (applyTys (sourceChanges inner) B)
result-source-reveal
    {Δᴸ = Δᴸ} {α = α} {X = X} {c = c} {A = A} {B = B}
    prefix inner c↑ =
  final-mode , final
  where
  applied =
    apply-reveal-conversions-exact
      {χs = sourceChanges inner}
      (weaken-reveal-conversion
        (leftStoreⁱ-prefix-inclusion prefix) c↑)

  final-mode = proj₁ applied

  final :
    RevealConversion final-mode
      (resultLeftCtx inner)
      (leftStoreⁱ (resultStore inner))
      (applyTyVars (sourceChanges inner) α)
      (applyTys (sourceChanges inner) X)
      (applyCoercions (sourceChanges inner) c)
      (applyTys (sourceChanges inner) A)
      (applyTys (sourceChanges inner) B)
  final =
    subst
      (λ Δ → RevealConversion final-mode Δ
        (leftStoreⁱ (resultStore inner))
        (applyTyVars (sourceChanges inner) α)
        (applyTys (sourceChanges inner) X)
        (applyCoercions (sourceChanges inner) c)
        (applyTys (sourceChanges inner) A)
        (applyTys (sourceChanges inner) B))
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → RevealConversion final-mode
          (applyTyCtxs (sourceChanges inner) Δᴸ) Σ
          (applyTyVars (sourceChanges inner) α)
          (applyTys (sourceChanges inner) X)
          (applyCoercions (sourceChanges inner) c)
          (applyTys (sourceChanges inner) A)
          (applyTys (sourceChanges inner) B))
        (sym (sourceStoreResult inner))
        (proj₂ applied))


result-source-conceal :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ μ α X c A B}
    {χ : StoreChange}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ χ) →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
  ∃[ μ′ ]
    ConcealConversion μ′
      (resultLeftCtx inner)
      (leftStoreⁱ (resultStore inner))
      (applyTyVars (sourceChanges inner) α)
      (applyTys (sourceChanges inner) X)
      (applyCoercions (sourceChanges inner) c)
      (applyTys (sourceChanges inner) A)
      (applyTys (sourceChanges inner) B)
result-source-conceal
    {Δᴸ = Δᴸ} {α = α} {X = X} {c = c} {A = A} {B = B}
    prefix inner c↓ =
  final-mode , final
  where
  applied =
    apply-conceal-conversions-exact
      {χs = sourceChanges inner}
      (weaken-conceal-conversion
        (leftStoreⁱ-prefix-inclusion prefix) c↓)

  final-mode = proj₁ applied

  final :
    ConcealConversion final-mode
      (resultLeftCtx inner)
      (leftStoreⁱ (resultStore inner))
      (applyTyVars (sourceChanges inner) α)
      (applyTys (sourceChanges inner) X)
      (applyCoercions (sourceChanges inner) c)
      (applyTys (sourceChanges inner) A)
      (applyTys (sourceChanges inner) B)
  final =
    subst
      (λ Δ → ConcealConversion final-mode Δ
        (leftStoreⁱ (resultStore inner))
        (applyTyVars (sourceChanges inner) α)
        (applyTys (sourceChanges inner) X)
        (applyCoercions (sourceChanges inner) c)
        (applyTys (sourceChanges inner) A)
        (applyTys (sourceChanges inner) B))
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → ConcealConversion final-mode
          (applyTyCtxs (sourceChanges inner) Δᴸ) Σ
          (applyTyVars (sourceChanges inner) α)
          (applyTys (sourceChanges inner) X)
          (applyCoercions (sourceChanges inner) c)
          (applyTys (sourceChanges inner) A)
          (applyTys (sourceChanges inner) B))
        (sym (sourceStoreResult inner))
        (proj₂ applied))
