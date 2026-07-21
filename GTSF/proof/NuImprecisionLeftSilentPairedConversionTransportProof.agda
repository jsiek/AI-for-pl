module proof.NuImprecisionLeftSilentPairedConversionTransportProof where

-- File Charter:
--   * Derives paired reveal/conceal transport from explicit structural
--     transport of stored and linked StoreCorresponds evidence.
--   * Transports each endpoint conversion through the ambient prefix and its
--     accumulated store changes, then restores the final result indices.
--   * Contains no recursive dispatcher or assumed projected-store recovery.

open import Agda.Builtin.Equality using (refl)
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; rename-conceal-conversion
  ; rename-reveal-conversion
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂; ∃-syntax)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_)
open import NuReduction using
  ( StoreChanges
  ; applyStores
  ; applyTyCtxs
  ; applyTys
  ; bind
  ; keep
  )
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (Term)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; paired-conceal
  ; paired-reveal
  )
open import Relation.Binary.PropositionalEquality using
  (subst; sym)
open import Store using (StoreIncl-drop)
open import TermTyping using (weakenCastᵈ)
open import Types using
  (Ty; TyCtx; TyVar)
open import proof.NuImprecisionLeftSilentPairedConversionTransportDef using
  (LeftSilentPairedConversionTransportᵀ)
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  (LineageAwareLeftSilentStoreCorrespondsTransportᵀ)
open import proof.NuImprecisionSimulationResultDef using
  ( LeftSilentInvariant
  ; WeakOneStepResult
  ; left-silent-invariant
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; sourceCtxResult
  ; sourceStoreResult
  ; targetCtxResult
  ; targetStoreResult
  )
open import proof.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.ReductionProperties using
  (applyCoercions; applyTyVars)
open import proof.TypePreservation using
  (modeRename-suc-weakenCast)
open import proof.TypeProperties using
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


result-source-reveal :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ μ α X c A B}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
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
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
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


result-target-reveal-silent :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ μ β X c A B}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  LeftSilentInvariant inner →
  RevealConversion μ Δᴿ (rightStoreⁱ ρ₀) β X c A B →
  RevealConversion μ
    (resultRightCtx inner)
    (rightStoreⁱ (resultStore inner))
    β X c A B
result-target-reveal-silent {Δᴿ = Δᴿ} prefix inner
    (left-silent-invariant refl refl) c↑ =
  subst
    (λ Δ → RevealConversion _ Δ
      (rightStoreⁱ (resultStore inner)) _ _ _ _ _)
    (sym (targetCtxResult inner))
    (subst
      (λ Σ → RevealConversion _ Δᴿ Σ _ _ _ _ _)
      (sym (targetStoreResult inner))
      (weaken-reveal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) c↑))


result-target-conceal-silent :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ μ β X c A B}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  LeftSilentInvariant inner →
  ConcealConversion μ Δᴿ (rightStoreⁱ ρ₀) β X c A B →
  ConcealConversion μ
    (resultRightCtx inner)
    (rightStoreⁱ (resultStore inner))
    β X c A B
result-target-conceal-silent {Δᴿ = Δᴿ} prefix inner
    (left-silent-invariant refl refl) c↓ =
  subst
    (λ Δ → ConcealConversion _ Δ
      (rightStoreⁱ (resultStore inner)) _ _ _ _ _)
    (sym (targetCtxResult inner))
    (subst
      (λ Σ → ConcealConversion _ Δᴿ Σ _ _ _ _ _)
      (sym (targetStoreResult inner))
      (weaken-conceal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) c↓))


left-silent-paired-conversion-transport-proofᵀ :
  LineageAwareLeftSilentStoreCorrespondsTransportᵀ →
  LeftSilentPairedConversionTransportᵀ
left-silent-paired-conversion-transport-proofᵀ
    correspondence-transport prefix inner
    silent@(left-silent-invariant refl refl) lineage coherent
    (paired-reveal corr c↑ c′↑) =
  paired-reveal
    (proj₂
      (correspondence-transport prefix inner silent lineage corr))
    (proj₂ (result-source-reveal prefix inner c↑))
    (result-target-reveal-silent prefix inner silent c′↑)
left-silent-paired-conversion-transport-proofᵀ
    correspondence-transport prefix inner
    silent@(left-silent-invariant refl refl) lineage coherent
    (paired-conceal corr c↓ c′↓) =
  paired-conceal
    (proj₂
      (correspondence-transport prefix inner silent lineage corr))
    (proj₂ (result-source-conceal prefix inner c↓))
    (result-target-conceal-silent prefix inner silent c′↓)
