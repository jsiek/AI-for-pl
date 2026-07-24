module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationFunctionContinuationFromSourceOnlyContextDef
  where

-- File Charter:
--   * Defines the source-only-incoming, source-only-function-final cell of
--     the contextual target-instantiation continuation.
--   * Retains both transported source-only indices and never reopens the
--     absent target binder as an independent right-only binder.
--   * Exposes target-context action and right-only store lineage beside the
--     continuation in the completed inner result world.
--   * Contains no implementation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; ModeEnv; inst)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; Σ-syntax)
open import Imprecision using
  ( NonVar
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  )
open import ImprecisionWf using
  (ImpCtx; ν; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  (StoreImpPrefix)
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using
  (Ty; TyCtx; ★; occurs; _⇒_; `∀)
open import proof.Right.Core.NuImprecisionRightContextAction using
  (applyRightImpCtxChanges)
open import proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix using
  (RightOnlyStoreImpPrefix)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
  using (rightCatchupIndexedResult)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( resultCtx
  ; resultStore
  ; sourceResult
  ; targetResult
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (lineageStore)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  ; worldRightCatchupStoreLineage
  )
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)


WorldCoherentRightTargetWidenInstantiationFunctionContinuationFromSourceOnlyContextᵀ :
  Set₁
WorldCoherentRightTargetWidenInstantiationFunctionContinuationFromSourceOnlyContextᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {C D : Ty} {s : Coercion} {μ : ModeEnv}
    {safeₚ safeq : NonVar D}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ `∀ C ⊣ Δᴿ}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ ★ ⇒ ★ ⊣ Δᴿ}
    {occₚ occq : occurs zero D ≡ true} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ inst (★ ⇒ ★) s ∶ `∀ C ⊑ ★ ⇒ ★ →
  (inner : WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} (ν safeₚ occₚ r)) →
  let indexed = rightCatchupIndexedResult
        (worldRightCatchupResult inner)
      result = weakIndexedResult indexed
  in
  resultCtx result ≡
    applyRightImpCtxChanges (targetTailChanges result) Φ →
  RightOnlyStoreImpPrefix
    (lineageStore (worldRightCatchupStoreLineage inner))
    (resultStore result) →
  Σ[ continued ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = sourceResult result}
      {M′ =
        targetResult result
          ⟨ applyCoercions (targetTailChanges result)
              (inst (★ ⇒ ★) s) ⟩}
      {ρ = resultStore result}
      (transportType result (ν safeq occq q)) ]
    (resultCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult continued)))
      ≡
      applyRightImpCtxChanges
        (targetTailChanges
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult continued))))
        (resultCtx result))
    ×
    RightOnlyStoreImpPrefix
      (lineageStore (worldRightCatchupStoreLineage continued))
      (resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult continued))))
