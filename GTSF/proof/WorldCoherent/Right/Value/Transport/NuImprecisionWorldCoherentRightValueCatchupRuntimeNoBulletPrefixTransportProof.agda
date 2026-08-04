module
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletPrefixTransportProof
  where

-- File Charter:
--   * Transports no-runtime-bullet term imprecision and fixed narrowings
--     through a world-coherent right-value catch-up prefix.
--   * Isolates stable allocation-prefix reasoning from the active QTI
--     recursion in the main transport proof.
--   * Contains no term-imprecision case analysis, postulate, hole, or
--     termination bypass.

open import proof.Store.Prefix.NuImprecisionTermStorePrefixLemma using
  (term-imprecision-store-prefixᵀ)
open import Data.List using (_∷_; [])
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( applyCoercion
  ; applyTerm
  ; applyTerms
  ; applyTy
  ; applyTyCtx
  ; applyTyCtxs
  ; applyTys
  ; keep
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (No•; Term)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import
  proof.NuCore.Relations.NuImprecisionQuotientedTyping
  using
  ( nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  )
open import
  proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
  using (rightCatchupIndexedResult)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepResult
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; sourceCtxResult
  ; sourceStoreResult
  ; targetTailChanges
  ; targetCtxResult
  ; targetStoreResult
  ; transportNo•Terms
  ; transportType
  ; weakIndexedResult
  ; weakIndexedTransport
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  )
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  )
open import
  proof.Core.Properties.NuNarrowingTransport
  using (apply-fixed-narrows-typing)
open import
  proof.Core.Properties.CoercionProperties
  using (ModeRename)
open import
  proof.Core.Properties.ReductionProperties
  using (applyCoercions)
open import
  proof.Core.Properties.TypePreservation
  using (term-weaken)
open import NarrowWiden using
  ( narrow-weaken
  ; _∣_∣_⊢_∶_⊒_
  )
open import Types using (Ty; TyCtx)


no-bullet-prefix-transportᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {V N′ M M′ : Term} {A A′ C C′ : Ty}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  No• M →
  No• M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ C ⊑ C′ ∶ q →
  (caught : WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = N′} {ρ = ρ⁺} p) →
  resultCtx
      (weakIndexedResult
        (rightCatchupIndexedResult
          (worldRightCatchupResult caught)))
    ∣ resultLeftCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))
    ∣ resultRightCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))
    ∣ resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))
    ∣ []
    ⊢ᴺ applyTerms
          (sourceChanges
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))))
          M
      ⊑ applyTerms
          (targetTailChanges
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))))
          (applyTerm keep M′)
    ⦂ applyTys
          (sourceChanges
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))))
          C
      ⊑ applyTys
          (targetTailChanges
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))))
          (applyTy keep C′)
    ∶ transportType
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))
        q
no-bullet-prefix-transportᵀ prefix noM noM′ M⊑M′ caught =
  transportNo•Terms
    (weakIndexedTransport
      (rightCatchupIndexedResult (worldRightCatchupResult caught)))
    noM noM′ relation⁺
  where
  source-typing⁺ =
    term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
      noM (nu-term-imprecision-source-typing M⊑M′)

  target-typing⁺ =
    term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
      noM′ (nu-term-imprecision-target-typing M⊑M′)

  relation⁺ =
    term-imprecision-store-prefixᵀ prefix M⊑M′ source-typing⁺ target-typing⁺


right-catchup-source-fixed-narrowingᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {M M′ : Term} {C C′ E F : Ty} {μ} {d}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  ModeRename suc μ μ →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ d ∶ E ⊒ F →
  μ ∣ resultLeftCtx inner ∣ leftStoreⁱ (resultStore inner)
    ⊢ applyCoercions (sourceChanges inner) d
      ∶ applyTys (sourceChanges inner) E
        ⊒ applyTys (sourceChanges inner) F
right-catchup-source-fixed-narrowingᵀ
    {Δᴸ = Δᴸ} mode-suc prefix inner d⊒ =
  subst
    (λ Δ → _ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) _
        ∶ applyTys (sourceChanges inner) _
          ⊒ applyTys (sourceChanges inner) _)
    (sym (sourceCtxResult inner))
    (subst
      (λ Σ → _ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
        ⊢ applyCoercions (sourceChanges inner) _
          ∶ applyTys (sourceChanges inner) _
            ⊒ applyTys (sourceChanges inner) _)
      (sym (sourceStoreResult inner))
      (apply-fixed-narrows-typing
        {χs = sourceChanges inner} mode-suc
        (narrow-weaken ≤-refl
          (leftStoreⁱ-prefix-inclusion prefix) d⊒)))


weak-one-step-transport-target-fixed-narrowingᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {M M′ : Term} {C C′ E′ F′ : Ty} {μ} {d′}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  ModeRename suc μ μ →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ d′ ∶ E′ ⊒ F′ →
  μ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
    ⊢ applyCoercions (targetTailChanges inner) (applyCoercion keep d′)
      ∶ applyTys (targetTailChanges inner) (applyTy keep E′)
        ⊒ applyTys (targetTailChanges inner) (applyTy keep F′)
weak-one-step-transport-target-fixed-narrowingᵀ
    {Δᴿ = Δᴿ} mode-suc prefix inner d′⊒ =
  subst
    (λ Δ → _ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
      ⊢ applyCoercions (targetTailChanges inner) (applyCoercion keep _)
        ∶ applyTys (targetTailChanges inner) (applyTy keep _)
          ⊒ applyTys (targetTailChanges inner) (applyTy keep _))
    (sym (targetCtxResult inner))
    (subst
      (λ Σ → _
        ∣ applyTyCtxs (targetTailChanges inner) (applyTyCtx keep Δᴿ)
        ∣ Σ
        ⊢ applyCoercions (targetTailChanges inner) (applyCoercion keep _)
          ∶ applyTys (targetTailChanges inner) (applyTy keep _)
            ⊒ applyTys (targetTailChanges inner) (applyTy keep _))
      (sym (targetStoreResult inner))
      (apply-fixed-narrows-typing
        {χs = keep ∷ targetTailChanges inner}
        mode-suc
        (narrow-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) d′⊒)))
