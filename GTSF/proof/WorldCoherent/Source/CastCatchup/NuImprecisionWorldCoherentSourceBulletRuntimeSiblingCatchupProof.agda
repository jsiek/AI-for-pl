module
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceBulletRuntimeSiblingCatchupProof
  where

-- File Charter:
--   * Carries one independent source-no-bullet, target-runtime sibling
--     through source-only post-allocation bullet catch-up.
--   * Reconstructs the allocated `α` relation exactly as ordinary
--     source-bullet catch-up does, then delegates both relations to the
--     ambient value runtime-sibling contract.
--   * Contains no recursive dispatcher implementation, postulate, hole,
--     allocation recovery, or permissive option.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_; Σ-syntax)

open import ImprecisionWf using
  ( ImpCtx
  ; NonVar
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ν
  )
open import NuReduction using
  ( applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  ; keep
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-left
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImpEntry
  ; LiftLeftCtxⁱ
  ; leftCtxⁱ
  ; rightCtxⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; ⇑ᵗᵐ
  ; _•
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; α⊑ᵀ
  ; prefix-reflⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; `∀
  ; ⇑ᵗ
  ; occurs
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( catchupIndexedResult
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentLeftCatchupIndexedResult
  ; worldCatchupResult
  )
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupRuntimeSiblingPrefixDef
  using (WorldCoherentLeftValueCatchupRuntimeSiblingAmbientᵀ)


world-coherent-source-bullet-runtime-sibling-catchup-proofᵀ :
  WorldCoherentLeftValueCatchupRuntimeSiblingAmbientᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ ρ⁺ : StoreImp
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {L V′ R R′ : Term} {A B′ C E E′ : Ty}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
    {{safe : NonVar C}}
    {occ : occurs zero C ≡ true} →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  StoreImpPrefix
    (store-left zero (⇑ᵗ A) h⇑A ∷ ρ′) ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) →
  AssumptionMembershipUnique ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) →
  StoreWf (suc Δᴸ) (leftStoreⁱ ρ⁺) →
  RuntimeOK ((⇑ᵗᵐ L) •) →
  Value V′ →
  No• V′ →
  Value L →
  No• L →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ([] {A = CtxImpEntry Φ Δᴸ Δᴿ})
    ([] {A = CtxImpEntry
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ V′ ⦂ `∀ C ⊑ B′ ∶ ν safe occ p →
  suc Δᴸ
    ∣ leftStoreⁱ (store-left zero (⇑ᵗ A) h⇑A ∷ ρ′)
    ∣ leftCtxⁱ ([] {A = CtxImpEntry
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ})
    ⊢ (⇑ᵗᵐ L) • ⦂ C →
  Δᴿ
    ∣ rightStoreⁱ (store-left zero (⇑ᵗ A) h⇑A ∷ ρ′)
    ∣ rightCtxⁱ ([] {A = CtxImpEntry
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ})
    ⊢ V′ ⦂ B′ →
  No• R →
  RuntimeOK R′ →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ []
    ⊢ᴺ R ⊑ R′ ⦂ E ⊑ E′ ∶ r →
  Σ[ caught ∈
    WorldCoherentLeftCatchupIndexedResult
      {N = (⇑ᵗᵐ L) •} {V′ = V′} {ρ = ρ⁺} p ]
    let result =
          weakIndexedResult
            (catchupIndexedResult (worldCatchupResult caught))
    in
    resultCtx result
      ∣ resultLeftCtx result
      ∣ resultRightCtx result
      ∣ resultStore result ∣ []
      ⊢ᴺ applyTerms (sourceChanges result) R
        ⊑ applyTerms (targetTailChanges result) (applyTerm keep R′)
      ⦂ applyTys (sourceChanges result) E
        ⊑ applyTys (targetTailChanges result) (applyTy keep E′)
      ∶ transportType result r
world-coherent-source-bullet-runtime-sibling-catchup-proofᵀ
    value-sibling h⇑A prefix coherent exclusive unique wfL okL•
    vV′ noV′ vL noL liftρ liftγ L⊑V′ L•⊢ V′⊢
    noR okR′ sibling =
  value-sibling prefix coherent exclusive unique wfL okL•
    vV′ noV′
    (α⊑ᵀ vL noL h⇑A liftρ liftγ L⊑V′
      prefix-reflⁱ L•⊢ V′⊢)
    noR okR′ sibling
