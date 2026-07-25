module
  proof.WorldCoherent.Final.Paired.NuImprecisionWorldCoherentFinalPairedCastRuntimeSiblingCatchupDef
  where

-- File Charter:
--   * Defines exact-final paired-cast catch-up while carrying one independent
--     source-no-bullet, target-runtime sibling.
--   * Covers paired conversions and compatible paired widenings after the
--     cast operand has reached a value or blame.
--   * Returns the caught result and sibling at one shared exact final world;
--     the conclusion is stated inline rather than through an outcome alias.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; Inert)
open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Data.Sum using (_⊎_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  ( applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  ; keep
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; Value; blame; _⟨_⟩)
open import QuotientedTermImprecision using
  ( PairedCast
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
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


WorldCoherentFinalPairedCastRuntimeSiblingCatchupᵀ : Set₁
WorldCoherentFinalPairedCastRuntimeSiblingCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W V′ R R′ : Term} {A A′ B B′ E E′ : Ty}
    {c c′ : Coercion}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  ((Value W × No• W) ⊎ (W ≡ blame)) →
  Value V′ →
  No• V′ →
  Inert c′ →
  PairedCast Φ Δᴸ Δᴿ ρ
    c c′ {A} {A′} {B} {B′} p q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ V′ ⦂ A ⊑ A′ ∶ p →
  No• R →
  RuntimeOK R′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ R ⊑ R′ ⦂ E ⊑ E′ ∶ r →
  Σ[ caught ∈
    WorldCoherentLeftCatchupIndexedResult
      {N = W ⟨ c ⟩} {V′ = V′ ⟨ c′ ⟩} {ρ = ρ} q ]
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
