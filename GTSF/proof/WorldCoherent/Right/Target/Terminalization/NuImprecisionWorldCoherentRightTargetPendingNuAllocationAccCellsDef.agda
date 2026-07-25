module
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingNuAllocationAccCellsDef
  where

-- File Charter:
--   * States the four exact incoming/final precision-index cells for pending
--     target-`ν` allocation after plain target instantiation, the generic
--     direct paired-lambda inert arbitrary-tail cell, and its source-only
--     empty-tail specialization.
--   * Keeps `∀ⁱ` and source-only `ν` constructor provenance explicit where
--     required and retains the original pre-beta QTI relation.
--   * Adds no matrix, result, view, outcome, compatibility wrapper, postulate,
--     hole, permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import CastImprecisionShape using (_⊢ᶜ_⦂_; widening)
open import Coercions using
  (Coercion; Inert; ModeEnv; inst)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (_<_; suc; zero)
open import Data.Product using (_×_; Σ-syntax)
open import Imprecision using
  ( NonVar
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  )
open import ImprecisionWf using
  (ImpCtx; ∀ⁱ_; ν; _∣_⊢_⊑_⊣_)
open import ImprecisionComposition using
  (ImprecisionShape; νˢ_; ⌊_⌋; _；_≋_)
open import Induction.WellFounded using (Acc)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (LiftCtxⁱ; LiftStoreⁱ; StoreImp; rightStoreⁱ)
import NuTerms
open import NuTerms using
  (No•; RuntimeOK; Term; Value; Λ_)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using
  (Ty; TyCtx; occurs; ★; `∀)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import proof.Right.Core.NuImprecisionRightContextAction using
  (applyRightImpCtxChanges)
open import proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix using
  (RightOnlyStoreImpPrefix)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
  using (rightCatchupIndexedResult)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  (resultCtx; resultStore; targetTailChanges; weakIndexedResult)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (lineageStore)
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationMeasureDef
  using (targetPendingAdministrationRank)
open import
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using
  ( TargetAdministrationSpine
  ; applyTargetPendingCasts
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  ; worldRightCatchupStoreLineage
  )


WorldCoherentRightTargetPendingNuAllocationPairedFromPairedAccᵀ :
  Set₁
WorldCoherentRightTargetPendingNuAllocationPairedFromPairedAccᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W : Term} {C D E F : Ty}
    {s : Coercion} {μ : ModeEnv} {cs : List Coercion}
    {shape : ImprecisionShape}
    {p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ C ⊣ suc Δᴿ}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ E ⊣ suc Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ `∀ D ⊑ F ⊣ Δᴿ} →
  (vW : Value W) →
  Acc _<_
    (targetPendingAdministrationRank vW (s ∷ cs)) →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ inst (`∀ E) s ∶ `∀ C ⊑ `∀ E →
  widening ⊢ᶜ inst (`∀ E) s ⦂ shape →
  ⌊ ∀ⁱ p ⌋ ； shape ≋ ⌊ ∀ⁱ r ⌋ →
  TargetAdministrationSpine ρ (`∀ D) (∀ⁱ r) q cs →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK
    (applyTargetPendingCasts (NuTerms.ν ★ W s) cs) →
  Value V →
  No• V →
  No• W →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ W ⦂ `∀ D ⊑ `∀ C ∶ ∀ⁱ p →
  Σ[ caught ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = V}
      {M′ =
        applyTargetPendingCasts (NuTerms.ν ★ W s) cs}
      {ρ = ρ} q ]
    (resultCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))
      ≡
      applyRightImpCtxChanges
        (targetTailChanges
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult caught))))
        Φ)
    ×
    RightOnlyStoreImpPrefix
      (lineageStore (worldRightCatchupStoreLineage caught))
      (resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught))))


WorldCoherentRightTargetPendingNuAllocationPairedFromSourceOnlyAccᵀ :
  Set₁
WorldCoherentRightTargetPendingNuAllocationPairedFromSourceOnlyAccᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W : Term} {C D E F : Ty}
    {s : Coercion} {μ : ModeEnv} {cs : List Coercion}
    {shape : ImprecisionShape}
    {safe : NonVar D}
    {occ : occurs zero D ≡ true}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ `∀ C ⊣ Δᴿ}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ E ⊣ suc Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ `∀ D ⊑ F ⊣ Δᴿ} →
  (vW : Value W) →
  Acc _<_
    (targetPendingAdministrationRank vW (s ∷ cs)) →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ inst (`∀ E) s ∶ `∀ C ⊑ `∀ E →
  widening ⊢ᶜ inst (`∀ E) s ⦂ shape →
  ⌊ ν safe occ p ⌋ ； shape ≋ ⌊ ∀ⁱ r ⌋ →
  TargetAdministrationSpine ρ (`∀ D) (∀ⁱ r) q cs →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK
    (applyTargetPendingCasts (NuTerms.ν ★ W s) cs) →
  Value V →
  No• V →
  No• W →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ W ⦂ `∀ D ⊑ `∀ C ∶ ν safe occ p →
  Σ[ caught ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = V}
      {M′ =
        applyTargetPendingCasts (NuTerms.ν ★ W s) cs}
      {ρ = ρ} q ]
    (resultCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))
      ≡
      applyRightImpCtxChanges
        (targetTailChanges
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult caught))))
        Φ)
    ×
    RightOnlyStoreImpPrefix
      (lineageStore (worldRightCatchupStoreLineage caught))
      (resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught))))


WorldCoherentRightTargetPendingNuAllocationSourceOnlyFromPairedAccᵀ :
  Set₁
WorldCoherentRightTargetPendingNuAllocationSourceOnlyFromPairedAccᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W : Term} {B C D F : Ty}
    {s : Coercion} {μ : ModeEnv} {cs : List Coercion}
    {shape : ImprecisionShape}
    {safe : NonVar D}
    {occ : occurs zero D ≡ true}
    {p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ C ⊣ suc Δᴿ}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ `∀ D ⊑ F ⊣ Δᴿ} →
  (vW : Value W) →
  Acc _<_
    (targetPendingAdministrationRank vW (s ∷ cs)) →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ inst B s ∶ `∀ C ⊑ B →
  widening ⊢ᶜ inst B s ⦂ shape →
  ⌊ ∀ⁱ p ⌋ ； shape ≋ ⌊ ν safe occ r ⌋ →
  TargetAdministrationSpine ρ (`∀ D) (ν safe occ r) q cs →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK
    (applyTargetPendingCasts (NuTerms.ν ★ W s) cs) →
  Value V →
  No• V →
  No• W →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ W ⦂ `∀ D ⊑ `∀ C ∶ ∀ⁱ p →
  Σ[ caught ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = V}
      {M′ =
        applyTargetPendingCasts (NuTerms.ν ★ W s) cs}
      {ρ = ρ} q ]
    (resultCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))
      ≡
      applyRightImpCtxChanges
        (targetTailChanges
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult caught))))
        Φ)
    ×
    RightOnlyStoreImpPrefix
      (lineageStore (worldRightCatchupStoreLineage caught))
      (resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught))))


WorldCoherentRightTargetPendingNuAllocationFromPairedLambdaAccᵀ :
  Set₁
WorldCoherentRightTargetPendingNuAllocationFromPairedLambdaAccᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {W W′ : Term} {B C D F : Ty}
    {s : Coercion} {μ : ModeEnv} {cs : List Coercion}
    {body-shape : ImprecisionShape}
    {p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ C ⊣ suc Δᴿ}
    {f : Φ ∣ Δᴸ ⊢ `∀ D ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ `∀ D ⊑ F ⊣ Δᴿ} →
  (vW′ : Value W′) →
  Acc _<_
    (targetPendingAdministrationRank (Λ vW′) (s ∷ cs)) →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ inst B s ∶ `∀ C ⊑ B →
  widening ⊢ᶜ inst B s ⦂ νˢ body-shape →
  ⌊ ∀ⁱ p ⌋ ； νˢ body-shape ≋ ⌊ f ⌋ →
  Inert s →
  TargetAdministrationSpine ρ (`∀ D) f q cs →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK
    (applyTargetPendingCasts
      (NuTerms.ν ★ (Λ W′) s) cs) →
  Value W →
  No• W →
  No• W′ →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  LiftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) [] [] →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ∀ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ D ⊑ C ∶ p →
  Σ[ caught ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = Λ W}
      {M′ =
        applyTargetPendingCasts
          (NuTerms.ν ★ (Λ W′) s) cs}
      {ρ = ρ}
      q ]
    (resultCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))
      ≡
      applyRightImpCtxChanges
        (targetTailChanges
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult caught))))
        Φ)
    ×
    RightOnlyStoreImpPrefix
      (lineageStore (worldRightCatchupStoreLineage caught))
      (resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught))))


WorldCoherentRightTargetPendingNuAllocationSourceOnlyFromPairedLambdaEmptyAccᵀ :
  Set₁
WorldCoherentRightTargetPendingNuAllocationSourceOnlyFromPairedLambdaEmptyAccᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {W W′ : Term} {B C D : Ty}
    {s : Coercion} {μ : ModeEnv}
    {body-shape : ImprecisionShape}
    {{safe : NonVar D}}
    {p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ C ⊣ suc Δᴿ}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ B ⊣ Δᴿ}
    {occ : occurs zero D ≡ true} →
  (vW′ : Value W′) →
  Acc _<_
    (targetPendingAdministrationRank (Λ vW′) (s ∷ [])) →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ inst B s ∶ `∀ C ⊑ B →
  widening ⊢ᶜ inst B s ⦂ νˢ body-shape →
  ⌊ ∀ⁱ p ⌋ ； νˢ body-shape ≋ ⌊ ν safe occ r ⌋ →
  Inert s →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK (NuTerms.ν ★ (Λ W′) s) →
  Value W →
  No• W →
  No• W′ →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  LiftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) [] [] →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ∀ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ D ⊑ C ∶ p →
  Σ[ caught ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = Λ W}
      {M′ = NuTerms.ν ★ (Λ W′) s}
      {ρ = ρ}
      (ν safe occ r) ]
    (resultCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))
      ≡
      applyRightImpCtxChanges
        (targetTailChanges
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult caught))))
        Φ)
    ×
    RightOnlyStoreImpPrefix
      (lineageStore (worldRightCatchupStoreLineage caught))
      (resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught))))


WorldCoherentRightTargetPendingNuAllocationSourceOnlyFromSourceOnlyAccᵀ :
  Set₁
WorldCoherentRightTargetPendingNuAllocationSourceOnlyFromSourceOnlyAccᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W : Term} {B C D F : Ty}
    {s : Coercion} {μ : ModeEnv} {cs : List Coercion}
    {shape : ImprecisionShape}
    {safeₚ safeᵣ : NonVar D}
    {occₚ occᵣ : occurs zero D ≡ true}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ `∀ C ⊣ Δᴿ}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ `∀ D ⊑ F ⊣ Δᴿ} →
  (vW : Value W) →
  Acc _<_
    (targetPendingAdministrationRank vW (s ∷ cs)) →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ inst B s ∶ `∀ C ⊑ B →
  widening ⊢ᶜ inst B s ⦂ shape →
  ⌊ ν safeₚ occₚ p ⌋ ； shape ≋ ⌊ ν safeᵣ occᵣ r ⌋ →
  TargetAdministrationSpine ρ (`∀ D)
    (ν safeᵣ occᵣ r) q cs →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK
    (applyTargetPendingCasts (NuTerms.ν ★ W s) cs) →
  Value V →
  No• V →
  No• W →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ W ⦂ `∀ D ⊑ `∀ C ∶ ν safeₚ occₚ p →
  Σ[ caught ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = V}
      {M′ =
        applyTargetPendingCasts (NuTerms.ν ★ W s) cs}
      {ρ = ρ} q ]
    (resultCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))
      ≡
      applyRightImpCtxChanges
        (targetTailChanges
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult caught))))
        Φ)
    ×
    RightOnlyStoreImpPrefix
      (lineageStore (worldRightCatchupStoreLineage caught))
      (resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught))))
