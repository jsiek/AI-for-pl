module
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingCastsInstResidualAccDef
  where

-- File Charter:
--   * Defines the focused plain-instantiation branch of the private
--     accessibility-indexed target pending-cast worker.
--   * Retains every possible framing-evidence provenance so the proof can
--     classify the reachable widening cases exhaustively.
--   * Keeps the hereditary tail and existing contextual catch-up conclusion
--     explicit, without an independent right-opened QTI index.
--   * Contains no implementation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using
  ( Coercion
  ; id-onlyᵈ
  ; inst
  ; instᵈ
  ; _∣_∣_⊢_∶_=⇒_
  )
open import Conversion using
  (ConcealConversion; RevealConversion)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (_<_; suc; zero)
open import Data.Product using (_,_; _×_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Induction.WellFounded using (Acc)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; Value)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using
  (Ty; TyCtx; WfTy; occurs; ★; `∀; ⟰ᵗ; ⇑ᵗ)
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


WorldCoherentRightTargetPendingCastsInstResidualAccᵀ : Set₁
WorldCoherentRightTargetPendingCastsInstResidualAccᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W : Term} {A B C D : Ty} {s : Coercion}
    {cs : List Coercion} {μ}
    {hB : WfTy Δᴿ B}
    {occ : occurs zero C ≡ true}
    {s⊢ : instᵈ μ ∣ suc Δᴿ
      ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
      ⊢ s ∶ C =⇒ ⇑ᵗ B}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ `∀ C ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ} →
  (vW : Value W) →
  Acc _<_
    (targetPendingAdministrationRank vW (inst B s ∷ cs)) →
  ((∃[ μ′ ] ∃[ β ] ∃[ X′ ]
      RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
        β X′ (inst B s) (`∀ C) B)
   ⊎
   (∃[ μ′ ] ∃[ β ] ∃[ X′ ]
      ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
        β X′ (inst B s) (`∀ C) B)
   ⊎
   (∃[ μ′ ]
      CastMode μ′ ×
      SealModeStore★ μ′ (rightStoreⁱ ρ) ×
      (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ inst B s ∶ `∀ C ⊒ B))
   ⊎
   (∃[ μ′ ]
      CastMode μ′ ×
      SealModeStore★ μ′ (rightStoreⁱ ρ) ×
      (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ inst B s ∶ `∀ C ⊑ B))
   ⊎
   (SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) ×
    (id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
      ⊢ inst B s ∶ `∀ C ⊑ B))) →
  TargetAdministrationSpine ρ A r q cs →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK
    (applyTargetPendingCasts W (inst B s ∷ cs)) →
  Value V →
  No• V →
  No• W →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ W ⦂ A ⊑ `∀ C ∶ p →
  Σ[ caught ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = V}
      {M′ =
        applyTargetPendingCasts W (inst B s ∷ cs)}
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
