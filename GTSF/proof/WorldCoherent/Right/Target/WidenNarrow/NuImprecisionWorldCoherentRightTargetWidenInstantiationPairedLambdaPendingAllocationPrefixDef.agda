module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaPendingAllocationPrefixDef
  where

-- File Charter:
--   * States the exact source-silent prefix produced by paired-lambda target
--     allocation beneath an arbitrary hereditary pending-cast spine.
--   * Ends at the shifted pending target
--     `applyTargetPendingCasts (W′ ⟨ s ⟩) (map ⇑ᶜ cs)`.
--   * Transports an arbitrary universal root through the post-beta relation
--     and spine needed by the smaller pending-cast call, plus the indexed
--     result, lineage, world, context, right-only prefix, and source-bullet
--     evidence needed for exact source-silent composition.
--   * Contains no implementation, result/view/outcome type, named conclusion
--     alias, postulate, hole, permissive option, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import CastImprecisionShape using (_⊢ᶜ_⦂_; widening)
open import Coercions using
  (Coercion; Inert; ModeEnv; inst; ⇑ᶜ)
open import Data.List using (List; []; map; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; Σ-syntax)
open import Imprecision using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  )
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; ∀ⁱ_)
open import ImprecisionComposition using
  (ImprecisionShape; νˢ_; ⌊_⌋; _；_≋_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuReduction using
  (applyTy; applyTys; bind; keep)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftStoreⁱ
  ; StoreImp
  ; rightStoreⁱ
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( LiftCtxⁱ
  )
open import NuTerms using
  (No•; RuntimeOK; Term; Value; Λ_; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using
  (Ty; TyCtx; ★; `∀)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepIndexedResult
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultSourceType
  ; resultStore
  ; resultTargetType
  ; sourceChanges
  ; sourceResult
  ; targetResult
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
  proof.Right.Core.NuImprecisionRightContextAction
  using (applyRightImpCtxChanges)
open import
  proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix
  using (RightOnlyStoreImpPrefix)
open import
  proof.Right.ValueCatchup.NuImprecisionRightValueCatchupSourceBulletTransportDef
  using (RightValueCatchupSourceBulletTransportᵀ)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (WeakOneStepStoreLineage; lineageStore)
open import
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using
  ( TargetAdministrationSpine
  ; applyTargetPendingCasts
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)


WorldCoherentRightTargetWidenInstantiationPairedLambdaPendingAllocationPrefixᵀ :
  Set₁
WorldCoherentRightTargetWidenInstantiationPairedLambdaPendingAllocationPrefixᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {W W′ : Term} {B C D F : Ty}
    {s : Coercion} {cs : List Coercion} {μ : ModeEnv}
    {p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ C ⊣ suc Δᴿ}
    {f : Φ ∣ Δᴸ ⊢ `∀ D ⊑ B ⊣ Δᴿ}
    {t : Φ ∣ Δᴸ ⊢ `∀ D ⊑ F ⊣ Δᴿ}
    {body-shape : ImprecisionShape} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK
    (applyTargetPendingCasts
      (NuTerms.ν ★ (Λ W′) s) cs) →
  Value W →
  No• W →
  Value W′ →
  No• W′ →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ inst B s ∶ `∀ C ⊑ B →
  Inert s →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρ∀ →
  LiftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) [] [] →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ∀ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ D ⊑ C ∶ p →
  widening ⊢ᶜ inst B s ⦂ νˢ body-shape →
  ⌊ ∀ⁱ p ⌋ ； νˢ body-shape ≋ ⌊ f ⌋ →
  TargetAdministrationSpine ρ⁺ (`∀ D) f t cs →
  Σ[ indexed ∈
    WeakOneStepIndexedResult
      {M = Λ W}
      {N′ =
        applyTargetPendingCasts
          (NuTerms.ν ★ (Λ W′) s) cs}
      {χ = keep}
      {ρ = ρ⁺}
      t ]
  let result = weakIndexedResult indexed
  in
  sourceChanges result ≡ []
  × sourceResult result ≡ Λ W
  × targetTailChanges result ≡ bind ★ ∷ keep ∷ []
  × targetResult result ≡
      applyTargetPendingCasts
        (W′ ⟨ s ⟩) (map ⇑ᶜ cs)
  × resultSourceType result ≡
      applyTys (sourceChanges result) (`∀ D)
  × resultTargetType result ≡
      applyTys (targetTailChanges result) (applyTy keep F)
  × (resultCtx result
      ∣ resultLeftCtx result
      ∣ resultRightCtx result
      ∣ resultStore result ∣ []
      ⊢ᴺ Λ W ⊑ W′ ⟨ s ⟩
        ⦂ applyTys (sourceChanges result) (`∀ D)
          ⊑ applyTys (targetTailChanges result) (applyTy keep B)
        ∶ transportType result f)
  × TargetAdministrationSpine
      (resultStore result)
      (applyTys (sourceChanges result) (`∀ D))
      (transportType result f)
      (transportType result t)
      (map ⇑ᶜ cs)
  × Σ[ lineage ∈ WeakOneStepStoreLineage result ]
    WorldCoherent (resultStore result)
    × SourceNameExclusive (resultCtx result)
    × AssumptionMembershipUnique (resultCtx result)
    × StoreWf (resultRightCtx result)
        (rightStoreⁱ (resultStore result))
    × resultCtx result ≡
        applyRightImpCtxChanges
          (targetTailChanges result) Φ
    × RightOnlyStoreImpPrefix
        (lineageStore lineage) (resultStore result)
    × RightValueCatchupSourceBulletTransportᵀ result
