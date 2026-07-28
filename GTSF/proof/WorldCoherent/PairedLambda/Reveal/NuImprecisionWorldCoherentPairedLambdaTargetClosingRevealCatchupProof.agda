module
  proof.WorldCoherent.PairedLambda.Reveal.NuImprecisionWorldCoherentPairedLambdaTargetClosingRevealCatchupProof
  where

-- File Charter:
--   * Dispatches generic paired-lambda target-closing reveal catch-up to the
--     structural `reveal-all` and active `reveal-unseal` semantic branches.
--   * Generalizes the reveal target before inversion, keeping defined type
--     shifts out of constructor indices and exposing their equality directly.
--   * Contains no semantic branch implementation, postulate, or permissive
--     option.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Coercions using (Coercion; ModeEnv)
open import Conversion using
  ( RevealConversion
  ; reveal-all
  ; reveal-fun
  ; reveal-id-base
  ; reveal-id-var
  ; reveal-id-★
  ; reveal-unseal
  )
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (suc-injective)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; ∀ⁱ_
  ; ν
  ; _∣_⊢_⊑_⊣_
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; store-left
  )
open import NuTerms using (No•; Term; Value; Λ_; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; WfTy; `∀; ⇑ᵗ)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using (⊑-source-liftνᵢ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)
open import proof.Core.Properties.ReductionProperties using
  ( ∀-injective
  ; renameᵗ-injective
  )
open import
  proof.WorldCoherent.PairedLambda.AllReveal.NuImprecisionWorldCoherentPairedLambdaTargetClosingAllRevealCatchupDef
  using (WorldCoherentPairedLambdaTargetClosingAllRevealCatchupᵀ)
open import
  proof.WorldCoherent.PairedLambda.Reveal.NuImprecisionWorldCoherentPairedLambdaTargetClosingRevealCatchupDef
  using (WorldCoherentPairedLambdaTargetClosingRevealCatchupᵀ)
open import
  proof.WorldCoherent.PairedLambda.Reveal.NuImprecisionWorldCoherentPairedLambdaTargetClosingUnsealCatchupDef
  using (WorldCoherentPairedLambdaTargetClosingUnsealCatchupᵀ)


private
  dispatch-target-closing-reveal :
    WorldCoherentPairedLambdaTargetClosingAllRevealCatchupᵀ →
    WorldCoherentPairedLambdaTargetClosingUnsealCatchupᵀ →
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
      {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
      {W W′ : Term} {A B C C′ T : Ty} {s : Coercion}
      {μ : ModeEnv}
      {p : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ}
      {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    WfTy Δᴸ A →
    (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
    RevealConversion μ (suc Δᴸ)
      (leftStoreⁱ (store-left zero (⇑ᵗ A) h⇑A ∷ ρν))
      zero (⇑ᵗ A) s C T →
    T ≡ ⇑ᵗ B →
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
    Value W →
    No• W →
    Value W′ →
    No• W′ →
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ∀ ∣ []
      ⊢ᴺ W ⊑ W′ ⦂ C ⊑ C′ ∶ r →
    WorldCoherentLeftCatchupIndexedResult
      {N = W ⟨ s ⟩}
      {V′ = Λ W′}
      {ρ = store-left zero (⇑ᵗ A) h⇑A ∷ ρν}
      (⊑-source-liftνᵢ p)

  dispatch-target-closing-reveal
      all-reveal unseal-reveal {B = `∀ D} {p = ∀ⁱ p}
      coherent exclusive wfL hA h⇑A
      (reveal-id-var hY ok) ()
  dispatch-target-closing-reveal
      all-reveal unseal-reveal {B = `∀ D} {p = ∀ⁱ p}
      coherent exclusive wfL hA h⇑A reveal-id-base ()
  dispatch-target-closing-reveal
      all-reveal unseal-reveal {B = `∀ D} {p = ∀ⁱ p}
      coherent exclusive wfL hA h⇑A reveal-id-★ ()
  dispatch-target-closing-reveal
      all-reveal unseal-reveal {B = `∀ D} {p = ∀ⁱ p}
      coherent exclusive wfL hA h⇑A (reveal-fun s↓ t↑) ()
  dispatch-target-closing-reveal
      all-reveal unseal-reveal {B = `∀ D} {μ = μ} {p = ∀ⁱ p}
      coherent exclusive wfL hA h⇑A
      (reveal-unseal hX αX∈Σ ok) target-eq
      liftν lift∀ vW noW vW′ noW′ W⊑W′
      with renameᵗ-injective suc-injective target-eq
  dispatch-target-closing-reveal
      all-reveal unseal-reveal {B = `∀ D} {μ = μ} {p = ∀ⁱ p}
      coherent exclusive wfL hA h⇑A
      (reveal-unseal hX αX∈Σ ok) target-eq
      liftν lift∀ vW noW vW′ noW′ W⊑W′ | refl =
    unseal-reveal {μ = μ} coherent exclusive wfL hA h⇑A
      (reveal-unseal hX αX∈Σ ok)
      liftν lift∀ vW noW vW′ noW′ W⊑W′
  dispatch-target-closing-reveal
      all-reveal unseal-reveal {B = `∀ D} {p = ∀ⁱ p}
      coherent exclusive wfL hA h⇑A
      (reveal-all inner) target-eq
      liftν lift∀ vW noW vW′ noW′ W⊑W′
      with ∀-injective target-eq
  dispatch-target-closing-reveal
      all-reveal unseal-reveal {B = `∀ D} {p = ∀ⁱ p}
      coherent exclusive wfL hA h⇑A
      (reveal-all inner) target-eq
      liftν lift∀ vW noW vW′ noW′ W⊑W′ | refl =
    all-reveal coherent exclusive wfL hA h⇑A inner
      liftν lift∀ vW noW vW′ noW′ W⊑W′

  dispatch-target-closing-reveal
      all-reveal unseal-reveal {B = `∀ D} {p = ν _ occ p}
      coherent exclusive wfL hA h⇑A
      (reveal-id-var hY ok) ()
  dispatch-target-closing-reveal
      all-reveal unseal-reveal {B = `∀ D} {p = ν _ occ p}
      coherent exclusive wfL hA h⇑A reveal-id-base ()
  dispatch-target-closing-reveal
      all-reveal unseal-reveal {B = `∀ D} {p = ν _ occ p}
      coherent exclusive wfL hA h⇑A reveal-id-★ ()
  dispatch-target-closing-reveal
      all-reveal unseal-reveal {B = `∀ D} {p = ν _ occ p}
      coherent exclusive wfL hA h⇑A (reveal-fun s↓ t↑) ()
  dispatch-target-closing-reveal
      all-reveal unseal-reveal {B = `∀ D} {μ = μ} {p = ν _ occ p}
      coherent exclusive wfL hA h⇑A
      (reveal-unseal hX αX∈Σ ok) target-eq
      liftν lift∀ vW noW vW′ noW′ W⊑W′
      with renameᵗ-injective suc-injective target-eq
  dispatch-target-closing-reveal
      all-reveal unseal-reveal {B = `∀ D} {μ = μ} {p = ν _ occ p}
      coherent exclusive wfL hA h⇑A
      (reveal-unseal hX αX∈Σ ok) target-eq
      liftν lift∀ vW noW vW′ noW′ W⊑W′ | refl =
    unseal-reveal {μ = μ} coherent exclusive wfL hA h⇑A
      (reveal-unseal hX αX∈Σ ok)
      liftν lift∀ vW noW vW′ noW′ W⊑W′
  dispatch-target-closing-reveal
      all-reveal unseal-reveal {B = `∀ D} {p = ν _ occ p}
      coherent exclusive wfL hA h⇑A
      (reveal-all inner) target-eq
      liftν lift∀ vW noW vW′ noW′ W⊑W′
      with ∀-injective target-eq
  dispatch-target-closing-reveal
      all-reveal unseal-reveal {B = `∀ D} {p = ν _ occ p}
      coherent exclusive wfL hA h⇑A
      (reveal-all inner) target-eq
      liftν lift∀ vW noW vW′ noW′ W⊑W′ | refl =
    all-reveal coherent exclusive wfL hA h⇑A inner
      liftν lift∀ vW noW vW′ noW′ W⊑W′


world-coherent-paired-lambda-target-closing-reveal-catchup-proofᵀ :
  WorldCoherentPairedLambdaTargetClosingAllRevealCatchupᵀ →
  WorldCoherentPairedLambdaTargetClosingUnsealCatchupᵀ →
  WorldCoherentPairedLambdaTargetClosingRevealCatchupᵀ
world-coherent-paired-lambda-target-closing-reveal-catchup-proofᵀ
    all-reveal unseal-reveal coherent exclusive wfL hA h⇑A s↑
    liftν lift∀ vW noW vW′ noW′ W⊑W′ =
  dispatch-target-closing-reveal all-reveal unseal-reveal
    coherent exclusive wfL hA h⇑A s↑ refl
    liftν lift∀ vW noW vW′ noW′ W⊑W′
