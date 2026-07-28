module
  proof.WorldCoherent.Source.NuPaired.NuImprecisionWorldCoherentSourceNuPairedAllConversionPostBetaTargetClosingCatchupProof
  where

-- File Charter:
--   * Dispatches post-`β-∀•` paired-conversion target closing to structural
--     all-reveal relation closing and active fresh-unseal cancellation.
--   * Packages the structural relation with coherent terminal value catch-up
--     while keeping paired reveal and conceal in one family.
--   * Contains no recursive semantic branch, postulate, or permissive option.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
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
open import Data.Product using (_,_)
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
  ; leftStoreⁱ-lift-left
  ; store-left
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; no•-⟨⟩
  ; ok-•
  ; ok-⟨⟩
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( PairedConversion
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)
open import Types using (Ty; TyCtx; WfTy; `∀; ⇑ᵗ)
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using (⊑-source-liftνᵢ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityProof using
  (source-name-exclusive-source-only-head)
open import
  proof.Source.NuPaired.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationDef
  using
    (SourceNuPairedAllConversionPostBetaAllRevealClosingRelationᵀ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceLemma using
  (world-coherent-left-allocation)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)
open import
  proof.WorldCoherent.Source.NuPaired.NuImprecisionWorldCoherentSourceNuPairedAllConversionPostBetaTargetClosingCatchupDef
  using
    (WorldCoherentSourceNuPairedAllConversionPostBetaTargetClosingCatchupᵀ)
open import
  proof.WorldCoherent.Source.NuPaired.NuImprecisionWorldCoherentSourceNuPairedAllConversionPostBetaUnsealClosingCatchupDef
  using
    (WorldCoherentSourceNuPairedAllConversionPostBetaUnsealClosingCatchupᵀ)
open import proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef using
  (WorldCoherentLeftValueCatchupᵀ)
open import proof.Core.Properties.NuStoreProperties using (StoreWf-bind)
open import proof.Core.Properties.TypeInjectivityProperties using
  ( ∀-injective
  ; renameᵗ-injective
  )


allocated-left-store-wf :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {A : Ty} →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  WfTy Δᴸ A →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  StoreWf (suc Δᴸ)
    (leftStoreⁱ (store-left zero (⇑ᵗ A) h⇑A ∷ ρν))
allocated-left-store-wf {A = A} wfL hA h⇑A liftν =
  subst (StoreWf _)
    (sym
      (cong ((zero , ⇑ᵗ A) ∷_) (leftStoreⁱ-lift-left liftν)))
    (StoreWf-bind wfL hA)


private
  dispatch-post-beta-target-closing :
    SourceNuPairedAllConversionPostBetaAllRevealClosingRelationᵀ →
    WorldCoherentLeftValueCatchupᵀ →
    WorldCoherentSourceNuPairedAllConversionPostBetaUnsealClosingCatchupᵀ →
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
      {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
      {V V′ : Term} {A B C C′ D D′ T : Ty}
      {c c′ s : Coercion} {μ : ModeEnv}
      {p : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ}
      {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ D ⊑ D′ ⊣ suc Δᴿ}
      {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
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
    Value V →
    No• V →
    Value V′ →
    No• V′ →
    PairedConversion Φ Δᴸ Δᴿ ρ
      (C.`∀ c) (C.`∀ c′)
      {`∀ D} {`∀ D′} {`∀ C} {`∀ C′}
      (∀ⁱ r) (∀ⁱ q) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ V ⊑ V′ ⦂ `∀ D ⊑ `∀ D′ ∶ ∀ⁱ r →
    WorldCoherentLeftCatchupIndexedResult
      {N = (((⇑ᵗᵐ V) •) ⟨ c ⟩) ⟨ s ⟩}
      {V′ = V′ ⟨ C.`∀ c′ ⟩}
      {ρ = store-left zero (⇑ᵗ A) h⇑A ∷ ρν}
      (⊑-source-liftνᵢ p)

  dispatch-post-beta-target-closing
      all-relation value-catchup unseal-catchup
      {B = `∀ D} {μ = μ} {p = ∀ⁱ p}
      coherent exclusive wfL hA h⇑A
      (reveal-id-var hY ok) ()
  dispatch-post-beta-target-closing
      all-relation value-catchup unseal-catchup
      {B = `∀ D} {μ = μ} {p = ∀ⁱ p}
      coherent exclusive wfL hA h⇑A reveal-id-base ()
  dispatch-post-beta-target-closing
      all-relation value-catchup unseal-catchup
      {B = `∀ D} {p = ∀ⁱ p}
      coherent exclusive wfL hA h⇑A reveal-id-★ ()
  dispatch-post-beta-target-closing
      all-relation value-catchup unseal-catchup
      {B = `∀ D} {p = ∀ⁱ p}
      coherent exclusive wfL hA h⇑A (reveal-fun s↓ t↑) ()
  dispatch-post-beta-target-closing
      all-relation value-catchup unseal-catchup
      {B = `∀ D} {μ = μ} {p = ∀ⁱ p}
      coherent exclusive wfL hA h⇑A
      (reveal-unseal hX αX∈Σ ok) target-eq
      liftν lift∀ vV noV vV′ noV′ conversion V⊑V′
      with renameᵗ-injective suc-injective target-eq
  dispatch-post-beta-target-closing
      all-relation value-catchup unseal-catchup
      {B = `∀ D} {μ = μ} {p = ∀ⁱ p}
      coherent exclusive wfL hA h⇑A
      (reveal-unseal hX αX∈Σ ok) target-eq
      liftν lift∀ vV noV vV′ noV′ conversion V⊑V′ | refl =
    unseal-catchup {μ = μ} coherent exclusive wfL hA h⇑A
      (reveal-unseal hX αX∈Σ ok)
      liftν lift∀ vV noV vV′ noV′ conversion V⊑V′
  dispatch-post-beta-target-closing
      all-relation value-catchup unseal-catchup
      {B = `∀ D} {p = ∀ⁱ p}
      coherent exclusive wfL hA h⇑A
      (reveal-all inner) target-eq
      liftν lift∀ vV noV vV′ noV′ conversion V⊑V′
      with ∀-injective target-eq
  dispatch-post-beta-target-closing
      all-relation value-catchup unseal-catchup
      {B = `∀ D} {p = ∀ⁱ p}
      coherent exclusive wfL hA h⇑A
      (reveal-all inner) target-eq
      liftν lift∀ vV noV vV′ noV′ conversion V⊑V′ | refl =
    value-catchup
      (world-coherent-left-allocation liftν coherent)
      (source-name-exclusive-source-only-head exclusive)
      (allocated-left-store-wf wfL hA h⇑A liftν)
      (ok-⟨⟩ (ok-⟨⟩ (ok-• vV noV)))
      (vV′ ⟨ C.`∀ _ ⟩)
      (no•-⟨⟩ noV′)
      (all-relation coherent exclusive wfL h⇑A inner liftν lift∀
        vV noV vV′ noV′ conversion V⊑V′)

  dispatch-post-beta-target-closing
      all-relation value-catchup unseal-catchup
      {B = `∀ D} {μ = μ} {p = ν _ occ p}
      coherent exclusive wfL hA h⇑A
      (reveal-id-var hY ok) ()
  dispatch-post-beta-target-closing
      all-relation value-catchup unseal-catchup
      {B = `∀ D} {μ = μ} {p = ν _ occ p}
      coherent exclusive wfL hA h⇑A reveal-id-base ()
  dispatch-post-beta-target-closing
      all-relation value-catchup unseal-catchup
      {B = `∀ D} {p = ν _ occ p}
      coherent exclusive wfL hA h⇑A reveal-id-★ ()
  dispatch-post-beta-target-closing
      all-relation value-catchup unseal-catchup
      {B = `∀ D} {p = ν _ occ p}
      coherent exclusive wfL hA h⇑A (reveal-fun s↓ t↑) ()
  dispatch-post-beta-target-closing
      all-relation value-catchup unseal-catchup
      {B = `∀ D} {μ = μ} {p = ν _ occ p}
      coherent exclusive wfL hA h⇑A
      (reveal-unseal hX αX∈Σ ok) target-eq
      liftν lift∀ vV noV vV′ noV′ conversion V⊑V′
      with renameᵗ-injective suc-injective target-eq
  dispatch-post-beta-target-closing
      all-relation value-catchup unseal-catchup
      {B = `∀ D} {μ = μ} {p = ν _ occ p}
      coherent exclusive wfL hA h⇑A
      (reveal-unseal hX αX∈Σ ok) target-eq
      liftν lift∀ vV noV vV′ noV′ conversion V⊑V′ | refl =
    unseal-catchup {μ = μ} coherent exclusive wfL hA h⇑A
      (reveal-unseal hX αX∈Σ ok)
      liftν lift∀ vV noV vV′ noV′ conversion V⊑V′
  dispatch-post-beta-target-closing
      all-relation value-catchup unseal-catchup
      {B = `∀ D} {p = ν _ occ p}
      coherent exclusive wfL hA h⇑A
      (reveal-all inner) target-eq
      liftν lift∀ vV noV vV′ noV′ conversion V⊑V′
      with ∀-injective target-eq
  dispatch-post-beta-target-closing
      all-relation value-catchup unseal-catchup
      {B = `∀ D} {p = ν _ occ p}
      coherent exclusive wfL hA h⇑A
      (reveal-all inner) target-eq
      liftν lift∀ vV noV vV′ noV′ conversion V⊑V′ | refl =
    value-catchup
      (world-coherent-left-allocation liftν coherent)
      (source-name-exclusive-source-only-head exclusive)
      (allocated-left-store-wf wfL hA h⇑A liftν)
      (ok-⟨⟩ (ok-⟨⟩ (ok-• vV noV)))
      (vV′ ⟨ C.`∀ _ ⟩)
      (no•-⟨⟩ noV′)
      (all-relation coherent exclusive wfL h⇑A inner liftν lift∀
        vV noV vV′ noV′ conversion V⊑V′)


world-coherent-source-ν-paired-all-conversion-post-beta-target-closing-catchup-proofᵀ :
  SourceNuPairedAllConversionPostBetaAllRevealClosingRelationᵀ →
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentSourceNuPairedAllConversionPostBetaUnsealClosingCatchupᵀ →
  WorldCoherentSourceNuPairedAllConversionPostBetaTargetClosingCatchupᵀ
world-coherent-source-ν-paired-all-conversion-post-beta-target-closing-catchup-proofᵀ
    all-relation value-catchup unseal-catchup
    coherent exclusive wfL hA h⇑A s↑ liftν lift∀
    vV noV vV′ noV′ conversion V⊑V′ =
  dispatch-post-beta-target-closing
    all-relation value-catchup unseal-catchup
    coherent exclusive wfL hA h⇑A s↑ refl liftν lift∀
    vV noV vV′ noV′ conversion V⊑V′
