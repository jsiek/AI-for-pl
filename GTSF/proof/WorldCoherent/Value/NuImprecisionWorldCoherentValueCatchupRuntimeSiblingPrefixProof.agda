module
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupRuntimeSiblingPrefixProof
  where

-- File Charter:
--   * Implements ambient-prefix target-value catch-up while carrying one
--     independent source-no-bullet, target-runtime sibling relation.
--   * Lifts the sibling to the ambient world once, then keeps the caught
--     result and exact final sibling together throughout structural recursion.
--   * Delegates only source-runtime and terminal quotient semantic joins to
--     their construction-time sibling-aware contracts.
--   * Contains no opaque-final-result sibling transport or permissive option.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([])
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax)

open import Coercions using
  (Inert; genᵈ; id-onlyᵈ; tag-or-idᵈ)
open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; narrowing; widening)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
import NarrowWiden as NW
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; genSafe→inert)
open import NuReduction using
  ( applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  ; keep
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; lift-left-ctx-[]
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-⟨⟩
  ; ƛ_
  ; Λ_
  ; $
  ; _⟨_⟩
  )
open import QuotientedTermImprecision
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using (Ty; TyCtx)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( catchupIndexedResult
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent-invariant
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
  proof.Store.Prefix.NuImprecisionStorePrefix
  using (store-imp-prefix-transⁱ)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (rel-store-embedding-reflⁱ)
open import
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  using
  ( embedded-creation-source-valueᴱ
  ; embedded-creation-target-no-bulletᴱ
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (weak-step-store-lineage)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupPrefixFrames
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentLeftCatchupIndexedResult
  ; worldCatchupResult
  ; world-coherent-left-indexed-catchup
  )
open import
  proof.WorldCoherent.Quotient.Final.NuImprecisionWorldCoherentQuotientFinalRuntimeSiblingCatchupDef
open import
  proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourceRuntimeSiblingCatchupDef
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupRuntimeSiblingPrefixDef
  using
  ( WorldCoherentLeftValueCatchupRuntimeSiblingAmbientᵀ
  ; WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ
  )
open import proof.Catchup.Core.NuImprecisionCatchupPrefixSupport using
  ( left-catchup-indexed-prefix-blameᵀ
  ; left-catchup-indexed-prefix-valueᵀ
  )
open import proof.DGG.Core.NuPreservation using
  (runtime-ν; runtime-⟨⟩)


world-coherent-left-value-catchup-runtime-sibling-ambientᵀ :
  WorldCoherentSourceRuntimeSiblingCatchupᵀ →
  WorldCoherentQuotientFinalRuntimeSiblingCatchupᵀ →
  WorldCoherentLeftValueCatchupRuntimeSiblingAmbientᵀ
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL vL′ noL′
    rel@(blame⊑ᵀ L′⊢) noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-prefix-blameᵀ prefix noL′ rel)
      (weak-step-store-lineage _
        rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL
    (vM′ ⟨ inert-d′ ⟩ ⟨ inert-u′ ⟩)
    (no•-⟨⟩ (no•-⟨⟩ noM′))
    (up⊑upᵀ
      (down⊑downᵀ
        d⊒ d-shape d′⊒ d′-shape M⊑M′ qD down-square)
      widening-pair pA u-shape u′-shape up-square)
    noR okR′ sibling =
  quotient-down-up-sibling quotient-catchup
    prefix okL vM′ noM′ inert-d′ inert-u′
    d⊒ d-shape d′⊒ d′-shape down-square
    widening-pair u-shape u′-shape up-square
    noR okR′ inner inner-sibling
  where
  inner-with-sibling =
    world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
      source-runtime quotient-catchup
      prefix coherent exclusive unique wfL
      (runtime-⟨⟩ (runtime-⟨⟩ okL))
      vM′ noM′ M⊑M′ noR okR′ sibling

  inner = proj₁ inner-with-sibling

  inner-sibling = proj₂ inner-with-sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL
    (vM′ ⟨ inert-d′ ⟩ ⟨ inert-u′ ⟩)
    (no•-⟨⟩ (no•-⟨⟩ noM′))
    (up⊑upᵀ
      (gen-down⊑gen-downᵀ
        d⊒ d-shape d′⊒ d′-shape M⊑M′ qD down-square)
      widening-pair pA u-shape u′-shape up-square)
    noR okR′ sibling =
  quotient-gen-down-up-sibling quotient-catchup
    prefix okL vM′ noM′ inert-d′ inert-u′
    d⊒ d-shape d′⊒ d′-shape down-square
    widening-pair u-shape u′-shape up-square
    noR okR′ inner inner-sibling
  where
  inner-with-sibling =
    world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
      source-runtime quotient-catchup
      prefix coherent exclusive unique wfL
      (runtime-⟨⟩ (runtime-⟨⟩ okL))
      vM′ noM′ M⊑M′ noR okR′ sibling

  inner = proj₁ inner-with-sibling

  inner-sibling = proj₂ inner-with-sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL
    (() ⟨ inert-u′ ⟩) noL′
    (down·up⊑down·upᵀ
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      L⊑L′ M⊑M′ down-square
      widening-pair u-shape u′-shape up-square compatible)
    noR okR′ sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL vL′ noL′
    (allocation-prefixᵀ prefix₀ inner L⊢ L′⊢)
    noR okR′ sibling =
  world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    (store-imp-prefix-transⁱ prefix₀ prefix)
    coherent exclusive unique wfL okL vL′ noL′ inner
    noR okR′ sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL
    (vL′ ⟨ inert ⟩) (no•-⟨⟩ noL′)
    (⊑cast⊒ᵀ mode seal★ c⊒ rel q c-shape comp)
    noR okR′ sibling
    with
      world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
        source-runtime quotient-catchup
        prefix coherent exclusive unique wfL okL
        vL′ noL′ rel noR okR′ sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL
    (vL′ ⟨ inert ⟩) (no•-⟨⟩ noL′)
    (⊑cast⊒ᵀ mode seal★ c⊒ rel q c-shape comp)
    noR okR′ sibling
    | inner@(world-coherent-left-indexed-catchup
        (left-indexed-catchup _
          (left-catchup-invariant
            (left-silent-invariant refl refl) _))
        _ _ _ _ _) ,
      inner-sibling =
  caught , inner-sibling
  where
  caught =
    world-coherent-left-catchup-prefix-target-narrow-castᵀ
      prefix mode seal★ c⊒ c-shape comp inner
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL
    (vL′ ⟨ inert ⟩) (no•-⟨⟩ noL′)
    (⊑cast⊑ᵀ mode seal★ c⊑ rel q c-shape comp)
    noR okR′ sibling
    with
      world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
        source-runtime quotient-catchup
        prefix coherent exclusive unique wfL okL
        vL′ noL′ rel noR okR′ sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL
    (vL′ ⟨ inert ⟩) (no•-⟨⟩ noL′)
    (⊑cast⊑ᵀ mode seal★ c⊑ rel q c-shape comp)
    noR okR′ sibling
    | inner@(world-coherent-left-indexed-catchup
        (left-indexed-catchup _
          (left-catchup-invariant
            (left-silent-invariant refl refl) _))
        _ _ _ _ _) ,
      inner-sibling =
  caught , inner-sibling
  where
  caught =
    world-coherent-left-catchup-prefix-target-widen-castᵀ
      prefix mode seal★ c⊑ c-shape comp inner
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL
    (vL′ ⟨ inert ⟩) (no•-⟨⟩ noL′)
    (⊑cast⊑idᵀ seal★ c⊑ rel q c-shape comp)
    noR okR′ sibling
    with
      world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
        source-runtime quotient-catchup
        prefix coherent exclusive unique wfL okL
        vL′ noL′ rel noR okR′ sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL
    (vL′ ⟨ inert ⟩) (no•-⟨⟩ noL′)
    (⊑cast⊑idᵀ seal★ c⊑ rel q c-shape comp)
    noR okR′ sibling
    | inner@(world-coherent-left-indexed-catchup
        (left-indexed-catchup _
          (left-catchup-invariant
            (left-silent-invariant refl refl) _))
        _ _ _ _ _) ,
      inner-sibling =
  caught , inner-sibling
  where
  caught =
    world-coherent-left-catchup-prefix-target-widen-id-castᵀ
      prefix seal★ c⊑ c-shape comp inner
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL
    (vL′ ⟨ inert ⟩) (no•-⟨⟩ noL′)
    (⊑conv↑ᵀ c↑ rel q replace)
    noR okR′ sibling
    with
      world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
        source-runtime quotient-catchup
        prefix coherent exclusive unique wfL okL
        vL′ noL′ rel noR okR′ sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL
    (vL′ ⟨ inert ⟩) (no•-⟨⟩ noL′)
    (⊑conv↑ᵀ c↑ rel q replace)
    noR okR′ sibling
    | inner@(world-coherent-left-indexed-catchup
        (left-indexed-catchup _
          (left-catchup-invariant
            (left-silent-invariant refl refl) _))
        _ _ _ _ _) ,
      inner-sibling =
  caught , inner-sibling
  where
  caught =
    world-coherent-left-catchup-prefix-target-reveal-castᵀ
      prefix c↑ replace inner
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL
    (vL′ ⟨ inert ⟩) (no•-⟨⟩ noL′)
    (⊑conv↓ᵀ c↓ rel q replace)
    noR okR′ sibling
    with
      world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
        source-runtime quotient-catchup
        prefix coherent exclusive unique wfL okL
        vL′ noL′ rel noR okR′ sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL
    (vL′ ⟨ inert ⟩) (no•-⟨⟩ noL′)
    (⊑conv↓ᵀ c↓ rel q replace)
    noR okR′ sibling
    | inner@(world-coherent-left-indexed-catchup
        (left-indexed-catchup _
          (left-catchup-invariant
            (left-silent-invariant refl refl) _))
        _ _ _ _ _) ,
      inner-sibling =
  caught , inner-sibling
  where
  caught =
    world-coherent-left-catchup-prefix-target-conceal-castᵀ
      prefix c↓ replace inner
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL () noL′
    (x⊑xᵀ x∈) noR okR′ sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL vL′ noL′
    rel@(ƛ⊑ƛᵀ hA hA′ body) noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-prefix-valueᵀ
        prefix okL (ƛ _) noL′ rel)
      (weak-step-store-lineage _
        rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL () noL′
    (·⊑·ᵀ L⊑L′ M⊑M′) noR okR′ sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL vL′ noL′
    rel@(Λ⊑Λᵀ liftρ liftγ vL vW′ body)
    noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-prefix-valueᵀ
        prefix okL (Λ vL) noL′ rel)
      (weak-step-store-lineage _
        rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL vL′ noL′
    rel@(Λ⊑ᵀ occ liftρ liftγ vL body)
    noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-prefix-valueᵀ
        prefix okL (Λ vL) noL′ rel)
      (weak-step-store-lineage _
        rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL vL′ noL′
    rel@(target-instantiationᵀ embedded)
    noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-prefix-valueᵀ
        prefix okL
        (embedded-creation-source-valueᴱ embedded)
        (embedded-creation-target-no-bulletᴱ embedded)
        rel)
      (weak-step-store-lineage _
        rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL () noL′
    (α⊑αᵀ vL noL vL′ noInnerL′ pA liftρ liftγ
      L⊑L′ L•⊢ L′•⊢)
    noR okR′ sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL vL′ noL′
    (α⊑ᵀ vL noL h⇑A liftρ lift-left-ctx-[]
      L⊑L′ L•⊢ L′•⊢)
    noR okR′ sibling =
  source-bullet-sibling source-runtime
    h⇑A prefix coherent exclusive unique wfL okL
    vL′ noL′ vL noL liftρ lift-left-ctx-[]
    L⊑L′ L•⊢ L′•⊢ noR okR′ sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL () noL′
    (⊑αᵀ vL′ noInnerL′ h⇑A liftρ liftγ N⊑L′ r N⊢ L′•⊢)
    noR okR′ sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL () noL′
    (ν⊑νᵀ hA hA′ s↑ s′↑ pA pA⇑ liftρ liftγ N⊑N′ replace)
    noR okR′ sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL vL′ noL′
    (ν⊑ᵀ hA h⇑A s↑ liftρ lift-left-ctx-[] N⊑L′ replace)
    noR okR′ sibling =
  source-ν-sibling source-runtime
    prefix hA h⇑A s↑ liftρ lift-left-ctx-[]
    vL′ noL′ noR okR′ inner replace inner-sibling
  where
  inner-with-sibling =
    world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
      source-runtime quotient-catchup
      prefix coherent exclusive unique wfL
      (runtime-ν okL) vL′ noL′ N⊑L′
      noR okR′ sibling

  inner = proj₁ inner-with-sibling

  inner-sibling = proj₂ inner-with-sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL () noL′
    (⊑νᵀ hA h⇑A s↑ liftρ liftγ pC N⊑N′ replace)
    noR okR′ sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL () noL′
    (νcast⊑νcastᵀ mode seal★ mode′ seal★′
      s⊑ s′⊑ compat liftρ liftγ N⊑N′
      s-shape s′-shape left-comp right-comp)
    noR okR′ sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL vL′ noL′
    (νcast⊑ᵀ mode seal★ s⊑ liftρ lift-left-ctx-[] N⊑L′
      s-shape comp)
    noR okR′ sibling =
  source-νcast-sibling source-runtime
    prefix mode seal★ s⊑ s-shape comp
    liftρ lift-left-ctx-[] vL′ noL′ noR okR′
    inner inner-sibling
  where
  inner-with-sibling =
    world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
      source-runtime quotient-catchup
      prefix coherent exclusive unique wfL
      (runtime-ν okL) vL′ noL′ N⊑L′
      noR okR′ sibling

  inner = proj₁ inner-with-sibling

  inner-sibling = proj₂ inner-with-sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL () noL′
    (⊑νcastᵀ mode seal★ s⊑ liftρ liftγ pC N⊑N′ s-shape comp)
    noR okR′ sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL vL′ noL′
    rel@κ⊑κᵀ noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-prefix-valueᵀ
        prefix okL ($ _) noL′ rel)
      (weak-step-store-lineage _
        rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL () noL′
    (⊕⊑⊕ᵀ L⊑L′ M⊑M′) noR okR′ sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL vW noW
    rel@(gen⊑groundᵀ mode seal★ (c⊢ , NW.gen safe)
      gH vV vW′ W⊢ V⊑Wtag q)
    noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-prefix-valueᵀ
        prefix okL
        (vV ⟨ genSafe→inert (NW.safe-gen safe) ⟩)
        noW rel)
      (weak-step-store-lineage _
        rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL vL′ noL′
    (cast⊒⊑ᵀ mode seal★ c⊒ N⊑L′ q c-shape comp)
    noR okR′ sibling =
  source-narrow-sibling source-runtime
    prefix mode seal★ c⊒ vL′ noL′ noR okR′
    inner inner-sibling q c-shape comp
  where
  inner-with-sibling =
    world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
      source-runtime quotient-catchup
      prefix coherent exclusive unique wfL
      (runtime-⟨⟩ okL) vL′ noL′ N⊑L′
      noR okR′ sibling

  inner = proj₁ inner-with-sibling

  inner-sibling = proj₂ inner-with-sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL vL′ noL′
    (cast⊑⊑ᵀ mode seal★ c⊑ N⊑L′ q c-shape comp)
    noR okR′ sibling =
  source-widen-sibling source-runtime
    prefix mode seal★ c⊑ vL′ noL′ noR okR′
    inner inner-sibling q c-shape comp
  where
  inner-with-sibling =
    world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
      source-runtime quotient-catchup
      prefix coherent exclusive unique wfL
      (runtime-⟨⟩ okL) vL′ noL′ N⊑L′
      noR okR′ sibling

  inner = proj₁ inner-with-sibling

  inner-sibling = proj₂ inner-with-sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL
    (vL′ ⟨ inert ⟩) (no•-⟨⟩ noL′)
    (conv⊑convᵀ conversion N⊑L′)
    noR okR′ sibling =
  source-paired-cast-sibling source-runtime
    prefix conversion vL′ noL′ inert noR okR′
    inner inner-sibling
  where
  inner-with-sibling =
    world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
      source-runtime quotient-catchup
      prefix coherent exclusive unique wfL
      (runtime-⟨⟩ okL) vL′ noL′ N⊑L′
      noR okR′ sibling

  inner = proj₁ inner-with-sibling

  inner-sibling = proj₂ inner-with-sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL vL′ noL′
    (conv↑⊑ᵀ c↑ N⊑L′ q replace)
    noR okR′ sibling =
  source-reveal-sibling source-runtime
    prefix c↑ vL′ noL′ noR okR′
    inner inner-sibling q replace
  where
  inner-with-sibling =
    world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
      source-runtime quotient-catchup
      prefix coherent exclusive unique wfL
      (runtime-⟨⟩ okL) vL′ noL′ N⊑L′
      noR okR′ sibling

  inner = proj₁ inner-with-sibling

  inner-sibling = proj₂ inner-with-sibling
world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okL vL′ noL′
    (conv↓⊑ᵀ c↓ N⊑L′ q replace)
    noR okR′ sibling =
  source-conceal-sibling source-runtime
    prefix c↓ vL′ noL′ noR okR′
    inner inner-sibling q replace
  where
  inner-with-sibling =
    world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
      source-runtime quotient-catchup
      prefix coherent exclusive unique wfL
      (runtime-⟨⟩ okL) vL′ noL′ N⊑L′
      noR okR′ sibling

  inner = proj₁ inner-with-sibling

  inner-sibling = proj₂ inner-with-sibling


world-coherent-left-value-catchup-runtime-sibling-prefix-proofᵀ :
  WorldCoherentSourceRuntimeSiblingCatchupᵀ →
  WorldCoherentQuotientFinalRuntimeSiblingCatchupᵀ →
  WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ
world-coherent-left-value-catchup-runtime-sibling-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL
    okL vL′ noL′ primary noR okR′ sibling R⊢ R′⊢ =
  world-coherent-left-value-catchup-runtime-sibling-ambientᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL
    okL vL′ noL′ primary noR okR′
    (allocation-prefixᵀ prefix sibling R⊢ R′⊢)
