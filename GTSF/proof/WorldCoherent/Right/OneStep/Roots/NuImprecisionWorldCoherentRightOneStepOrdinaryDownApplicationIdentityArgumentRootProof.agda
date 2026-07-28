module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepOrdinaryDownApplicationIdentityArgumentRootProof
  where

-- File Charter:
--   * Implements the identity root for an active target narrowing in the
--     argument of `ordinary-down-applicationᵖᵀ`.
--   * Collapses the reflexive quotient boundary against the target identity
--     and builds the exact source-only narrowing application residual beneath
--     the outer widening.
--   * Keeps arbitrary cast modes, both original quotient boundary squares,
--     and the ambient store prefix.
--   * Contains no intermediate imprecision index, QTIP-to-QTI conversion,
--     paired-widening compatibility, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (_≡_; refl)
import CastImprecisionShape as CastShape
import Coercions as C
open import Coercions using (Coercion; ModeEnv; id)
open import Data.List using ([])
open import Data.Product using (_,_)
open import ForallPermutation using (≈∀-refl; quotientᵖ)
open import ImprecisionComposition using
  ( ⌊_⌋
  ; idˣˢ
  ; idιˢ
  ; _；_≋_
  ; _；⌊_⌋≋ᵖ_；_
  ; comp-idˣ-idˣ
  ; comp-idι-idι
  ; comp-ν
  ; compose-right-id★
  ; quotient-boundary-square
  ; source-perm-refl
  )
open import ImprecisionWf using
  (ImpCtx; _↦_; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuReduction using
  ( keep
  ; pure-step
  ; shift-keep
  ; β-id
  ; ξ-·₂
  ; ξ-⟨⟩
  ; _—→_
  ; _—→[_]_
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  (RuntimeOK; Term; Value; _·_; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; allocation-prefixᵀ
  ; prefix-reflⁱ
  ; source-down-applicationᵖᵀ
  ; up⊑upᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (CastMode; SealModeStore★; _∣_∣_⊢_⦂_)
open import Types using (Ty; TyCtx; _⇒_)
open import proof.Core.Properties.TypePreservation using (preservation)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import proof.OneStep.NuImprecisionOneStepRelated using
  (weak-one-step-indexed-relatedᵀ)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (weak-step-store-lineage)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (rel-store-embedding-reflⁱ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-indexed-outcome-related
  )


private
  preservation-keep :
    ∀ {Δ Σ M N A} →
    StoreWf Δ Σ →
    RuntimeOK M →
    Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
    M —→[ keep ] N →
    Δ ∣ Σ ∣ [] ⊢ N ⦂ A
  preservation-keep {Δ = Δ} {Σ = Σ} {M = M} {N = N} {A = A}
      wfΣ okM M⊢ M→N =
    preservation
      {Δ = Δ} {Σ = Σ} {M = M} {N = N} {A = A} {χ = keep}
      wfΣ okM M⊢ M→N

  compose-right-idˣ :
    ∀ {source result} →
    source ； idˣˢ ≋ result →
    source ≡ result
  compose-right-idˣ comp-idˣ-idˣ = refl
  compose-right-idˣ (comp-ν comp)
      with compose-right-idˣ comp
  compose-right-idˣ (comp-ν comp) | refl = refl

  compose-right-idι :
    ∀ {source result} →
    source ； idιˢ ≋ result →
    source ≡ result
  compose-right-idι comp-idι-idι = refl
  compose-right-idι (comp-ν comp)
      with compose-right-idι comp
  compose-right-idι (comp-ν comp) | refl = refl

  identity-target-quotient-source-composition :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {X X′ C C′ I : Ty}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
      {source-shape target-shape} →
    CastShape.narrowing CastShape.⊢ᶜ id I ⦂ target-shape →
    source-shape ；⌊ pX ⌋≋ᵖ
      (quotientᵖ ≈∀-refl pC ≈∀-refl) ； target-shape →
    source-shape ； ⌊ pX ⌋ ≋ ⌊ pC ⌋
  identity-target-quotient-source-composition
      CastShape.shape-id-var
      (quotient-boundary-square
        source-perm-refl source-composition
        source-perm-refl target-composition)
      with compose-right-idˣ target-composition
  identity-target-quotient-source-composition
      CastShape.shape-id-var
      (quotient-boundary-square
        source-perm-refl source-composition
        source-perm-refl target-composition)
      | refl =
    source-composition
  identity-target-quotient-source-composition
      CastShape.shape-id-base
      (quotient-boundary-square
        source-perm-refl source-composition
        source-perm-refl target-composition)
      with compose-right-idι target-composition
  identity-target-quotient-source-composition
      CastShape.shape-id-base
      (quotient-boundary-square
        source-perm-refl source-composition
        source-perm-refl target-composition)
      | refl =
    source-composition
  identity-target-quotient-source-composition
      CastShape.shape-id-star
      (quotient-boundary-square
        source-perm-refl source-composition
        source-perm-refl target-composition)
      with compose-right-id★ target-composition
  identity-target-quotient-source-composition
      CastShape.shape-id-star
      (quotient-boundary-square
        source-perm-refl source-composition
        source-perm-refl target-composition)
      | refl =
    source-composition


world-coherent-right-one-step-ordinary-down-application-identity-argument-root-proofᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ M M′ M₁′ : Term}
    {X X′ C C′ B B′ E E′ I : Ty}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {pE : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
    {d u u′ : Coercion}
    {μ μ′ : ModeEnv}
    {d-shape d′-shape u-shape u′-shape} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreImpPrefix ρᵇ ρ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK ((L · (M ⟨ d ⟩)) ⟨ u ⟩) →
  RuntimeOK ((L′ · (M′ ⟨ id I ⟩)) ⟨ u′ ⟩) →
  Δᴸ ∣ leftStoreⁱ ρ ∣ []
    ⊢ (L · (M ⟨ d ⟩)) ⟨ u ⟩ ⦂ E →
  Δᴿ ∣ rightStoreⁱ ρ ∣ []
    ⊢ (L′ · (M′ ⟨ id I ⟩)) ⟨ u′ ⟩ ⦂ E′ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρᵇ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ ⊢ d ∶ X ⊒ C →
  CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρᵇ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ ⊢ id I ∶ X′ ⊒ C′ →
  CastShape.narrowing CastShape.⊢ᶜ id I ⦂ d′-shape →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ C ⇒ B ⊑ C′ ⇒ B′ ∶ pC ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ X ⊑ X′ ∶ pX →
  d-shape ；⌊ pX ⌋≋ᵖ
    (quotientᵖ ≈∀-refl pC ≈∀-refl) ； d′-shape →
  QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ B B′ E E′ →
  CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
  CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape →
  u-shape ；⌊ pE ⌋≋ᵖ
    (quotientᵖ ≈∀-refl pB ≈∀-refl) ； u′-shape →
  Value L′ →
  Value M′ →
  M′ ⟨ id I ⟩ —→ M₁′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (L · (M ⟨ d ⟩)) ⟨ u ⟩}
    {N′ = (L′ · M₁′) ⟨ u′ ⟩}
    {χ = keep} {ρ = ρ} pE
world-coherent-right-one-step-ordinary-down-application-identity-argument-root-proofᵀ
    {Δᴿ = Δᴿ} {ρ = ρ} {L′ = L′} {M′ = M′}
    {E′ = E′} {I = I} {pC = pC} {pE = pE} {u′ = u′}
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′
    (C.cast-id wfI allowed , narrow-id) d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    vL′ vM′ root@(β-id vV′) =
  world-indexed-outcome-related
    (weak-one-step-indexed-relatedᵀ current-relation)
    (weak-step-store-lineage
      _ rel-store-embedding-reflⁱ prefix-reflⁱ)
    coherent exclusive unique
  where
  quotient-application =
    source-down-applicationᵖᵀ
      mode seal★ d⊒ d-shape L⊑L′ M⊑M′
      (identity-target-quotient-source-composition
        d′-shape down-square)
      vL′ vM′

  base-relation =
    up⊑upᵀ
      quotient-application
      widening pE
      u-shape u′-shape up-square

  target-step =
    ξ-⟨⟩ (ξ-·₂ vL′ shift-keep (pure-step root))

  target-result-typing :
    Δᴿ ∣ rightStoreⁱ ρ ∣ []
      ⊢ (L′ · M′) ⟨ u′ ⟩ ⦂ E′
  target-result-typing =
    preservation-keep wfR ok-target target-typing target-step

  current-relation =
    allocation-prefixᵀ prefix base-relation
      source-typing target-result-typing
