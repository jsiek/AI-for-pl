module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownFrameProof
  where

-- File Charter:
--   * Proves target `ξ-⟨⟩` framing through a quotient downcast followed by
--     its enclosing quotient widening.
--   * Proves one direct inner-blame root for every admitted spine mode by
--     lifting source blame through the two enclosing source casts.
--   * Uses ordinary prefix-aware one-step recursion only at the embedded QTI
--     body of `paired-downᵀ`.
--   * Preserves the arbitrary leading target store change, target tail,
--     relational-store lineage, and all indexed transport coherence.
--   * Contains no active downcast root, quotient application case,
--     dispatcher, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (refl)
import CastImprecisionShape as CastShape
open import Coercions using
  ( Coercion
  ; _∣_⊢_∶_=⇒_
  )
open import Conversion using
  (conversion↑⇒coercion; conversion↓⇒coercion)
open import Data.List using ([]; _∷_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import NarrowWiden using
  ( narrow-weaken
  ; widen-weaken
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using
  ( keep
  ; StoreChange
  ; applyCoercion
  ; applyTy
  ; applyTys
  ; _—→[_]_
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  (RuntimeOK; Term; blame; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; closeᵀ
  ; quotient-cast-widening
  ; quotient-id-widening
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import QuotientImprecisionCompatibility using
  ( ReductionClosedQuotientWideningCompatible
  ; QuotientNarrowingEliminationCompatible
  ; SpineCastMode
  )
open import TermTyping using
  ( _∣_∣_⊢_⦂_
  ; ⊢⟨⟩↑
  ; ⊢⟨⟩↓
  ; ⊢⟨⟩⊒
  ; ⊢⟨⟩⊑
  )
open import Types using (Ty; TyCtx)
open import proof.Core.Properties.CoercionProperties using
  (coercion-endpoints-unique)
open import proof.Core.Properties.NarrowWidenProperties using
  (narrowing⇒coercion; widening⇒coercion)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; cast-↠)
open import
  proof.Core.Properties.NuCastImprecisionShapeProperties
  using (cast-shape-applyCoercions)
open import proof.Core.Properties.NuRuntimeProperties using (runtime-⟨⟩)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepIndexedResult
  ; WeakOneStepResult
  ; canonicalIndexedResults
  ; relatedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceCatchup
  ; sourceChanges
  ; sourceCtxResult
  ; sourceResult
  ; sourceStoreResult
  ; sourceTypeResult
  ; targetCtxResult
  ; targetResult
  ; targetStoreResult
  ; targetTail
  ; targetTailChanges
  ; targetTypeResult
  ; transportAllBody
  ; transportAllBodyPairedReplacementCoherent
  ; transportAllCoherent
  ; transportArrowCoherent
  ; transportLeftReplacementCoherent
  ; transportNo•Terms
  ; transportPairedReplacementCoherent
  ; transportRightBody
  ; transportRightBodyRightReplacementCoherent
  ; transportRightBodyShapeCoherent
  ; transportRightReplacementCoherent
  ; transportShapeCoherent
  ; transportSourceNu
  ; transportSourceNuBodyLeftReplacementCoherent
  ; transportType
  ; weak-indexed-result
  ; weak-step-result
  ; weak-step-transport
  ; weak-step-type-coherence
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-indexed-outcome-related
  ; world-indexed-outcome-source-blame
  )
open import
  proof.WorldCoherent.Right.OneStep.Cases.NuImprecisionWorldCoherentRightOneStepPrefixDef
  using (WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ)
open import
  proof.OneStep.NuImprecisionWeakOneStepReplacementTransport
  using
  ( weak-one-step-transport-quotientᵀ
  ; weak-one-step-transport-quotient-boundary-square
  )
open import
  proof.Right.Core.NuImprecisionQuotientDownTransportProof
  using (quotient-down-transportᵀ)
open import
  proof.Right.Core.NuImprecisionQuotientWideningTransportProof
  using (quotient-widening-pair-transportᵀ)
open import
  proof.OneStep.NuImprecisionWeakOneStepQuotientCompatibilityTransport
  using (weak-one-step-transport-quotient-widening-compatibleᵀ)
open import proof.Target.Core.NuImprecisionTargetBlameCatchup using
  (cast-blame-tailᵀ; left-catchup-target-blameᵀ)


private
  cast-body-typing :
    ∀ {Δ Σ Γ M c D A} →
    Δ ∣ Σ ⊢ c ∶ D =⇒ A →
    Δ ∣ Σ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ A →
    Δ ∣ Σ ∣ Γ ⊢ M ⦂ D
  cast-body-typing c⊢ (⊢⟨⟩↑ d⊢ M⊢)
      with coercion-endpoints-unique
        c⊢ (_ , conversion↑⇒coercion d⊢)
  cast-body-typing c⊢ (⊢⟨⟩↑ d⊢ M⊢)
      | refl , refl = M⊢
  cast-body-typing c⊢ (⊢⟨⟩↓ d⊢ M⊢)
      with coercion-endpoints-unique
        c⊢ (_ , conversion↓⇒coercion d⊢)
  cast-body-typing c⊢ (⊢⟨⟩↓ d⊢ M⊢)
      | refl , refl = M⊢
  cast-body-typing c⊢ (⊢⟨⟩⊒ mode seal★ d⊢ M⊢)
      with coercion-endpoints-unique
        c⊢ (narrowing⇒coercion (_ , d⊢))
  cast-body-typing c⊢ (⊢⟨⟩⊒ mode seal★ d⊢ M⊢)
      | refl , refl = M⊢
  cast-body-typing c⊢ (⊢⟨⟩⊑ mode seal★ d⊢ M⊢)
      with coercion-endpoints-unique
        c⊢ (widening⇒coercion (_ , d⊢))
  cast-body-typing c⊢ (⊢⟨⟩⊑ mode seal★ d⊢ M⊢)
      | refl , refl = M⊢


  source-widening-coercion :
    ∀ {Φ Δᴸ Δᴿ ρᵇ ρ u u′ D D′ A A′} →
    StoreImpPrefix {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} ρᵇ ρ →
    QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ D D′ A A′ →
    Δᴸ ∣ leftStoreⁱ ρ ⊢ u ∶ D =⇒ A
  source-widening-coercion prefix
      (quotient-id-widening u⊑ u′⊑) =
    widening⇒coercion
      (_ , widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) u⊑)
  source-widening-coercion prefix
      (quotient-cast-widening
        mode seal★ u⊑ mode′ seal★′ u′⊑) =
    widening⇒coercion
      (_ , widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) u⊑)


  target-widening-coercion :
    ∀ {Φ Δᴸ Δᴿ ρᵇ ρ u u′ D D′ A A′} →
    StoreImpPrefix {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} ρᵇ ρ →
    QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ D D′ A A′ →
    Δᴿ ∣ rightStoreⁱ ρ ⊢ u′ ∶ D′ =⇒ A′
  target-widening-coercion prefix
      (quotient-id-widening u⊑ u′⊑) =
    widening⇒coercion
      (_ , widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) u′⊑)
  target-widening-coercion prefix
      (quotient-cast-widening
        mode seal★ u⊑ mode′ seal★′ u′⊑) =
    widening⇒coercion
      (_ , widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) u′⊑)


  double-cast-result :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M M′ : Term} {C C′ A A′ : Ty}
      {d d′ u u′ : Coercion} {χ : StoreChange}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    (inner : WeakOneStepResult ρ M M′ C C′ χ) →
    (resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ
        (sourceResult inner ⟨
          applyCoercions (sourceChanges inner) d ⟩) ⟨
            applyCoercions (sourceChanges inner) u ⟩
        ⊑
        (targetResult inner ⟨
          applyCoercions (targetTailChanges inner)
            (applyCoercion χ d′) ⟩) ⟨
              applyCoercions (targetTailChanges inner)
                (applyCoercion χ u′) ⟩
        ⦂ applyTys (sourceChanges inner) A
          ⊑ applyTys (targetTailChanges inner) (applyTy χ A′)
        ∶ transportType inner pA) →
    WeakOneStepResult ρ
      ((M ⟨ d ⟩) ⟨ u ⟩)
      ((M′ ⟨ applyCoercion χ d′ ⟩) ⟨ applyCoercion χ u′ ⟩)
      A A′ χ
  double-cast-result
      {M = M} {M′ = M′} {A = A} {A′ = A′}
      {d = d} {d′ = d′} {u = u} {u′ = u′}
      {χ = χ} {pA = pA} inner final =
    weak-step-result
      (sourceChanges inner)
      (targetTailChanges inner)
      ((sourceResult inner ⟨
        applyCoercions (sourceChanges inner) d ⟩) ⟨
          applyCoercions (sourceChanges inner) u ⟩)
      ((targetResult inner ⟨
        applyCoercions (targetTailChanges inner)
          (applyCoercion χ d′) ⟩) ⟨
            applyCoercions (targetTailChanges inner)
              (applyCoercion χ u′) ⟩)
      (resultCtx inner)
      (resultLeftCtx inner)
      (resultRightCtx inner)
      (sourceCtxResult inner)
      (targetCtxResult inner)
      (resultStore inner)
      (applyTys (sourceChanges inner) A)
      (applyTys (targetTailChanges inner) (applyTy χ A′))
      refl
      refl
      (transportType inner)
      (transportAllBody inner)
      (transportRightBody inner)
      (transportSourceNu inner)
      (transportType inner pA)
      (cast-↠ (cast-↠ (sourceCatchup inner)))
      (cast-↠ (cast-↠ (targetTail inner)))
      (sourceStoreResult inner)
      (targetStoreResult inner)
      final


world-coherent-right-one-step-quotient-down-target-blame-rootᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {M : Term} {C C′ D D′ A A′ : Ty}
    {d d′ u u′ : Coercion} {d-shape d′-shape u-shape u′-shape}
    {μ μ′}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  RuntimeOK ((M ⟨ d ⟩) ⟨ u ⟩) →
  SpineCastMode (leftStoreⁱ ρᵇ) μ →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ ⊢ d ∶ C ⊒ D →
  CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
  SpineCastMode (rightStoreⁱ ρᵇ) μ′ →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ ⊢ d′ ∶ C′ ⊒ D′ →
  CastShape.narrowing CastShape.⊢ᶜ d′ ⦂ d′-shape →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ M ⊑ blame ⦂ C ⊑ C′ ∶ pC →
  d-shape ；⌊ pC ⌋≋ᵖ qD ； d′-shape →
  QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ D D′ A A′ →
  CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
  CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape →
  u-shape ；⌊ pA ⌋≋ᵖ qD ； u′-shape →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (M ⟨ d ⟩) ⟨ u ⟩}
    {N′ = blame ⟨ u′ ⟩} {χ = keep} {ρ = ρ} pA
world-coherent-right-one-step-quotient-down-target-blame-rootᵀ
    ok-source source-mode d⊒ d-shape target-mode d′⊒ d′-shape
    M⊑blame down-square
    widening u-shape u′-shape up-square
    with left-catchup-target-blameᵀ
      (runtime-⟨⟩ (runtime-⟨⟩ ok-source)) M⊑blame
world-coherent-right-one-step-quotient-down-target-blame-rootᵀ
    ok-source source-mode d⊒ d-shape target-mode d′⊒ d′-shape
    M⊑blame down-square
    widening u-shape u′-shape up-square
    | χs , M↠blame =
  world-indexed-outcome-source-blame
    (cast-blame-tailᵀ (cast-blame-tailᵀ M↠blame))


world-coherent-right-one-step-quotient-down-frameᵀ :
  WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L′ : Term} {C C′ D D′ A A′ : Ty}
    {d d′ u u′ : Coercion} {d-shape d′-shape u-shape u′-shape}
    {μ μ′} {χ : StoreChange}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreImpPrefix ρᵇ ρ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK ((M ⟨ d ⟩) ⟨ u ⟩) →
  RuntimeOK ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ (M ⟨ d ⟩) ⟨ u ⟩ ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ ∣ []
    ⊢ (M′ ⟨ d′ ⟩) ⟨ u′ ⟩ ⦂ A′ →
  SpineCastMode (leftStoreⁱ ρᵇ) μ →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ ⊢ d ∶ C ⊒ D →
  CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
  SpineCastMode (rightStoreⁱ ρᵇ) μ′ →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ ⊢ d′ ∶ C′ ⊒ D′ →
  CastShape.narrowing CastShape.⊢ᶜ d′ ⦂ d′-shape →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ C ⊑ C′ ∶ pC →
  d-shape ；⌊ pC ⌋≋ᵖ qD ； d′-shape →
  QuotientNarrowingEliminationCompatible
    Φ Δᴸ Δᴿ d d′ pC qD d-shape d′-shape →
  QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ D D′ A A′ →
  CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
  CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape →
  u-shape ；⌊ pA ⌋≋ᵖ qD ； u′-shape →
  ReductionClosedQuotientWideningCompatible
    Φ Δᴸ Δᴿ u u′ qD pA u-shape u′-shape →
  M′ —→[ χ ] L′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (M ⟨ d ⟩) ⟨ u ⟩}
    {N′ = (L′ ⟨ applyCoercion χ d′ ⟩) ⟨ applyCoercion χ u′ ⟩}
    {χ = χ} {ρ = ρ} pA
world-coherent-right-one-step-quotient-down-frameᵀ
    recurse
    {ρᵇ = ρᵇ} {ρ = ρ} {M = M} {M′ = M′} {L′ = L′}
    {C = C} {C′ = C′} {D = D} {D′ = D′} {A = A} {A′ = A′}
    {d = d} {d′ = d′} {u = u} {u′ = u′}
    {χ = χ} {pC = pC} {pA = pA}
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    source-mode d⊒ d-shape target-mode d′⊒ d′-shape M⊑M′
    down-square elimination
    widening u-shape u′-shape up-square compatible
    target-step =
  frame
    (recurse prefix coherent exclusive unique wfL wfR
      (runtime-⟨⟩ (runtime-⟨⟩ ok-source))
      (runtime-⟨⟩ (runtime-⟨⟩ ok-target))
      M⊑M′ source-body-typing target-body-typing target-step)
  where
  source-down-current =
    narrowing⇒coercion
      (_ , narrow-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) d⊒)

  target-down-current =
    narrowing⇒coercion
      (_ , narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) d′⊒)

  source-body-typing =
    cast-body-typing source-down-current
      (cast-body-typing
        (source-widening-coercion prefix widening) source-typing)

  target-body-typing =
    cast-body-typing target-down-current
      (cast-body-typing
        (target-widening-coercion prefix widening) target-typing)

  frame :
    WorldCoherentWeakOneStepIndexedOutcome
      {M = M} {N′ = L′} {χ = χ} {ρ = ρ} pC →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = (M ⟨ d ⟩) ⟨ u ⟩}
      {N′ =
        (L′ ⟨ applyCoercion χ d′ ⟩) ⟨ applyCoercion χ u′ ⟩}
      {χ = χ} {ρ = ρ} pA
  frame
      (world-indexed-outcome-related
        indexed lineage final-coherent final-exclusive final-unique) =
    world-indexed-outcome-related
      framed-indexed
      (weak-step-store-lineage
        (lineageStore lineage)
        (lineageEmbedding lineage)
        (lineagePrefix lineage))
      final-coherent final-exclusive final-unique
    where
    inner = weakIndexedResult indexed

    final-down =
      quotient-down-transportᵀ
        prefix indexed source-mode d⊒ d-shape
        target-mode d′⊒ d′-shape down-square
        final-unique elimination

    final-widening =
      quotient-widening-pair-transportᵀ prefix inner widening

    final-compatible =
      weak-one-step-transport-quotient-widening-compatibleᵀ
        inner (weakIndexedTypeCoherence indexed)
        final-unique compatible

    final-relation =
      closeᵀ final-down final-widening (transportType inner pA)
        (cast-shape-applyCoercions
          (sourceChanges inner) u-shape)
        (cast-shape-applyCoercions
          (χ ∷ targetTailChanges inner) u′-shape)
        (weak-one-step-transport-quotient-boundary-square
          inner (weakIndexedTypeCoherence indexed) up-square)
        final-compatible

    framed = double-cast-result inner final-relation

    framed-indexed =
      weak-indexed-result framed (relatedResults framed)
        (weak-step-transport
          (transportNo•Terms (weakIndexedTransport indexed)))
        (weak-step-type-coherence
          (transportArrowCoherent (weakIndexedTypeCoherence indexed))
          (transportAllCoherent (weakIndexedTypeCoherence indexed))
          (transportShapeCoherent (weakIndexedTypeCoherence indexed))
          (transportRightBodyShapeCoherent
            (weakIndexedTypeCoherence indexed))
          (transportLeftReplacementCoherent
            (weakIndexedTypeCoherence indexed))
          (transportRightReplacementCoherent
            (weakIndexedTypeCoherence indexed))
          (transportPairedReplacementCoherent
            (weakIndexedTypeCoherence indexed))
          (transportAllBodyPairedReplacementCoherent
            (weakIndexedTypeCoherence indexed))
          (transportSourceNuBodyLeftReplacementCoherent
            (weakIndexedTypeCoherence indexed))
          (transportRightBodyRightReplacementCoherent
            (weakIndexedTypeCoherence indexed)))
  frame (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame
      (cast-blame-tailᵀ (cast-blame-tailᵀ source↠))
