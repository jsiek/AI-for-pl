module
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetInertFramingProof
  where

-- File Charter:
--   * Proves right-target inert-cast framing for completed strong right-value
--     catch-up results.
--   * Dispatches the statement's reveal, conceal, narrowing, widening, and
--     identity-mode widening alternatives directly to the focused target-frame
--     infrastructure.
--   * Preserves source silence, transport, type coherence, store lineage,
--     world coherence, source-name exclusivity, and target-store
--     well-formedness.
--   * Contains no result type, outcome type, alias, postulate, hole,
--     incomplete match, permissive option, or compatibility wrapper.

open import Data.List using (_∷_)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl; subst; sym)

open import Coercions using
  (id-onlyᵈ; id-only≤tag-or-idᵈ)
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import NarrowWiden using
  ( narrow-weaken
  ; widen-mode-relax
  ; widen-weaken
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using (applyTyCtxs; applyTys; keep)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( rightStoreⁱ
  )
open import proof.Core.Properties.CastImprecision using
  ( seal★-tag-or-id
  )
open import NuTerms using (no•-⟨⟩; _⟨_⟩)
open import QuotientedTermImprecision using
  ( ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import TermTyping using
  (SealModeStore★; cast-tag-or-id)
open import proof.Core.Properties.CoercionProperties using (modeRename-id-only)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  ( right-value-indexed-catchup
  ; rightCatchupIndexedResult
  ; rightCatchupSourceChangesEmpty
  ; rightCatchupSourceNoBullet
  ; rightCatchupSourceUnchanged
  ; rightCatchupSourceValue
  ; rightCatchupTargetNoBullet
  ; rightCatchupTargetValue
  )
open import proof.Catchup.Simulation.NuImprecisionSimulation using
  ( weak-one-step-target-cast-frame-coherenceᵀ
  ; weak-one-step-target-cast-frame-transportᵀ
  ; weak-one-step-target-cast-frameᵀ
  )
open import proof.Core.Properties.NuNarrowingTransport using
  (apply-narrows-typing)
open import proof.Core.Properties.NuConversionTransport
  using
  ( apply-conceal-conversions-exact
  ; apply-reveal-conversions-exact
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( canonicalIndexedResults
  ; relatedResults
  ; resultRightCtx
  ; resultStore
  ; targetCtxResult
  ; targetStoreResult
  ; targetTailChanges
  ; transportRightReplacementCoherent
  ; transportShapeCoherent
  ; transportType
  ; weak-indexed-result
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (rightStoreⁱ-prefix-inclusion)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( world-coherent-right-value-indexed-catchup
  )
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetInertFramingDef
  using (WorldCoherentRightTargetInertFramingᵀ)
open import proof.Core.Properties.NuWideningTransport using
  (apply-fixed-widens-typing; apply-widens-typing)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; applyCoercions-preserves-Inert; applyTyVars)
open import proof.Core.Properties.TypePreservation using (seal★-weaken)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( cast-shape-applyCoercions
  ; imprecision-composition-shape-transport
  )


world-coherent-right-target-inert-framing-proofᵀ :
  WorldCoherentRightTargetInertFramingᵀ
world-coherent-right-target-inert-framing-proofᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c}
    {p = p} {q = q}
    prefix inert (inj₁ (_ , β , X′ , c↑ , replace))
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent exclusive unique wfR)
    with apply-reveal-conversions-exact
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult (rightCatchupIndexedResult catchup))}
      (weaken-reveal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) c↑)
world-coherent-right-target-inert-framing-proofᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c}
    {p = p} {q = q}
    prefix inert (inj₁ (_ , β , X′ , c↑ , replace))
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent exclusive unique wfR)
    | μ″ , c″↑ =
  world-coherent-right-value-indexed-catchup
    (right-value-indexed-catchup framed
      (rightCatchupSourceChangesEmpty catchup)
      (rightCatchupSourceUnchanged catchup)
      (rightCatchupSourceValue catchup)
      (rightCatchupSourceNoBullet catchup)
      (rightCatchupTargetValue catchup ⟨ inert⁺ ⟩)
      (no•-⟨⟩ (rightCatchupTargetNoBullet catchup)))
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    source-bullet-transport coherent exclusive unique wfR
  where
  indexed = rightCatchupIndexedResult catchup
  inner = weakIndexedResult indexed

  inert⁺ =
    applyCoercions-preserves-Inert (targetTailChanges inner) inert

  final-conversion :
    RevealConversion μ″ (resultRightCtx inner)
      (rightStoreⁱ (resultStore inner))
      (applyTyVars (targetTailChanges inner) β)
      (applyTys (targetTailChanges inner) X′)
      (applyCoercions (targetTailChanges inner) c)
      (applyTys (targetTailChanges inner) A′)
      (applyTys (targetTailChanges inner) B′)
  final-conversion =
    subst
      (λ Δ → RevealConversion μ″ Δ
        (rightStoreⁱ (resultStore inner))
        (applyTyVars (targetTailChanges inner) β)
        (applyTys (targetTailChanges inner) X′)
        (applyCoercions (targetTailChanges inner) c)
        (applyTys (targetTailChanges inner) A′)
        (applyTys (targetTailChanges inner) B′))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → RevealConversion μ″
          (applyTyCtxs (targetTailChanges inner) Δᴿ) Σ
          (applyTyVars (targetTailChanges inner) β)
          (applyTys (targetTailChanges inner) X′)
          (applyCoercions (targetTailChanges inner) c)
          (applyTys (targetTailChanges inner) A′)
          (applyTys (targetTailChanges inner) B′))
        (sym (targetStoreResult inner)) c″↑)

  final-relation =
    ⊑conv↑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)
      (transportRightReplacementCoherent
        (weakIndexedTypeCoherence indexed) replace)

  first =
    weak-one-step-target-cast-frameᵀ inner final-relation

  framed-transport =
    weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport (rightCatchupIndexedResult catchup))

  framed-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence (rightCatchupIndexedResult catchup))

  framed =
    weak-indexed-result first (relatedResults first)
      framed-transport framed-coherence
world-coherent-right-target-inert-framing-proofᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c}
    {p = p} {q = q}
    prefix inert (inj₂ (inj₁ (_ , β , X′ , c↓ , replace)))
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent exclusive unique wfR)
    with apply-conceal-conversions-exact
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult (rightCatchupIndexedResult catchup))}
      (weaken-conceal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) c↓)
world-coherent-right-target-inert-framing-proofᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c}
    {p = p} {q = q}
    prefix inert (inj₂ (inj₁ (_ , β , X′ , c↓ , replace)))
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent exclusive unique wfR)
    | μ″ , c″↓ =
  world-coherent-right-value-indexed-catchup
    (right-value-indexed-catchup framed
      (rightCatchupSourceChangesEmpty catchup)
      (rightCatchupSourceUnchanged catchup)
      (rightCatchupSourceValue catchup)
      (rightCatchupSourceNoBullet catchup)
      (rightCatchupTargetValue catchup ⟨ inert⁺ ⟩)
      (no•-⟨⟩ (rightCatchupTargetNoBullet catchup)))
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    source-bullet-transport coherent exclusive unique wfR
  where
  indexed = rightCatchupIndexedResult catchup
  inner = weakIndexedResult indexed

  inert⁺ =
    applyCoercions-preserves-Inert (targetTailChanges inner) inert

  final-conversion :
    ConcealConversion μ″ (resultRightCtx inner)
      (rightStoreⁱ (resultStore inner))
      (applyTyVars (targetTailChanges inner) β)
      (applyTys (targetTailChanges inner) X′)
      (applyCoercions (targetTailChanges inner) c)
      (applyTys (targetTailChanges inner) A′)
      (applyTys (targetTailChanges inner) B′)
  final-conversion =
    subst
      (λ Δ → ConcealConversion μ″ Δ
        (rightStoreⁱ (resultStore inner))
        (applyTyVars (targetTailChanges inner) β)
        (applyTys (targetTailChanges inner) X′)
        (applyCoercions (targetTailChanges inner) c)
        (applyTys (targetTailChanges inner) A′)
        (applyTys (targetTailChanges inner) B′))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → ConcealConversion μ″
          (applyTyCtxs (targetTailChanges inner) Δᴿ) Σ
          (applyTyVars (targetTailChanges inner) β)
          (applyTys (targetTailChanges inner) X′)
          (applyCoercions (targetTailChanges inner) c)
          (applyTys (targetTailChanges inner) A′)
          (applyTys (targetTailChanges inner) B′))
        (sym (targetStoreResult inner)) c″↓)

  final-relation =
    ⊑conv↓ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)
      (transportRightReplacementCoherent
        (weakIndexedTypeCoherence indexed) replace)

  first =
    weak-one-step-target-cast-frameᵀ inner final-relation

  framed-transport =
    weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport (rightCatchupIndexedResult catchup))

  framed-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence (rightCatchupIndexedResult catchup))

  framed =
    weak-indexed-result first (relatedResults first)
      framed-transport framed-coherence
world-coherent-right-target-inert-framing-proofᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c}
    {p = p} {q = q}
    prefix inert
    (inj₂ (inj₂ (inj₁
      (_ , shape , mode , seal★ , c⊒ , shape-proof , comp))))
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent exclusive unique wfR)
    with apply-narrows-typing
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult (rightCatchupIndexedResult catchup))}
      mode
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c⊒)
world-coherent-right-target-inert-framing-proofᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c}
    {p = p} {q = q}
    prefix inert
    (inj₂ (inj₂ (inj₁
      (_ , shape , mode , seal★ , c⊒ , shape-proof , comp))))
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent exclusive unique wfR)
    | μ″ , mode″ , seal★″ , c″⊒ =
  world-coherent-right-value-indexed-catchup
    (right-value-indexed-catchup framed
      (rightCatchupSourceChangesEmpty catchup)
      (rightCatchupSourceUnchanged catchup)
      (rightCatchupSourceValue catchup)
      (rightCatchupSourceNoBullet catchup)
      (rightCatchupTargetValue catchup ⟨ inert⁺ ⟩)
      (no•-⟨⟩ (rightCatchupTargetNoBullet catchup)))
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    source-bullet-transport coherent exclusive unique wfR
  where
  indexed = rightCatchupIndexedResult catchup
  inner = weakIndexedResult indexed

  inert⁺ =
    applyCoercions-preserves-Inert (targetTailChanges inner) inert

  final-seal :
    SealModeStore★ μ″ (rightStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ″)
      (sym (targetStoreResult inner)) seal★″

  final-cast :
    μ″ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
      ⊢ applyCoercions (targetTailChanges inner) c
        ∶ applyTys (targetTailChanges inner) A′
          ⊒ applyTys (targetTailChanges inner) B′
  final-cast =
    subst
      (λ Δ → μ″ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner) c
          ∶ applyTys (targetTailChanges inner) A′
            ⊒ applyTys (targetTailChanges inner) B′)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → μ″ ∣ applyTyCtxs (targetTailChanges inner) Δᴿ ∣ Σ
          ⊢ applyCoercions (targetTailChanges inner) c
            ∶ applyTys (targetTailChanges inner) A′
              ⊒ applyTys (targetTailChanges inner) B′)
        (sym (targetStoreResult inner)) c″⊒)

  final-relation =
    ⊑cast⊒ᵀ mode″ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions
        (targetTailChanges inner) shape-proof)
      (imprecision-composition-shape-transport
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed) q)
        refl
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed) p)
        comp)

  first =
    weak-one-step-target-cast-frameᵀ inner final-relation

  framed-transport =
    weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport (rightCatchupIndexedResult catchup))

  framed-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence (rightCatchupIndexedResult catchup))

  framed =
    weak-indexed-result first (relatedResults first)
      framed-transport framed-coherence
world-coherent-right-target-inert-framing-proofᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c}
    {p = p} {q = q}
    prefix inert
    (inj₂ (inj₂ (inj₂ (inj₁
      (_ , shape , mode , seal★ , c⊑ , shape-proof , comp)))))
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent exclusive unique wfR)
    with apply-widens-typing
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult (rightCatchupIndexedResult catchup))}
      mode
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c⊑)
world-coherent-right-target-inert-framing-proofᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c}
    {p = p} {q = q}
    prefix inert
    (inj₂ (inj₂ (inj₂ (inj₁
      (_ , shape , mode , seal★ , c⊑ , shape-proof , comp)))))
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent exclusive unique wfR)
    | μ″ , mode″ , seal★″ , c″⊑ =
  world-coherent-right-value-indexed-catchup
    (right-value-indexed-catchup framed
      (rightCatchupSourceChangesEmpty catchup)
      (rightCatchupSourceUnchanged catchup)
      (rightCatchupSourceValue catchup)
      (rightCatchupSourceNoBullet catchup)
      (rightCatchupTargetValue catchup ⟨ inert⁺ ⟩)
      (no•-⟨⟩ (rightCatchupTargetNoBullet catchup)))
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    source-bullet-transport coherent exclusive unique wfR
  where
  indexed = rightCatchupIndexedResult catchup
  inner = weakIndexedResult indexed

  inert⁺ =
    applyCoercions-preserves-Inert (targetTailChanges inner) inert

  final-seal :
    SealModeStore★ μ″ (rightStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ″)
      (sym (targetStoreResult inner)) seal★″

  final-cast :
    μ″ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
      ⊢ applyCoercions (targetTailChanges inner) c
        ∶ applyTys (targetTailChanges inner) A′
          ⊑ applyTys (targetTailChanges inner) B′
  final-cast =
    subst
      (λ Δ → μ″ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner) c
          ∶ applyTys (targetTailChanges inner) A′
            ⊑ applyTys (targetTailChanges inner) B′)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → μ″ ∣ applyTyCtxs (targetTailChanges inner) Δᴿ ∣ Σ
          ⊢ applyCoercions (targetTailChanges inner) c
            ∶ applyTys (targetTailChanges inner) A′
              ⊑ applyTys (targetTailChanges inner) B′)
        (sym (targetStoreResult inner)) c″⊑)

  final-relation =
    ⊑cast⊑ᵀ mode″ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions
        (targetTailChanges inner) shape-proof)
      (imprecision-composition-shape-transport
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed) p)
        refl
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed) q)
        comp)

  first =
    weak-one-step-target-cast-frameᵀ inner final-relation

  framed-transport =
    weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport (rightCatchupIndexedResult catchup))

  framed-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence (rightCatchupIndexedResult catchup))

  framed =
    weak-indexed-result first (relatedResults first)
      framed-transport framed-coherence
world-coherent-right-target-inert-framing-proofᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c}
    {p = p} {q = q}
    prefix inert
    (inj₂ (inj₂ (inj₂ (inj₂
      (seal★ , shape , c⊑ , shape-proof , comp)))))
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent exclusive unique wfR) =
  world-coherent-right-value-indexed-catchup
    (right-value-indexed-catchup framed
      (rightCatchupSourceChangesEmpty catchup)
      (rightCatchupSourceUnchanged catchup)
      (rightCatchupSourceValue catchup)
      (rightCatchupSourceNoBullet catchup)
      (rightCatchupTargetValue catchup ⟨ inert⁺ ⟩)
      (no•-⟨⟩ (rightCatchupTargetNoBullet catchup)))
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    source-bullet-transport coherent exclusive unique wfR
  where
  indexed = rightCatchupIndexedResult catchup
  inner = weakIndexedResult indexed

  inert⁺ =
    applyCoercions-preserves-Inert (targetTailChanges inner) inert

  c″⊑ =
    apply-fixed-widens-typing
      {χs = keep ∷ targetTailChanges inner}
      (modeRename-id-only suc)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c⊑)

  final-cast :
    id-onlyᵈ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
      ⊢ applyCoercions (targetTailChanges inner) c
        ∶ applyTys (targetTailChanges inner) A′
          ⊑ applyTys (targetTailChanges inner) B′
  final-cast =
    subst
      (λ Δ → id-onlyᵈ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner) c
          ∶ applyTys (targetTailChanges inner) A′
            ⊑ applyTys (targetTailChanges inner) B′)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → id-onlyᵈ
          ∣ applyTyCtxs (targetTailChanges inner) Δᴿ ∣ Σ
          ⊢ applyCoercions (targetTailChanges inner) c
            ∶ applyTys (targetTailChanges inner) A′
              ⊑ applyTys (targetTailChanges inner) B′)
        (sym (targetStoreResult inner)) c″⊑)

  final-relation =
    ⊑cast⊑ᵀ cast-tag-or-id seal★-tag-or-id
      (widen-mode-relax id-only≤tag-or-idᵈ final-cast)
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions
        (targetTailChanges inner) shape-proof)
      (imprecision-composition-shape-transport
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed) p)
        refl
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed) q)
        comp)

  first =
    weak-one-step-target-cast-frameᵀ inner final-relation

  framed-transport =
    weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport (rightCatchupIndexedResult catchup))

  framed-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence (rightCatchupIndexedResult catchup))

  framed =
    weak-indexed-result first (relatedResults first)
      framed-transport framed-coherence
