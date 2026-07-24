module
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowFunUntagGenRootContextProof
  where

-- File Charter:
--   * Proves the contextual eager target `fun-untag-gen` narrowing root.
--   * Builds a local terminal seed in the inner result world, cancels the
--     function tag, inertly frames the transported `gen`, and resumes after
--     the whole-cast `β-seq` step.
--   * Takes every major contextual capability as a theorem argument.
--   * Contains no result/view/outcome type, postulate, hole, permissive
--     option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import Data.List using ([]; _∷_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; _×_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym)
open import ImprecisionWf using
  ( ImpCtx
  ; ∀ⁱ_
  ; ν
  ; _∣_⊢_⊑_⊣_
  )
import NarrowWiden as NW
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuReduction using
  ( applyStores
  ; applyTyCtxs
  ; applyTys
  ; keep
  ; pure-step
  ; _—→[_]_
  )
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using
  (No•; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( prefix-reflⁱ
  ; ⊑cast⊒ᵀ
  )
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using
  (Ground; Ty; TyCtx; ★; ★⇒★; ＇_; ‵_; ⇑ᵗ; _⇒_; `∀)
open import proof.Right.Core.NuImprecisionRightContextAction using
  (applyRightImpCtxChanges)
open import proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix using
  (RightOnlyStoreImpPrefix)
open import proof.Target.SealTag.NuImprecisionTargetGroundUniqueness using
  (universal-star-to-function)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
  using
  ( rightCatchupIndexedResult
  ; rightCatchupSourceNoBullet
  ; rightCatchupSourceUnchanged
  ; rightCatchupSourceValue
  ; rightCatchupTargetNoBullet
  ; rightCatchupTargetValue
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( apply-narrows-typing
  ; nu-term-imprecision-transport-typesᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepResult
  ; canonicalIndexedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceResult
  ; targetCtxResult
  ; targetResult
  ; targetStoreResult
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (lineageStore)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (rightStoreⁱ-prefix-inclusion)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; world-coherent-right-value-indexed-catchup
  ; worldRightCatchupResult
  ; worldRightCatchupStoreLineage
  )
open import
  proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalContextDef
  using (WorldCoherentRightValueTerminalContextᵀ)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowFunUntagGenRootContextDef
  using (WorldCoherentRightTargetNarrowFunUntagGenRootContextᵀ)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowUntagRootContextDef
  using (WorldCoherentRightTargetNarrowUntagRootContextᵀ)
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetInertFramingContextDef
  using (WorldCoherentRightTargetInertFramingContextᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetStepResumeContextDef
  using (WorldCoherentRightTargetStepResumeContextᵀ)
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions
  ; applyCoercions-preserves-Inert
  ; applyTys-⇒
  )
open import proof.Core.Properties.TypePreservation using
  (seal★-weaken)


private
  applyTy-preserves-Ground :
    ∀ χ {G} →
    Ground G →
    Ground (NuReduction.applyTy χ G)
  applyTy-preserves-Ground keep gG = gG
  applyTy-preserves-Ground (NuReduction.bind A) (＇ α) = ＇ _
  applyTy-preserves-Ground (NuReduction.bind A) (‵ ι) = ‵ ι
  applyTy-preserves-Ground (NuReduction.bind A) ★⇒★ = ★⇒★

  applyTys-preserves-Ground :
    ∀ χs {G} →
    Ground G →
    Ground (applyTys χs G)
  applyTys-preserves-Ground [] gG = gG
  applyTys-preserves-Ground (χ ∷ χs) gG =
    applyTys-preserves-Ground χs (applyTy-preserves-Ground χ gG)

  applyTys-star :
    ∀ χs →
    applyTys χs ★ ≡ ★
  applyTys-star [] = refl
  applyTys-star (keep ∷ χs) = applyTys-star χs
  applyTys-star (NuReduction.bind A ∷ χs) = applyTys-star χs

  applyCoercions-untag :
    ∀ χs H →
    applyCoercions χs (H C.？) ≡ applyTys χs H C.？
  applyCoercions-untag [] H = refl
  applyCoercions-untag (keep ∷ χs) H =
    applyCoercions-untag χs H
  applyCoercions-untag (NuReduction.bind A ∷ χs) H =
    applyCoercions-untag χs (⇑ᵗ H)

  applyCoercions-sequence :
    ∀ χs s t →
    applyCoercions χs (s C.︔ t) ≡
      applyCoercions χs s C.︔ applyCoercions χs t
  applyCoercions-sequence [] s t = refl
  applyCoercions-sequence (keep ∷ χs) s t =
    applyCoercions-sequence χs s t
  applyCoercions-sequence (NuReduction.bind A ∷ χs) s t =
    applyCoercions-sequence χs (C.⇑ᶜ s) (C.⇑ᶜ t)

  post-catchup-sequence-step :
    ∀ χs {V s t} →
    Value V →
    V ⟨ applyCoercions χs (s C.︔ t) ⟩ —→[ keep ]
      V ⟨ applyCoercions χs s ⟩
        ⟨ applyCoercions χs t ⟩
  post-catchup-sequence-step χs {s = s} {t = t} vV
      rewrite applyCoercions-sequence χs s t =
    pure-step (NuReduction.β-seq vV)

  eager-intermediate :
    ∀ {Φ Δᴸ Δᴿ A C} →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ) →
    Φ ∣ Δᴸ ⊢ A ⊑ `∀ C ⊣ Δᴿ →
    Φ ∣ Δᴸ ⊢ A ⊑ ★ ⇒ ★ ⊣ Δᴿ
  eager-intermediate p (∀ⁱ q) =
    universal-star-to-function p
  eager-intermediate p (ν safe occ q) =
    universal-star-to-function p

  final-narrow-component :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (result : WeakOneStepResult ρ V M′ A B keep)
      {μ C D c} →
    μ ∣ applyTyCtxs (targetTailChanges result) Δᴿ
      ∣ applyStores (targetTailChanges result) (rightStoreⁱ ρ)
      ⊢ applyCoercions (targetTailChanges result) c
        ∶ applyTys (targetTailChanges result) C
          ⊒ applyTys (targetTailChanges result) D →
    μ ∣ resultRightCtx result ∣ rightStoreⁱ (resultStore result)
      ⊢ applyCoercions (targetTailChanges result) c
        ∶ applyTys (targetTailChanges result) C
          ⊒ applyTys (targetTailChanges result) D
  final-narrow-component result c⊒ =
    subst
      (λ Δ → _ ∣ Δ ∣ rightStoreⁱ (resultStore result)
        ⊢ applyCoercions (targetTailChanges result) _
          ∶ applyTys (targetTailChanges result) _
            ⊒ applyTys (targetTailChanges result) _)
      (sym (targetCtxResult result))
      (subst
        (λ Σ → _ ∣ applyTyCtxs (targetTailChanges result) _ ∣ Σ
          ⊢ applyCoercions (targetTailChanges result) _
            ∶ applyTys (targetTailChanges result) _
              ⊒ applyTys (targetTailChanges result) _)
        (sym (targetStoreResult result)) c⊒)

  final-seal-mode :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (result : WeakOneStepResult ρ V M′ A B keep)
      {μ} →
    SealModeStore★ μ
      (applyStores (targetTailChanges result) (rightStoreⁱ ρ)) →
    SealModeStore★ μ (rightStoreⁱ (resultStore result))
  final-seal-mode result seal★ =
    subst (SealModeStore★ _)
      (sym (targetStoreResult result)) seal★

  transport-contextual-catchup-target :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ N′ : Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    M′ ≡ N′ →
    Σ[ caught ∈
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ} p ]
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
              (worldRightCatchupResult caught)))) →
    Σ[ caught ∈
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = N′} {ρ = ρ} p ]
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
  transport-contextual-catchup-target refl caught = caught


world-coherent-right-target-narrow-fun-untag-gen-root-context-proofᵀ :
  WorldCoherentRightValueTerminalContextᵀ →
  WorldCoherentRightTargetNarrowUntagRootContextᵀ →
  WorldCoherentRightTargetInertFramingContextᵀ →
  WorldCoherentRightTargetStepResumeContextᵀ →
  WorldCoherentRightTargetNarrowFunUntagGenRootContextᵀ
world-coherent-right-target-narrow-fun-untag-gen-root-context-proofᵀ
    terminal untag inert resume
    {p = p} {q = q} prefix mode seal★
    (C.cast-seq
      untag⊢@(C.cast-untag hG gG tag-ok)
      gen⊢@(C.cast-gen hFun occ gen-body⊢) ,
      NW.fun-untag-gen safe)
    inner@(world-coherent-right-value-indexed-catchup
      catchup lineage bullet final-world final-exclusive final-unique
      final-wfR)
    context-eq right-prefix framed
    with apply-narrows-typing
      {χs = targetTailChanges result}
      mode
      (seal★-weaken
        (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (NW.narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix)
        (untag⊢ , NW.untag ★⇒★))
       | apply-narrows-typing
      {χs = targetTailChanges result}
      mode
      (seal★-weaken
        (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (NW.narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix)
        (gen⊢ , NW.gen safe))
  where
  indexed = rightCatchupIndexedResult catchup
  result = weakIndexedResult indexed
world-coherent-right-target-narrow-fun-untag-gen-root-context-proofᵀ
    terminal untag inert resume
    {p = p} {q = q} prefix mode seal★
    (C.cast-seq
      untag⊢@(C.cast-untag hG gG tag-ok)
      gen⊢@(C.cast-gen hFun occ gen-body⊢) ,
      NW.fun-untag-gen safe)
    inner@(world-coherent-right-value-indexed-catchup
      catchup lineage bullet final-world final-exclusive final-unique
      final-wfR)
    context-eq right-prefix framed
    | modeU , castU , sealU , untag-applied
    | modeG , castG , sealG , gen-applied
    with final-narrow-component result untag-applied
       | final-narrow-component result gen-applied
  where
  indexed = rightCatchupIndexedResult catchup
  result = weakIndexedResult indexed
world-coherent-right-target-narrow-fun-untag-gen-root-context-proofᵀ
    terminal untag inert resume
    {p = p} {q = q} prefix mode seal★
    (C.cast-seq
      untag⊢@(C.cast-untag hG gG tag-ok)
      gen⊢@(C.cast-gen hFun occ gen-body⊢) ,
      NW.fun-untag-gen safe)
    inner@(world-coherent-right-value-indexed-catchup
      catchup lineage bullet final-world final-exclusive final-unique
      final-wfR)
    context-eq right-prefix framed
    | modeU , castU , sealU , untag-applied
    | modeG , castG , sealG , gen-applied
    | untag-final | gen-final
    with terminal
      {ρ₀ = resultStore result}
      {ρ⁺ = resultStore result}
      prefix-reflⁱ final-world final-exclusive final-unique final-wfR
      (subst Value
        (sym (rightCatchupSourceUnchanged catchup))
        (rightCatchupSourceValue catchup))
      (subst No•
        (sym (rightCatchupSourceUnchanged catchup))
        (rightCatchupSourceNoBullet catchup))
      (rightCatchupTargetValue catchup)
      (rightCatchupTargetNoBullet catchup)
      (nu-term-imprecision-transport-typesᵀ
        refl
        (applyTys-star (targetTailChanges result))
        refl
        (canonicalIndexedResults indexed))
  where
  indexed = rightCatchupIndexedResult catchup
  result = weakIndexedResult indexed
world-coherent-right-target-narrow-fun-untag-gen-root-context-proofᵀ
    terminal untag inert resume
    {p = p} {q = q} prefix mode seal★
    (C.cast-seq
      untag⊢@(C.cast-untag hG gG tag-ok)
      gen⊢@(C.cast-gen hFun occ gen-body⊢) ,
      NW.fun-untag-gen safe)
    inner@(world-coherent-right-value-indexed-catchup
      catchup lineage bullet final-world final-exclusive final-unique
      final-wfR)
    context-eq right-prefix framed
    | modeU , castU , sealU , untag-applied
    | modeG , castG , sealG , gen-applied
    | untag-final | gen-final
    | seed , seed-context , seed-prefix
    with apply-narrows-typing
      {χs = targetTailChanges seed-result}
      castU
      (final-seal-mode result sealU)
      (subst
        (λ X → modeU ∣ resultRightCtx result
          ∣ rightStoreⁱ (resultStore result)
          ⊢ applyCoercions (targetTailChanges result)
              ((★ ⇒ ★) C.？)
            ∶ X ⊒ applyTys (targetTailChanges result) (★ ⇒ ★))
        (applyTys-star (targetTailChanges result))
        untag-final)
  where
  indexed = rightCatchupIndexedResult catchup
  result = weakIndexedResult indexed
  seed-indexed =
    rightCatchupIndexedResult (worldRightCatchupResult seed)
  seed-result = weakIndexedResult seed-indexed
world-coherent-right-target-narrow-fun-untag-gen-root-context-proofᵀ
    terminal untag inert resume
    {p = p} {q = q} prefix mode seal★
    (C.cast-seq
      untag⊢@(C.cast-untag hG gG tag-ok)
      gen⊢@(C.cast-gen hFun occ gen-body⊢) ,
      NW.fun-untag-gen safe)
    inner@(world-coherent-right-value-indexed-catchup
      catchup lineage bullet final-world final-exclusive final-unique
      final-wfR)
    context-eq right-prefix framed
    | modeU , castU , sealU , untag-applied
    | modeG , castG , sealG , gen-applied
    | untag-final | gen-final
    | seed , seed-context , seed-prefix
    | modeU′ , castU′ , sealU′ , untag-twice
    with final-narrow-component seed-result untag-twice
  where
  indexed = rightCatchupIndexedResult catchup
  result = weakIndexedResult indexed
  seed-indexed =
    rightCatchupIndexedResult (worldRightCatchupResult seed)
  seed-result = weakIndexedResult seed-indexed
world-coherent-right-target-narrow-fun-untag-gen-root-context-proofᵀ
    terminal untag inert resume
    {p = p} {q = q} prefix mode seal★
    (C.cast-seq
      untag⊢@(C.cast-untag hG gG tag-ok)
      gen⊢@(C.cast-gen hFun occ gen-body⊢) ,
      NW.fun-untag-gen safe)
    inner@(world-coherent-right-value-indexed-catchup
      catchup lineage bullet final-world final-exclusive final-unique
      final-wfR)
    context-eq right-prefix framed
    | modeU , castU , sealU , untag-applied
    | modeG , castG , sealG , gen-applied
    | untag-final | gen-final
    | seed , seed-context , seed-prefix
    | modeU′ , castU′ , sealU′ , untag-twice
    | untag-seed-final
    with untag
      (applyTys-preserves-Ground
        (targetTailChanges result) ★⇒★)
      seed seed-context seed-prefix
      (⊑cast⊒ᵀ castU′
        (final-seal-mode seed-result sealU′)
        (subst
          (λ c → modeU′ ∣ resultRightCtx seed-result
            ∣ rightStoreⁱ (resultStore seed-result)
            ⊢ c ∶
              applyTys (targetTailChanges seed-result) ★
                ⊒
              applyTys (targetTailChanges seed-result)
                (applyTys (targetTailChanges result) (★ ⇒ ★)))
          (cong
            (applyCoercions (targetTailChanges seed-result))
            (applyCoercions-untag
              (targetTailChanges result) (★ ⇒ ★)))
          untag-seed-final)
        (canonicalIndexedResults seed-indexed)
        (transportType seed-result intermediate-final))
  where
  indexed = rightCatchupIndexedResult catchup
  result = weakIndexedResult indexed
  intermediate = eager-intermediate p q
  intermediate-final = transportType result intermediate
  seed-indexed =
    rightCatchupIndexedResult (worldRightCatchupResult seed)
  seed-result = weakIndexedResult seed-indexed
world-coherent-right-target-narrow-fun-untag-gen-root-context-proofᵀ
    terminal untag inert resume
    {p = p} {q = q} prefix mode seal★
    (C.cast-seq
      untag⊢@(C.cast-untag hG gG tag-ok)
      gen⊢@(C.cast-gen hFun occ gen-body⊢) ,
      NW.fun-untag-gen safe)
    inner@(world-coherent-right-value-indexed-catchup
      catchup lineage bullet final-world final-exclusive final-unique
      final-wfR)
    context-eq right-prefix framed
    | modeU , castU , sealU , untag-applied
    | modeG , castG , sealG , gen-applied
    | untag-final | gen-final
    | seed , seed-context , seed-prefix
    | modeU′ , castU′ , sealU′ , untag-twice
    | untag-seed-final
    | untagged , untagged-context , untagged-prefix
    with transport-contextual-catchup-target
      (cong
        (λ c →
          targetResult result ⟨ c ⟩
            ⟨ applyCoercions (targetTailChanges result)
                (C.gen (★ ⇒ ★) _) ⟩)
        (sym
          (applyCoercions-untag
            (targetTailChanges result) (★ ⇒ ★))))
      (inert
        {ρ₀ = resultStore result}
        {ρ⁺ = resultStore result}
        prefix-reflⁱ
        (applyCoercions-preserves-Inert
          (targetTailChanges result)
          (NW.genSafe→inert (NW.safe-gen safe)))
        (inj₂ (inj₂ (inj₁
          (modeG , castG , final-seal-mode result sealG ,
            gen-final))))
        untagged untagged-context untagged-prefix)
  where
  indexed = rightCatchupIndexedResult catchup
  result = weakIndexedResult indexed
  intermediate = eager-intermediate p q
  intermediate-final = transportType result intermediate
  seed-indexed =
    rightCatchupIndexedResult (worldRightCatchupResult seed)
  seed-result = weakIndexedResult seed-indexed
world-coherent-right-target-narrow-fun-untag-gen-root-context-proofᵀ
    terminal untag inert resume
    {p = p} {q = q} prefix mode seal★
    (C.cast-seq
      untag⊢@(C.cast-untag hG gG tag-ok)
      gen⊢@(C.cast-gen hFun occ gen-body⊢) ,
      NW.fun-untag-gen safe)
    inner@(world-coherent-right-value-indexed-catchup
      catchup lineage bullet final-world final-exclusive final-unique
      final-wfR)
    context-eq right-prefix framed
    | modeU , castU , sealU , untag-applied
    | modeG , castG , sealG , gen-applied
    | untag-final | gen-final
    | seed , seed-context , seed-prefix
    | modeU′ , castU′ , sealU′ , untag-twice
    | untag-seed-final
    | untagged , untagged-context , untagged-prefix
    | continued , continued-context , continued-prefix
    =
  resume inner context-eq right-prefix framed
    (post-catchup-sequence-step
      (targetTailChanges
        (weakIndexedResult
          (rightCatchupIndexedResult catchup)))
      (rightCatchupTargetValue catchup))
    continued continued-context continued-prefix
