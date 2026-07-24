module
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowFunUntagGenRootProof
  where

-- File Charter:
--   * Proves ordinary world-coherent resumption of the eager target
--     `fun-untag-gen` narrowing root.
--   * Uses ordinary target untag resumption, inert `gen` framing, and the
--     post-catch-up sequence step without requiring contextual witnesses.
--   * Takes every major capability as a theorem argument.
--   * Contains no result/view/outcome type, postulate, hole, permissive
--     option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import Data.List using ([]; _∷_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
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
open import NarrowWiden using
  (narrow-weaken; _∣_∣_⊢_∶_⊒_)
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
  (No•; Term; Value; no•-⟨⟩; ok-no; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; prefix-reflⁱ
  ; ⊑cast⊒ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using
  (Ty; TyCtx; ★; ★⇒★; ⇑ᵗ; _⇒_; `∀)
open import proof.Target.SealTag.NuImprecisionTargetGroundUniqueness using
  (universal-star-to-function)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowFunUntagGenRootDef
  using (WorldCoherentRightTargetNarrowFunUntagGenRootᵀ)
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetInertFramingDef
  using (WorldCoherentRightTargetInertFramingᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetStepResumeDef
  using (WorldCoherentRightTargetStepResumeᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetNarrowUntagRootDef
  using (WorldCoherentRightTargetNarrowUntagRootᵀ)
open import
  proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalDef
  using (WorldCoherentRightValueTerminalᵀ)
open import
  proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
  using
  ( rightCatchupIndexedResult
  ; rightCatchupSourceNoBullet
  ; rightCatchupSourceUnchanged
  ; rightCatchupSourceValue
  ; rightCatchupTargetNoBullet
  ; rightCatchupTargetValue
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationCore
  using
  ( apply-narrows-typing
  ; nu-term-imprecision-transport-typesᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepResult
  ; canonicalIndexedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; sourceResult
  ; targetCtxResult
  ; targetResult
  ; targetStoreResult
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import
  proof.Store.Prefix.NuImprecisionStorePrefix
  using (rightStoreⁱ-prefix-inclusion)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; world-coherent-right-value-indexed-catchup
  ; worldRightCatchupResult
  )
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions
  ; applyCoercions-preserves-Inert
  )
open import proof.Core.Properties.TypePreservation using
  (seal★-weaken)


private
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

  transport-catchup-target :
    ∀ {Φ Δᴸ Δᴿ V M′ N′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    M′ ≡ N′ →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ} p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = N′} {ρ = ρ} p
  transport-catchup-target refl caught = caught

  narrow-framed-relation :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B D : Ty} {c : C.Coercion} {μ : C.ModeEnv}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ} →
    StoreImpPrefix ρ₀ ρ⁺ →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ₀) →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ B ⊒ D →
    (inner :
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p) →
    (let result =
           weakIndexedResult
             (rightCatchupIndexedResult
               (worldRightCatchupResult inner))
     in
     resultCtx result
       ∣ resultLeftCtx result
       ∣ resultRightCtx result
       ∣ resultStore result ∣ []
       ⊢ᴺ sourceResult result ⊑
         targetResult result
           ⟨ applyCoercions (targetTailChanges result) c ⟩
       ⦂ applyTys (sourceChanges result) A
         ⊑ applyTys (targetTailChanges result) D
       ∶ transportType result q)
  narrow-framed-relation
      {Δᴿ = Δᴿ} {B = B} {D = D} {c = c} {q = q}
      prefix mode seal★ c⊒
      inner@(world-coherent-right-value-indexed-catchup
        catchup lineage bullet final-world final-exclusive final-unique
        final-wfR)
      with apply-narrows-typing
        {χs = keep ∷ targetTailChanges result}
        mode
        (seal★-weaken
          (rightStoreⁱ-prefix-inclusion prefix) seal★)
        (narrow-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) c⊒)
    where
    result =
      weakIndexedResult (rightCatchupIndexedResult catchup)
  narrow-framed-relation
      {Δᴿ = Δᴿ} {B = B} {D = D} {c = c} {q = q}
      prefix mode seal★ c⊒
      inner@(world-coherent-right-value-indexed-catchup
        catchup lineage bullet final-world final-exclusive final-unique
        final-wfR)
      | μ′ , mode′ , seal★′ , c⊒′ =
    ⊑cast⊒ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed)
      (transportType result q)
    where
    indexed = rightCatchupIndexedResult catchup
    result = weakIndexedResult indexed

    final-seal =
      subst (SealModeStore★ μ′)
        (sym (targetStoreResult result)) seal★′

    final-cast =
      subst
        (λ Δ → μ′ ∣ Δ ∣ rightStoreⁱ (resultStore result)
          ⊢ applyCoercions (targetTailChanges result) c
            ∶ applyTys (targetTailChanges result) B
              ⊒ applyTys (targetTailChanges result) D)
        (sym (targetCtxResult result))
        (subst
          (λ Σ → μ′
            ∣ applyTyCtxs (targetTailChanges result) Δᴿ ∣ Σ
            ⊢ applyCoercions (targetTailChanges result) c
              ∶ applyTys (targetTailChanges result) B
                ⊒ applyTys (targetTailChanges result) D)
          (sym (targetStoreResult result)) c⊒′)


world-coherent-right-target-narrow-fun-untag-gen-root-proofᵀ :
  WorldCoherentRightValueTerminalᵀ →
  WorldCoherentRightTargetNarrowUntagRootᵀ →
  WorldCoherentRightTargetInertFramingᵀ →
  WorldCoherentRightTargetStepResumeᵀ →
  WorldCoherentRightTargetNarrowFunUntagGenRootᵀ
world-coherent-right-target-narrow-fun-untag-gen-root-proofᵀ
    terminal untag inert resume
    {p = p} {q = q} prefix coherent exclusive unique wfR runtime
    vV noV mode seal★
    c⊒@(C.cast-seq
      untag⊢@(C.cast-untag hG gG tag-ok)
      gen⊢@(C.cast-gen hFun occ gen-body⊢) ,
      NW.fun-untag-gen safe)
    relation
    inner@(world-coherent-right-value-indexed-catchup
      catchup lineage bullet final-world final-exclusive final-unique
      final-wfR)
    with apply-narrows-typing
      {χs = targetTailChanges result}
      mode
      (seal★-weaken
        (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix)
        (untag⊢ , NW.untag ★⇒★))
       | apply-narrows-typing
      {χs = targetTailChanges result}
      mode
      (seal★-weaken
        (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix)
        (gen⊢ , NW.gen safe))
  where
  indexed = rightCatchupIndexedResult catchup
  result = weakIndexedResult indexed
world-coherent-right-target-narrow-fun-untag-gen-root-proofᵀ
    terminal untag inert resume
    {p = p} {q = q} prefix coherent exclusive unique wfR runtime
    vV noV mode seal★
    c⊒@(C.cast-seq
      untag⊢@(C.cast-untag hG gG tag-ok)
      gen⊢@(C.cast-gen hFun occ gen-body⊢) ,
      NW.fun-untag-gen safe)
    relation
    inner@(world-coherent-right-value-indexed-catchup
      catchup lineage bullet final-world final-exclusive final-unique
      final-wfR)
    | μU , modeU , sealU , untag-applied
    | μG , modeG , sealG , gen-applied
    with final-narrow-component result untag-applied
       | final-narrow-component result gen-applied
  where
  indexed = rightCatchupIndexedResult catchup
  result = weakIndexedResult indexed
world-coherent-right-target-narrow-fun-untag-gen-root-proofᵀ
    terminal untag inert resume
    {p = p} {q = q} prefix coherent exclusive unique wfR runtime
    vV noV mode seal★
    c⊒@(C.cast-seq
      untag⊢@(C.cast-untag hG gG tag-ok)
      gen⊢@(C.cast-gen hFun occ gen-body⊢) ,
      NW.fun-untag-gen safe)
    relation
    inner@(world-coherent-right-value-indexed-catchup
      catchup lineage bullet final-world final-exclusive final-unique
      final-wfR)
    | μU , modeU , sealU , untag-applied
    | μG , modeG , sealG , gen-applied
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
      seed-relation
  where
  indexed = rightCatchupIndexedResult catchup
  result = weakIndexedResult indexed
  seed-relation =
    nu-term-imprecision-transport-typesᵀ
      refl
      (applyTys-star (targetTailChanges result))
      refl
      (canonicalIndexedResults indexed)
world-coherent-right-target-narrow-fun-untag-gen-root-proofᵀ
    terminal untag inert resume
    {p = p} {q = q} prefix coherent exclusive unique wfR runtime
    vV noV mode seal★
    c⊒@(C.cast-seq
      untag⊢@(C.cast-untag hG gG tag-ok)
      gen⊢@(C.cast-gen hFun occ gen-body⊢) ,
      NW.fun-untag-gen safe)
    relation
    inner@(world-coherent-right-value-indexed-catchup
      catchup lineage bullet final-world final-exclusive final-unique
      final-wfR)
    | μU , modeU , sealU , untag-applied
    | μG , modeG , sealG , gen-applied
    | untag-final | gen-final
    | seed
    with untag
      {H = ground-final}
      {q = intermediate-final}
      prefix-reflⁱ final-world final-exclusive final-unique final-wfR
      (ok-no (no•-⟨⟩ (rightCatchupTargetNoBullet catchup)))
      (subst Value
        (sym (rightCatchupSourceUnchanged catchup))
        (rightCatchupSourceValue catchup))
      (subst No•
        (sym (rightCatchupSourceUnchanged catchup))
        (rightCatchupSourceNoBullet catchup))
      modeU
      (final-seal-mode result sealU)
      untag-root-cast
      seed-relation
      seed
  where
  indexed = rightCatchupIndexedResult catchup
  result = weakIndexedResult indexed
  intermediate = eager-intermediate p q
  intermediate-final = transportType result intermediate
  ground-final = applyTys (targetTailChanges result) (★ ⇒ ★)

  seed-relation =
    nu-term-imprecision-transport-typesᵀ
      refl
      (applyTys-star (targetTailChanges result))
      refl
      (canonicalIndexedResults indexed)

  untag-root-cast =
    subst
      (λ c → μU ∣ resultRightCtx result
        ∣ rightStoreⁱ (resultStore result)
        ⊢ c ∶ ★ ⊒ ground-final)
      (applyCoercions-untag
        (targetTailChanges result) (★ ⇒ ★))
      (subst
        (λ X → μU ∣ resultRightCtx result
          ∣ rightStoreⁱ (resultStore result)
          ⊢ applyCoercions (targetTailChanges result)
              ((★ ⇒ ★) C.？)
            ∶ X ⊒ ground-final)
        (applyTys-star (targetTailChanges result))
        untag-final)
world-coherent-right-target-narrow-fun-untag-gen-root-proofᵀ
    terminal untag inert resume
    {p = p} {q = q} prefix coherent exclusive unique wfR runtime
    vV noV mode seal★
    c⊒@(C.cast-seq
      untag⊢@(C.cast-untag hG gG tag-ok)
      gen⊢@(C.cast-gen hFun occ gen-body⊢) ,
      NW.fun-untag-gen safe)
    relation
    inner@(world-coherent-right-value-indexed-catchup
      catchup lineage bullet final-world final-exclusive final-unique
      final-wfR)
    | μU , modeU , sealU , untag-applied
    | μG , modeG , sealG , gen-applied
    | untag-final | gen-final
    | seed
    | untagged
    with transport-catchup-target
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
          (μG , modeG , final-seal-mode result sealG ,
            gen-final))))
        untagged)
  where
  indexed = rightCatchupIndexedResult catchup
  result = weakIndexedResult indexed
world-coherent-right-target-narrow-fun-untag-gen-root-proofᵀ
    terminal untag inert resume
    {p = p} {q = q} prefix coherent exclusive unique wfR runtime
    vV noV mode seal★
    c⊒@(C.cast-seq
      untag⊢@(C.cast-untag hG gG tag-ok)
      gen⊢@(C.cast-gen hFun occ gen-body⊢) ,
      NW.fun-untag-gen safe)
    relation
    inner@(world-coherent-right-value-indexed-catchup
      catchup lineage bullet final-world final-exclusive final-unique
      final-wfR)
    | μU , modeU , sealU , untag-applied
    | μG , modeG , sealG , gen-applied
    | untag-final | gen-final
    | seed
    | untagged
    | continued =
  resume inner
    (narrow-framed-relation prefix mode seal★ c⊒ inner)
    (post-catchup-sequence-step
      (targetTailChanges result)
      (rightCatchupTargetValue catchup))
    continued
  where
  indexed = rightCatchupIndexedResult catchup
  result = weakIndexedResult indexed
