module
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceNarrowRuntimeSiblingCatchupProof
  where

-- File Charter:
--   * Carries one independent runtime sibling through source narrowing.
--   * Recursively catches a framed source value with the sibling and composes
--     that result through the exact silent-resumption sibling join.
--   * Keeps the terminal source-blame frame store-neutral and definitionally
--     preserves the sibling there.
--   * Contains no allocation recovery, postulate, hole, or permissive option.

open import proof.NuCore.Relations.NuImprecisionQuotientedTyping
open import Agda.Builtin.Equality using (refl)
open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; narrowing)
open import Coercions using (Coercion; ModeEnv)
open import Data.List using ([])
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import ImprecisionComposition using
  (ImprecisionShape; _；_≋_; ⌊_⌋)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; narrow-weaken
  )
open import NuReduction using
  ( applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  ; blame-⟨⟩
  ; keep
  ; pure-step
  )
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-blame
  ; ok-no
  ; ok-⟨⟩
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; blame⊑ᵀ
  ; prefix-reflⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
open import proof.Catchup.Core.NuImprecisionCatchupComposition using
  ( weak-one-step-keep-source-catchup-type-coherenceᵀ
  ; weak-one-step-keep-source-catchup-transportᵀ
  ; weak-one-step-keep-source-catchupᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulation using
  (weak-one-step-source-narrow-cast-indexed-frameᵀ)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  (weak-one-step-reindexᵀ)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( canonicalIndexedResults
  ; catchupIndexedResult
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent-indexed
  ; left-silent-invariant
  ; relatedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; resultType
  ; sourceChanges
  ; targetTailChanges
  ; transportType
  ; weak-indexed-result
  ; weakIndexedResult
  )
open import proof.Core.Properties.TypePreservation using
  (seal★-weaken)
open import proof.Core.Properties.ReductionProperties using
  (applyTerms-preserves-No•; applyTerms-preserves-RuntimeOK)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (weak-step-store-lineage)
open import
  proof.Store.Prefix.NuImprecisionStorePrefix
  using (leftStoreⁱ-prefix-inclusion)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (rel-store-embedding-reflⁱ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupRuntimeSiblingComposition
  using
  (world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentLeftCatchupIndexedResult
  ; worldCatchupResult
  ; world-coherent-left-indexed-catchup
  )
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupRuntimeSiblingPrefixDef
  using (WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ)

world-coherent-source-narrow-runtime-sibling-catchup-proofᵀ :
  WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V′ R R′ : Term} {A B B′ E E′ : Ty}
    {c : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
    {s : ImprecisionShape} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊒ B →
  Value V′ →
  No• V′ →
  No• R →
  RuntimeOK R′ →
  (inner :
    WorldCoherentLeftCatchupIndexedResult
      {N = N} {V′ = V′} {ρ = ρ⁺} p) →
  (let result =
         weakIndexedResult
           (catchupIndexedResult (worldCatchupResult inner))
   in
   resultCtx result
     ∣ resultLeftCtx result
     ∣ resultRightCtx result
     ∣ resultStore result ∣ []
     ⊢ᴺ applyTerms (sourceChanges result) R
       ⊑ applyTerms (targetTailChanges result) (applyTerm keep R′)
     ⦂ applyTys (sourceChanges result) E
       ⊑ applyTys (targetTailChanges result) (applyTy keep E′)
     ∶ transportType result r) →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  narrowing ⊢ᶜ c ⦂ s →
  s ； ⌊ p ⌋ ≋ ⌊ q ⌋ →
  Σ[ caught ∈
    WorldCoherentLeftCatchupIndexedResult
      {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} q ]
    let result =
          weakIndexedResult
            (catchupIndexedResult (worldCatchupResult caught))
    in
    resultCtx result
      ∣ resultLeftCtx result
      ∣ resultRightCtx result
      ∣ resultStore result ∣ []
      ⊢ᴺ applyTerms (sourceChanges result) R
        ⊑ applyTerms (targetTailChanges result) (applyTerm keep R′)
      ⦂ applyTys (sourceChanges result) E
        ⊑ applyTys (targetTailChanges result) (applyTy keep E′)
      ∶ transportType result r
world-coherent-source-narrow-runtime-sibling-catchup-proofᵀ
    value-sibling
    {R = R} {R′ = R′} {E = E} {E′ = E′} {r = r}
    prefix mode seal★ c⊒
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q c-shape comp
    with final
world-coherent-source-narrow-runtime-sibling-catchup-proofᵀ
    value-sibling
    {R = R} {R′ = R′} {E = E} {E′ = E′} {r = r}
    prefix mode seal★ c⊒
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q c-shape comp
    | inj₁ (vW , noW) =
  world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    first-silent first-lineage recursive
  where
  source-store-incl = leftStoreⁱ-prefix-inclusion prefix

  seal★⁺ = seal★-weaken source-store-incl seal★

  c⊒⁺ = narrow-weaken ≤-refl source-store-incl c⊒

  framed =
    weak-one-step-source-narrow-cast-indexed-frameᵀ
      mode seal★⁺ c⊒⁺ c-shape comp indexed

  first = weakIndexedResult framed

  first-silent =
    left-silent-indexed framed
      (left-silent-invariant refl refl)
      (ok-⟨⟩ (ok-no noW))

  first-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  recursive =
    value-sibling
      {Φ = resultCtx first}
      {Δᴸ = resultLeftCtx first}
      {Δᴿ = resultRightCtx first}
      {ρᵇ = resultStore first}
      {ρ = resultStore first}
      {R = applyTerms (sourceChanges first) R}
      {R′ = applyTerms (targetTailChanges first)
        (applyTerm keep R′)}
      {C = applyTys (sourceChanges first) E}
      {C′ = applyTys (targetTailChanges first)
        (applyTy keep E′)}
      {q = transportType first r}
      prefix-reflⁱ coherent exclusive unique wfL
      (ok-⟨⟩ (ok-no noW)) vV′ noV′
      (canonicalIndexedResults framed)
      (applyTerms-preserves-No• (sourceChanges first) noR)
      (applyTerms-preserves-RuntimeOK
        (targetTailChanges first) okR′)
      inner-sibling
      (nu-term-imprecision-source-typing inner-sibling)
      (nu-term-imprecision-target-typing inner-sibling)
world-coherent-source-narrow-runtime-sibling-catchup-proofᵀ
    value-sibling prefix mode seal★ c⊒
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q c-shape comp
    | inj₂ refl =
  world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    first-silent first-lineage
    (second-caught , inner-sibling)
  where
  source-store-incl = leftStoreⁱ-prefix-inclusion prefix

  seal★⁺ = seal★-weaken source-store-incl seal★

  c⊒⁺ = narrow-weaken ≤-refl source-store-incl c⊒

  framed =
    weak-one-step-source-narrow-cast-indexed-frameᵀ
      mode seal★⁺ c⊒⁺ c-shape comp indexed

  first-silent =
    left-silent-indexed framed
      (left-silent-invariant refl refl)
      (ok-⟨⟩ (ok-no no•-blame))

  first-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  terminal-first-raw = weakIndexedResult framed

  terminal-first =
    weak-one-step-reindexᵀ terminal-first-raw refl refl
      (canonicalIndexedResults framed)

  terminal-target⊢ =
    nu-term-imprecision-target-typing
      (relatedResults terminal-first)

  terminal-second-relation = blame⊑ᵀ terminal-target⊢

  terminal-second = weak-one-step-keep-source-catchupᵀ
    {p = resultType terminal-first}
    (pure-step blame-⟨⟩) terminal-second-relation

  terminal-second-indexed =
    weak-indexed-result
      terminal-second terminal-second-relation
      (weak-one-step-keep-source-catchup-transportᵀ
        (pure-step blame-⟨⟩) terminal-second-relation)
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        (pure-step blame-⟨⟩) terminal-second-relation)

  terminal-second-catchup =
    left-indexed-catchup terminal-second-indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl)
        (inj₂ refl))

  second-caught =
    world-coherent-left-indexed-catchup
      terminal-second-catchup
      (weak-step-store-lineage
        (resultStore terminal-first)
        rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
