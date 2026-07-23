module proof.WorldCoherent.Source.RevealConceal.NuImprecisionWorldCoherentSourceRevealCatchupProof where

-- File Charter:
--   * Proves coherent catch-up through one source reveal conversion.
--   * Dispatches exhaustively on the `RevealConversion` provenance.
--   * Delegates the active `reveal-unseal` branch to the supplied whole
--     source-unseal catch-up contract.
--   * Handles identity and inert reveal forms with strict source-cast frames.

open import Agda.Builtin.Equality using (refl)
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
  ; weaken-reveal-conversion
  )
open import Data.List using ([])
open import Data.Product using (_,_; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (applyTyCtxs; applyTys; blame-⟨⟩; pure-step)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (No•; Term; Value; blame; no•-⟨⟩; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; blame⊑ᵀ
  ; conv↑⊑ᵀ
  ; nu-term-imprecision-target-typing
  ; prefix-reflⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Relation.Binary.PropositionalEquality using (subst; sym)
import Relation.Binary.HeterogeneousEquality as HE
open import Types using (Atom; Ty; TyCtx; TyVar; ＇_; ‵_; ★)

open import proof.Catchup.Core.NuImprecisionCatchupComposition using
  ( weak-one-step-keep-source-catchup-type-coherenceᵀ
  ; weak-one-step-keep-source-catchup-transportᵀ
  ; weak-one-step-keep-source-catchupᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulation using
  ( weak-one-step-source-cast-frame-coherenceᵀ
  ; weak-one-step-source-cast-frame-silentᵀ
  ; weak-one-step-source-cast-frame-transportᵀ
  ; weak-one-step-source-cast-frameᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( apply-reveal-conversions
  ; subst²-to-≅
  ; weak-one-step-compose-type-to-nested≅
  ; weak-one-step-index-resultᵀ
  ; weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
  ; weak-one-step-prepend-left-silent-preserves-transportᵀ
  ; weak-one-step-prepend-left-silentᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepIndexedResult
  ; canonicalIndexedResults
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent
  ; left-silent-invariant
  ; relatedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultSourceType
  ; resultStore
  ; resultTargetType
  ; resultType
  ; sourceChanges
  ; sourceCtxResult
  ; sourceResult
  ; sourceStoreResult
  ; sourceTypeResult
  ; targetResult
  ; targetTypeResult
  ; transportType
  ; weak-indexed-result
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  (rel-store-embedding-reflⁱ)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  (weak-step-store-lineage)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageProof using
  (weak-one-step-prepend-left-silent-store-lineageᵀ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  ( WorldCoherentLeftCatchupIndexedResult
  ; world-coherent-left-indexed-catchup
  )
open import proof.WorldCoherent.Source.RevealConceal.NuImprecisionWorldCoherentSourceConcealCatchup using
  ( applyTys-preserves-Atom
  ; atomic-source-value-reindexᵀ
  ; post-catchup-β-id
  )
open import proof.WorldCoherent.Source.RevealConceal.NuImprecisionWorldCoherentSourceRevealCatchupDef using
  (WorldCoherentSourceRevealCatchupᵀ)
open import proof.WorldCoherent.Source.RevealConceal.NuImprecisionWorldCoherentSourceUnsealCatchupDef using
  (WorldCoherentSourceUnsealCatchupᵀ)
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions
  ; applyCoercions-preserves-Inert
  )


result-reveal-conversionᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A B B′ c μ α X χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (indexed : WeakOneStepIndexedResult
    {M = M} {N′ = V′} {χ = χ} {ρ = ρ} p) →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  let inner = weakIndexedResult indexed in
  ∃[ μ′ ] ∃[ α′ ] ∃[ X′ ]
    RevealConversion μ′ (resultLeftCtx inner)
      (leftStoreⁱ (resultStore inner)) α′ X′
      (applyCoercions (sourceChanges inner) c)
      (applyTys (sourceChanges inner) A)
      (applyTys (sourceChanges inner) B)
result-reveal-conversionᵀ {Δᴸ = Δᴸ} {A = A} {B = B}
    {c = c} indexed c↑
    with apply-reveal-conversions
      {χs = sourceChanges (weakIndexedResult indexed)} c↑
result-reveal-conversionᵀ {Δᴸ = Δᴸ} {A = A} {B = B}
    {c = c} indexed c↑
    | μ′ , α′ , X′ , c′↑ =
  μ′ , α′ , X′ , final-conversion
  where
  inner = weakIndexedResult indexed

  final-conversion :
    RevealConversion μ′ (resultLeftCtx inner)
      (leftStoreⁱ (resultStore inner)) α′ X′
      (applyCoercions (sourceChanges inner) c)
      (applyTys (sourceChanges inner) A)
      (applyTys (sourceChanges inner) B)
  final-conversion =
    subst
      (λ Δ → RevealConversion μ′ Δ
        (leftStoreⁱ (resultStore inner)) α′ X′
        (applyCoercions (sourceChanges inner) c)
        (applyTys (sourceChanges inner) A)
        (applyTys (sourceChanges inner) B))
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → RevealConversion μ′
          (applyTyCtxs (sourceChanges inner) Δᴸ) Σ α′ X′
          (applyCoercions (sourceChanges inner) c)
          (applyTys (sourceChanges inner) A)
          (applyTys (sourceChanges inner) B))
        (sym (sourceStoreResult inner)) c′↑)


world-coherent-source-inert-reveal-castᵀ :
  ∀ {Φ Δᴸ Δᴿ ρ N V′ A B B′ c μ α X}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  C.Inert c →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  WorldCoherentLeftCatchupIndexedResult
    {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ} q
world-coherent-source-inert-reveal-castᵀ inert c↑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive wfL)
    q
    with result-reveal-conversionᵀ indexed c↑ | final
world-coherent-source-inert-reveal-castᵀ inert c↑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive wfL)
    q
    | μ′ , α′ , X′ , final-conversion
    | inj₁ (vW , noW) =
  world-coherent-left-indexed-catchup
    (left-indexed-catchup framed
      (left-catchup-invariant first-silent
        (inj₁ (vW ⟨ inert′ ⟩ , no•-⟨⟩ noW))))
    (weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix)
    coherent exclusive wfL
  where
  inner = weakIndexedResult indexed

  final-relation =
    conv↑⊑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first (relatedResults first)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

  inert′ =
    applyCoercions-preserves-Inert (sourceChanges inner) inert

  first-silent =
    weak-one-step-source-cast-frame-silentᵀ
      inner final-relation (left-silent-invariant refl refl)

  first-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)

  first-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)
world-coherent-source-inert-reveal-castᵀ inert c↑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive wfL)
    q
    | μ′ , α′ , X′ , final-conversion
    | inj₂ refl =
  world-coherent-left-indexed-catchup
    (left-indexed-catchup
      (weak-one-step-index-resultᵀ combined type-eq
        combined-transport combined-coherence)
      (left-catchup-invariant
        (left-silent-invariant refl refl) (inj₂ refl)))
    combined-lineage coherent exclusive wfL
  where
  inner = weakIndexedResult indexed

  final-relation =
    conv↑⊑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first (relatedResults first)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

  first-silent =
    weak-one-step-source-cast-frame-silentᵀ
      inner final-relation (left-silent-invariant refl refl)

  target⊢ =
    nu-term-imprecision-target-typing (relatedResults first)

  second-relation :
    resultCtx first
      ∣ resultLeftCtx first
      ∣ resultRightCtx first
      ∣ resultStore first ∣ []
      ⊢ᴺ blame ⊑ targetResult first
      ⦂ resultSourceType first ⊑ resultTargetType first
      ∶ resultType first
  second-relation = blame⊑ᵀ target⊢

  second = weak-one-step-keep-source-catchupᵀ
    {Φ = resultCtx first}
    {Δᴸ = resultLeftCtx first}
    {Δᴿ = resultRightCtx first}
    {A = resultSourceType first}
    {B = resultTargetType first}
    {p = resultType first}
    {ρ = resultStore first}
    (pure-step blame-⟨⟩) second-relation

  combined = weak-one-step-prepend-left-silentᵀ
    (left-silent first first-silent) second

  second-lineage =
    weak-step-store-lineage
      (resultStore first) rel-store-embedding-reflⁱ prefix-reflⁱ

  combined-lineage =
    weak-one-step-prepend-left-silent-store-lineageᵀ
      (left-silent first first-silent) second
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      second-lineage

  type-eq = HE.≅-to-≡
    (HE.trans
      (subst²-to-≅
        {P = λ S T → resultCtx combined ∣ resultLeftCtx combined
          ⊢ S ⊑ T ⊣ resultRightCtx combined}
        (sourceTypeResult combined)
        (targetTypeResult combined)
        (resultType combined))
      (HE.sym (weak-one-step-compose-type-to-nested≅
        first second q)))

  first-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)

  first-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)

  combined-transport =
    weak-one-step-prepend-left-silent-preserves-transportᵀ
      (left-silent first first-silent) second
      first-transport
      (weak-one-step-keep-source-catchup-transportᵀ
        (pure-step blame-⟨⟩) second-relation)

  combined-coherence =
    weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
      (left-silent first first-silent) second
      first-coherence
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        (pure-step blame-⟨⟩) second-relation)


world-coherent-source-id-reveal-castᵀ :
  ∀ {Φ Δᴸ Δᴿ ρ N V′ A B′ μ α X}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  Atom A →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X
    (C.id A) A A →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  WorldCoherentLeftCatchupIndexedResult
    {N = N ⟨ C.id A ⟩} {V′ = V′} {ρ = ρ} q
world-coherent-source-id-reveal-castᵀ atom c↑
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive wfL)
    q
    with result-reveal-conversionᵀ indexed c↑ | final
world-coherent-source-id-reveal-castᵀ atom c↑
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive wfL)
    q
    | μ′ , α′ , X′ , final-conversion
    | inj₁ (vW , noW) =
  world-coherent-left-indexed-catchup
    (left-indexed-catchup
      (weak-one-step-index-resultᵀ combined type-eq
        combined-transport combined-coherence)
      (left-catchup-invariant
        (left-silent-invariant refl refl) (inj₁ (vW , noW))))
    combined-lineage coherent exclusive wfL
  where
  inner = weakIndexedResult indexed

  final-relation =
    conv↑⊑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  first-silent =
    weak-one-step-source-cast-frame-silentᵀ
      inner final-relation (left-silent-invariant refl refl)

  source-atom =
    applyTys-preserves-Atom (sourceChanges inner) atom

  second-relation :
    resultCtx first
      ∣ resultLeftCtx first
      ∣ resultRightCtx first
      ∣ resultStore first ∣ []
      ⊢ᴺ sourceResult inner ⊑ targetResult first
      ⦂ resultSourceType first ⊑ resultTargetType first
      ∶ resultType first
  second-relation =
    atomic-source-value-reindexᵀ source-atom vW
      (canonicalIndexedResults indexed) (transportType inner q)

  second = weak-one-step-keep-source-catchupᵀ
    {Φ = resultCtx first}
    {Δᴸ = resultLeftCtx first}
    {Δᴿ = resultRightCtx first}
    {A = resultSourceType first}
    {B = resultTargetType first}
    {p = resultType first}
    {ρ = resultStore first}
    (post-catchup-β-id (sourceChanges inner) vW)
    second-relation

  combined = weak-one-step-prepend-left-silentᵀ
    (left-silent first first-silent) second

  second-lineage =
    weak-step-store-lineage
      (resultStore first) rel-store-embedding-reflⁱ prefix-reflⁱ

  combined-lineage =
    weak-one-step-prepend-left-silent-store-lineageᵀ
      (left-silent first first-silent) second
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      second-lineage

  type-eq = HE.≅-to-≡
    (HE.trans
      (subst²-to-≅
        {P = λ S T → resultCtx combined ∣ resultLeftCtx combined
          ⊢ S ⊑ T ⊣ resultRightCtx combined}
        (sourceTypeResult combined)
        (targetTypeResult combined)
        (resultType combined))
      (HE.sym (weak-one-step-compose-type-to-nested≅
        first second q)))

  first-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)

  first-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)

  combined-transport =
    weak-one-step-prepend-left-silent-preserves-transportᵀ
      (left-silent first first-silent) second
      first-transport
      (weak-one-step-keep-source-catchup-transportᵀ
        (post-catchup-β-id (sourceChanges inner) vW)
        second-relation)

  combined-coherence =
    weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
      (left-silent first first-silent) second
      first-coherence
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        (post-catchup-β-id (sourceChanges inner) vW)
        second-relation)
world-coherent-source-id-reveal-castᵀ atom c↑
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive wfL)
    q
    | μ′ , α′ , X′ , final-conversion
    | inj₂ refl =
  world-coherent-left-indexed-catchup
    (left-indexed-catchup
      (weak-one-step-index-resultᵀ combined type-eq
        combined-transport combined-coherence)
      (left-catchup-invariant
        (left-silent-invariant refl refl) (inj₂ refl)))
    combined-lineage coherent exclusive wfL
  where
  inner = weakIndexedResult indexed

  final-relation =
    conv↑⊑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  first-silent =
    weak-one-step-source-cast-frame-silentᵀ
      inner final-relation (left-silent-invariant refl refl)

  target⊢ =
    nu-term-imprecision-target-typing (relatedResults first)

  second-relation :
    resultCtx first
      ∣ resultLeftCtx first
      ∣ resultRightCtx first
      ∣ resultStore first ∣ []
      ⊢ᴺ blame ⊑ targetResult first
      ⦂ resultSourceType first ⊑ resultTargetType first
      ∶ resultType first
  second-relation = blame⊑ᵀ target⊢

  second = weak-one-step-keep-source-catchupᵀ
    {Φ = resultCtx first}
    {Δᴸ = resultLeftCtx first}
    {Δᴿ = resultRightCtx first}
    {A = resultSourceType first}
    {B = resultTargetType first}
    {p = resultType first}
    {ρ = resultStore first}
    (pure-step blame-⟨⟩)
    second-relation

  combined = weak-one-step-prepend-left-silentᵀ
    (left-silent first first-silent) second

  second-lineage =
    weak-step-store-lineage
      (resultStore first) rel-store-embedding-reflⁱ prefix-reflⁱ

  combined-lineage =
    weak-one-step-prepend-left-silent-store-lineageᵀ
      (left-silent first first-silent) second
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      second-lineage

  type-eq = HE.≅-to-≡
    (HE.trans
      (subst²-to-≅
        {P = λ S T → resultCtx combined ∣ resultLeftCtx combined
          ⊢ S ⊑ T ⊣ resultRightCtx combined}
        (sourceTypeResult combined)
        (targetTypeResult combined)
        (resultType combined))
      (HE.sym (weak-one-step-compose-type-to-nested≅
        first second q)))

  first-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)

  first-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)

  combined-transport =
    weak-one-step-prepend-left-silent-preserves-transportᵀ
      (left-silent first first-silent) second
      first-transport
      (weak-one-step-keep-source-catchup-transportᵀ
        (pure-step blame-⟨⟩)
        second-relation)

  combined-coherence =
    weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
      (left-silent first first-silent) second
      first-coherence
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        (pure-step blame-⟨⟩)
        second-relation)


world-coherent-source-reveal-catchup-proofᵀ :
  WorldCoherentSourceUnsealCatchupᵀ →
  WorldCoherentSourceRevealCatchupᵀ
world-coherent-source-reveal-catchup-proofᵀ
    unseal-catchup prefix c↑@(reveal-id-var {Y = Y} hY ok)
    vV′ noV′ catchup q =
  world-coherent-source-id-reveal-castᵀ
    (＇ Y)
    (weaken-reveal-conversion
      (leftStoreⁱ-prefix-inclusion prefix) c↑)
    catchup q
world-coherent-source-reveal-catchup-proofᵀ
    unseal-catchup prefix c↑@reveal-id-base
    vV′ noV′ catchup q =
  world-coherent-source-id-reveal-castᵀ
    (‵ _)
    (weaken-reveal-conversion
      (leftStoreⁱ-prefix-inclusion prefix) c↑)
    catchup q
world-coherent-source-reveal-catchup-proofᵀ
    unseal-catchup prefix c↑@reveal-id-★
    vV′ noV′ catchup q =
  world-coherent-source-id-reveal-castᵀ
    ★
    (weaken-reveal-conversion
      (leftStoreⁱ-prefix-inclusion prefix) c↑)
    catchup q
world-coherent-source-reveal-catchup-proofᵀ
    unseal-catchup prefix c↑@(reveal-unseal hX α∈Σ ok)
    vV′ noV′ catchup q =
  unseal-catchup prefix c↑ vV′ noV′ catchup q
world-coherent-source-reveal-catchup-proofᵀ
    unseal-catchup prefix c↑@(reveal-fun {s = s} {t = t} c↓ c↑′)
    vV′ noV′ catchup q =
  world-coherent-source-inert-reveal-castᵀ
    (C._↦_ s t)
    (weaken-reveal-conversion
      (leftStoreⁱ-prefix-inclusion prefix) c↑)
    catchup q
world-coherent-source-reveal-catchup-proofᵀ
    unseal-catchup prefix c↑@(reveal-all {s = s} c↑′)
    vV′ noV′ catchup q =
  world-coherent-source-inert-reveal-castᵀ
    (C.`∀ s)
    (weaken-reveal-conversion
      (leftStoreⁱ-prefix-inclusion prefix) c↑)
    catchup q
