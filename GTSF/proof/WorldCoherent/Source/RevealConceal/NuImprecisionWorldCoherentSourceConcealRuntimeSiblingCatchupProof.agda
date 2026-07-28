module
  proof.WorldCoherent.Source.RevealConceal.NuImprecisionWorldCoherentSourceConcealRuntimeSiblingCatchupProof
  where

-- File Charter:
--   * Carries one independent runtime sibling through source concealment.
--   * Dispatches exhaustively on identity and inert concealment provenance.
--   * Joins every active or blame completion with the sibling at one exact
--     final weak result.
--   * Contains no allocation transport, postulate, hole, or permissive option.

open import proof.NuCore.Relations.NuImprecisionQuotientedTyping
open import Agda.Builtin.Equality using (refl)
import Conversion as Conv
import Coercions as C
open import Coercions using (Coercion; ModeEnv)
open import ConversionIndexCompatibility using (_[_↦_]ᴸ_)
open import Data.List using ([])
open import Data.Product using (_,_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  ( applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  ; blame-⟨⟩
  ; keep
  ; pure-step
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-blame
  ; no•-⟨⟩
  ; ok-no
  ; ok-⟨⟩
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; blame⊑ᵀ
  ; conv↓⊑ᵀ
  ; prefix-reflⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Atom; Ty; TyCtx; TyVar; ＇_; ‵_; ★)
open import
  proof.Catchup.Core.NuImprecisionCatchupComposition
  using
  ( weak-one-step-keep-source-catchup-type-coherenceᵀ
  ; weak-one-step-keep-source-catchup-transportᵀ
  ; weak-one-step-keep-source-catchupᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulation
  using
  ( weak-one-step-source-cast-frame-coherenceᵀ
  ; weak-one-step-source-cast-frame-silentᵀ
  ; weak-one-step-source-cast-frame-transportᵀ
  ; weak-one-step-source-cast-frameᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationCore
  using (weak-one-step-reindexᵀ)
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
  ; transportLeftReplacementCoherent
  ; weak-indexed-result
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (rel-store-embedding-reflⁱ)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (weak-step-store-lineage)
open import
  proof.Store.Prefix.NuImprecisionStorePrefix
  using (leftStoreⁱ-prefix-inclusion)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentLeftCatchupIndexedResult
  ; worldCatchupResult
  ; world-coherent-left-indexed-catchup
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupRuntimeSiblingComposition
  using
  (world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ)
open import
  proof.WorldCoherent.Source.RevealConceal.NuImprecisionWorldCoherentSourceConcealCatchup
  using
  ( applyTys-preserves-Atom
  ; atomic-source-value-reindexᵀ
  ; post-catchup-β-id
  ; result-conceal-conversionᵀ
  )
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions-preserves-Inert)


world-coherent-source-id-conceal-runtime-sibling-catchupᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {N V′ R R′ : Term} {A B′ X E E′ : Ty}
    {μ : ModeEnv} {α : TyVar}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ} →
  Atom A →
  Conv.ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X
    (C.id A) A A →
  Value V′ →
  No• V′ →
  No• R →
  RuntimeOK R′ →
  (inner :
    WorldCoherentLeftCatchupIndexedResult
      {N = N} {V′ = V′} {ρ = ρ} p) →
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
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  q [ α ↦ X ]ᴸ p →
  Σ[ caught ∈
    WorldCoherentLeftCatchupIndexedResult
      {N = N ⟨ C.id A ⟩} {V′ = V′} {ρ = ρ} q ]
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
world-coherent-source-id-conceal-runtime-sibling-catchupᵀ
    atom c↓ vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q replacement
    with result-conceal-conversionᵀ indexed c↓ | final
world-coherent-source-id-conceal-runtime-sibling-catchupᵀ
    atom c↓ vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q replacement
    | μ′ , final-conversion
    | inj₁ (vW , noW) =
  world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    first-silent first-lineage
    (second-caught , inner-sibling)
  where
  inner = weakIndexedResult indexed

  final-relation =
    conv↓⊑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)
      (transportLeftReplacementCoherent
        (weakIndexedTypeCoherence indexed) replacement)

  first-raw = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first-raw (relatedResults first-raw)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

  first = weakIndexedResult framed

  first-silent =
    left-silent-indexed framed
      (weak-one-step-source-cast-frame-silentᵀ
        inner final-relation silent)
      (ok-⟨⟩ (ok-no noW))

  first-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  source-atom =
    applyTys-preserves-Atom (sourceChanges inner) atom

  second-relation =
    atomic-source-value-reindexᵀ source-atom vW
      (canonicalIndexedResults indexed) (transportType inner q)

  second = weak-one-step-keep-source-catchupᵀ
    (post-catchup-β-id (sourceChanges inner) vW)
    second-relation

  second-indexed =
    weak-indexed-result
      second second-relation
      (weak-one-step-keep-source-catchup-transportᵀ
        (post-catchup-β-id (sourceChanges inner) vW)
        second-relation)
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        (post-catchup-β-id (sourceChanges inner) vW)
        second-relation)

  second-catchup =
    left-indexed-catchup second-indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl)
        (inj₁ (vW , noW)))

  second-caught =
    world-coherent-left-indexed-catchup
      second-catchup
      (weak-step-store-lineage
        (resultStore first)
        rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-source-id-conceal-runtime-sibling-catchupᵀ
    atom c↓ vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q replacement
    | μ′ , final-conversion
    | inj₂ refl =
  world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    first-silent first-lineage
    (second-caught , inner-sibling)
  where
  inner = weakIndexedResult indexed

  final-relation =
    conv↓⊑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)
      (transportLeftReplacementCoherent
        (weakIndexedTypeCoherence indexed) replacement)

  first-raw = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first-raw (relatedResults first-raw)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

  first = weakIndexedResult framed

  first-silent =
    left-silent-indexed framed
      (left-silent-invariant refl refl)
      (ok-⟨⟩ (ok-no no•-blame))

  first-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  terminal-first =
    weak-one-step-reindexᵀ first refl refl
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


world-coherent-source-inert-conceal-runtime-sibling-catchupᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {N V′ R R′ : Term} {A B B′ X E E′ : Ty}
    {c : Coercion} {μ : ModeEnv} {α : TyVar}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ} →
  C.Inert c →
  Conv.ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  Value V′ →
  No• V′ →
  No• R →
  RuntimeOK R′ →
  (inner :
    WorldCoherentLeftCatchupIndexedResult
      {N = N} {V′ = V′} {ρ = ρ} p) →
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
  q [ α ↦ X ]ᴸ p →
  Σ[ caught ∈
    WorldCoherentLeftCatchupIndexedResult
      {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ} q ]
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
world-coherent-source-inert-conceal-runtime-sibling-catchupᵀ
    inert c↓ vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q replacement
    with result-conceal-conversionᵀ indexed c↓ | final
world-coherent-source-inert-conceal-runtime-sibling-catchupᵀ
    inert c↓ vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q replacement
    | μ′ , final-conversion
    | inj₁ (vW , noW) =
  caught , inner-sibling
  where
  inner = weakIndexedResult indexed

  final-relation =
    conv↓⊑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)
      (transportLeftReplacementCoherent
        (weakIndexedTypeCoherence indexed) replacement)

  first-raw = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first-raw (relatedResults first-raw)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

  inert′ =
    applyCoercions-preserves-Inert (sourceChanges inner) inert

  first-silent =
    weak-one-step-source-cast-frame-silentᵀ
      inner final-relation silent

  caught =
    world-coherent-left-indexed-catchup
      (left-indexed-catchup framed
        (left-catchup-invariant first-silent
          (inj₁ (vW ⟨ inert′ ⟩ , no•-⟨⟩ noW))))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL
world-coherent-source-inert-conceal-runtime-sibling-catchupᵀ
    inert c↓ vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q replacement
    | μ′ , final-conversion
    | inj₂ refl =
  world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    first-silent first-lineage
    (second-caught , inner-sibling)
  where
  inner = weakIndexedResult indexed

  final-relation =
    conv↓⊑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)
      (transportLeftReplacementCoherent
        (weakIndexedTypeCoherence indexed) replacement)

  first-raw = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first-raw (relatedResults first-raw)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

  first = weakIndexedResult framed

  first-silent =
    left-silent-indexed framed
      (left-silent-invariant refl refl)
      (ok-⟨⟩ (ok-no no•-blame))

  first-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  terminal-first =
    weak-one-step-reindexᵀ first refl refl
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


world-coherent-source-conceal-runtime-sibling-catchup-proofᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V′ R R′ : Term} {A B B′ X E E′ : Ty}
    {c : Coercion} {μ : ModeEnv} {α : TyVar}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  Conv.ConcealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
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
  q [ α ↦ X ]ᴸ p →
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
world-coherent-source-conceal-runtime-sibling-catchup-proofᵀ
    prefix c↓@(Conv.conceal-id-var {Y = Y} hY ok)
    vV′ noV′ noR okR′
    inner inner-sibling q replacement =
  world-coherent-source-id-conceal-runtime-sibling-catchupᵀ
    (＇ Y)
    (Conv.weaken-conceal-conversion
      (leftStoreⁱ-prefix-inclusion prefix) c↓)
    vV′ noV′ noR okR′ inner inner-sibling q replacement
world-coherent-source-conceal-runtime-sibling-catchup-proofᵀ
    prefix c↓@Conv.conceal-id-base
    vV′ noV′ noR okR′
    inner inner-sibling q replacement =
  world-coherent-source-id-conceal-runtime-sibling-catchupᵀ
    (‵ _)
    (Conv.weaken-conceal-conversion
      (leftStoreⁱ-prefix-inclusion prefix) c↓)
    vV′ noV′ noR okR′ inner inner-sibling q replacement
world-coherent-source-conceal-runtime-sibling-catchup-proofᵀ
    prefix c↓@Conv.conceal-id-★
    vV′ noV′ noR okR′
    inner inner-sibling q replacement =
  world-coherent-source-id-conceal-runtime-sibling-catchupᵀ
    ★
    (Conv.weaken-conceal-conversion
      (leftStoreⁱ-prefix-inclusion prefix) c↓)
    vV′ noV′ noR okR′ inner inner-sibling q replacement
world-coherent-source-conceal-runtime-sibling-catchup-proofᵀ
    prefix c↓@(Conv.conceal-seal hX α∈Σ ok)
    vV′ noV′ noR okR′
    inner inner-sibling q replacement =
  world-coherent-source-inert-conceal-runtime-sibling-catchupᵀ
    (C.seal _ _)
    (Conv.weaken-conceal-conversion
      (leftStoreⁱ-prefix-inclusion prefix) c↓)
    vV′ noV′ noR okR′ inner inner-sibling q replacement
world-coherent-source-conceal-runtime-sibling-catchup-proofᵀ
    prefix c↓@(Conv.conceal-fun {s = s} {t = t} c↑ c↓′)
    vV′ noV′ noR okR′
    inner inner-sibling q replacement =
  world-coherent-source-inert-conceal-runtime-sibling-catchupᵀ
    (C._↦_ s t)
    (Conv.weaken-conceal-conversion
      (leftStoreⁱ-prefix-inclusion prefix) c↓)
    vV′ noV′ noR okR′ inner inner-sibling q replacement
world-coherent-source-conceal-runtime-sibling-catchup-proofᵀ
    prefix c↓@(Conv.conceal-all {s = s} c↓′)
    vV′ noV′ noR okR′
    inner inner-sibling q replacement =
  world-coherent-source-inert-conceal-runtime-sibling-catchupᵀ
    (C.`∀ s)
    (Conv.weaken-conceal-conversion
      (leftStoreⁱ-prefix-inclusion prefix) c↓)
    vV′ noV′ noR okR′ inner inner-sibling q replacement
