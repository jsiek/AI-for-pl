module proof.WorldCoherent.Source.RevealConceal.NuImprecisionWorldCoherentSourceConcealCatchup where

-- File Charter:
--   * Proves the source-conceal branch of coherent source-runtime catch-up.
--   * Handles identity conceal conversions by one post-catch-up `β-id` step.
--   * Handles seal, arrow, and universal conceal conversions as inert casts.
--   * Preserves the final `WorldCoherent` evidence carried by the input
--     coherent catch-up and depends only on strict catch-up/frame support.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; conceal-all
  ; conceal-fun
  ; conceal-id-base
  ; conceal-id-var
  ; conceal-id-★
  ; conceal-seal
  ; weaken-conceal-conversion
  )
open import ConversionIndexCompatibility using (_[_↦_]ᴸ_)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using
  ( ⌊_⌋
  ; _；⌊_⌋≋ᵖ_；_
  ; quotient-boundary-square
  )
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; idι
  ; ν
  )
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using
  ( applyStores
  ; applyTy
  ; applyTyCtxs
  ; applyTys
  ; bind
  ; blame-⟨⟩
  ; keep
  ; pure-step
  ; β-id
  ; _—→[_]_
  )
open import NuTermImprecision using
  ( CtxImp
  ; CtxImpEntry
  ; LiftLeftCtxⁱ
  ; LiftLeftStoreⁱ
  ; StoreImp
  ; leftCtxⁱ
  ; leftStoreⁱ
  ; rightCtxⁱ
  ; rightStoreⁱ
  ; store-left
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; blame
  ; no•-⟨⟩
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; allocation-prefixᵀ
  ; blame⊑ᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↓⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv⊑convᵀ
  ; down·up⊑down·upᵀ
  ; nu-term-imprecision-target-typing
  ; prefix-reflⁱ
  ; up⊑upᵀ
  ; x⊑xᵀ
  ; Λ⊑Λᵀ
  ; Λ⊑ᵀ
  ; α⊑αᵀ
  ; α⊑ᵀ
  ; κ⊑κᵀ
  ; ν⊑νᵀ
  ; ν⊑ᵀ
  ; ·⊑·ᵀ
  ; ƛ⊑ƛᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↓ᵀ
  ; ⊑conv↑ᵀ
  ; ⊕⊑⊕ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
import Relation.Binary.HeterogeneousEquality as HE

open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; _∣_∣_⊢_⦂_
  )
open import Types using
  ( Atom
  ; Ty
  ; TyCtx
  ; TyVar
  ; WfTy
  ; ＇_
  ; ‵_
  ; ★
  ; `∀
  ; ⇑ᵗ
  ; ⟰ᵗ
  ; occurs
  )
import Coercions as C
open import Coercions using (Coercion; ModeEnv; instᵈ)
open import
  proof.Core.Properties.ConversionIndexCompatibilityProperties
  using
  ( replace-left-source-shape
  ; replace-left-target-shape
  ; replace-right-source-shape
  ; replace-right-target-shape
  )
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( imprecision-composition-shape-transport
  ; shape-target-lift-rightᵢ
  ; source-atom-shape-unique
  )
open import
  proof.NuCore.Relations.NuImprecisionPairedCastResultShape
  using (paired-cast-result-shape-reindexᵀ)
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
  ( subst²-to-≅
  ; weak-one-step-compose-type-to-nested≅
  ; weak-one-step-index-resultᵀ
  ; weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
  ; weak-one-step-prepend-left-silent-preserves-transportᵀ
  ; weak-one-step-prepend-left-silentᵀ
  )
open import proof.Core.Properties.NuConversionTransport
  using (apply-conceal-conversions-exact)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( LeftCatchupIndexedResult
  ; LeftSilentInvariant
  ; WeakOneStepIndexedResult
  ; WeakOneStepResult
  ; WeakOneStepTransport
  ; WeakOneStepTypeCoherence
  ; canonicalIndexedResults
  ; catchupIndexedInvariant
  ; catchupIndexedResult
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
  ; silentInvariant
  ; sourceChanges
  ; sourceCtxResult
  ; sourceResult
  ; sourceStoreResult
  ; sourceTypeResult
  ; targetResult
  ; targetTypeResult
  ; transportLeftReplacementCoherent
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
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions
  ; applyTyVars
  ; applyCoercions-preserves-Inert
  )


applyTy-preserves-Atom :
  ∀ χ {A} →
  Atom A →
  Atom (applyTy χ A)
applyTy-preserves-Atom keep atom = atom
applyTy-preserves-Atom (bind A) (＇ X) = ＇ (suc X)
applyTy-preserves-Atom (bind A) (‵ ι) = ‵ ι
applyTy-preserves-Atom (bind A) ★ = ★

applyTys-preserves-Atom :
  ∀ χs {A} →
  Atom A →
  Atom (applyTys χs A)
applyTys-preserves-Atom [] atom = atom
applyTys-preserves-Atom (χ ∷ χs) atom =
  applyTys-preserves-Atom χs (applyTy-preserves-Atom χ atom)


private
  quotient-boundary-source-reindex :
    ∀ {Φ Δᴸ Δᴿ A A′ B B′}
      {p q : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {r : Φ ∣ Δᴸ ⊢ B ⊑ᵖ B′ ⊣ Δᴿ}
      {s s′} →
    ⌊ p ⌋ ≡ ⌊ q ⌋ →
    s ；⌊ p ⌋≋ᵖ r ； s′ →
    s ；⌊ q ⌋≋ᵖ r ； s′
  quotient-boundary-source-reindex eq
      (quotient-boundary-square
        source-shape left-composition target-shape right-composition) =
    quotient-boundary-square
      source-shape
      (imprecision-composition-shape-transport
        refl (sym eq) refl left-composition)
      target-shape
      right-composition


post-catchup-β-id :
  ∀ χs {V A} →
  Value V →
  V ⟨ applyCoercions χs (C.id A) ⟩ —→[ keep ] V
post-catchup-β-id [] vV = pure-step (β-id vV)
post-catchup-β-id (keep ∷ χs) vV =
  post-catchup-β-id χs vV
post-catchup-β-id (bind A ∷ χs) {A = B} vV =
  post-catchup-β-id χs {A = ⇑ᵗ B} vV

atomic-source-value-reindexᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Atom A →
  Value M →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ q
atomic-source-value-reindexᵀ atom () (blame⊑ᵀ M′⊢) q
atomic-source-value-reindexᵀ atom () (x⊑xᵀ x∈) q
atomic-source-value-reindexᵀ () vM (ƛ⊑ƛᵀ hA hA′ N⊑N′) q
atomic-source-value-reindexᵀ atom () (·⊑·ᵀ L⊑L′ M⊑M′) q
atomic-source-value-reindexᵀ atom (() ⟨ inert-u ⟩)
    (down·up⊑down·upᵀ
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      L⊑L′ M⊑M′ down-square
      widening-pair u-shape u′-shape up-square compatible)
    q
atomic-source-value-reindexᵀ atom vM
    (up⊑upᵀ M⊑M′ widening p
      source-shape target-shape square) q =
  up⊑upᵀ M⊑M′ widening q source-shape target-shape
    (quotient-boundary-source-reindex
      (source-atom-shape-unique atom p q) square)
atomic-source-value-reindexᵀ () vM
    (Λ⊑Λᵀ liftρ liftγ vV vV′ V⊑V′) q
atomic-source-value-reindexᵀ () vM
    (Λ⊑ᵀ occ liftρ liftγ vV V⊑M′) q
atomic-source-value-reindexᵀ atom ()
    (α⊑αᵀ vL noL vL′ noL′ p↑ liftρ liftγ
      L⊑L′ L•⊢ L′•⊢) q
atomic-source-value-reindexᵀ atom ()
    (α⊑ᵀ vL noL hA liftρ liftγ L⊑M′ L•⊢ M′⊢) q
atomic-source-value-reindexᵀ atom vM
    (allocation-prefixᵀ prefix M⊑M′ M⊢ M′⊢) q =
  allocation-prefixᵀ prefix
    (atomic-source-value-reindexᵀ atom vM M⊑M′ q)
    M⊢ M′⊢
atomic-source-value-reindexᵀ atom ()
    (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
      liftρ liftγ N⊑N′ replacement) q
atomic-source-value-reindexᵀ atom ()
    (ν⊑ᵀ hA h⇑A s↑ liftρ liftγ N⊑N′ replacement) q
atomic-source-value-reindexᵀ atom vM κ⊑κᵀ idι =
  κ⊑κᵀ
atomic-source-value-reindexᵀ atom () (⊕⊑⊕ᵀ L⊑L′ M⊑M′) q
atomic-source-value-reindexᵀ atom vM
    (cast⊒⊑ᵀ mode seal★ c⊒ M⊑M′ p c-shape comp) q =
  cast⊒⊑ᵀ mode seal★ c⊒ M⊑M′ q c-shape
    (imprecision-composition-shape-transport
      refl refl
      (sym (source-atom-shape-unique atom p q))
      comp)
atomic-source-value-reindexᵀ atom vM
    (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ p c-shape comp) q =
  cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ q c-shape
    (imprecision-composition-shape-transport
      refl
      (sym (source-atom-shape-unique atom p q))
      refl comp)
atomic-source-value-reindexᵀ atom vM
    (⊑cast⊒ᵀ mode seal★ c⊒ M⊑M′ p c-shape comp) q =
  ⊑cast⊒ᵀ mode seal★ c⊒ M⊑M′ q c-shape
    (imprecision-composition-shape-transport
      (sym (source-atom-shape-unique atom p q))
      refl refl comp)
atomic-source-value-reindexᵀ atom vM
    (⊑cast⊑ᵀ mode seal★ c⊑ M⊑M′ p c-shape comp) q =
  ⊑cast⊑ᵀ mode seal★ c⊑ M⊑M′ q c-shape
    (imprecision-composition-shape-transport
      refl refl
      (sym (source-atom-shape-unique atom p q))
      comp)
atomic-source-value-reindexᵀ atom vM
    (⊑cast⊑idᵀ seal★ c⊑ M⊑M′ p c-shape comp) q =
  ⊑cast⊑idᵀ seal★ c⊑ M⊑M′ q c-shape
    (imprecision-composition-shape-transport
      refl refl
      (sym (source-atom-shape-unique atom p q))
      comp)
atomic-source-value-reindexᵀ atom vM
    (conv⊑convᵀ {q = p} paired M⊑M′) q =
  conv⊑convᵀ
    (paired-cast-result-shape-reindexᵀ
      (source-atom-shape-unique atom p q)
      paired)
    M⊑M′
atomic-source-value-reindexᵀ atom vM
    (conv↑⊑ᵀ c↑ M⊑M′ p replacement) q =
  conv↑⊑ᵀ c↑ M⊑M′ q
    (replace-left-target-shape
      (sym (source-atom-shape-unique atom p q))
      replacement)
atomic-source-value-reindexᵀ atom vM
    (conv↓⊑ᵀ c↓ M⊑M′ p replacement) q =
  conv↓⊑ᵀ c↓ M⊑M′ q
    (replace-left-source-shape
      (sym (source-atom-shape-unique atom p q))
      replacement)
atomic-source-value-reindexᵀ atom vM
    (⊑conv↑ᵀ c↑ M⊑M′ p replacement) q =
  ⊑conv↑ᵀ c↑ M⊑M′ q
    (replace-right-target-shape
      (sym (source-atom-shape-unique atom p q))
      replacement)
atomic-source-value-reindexᵀ atom vM
    (⊑conv↓ᵀ c↓ M⊑M′ p replacement) q =
  ⊑conv↓ᵀ c↓ M⊑M′ q
    (replace-right-source-shape
      (sym (source-atom-shape-unique atom p q))
      replacement)

result-conceal-conversionᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A B B′ c μ α X χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (indexed : WeakOneStepIndexedResult
    {M = M} {N′ = V′} {χ = χ} {ρ = ρ} p) →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  let inner = weakIndexedResult indexed in
  ∃[ μ′ ]
    ConcealConversion μ′ (resultLeftCtx inner)
      (leftStoreⁱ (resultStore inner))
      (applyTyVars (sourceChanges inner) α)
      (applyTys (sourceChanges inner) X)
      (applyCoercions (sourceChanges inner) c)
      (applyTys (sourceChanges inner) A)
      (applyTys (sourceChanges inner) B)
result-conceal-conversionᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} {α = α} {X = X}
    indexed c↓
    with apply-conceal-conversions-exact
      {χs = sourceChanges (weakIndexedResult indexed)} c↓
result-conceal-conversionᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} {α = α} {X = X}
    indexed c↓
    | μ′ , c′↓ =
  μ′ , final-conversion
  where
  inner = weakIndexedResult indexed

  final-conversion :
    ConcealConversion μ′ (resultLeftCtx inner)
      (leftStoreⁱ (resultStore inner))
      (applyTyVars (sourceChanges inner) α)
      (applyTys (sourceChanges inner) X)
      (applyCoercions (sourceChanges inner) c)
      (applyTys (sourceChanges inner) A)
      (applyTys (sourceChanges inner) B)
  final-conversion =
    subst
      (λ Δ → ConcealConversion μ′ Δ
        (leftStoreⁱ (resultStore inner))
        (applyTyVars (sourceChanges inner) α)
        (applyTys (sourceChanges inner) X)
        (applyCoercions (sourceChanges inner) c)
        (applyTys (sourceChanges inner) A)
        (applyTys (sourceChanges inner) B))
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → ConcealConversion μ′
          (applyTyCtxs (sourceChanges inner) Δᴸ) Σ
          (applyTyVars (sourceChanges inner) α)
          (applyTys (sourceChanges inner) X)
          (applyCoercions (sourceChanges inner) c)
          (applyTys (sourceChanges inner) A)
          (applyTys (sourceChanges inner) B))
        (sym (sourceStoreResult inner)) c′↓)

world-coherent-source-inert-conceal-castᵀ :
  ∀ {Φ Δᴸ Δᴿ ρ N V′ A B B′ c μ α X}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  C.Inert c →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  q [ α ↦ X ]ᴸ p →
  WorldCoherentLeftCatchupIndexedResult
    {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ} q
world-coherent-source-inert-conceal-castᵀ inert c↓
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q replacement
    with result-conceal-conversionᵀ indexed c↓
world-coherent-source-inert-conceal-castᵀ inert c↓
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q replacement
    | μ′ , final-conversion
    with final
world-coherent-source-inert-conceal-castᵀ inert c↓
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q replacement
    | μ′ , final-conversion
    | inj₁ (vW , noW) =
  world-coherent-left-indexed-catchup
    (left-indexed-catchup framed
      (left-catchup-invariant first-silent
        (inj₁ (vW ⟨ inert′ ⟩ , no•-⟨⟩ noW))))
    (weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix)
    coherent exclusive unique wfL
  where
  inner = weakIndexedResult indexed

  final-relation =
    conv↓⊑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)
      (transportLeftReplacementCoherent
        (weakIndexedTypeCoherence indexed) replacement)

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
world-coherent-source-inert-conceal-castᵀ inert c↓
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q replacement
    | μ′ , final-conversion
    | inj₂ refl =
  world-coherent-left-indexed-catchup
    (left-indexed-catchup
      (weak-one-step-index-resultᵀ combined type-eq
        combined-transport combined-coherence)
      (left-catchup-invariant
        (left-silent-invariant refl refl) (inj₂ refl)))
    combined-lineage coherent exclusive unique wfL
  where
  inner = weakIndexedResult indexed

  final-relation =
    conv↓⊑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)
      (transportLeftReplacementCoherent
        (weakIndexedTypeCoherence indexed) replacement)

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

world-coherent-source-id-conceal-castᵀ :
  ∀ {Φ Δᴸ Δᴿ ρ N V′ A B′ μ α X}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  Atom A →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X
    (C.id A) A A →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  q [ α ↦ X ]ᴸ p →
  WorldCoherentLeftCatchupIndexedResult
    {N = N ⟨ C.id A ⟩} {V′ = V′} {ρ = ρ} q
world-coherent-source-id-conceal-castᵀ atom c↓
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q replacement
    with result-conceal-conversionᵀ indexed c↓
world-coherent-source-id-conceal-castᵀ atom c↓
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q replacement
    | μ′ , final-conversion
    with final
world-coherent-source-id-conceal-castᵀ atom c↓
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q replacement
    | μ′ , final-conversion
    | inj₁ (vW , noW) =
  world-coherent-left-indexed-catchup
    (left-indexed-catchup
      (weak-one-step-index-resultᵀ combined type-eq
        combined-transport combined-coherence)
      (left-catchup-invariant
        (left-silent-invariant refl refl) (inj₁ (vW , noW))))
    combined-lineage coherent exclusive unique wfL
  where
  inner = weakIndexedResult indexed

  final-relation =
    conv↓⊑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)
      (transportLeftReplacementCoherent
        (weakIndexedTypeCoherence indexed) replacement)

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
world-coherent-source-id-conceal-castᵀ atom c↓
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q replacement
    | μ′ , final-conversion
    | inj₂ refl =
  world-coherent-left-indexed-catchup
    (left-indexed-catchup
      (weak-one-step-index-resultᵀ combined type-eq
        combined-transport combined-coherence)
      (left-catchup-invariant
        (left-silent-invariant refl refl) (inj₂ refl)))
    combined-lineage coherent exclusive unique wfL
  where
  inner = weakIndexedResult indexed

  final-relation =
    conv↓⊑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)
      (transportLeftReplacementCoherent
        (weakIndexedTypeCoherence indexed) replacement)

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

world-coherent-source-conceal-castᵀ :
  ∀ {Φ Δᴸ Δᴿ ρ N V′ A B B′ c μ α X}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  q [ α ↦ X ]ᴸ p →
  WorldCoherentLeftCatchupIndexedResult
    {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ} q
world-coherent-source-conceal-castᵀ {A = ＇ Y}
    c↓@(conceal-id-var hY ok) catchup q replacement =
  world-coherent-source-id-conceal-castᵀ
    (＇ Y) c↓ catchup q replacement
world-coherent-source-conceal-castᵀ {A = ‵ ι}
    c↓@conceal-id-base catchup q replacement =
  world-coherent-source-id-conceal-castᵀ
    (‵ ι) c↓ catchup q replacement
world-coherent-source-conceal-castᵀ
    c↓@conceal-id-★ catchup q replacement =
  world-coherent-source-id-conceal-castᵀ
    ★ c↓ catchup q replacement
world-coherent-source-conceal-castᵀ {α = α} {X = X}
    c↓@(conceal-seal hX α∈Σ ok) catchup q replacement =
  world-coherent-source-inert-conceal-castᵀ
    (C.seal X α) c↓ catchup q replacement
world-coherent-source-conceal-castᵀ
    c↓@(conceal-fun {s = s} {t = t} c↑ c↓′)
    catchup q replacement =
  world-coherent-source-inert-conceal-castᵀ
    (C._↦_ s t) c↓ catchup q replacement
world-coherent-source-conceal-castᵀ
    c↓@(conceal-all {s = s} c↓′) catchup q replacement =
  world-coherent-source-inert-conceal-castᵀ
    (C.`∀ s) c↓ catchup q replacement

world-coherent-source-conceal-catchupᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V′ : Term} {A B B′ X : Ty} {c : Coercion}
    {μ : ModeEnv} {α : TyVar}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺} p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  q [ α ↦ X ]ᴸ p →
  WorldCoherentLeftCatchupIndexedResult
    {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} q
world-coherent-source-conceal-catchupᵀ
    prefix c↓ catchup q replacement =
  world-coherent-source-conceal-castᵀ
    (weaken-conceal-conversion
      (leftStoreⁱ-prefix-inclusion prefix) c↓)
    catchup q replacement
