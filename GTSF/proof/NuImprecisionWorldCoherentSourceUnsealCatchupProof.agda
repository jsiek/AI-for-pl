module proof.NuImprecisionWorldCoherentSourceUnsealCatchupProof where

-- File Charter:
--   * Proves coherent catch-up through one active source unseal.
--   * Cancels the terminal source seal in the final coherent world.
--   * Composes the resulting seal-unseal step with the inner catch-up.
--   * Uses the strict source-cast terminal frame when the source is blame.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import Coercions using (unseal)
open import Conversion using
  ( RevealConversion
  ; reveal-unseal
  ; weaken-reveal-conversion
  )
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (suc)
open import Data.Product using (_,_; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  ( StoreChanges
  ; _—→[_]_
  ; applyTyCtxs
  ; applyTys
  ; bind
  ; keep
  ; pure-step
  ; seal-unseal
  )
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ)
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; no•-⟨⟩
  ; _⟨_⟩
  )
open import NuStore using (StoreWf)
open import QuotientedTermImprecision using
  ( conv↑⊑ᵀ
  ; nu-term-imprecision-source-typing
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Relation.Binary.PropositionalEquality using
  (subst; sym)
import Relation.Binary.HeterogeneousEquality as HE

open import proof.NuImprecisionCatchupComposition using
  ( weak-one-step-keep-source-catchup-type-coherenceᵀ
  ; weak-one-step-keep-source-catchup-transportᵀ
  ; weak-one-step-keep-source-catchupᵀ
  )
open import proof.NuImprecisionCatchupSourceCastTerminal using
  (left-catchup-indexed-source-cast-blame-frameᵀ)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionSimulation using
  ( weak-one-step-source-cast-frame-coherenceᵀ
  ; weak-one-step-source-cast-frame-silentᵀ
  ; weak-one-step-source-cast-frame-transportᵀ
  ; weak-one-step-source-cast-frameᵀ
  )
open import proof.NuImprecisionSimulationCore using
  ( apply-reveal-conversions
  ; subst²-to-≅
  ; weak-one-step-compose-type-to-nested≅
  ; weak-one-step-index-resultᵀ
  ; weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
  ; weak-one-step-prepend-left-silent-preserves-transportᵀ
  ; weak-one-step-prepend-left-silentᵀ
  )
open import proof.NuImprecisionSimulationResultDef using
  ( WeakOneStepIndexedResult
  ; canonicalIndexedResults
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
  )
open import proof.NuImprecisionSourceSealCancellationDef using
  (SourceSealCancellationᵀ)
open import proof.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion)
open import proof.NuImprecisionWorldCoherentResultDef using
  ( world-coherent-left-indexed-catchup
  )
open import proof.NuImprecisionWorldCoherentSourceUnsealCatchupDef using
  (WorldCoherentSourceUnsealCatchupᵀ)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuProgress using
  (SealView; canonical-＇; sv-seal)
open import proof.ReductionProperties using
  (applyCoercions)
open import TermTyping using (forget; _∣_∣_⊢_⦂_)
open import Types using
  (Store; Ty; TyCtx; TyVar; ＇_; ⇑ᵗ)


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


seal-no•⁻¹ :
  ∀ {V A α} →
  No• (V ⟨ C.seal A α ⟩) →
  No• V
seal-no•⁻¹ (no•-⟨⟩ noV) = noV


data AppliedUnseal (χs : StoreChanges) (α : TyVar) (X : Ty) : Set where
  applied-unseal :
    ∀ {α′ X′} →
    applyCoercions χs (unseal α X) ≡ unseal α′ X′ →
    applyTys χs (＇ α) ≡ ＇ α′ →
    applyTys χs X ≡ X′ →
    AppliedUnseal χs α X


applied-unseal-view :
  ∀ χs α X →
  AppliedUnseal χs α X
applied-unseal-view [] α X = applied-unseal refl refl refl
applied-unseal-view (keep ∷ χs) α X
    with applied-unseal-view χs α X
applied-unseal-view (keep ∷ χs) α X
    | applied-unseal coercion-eq source-eq target-eq =
  applied-unseal coercion-eq source-eq target-eq
applied-unseal-view (bind A ∷ χs) α X
    with applied-unseal-view χs (suc α) (⇑ᵗ X)
applied-unseal-view (bind A ∷ χs) α X
    | applied-unseal coercion-eq source-eq target-eq =
  applied-unseal coercion-eq source-eq target-eq


applied-unseal-for-conversion :
  ∀ {μ Δ Σ α X} χs →
  RevealConversion μ Δ Σ α X
    (unseal α X) (＇ α) X →
  AppliedUnseal χs α X
applied-unseal-for-conversion χs c↑ =
  applied-unseal-view χs _ _


canonical-applied-var :
  ∀ {Δ : TyCtx} {Σ : Store} {V : Term} {A : Ty} {α : TyVar} →
  A ≡ ＇ α →
  Value V →
  Δ ∣ Σ ∣ [] ⊢ V ⦂ A →
  SealView {α = α} V
canonical-applied-var refl vV V⊢ = canonical-＇ vV (forget V⊢)


reveal-unseal-membership :
  ∀ {μ Δ Σ β Y c A B α X} →
  c ≡ unseal α X →
  A ≡ ＇ α →
  B ≡ X →
  RevealConversion μ Δ Σ β Y c A B →
  (α , X) ∈ Σ
reveal-unseal-membership refl refl refl
    (reveal-unseal hX αX∈Σ ok) =
  αX∈Σ


cancel-applied-source-seal :
  ∀ {Φ Δᴸ Δᴿ V W B A D X Y α}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  SourceSealCancellationᵀ →
  A ≡ ＇ α →
  D ≡ X →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  Value V →
  Value W →
  No• W →
  (α , X) ∈ leftStoreⁱ ρ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⟨ C.seal Y α ⟩ ⊑ W ⦂ A ⊑ B ∶ p →
  (q : Φ ∣ Δᴸ ⊢ D ⊑ B ⊣ Δᴿ) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ W ⦂ D ⊑ B ∶ q
cancel-applied-source-seal cancel refl refl coherent exclusive wfL
    vV vW noW αX∈Σ relation q =
  cancel coherent exclusive wfL vV vW noW αX∈Σ relation q


applied-seal-unseal-step :
  ∀ {V Y c α X} →
  c ≡ unseal α X →
  Value V →
  V ⟨ C.seal Y α ⟩ ⟨ c ⟩ —→[ keep ] V
applied-seal-unseal-step refl vV = pure-step (seal-unseal vV)


world-coherent-source-unseal-catchup-proofᵀ :
  SourceSealCancellationᵀ →
  WorldCoherentSourceUnsealCatchupᵀ
world-coherent-source-unseal-catchup-proofᵀ
    cancel prefix c↑ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final)
        inner-transport inner-coherence)
      coherent exclusive wfL)
    q
    with result-reveal-conversionᵀ indexed
      (weaken-reveal-conversion
        (leftStoreⁱ-prefix-inclusion prefix) c↑)
       | applied-unseal-for-conversion
           (sourceChanges (weakIndexedResult indexed)) c↑
world-coherent-source-unseal-catchup-proofᵀ
    cancel prefix c↑ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final)
        inner-transport inner-coherence)
      coherent exclusive wfL)
    q
    | μ′ , α′ , X′ , final-conversion
    | applied-unseal coercion-eq source-eq target-eq
    with final
world-coherent-source-unseal-catchup-proofᵀ
    cancel prefix c↑ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final)
        inner-transport inner-coherence)
      coherent exclusive wfL)
    q
    | μ′ , α′ , X′ , final-conversion
    | applied-unseal coercion-eq source-eq target-eq
    | inj₁ (vS , noS)
    with canonical-applied-var source-eq vS
      (nu-term-imprecision-source-typing
        (canonicalIndexedResults indexed))
world-coherent-source-unseal-catchup-proofᵀ
    cancel prefix c↑ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final)
        inner-transport inner-coherence)
      coherent exclusive wfL)
    q
    | μ′ , α′ , X′ , final-conversion
    | applied-unseal coercion-eq source-eq target-eq
    | inj₁ (vS , noS)
    | sv-seal {W = W} {A = Y} vW refl =
  world-coherent-left-indexed-catchup
    (left-indexed-catchup
      (weak-one-step-index-resultᵀ combined type-eq)
      (left-catchup-invariant
        (left-silent-invariant refl refl)
        (inj₁ (vW , seal-no•⁻¹ noS)))
      combined-transport combined-coherence)
    coherent exclusive wfL
  where
  inner = weakIndexedResult indexed

  final-relation =
    conv↑⊑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  first-silent =
    weak-one-step-source-cast-frame-silentᵀ
      inner final-relation (left-silent-invariant refl refl)

  final-membership =
    reveal-unseal-membership coercion-eq source-eq target-eq
      final-conversion

  final-step = applied-seal-unseal-step coercion-eq vW

  second-relation :
    resultCtx first
      ∣ resultLeftCtx first
      ∣ resultRightCtx first
      ∣ resultStore first ∣ []
      ⊢ᴺ W ⊑ targetResult first
      ⦂ resultSourceType first ⊑ resultTargetType first
      ∶ resultType first
  second-relation =
    cancel-applied-source-seal cancel source-eq target-eq
      coherent exclusive wfL vW vV′ noV′ final-membership
      (canonicalIndexedResults indexed) (transportType inner q)

  second = weak-one-step-keep-source-catchupᵀ
    {Φ = resultCtx first}
    {Δᴸ = resultLeftCtx first}
    {Δᴿ = resultRightCtx first}
    {A = resultSourceType first}
    {B = resultTargetType first}
    {p = resultType first}
    {ρ = resultStore first}
    final-step second-relation

  combined = weak-one-step-prepend-left-silentᵀ
    (left-silent first first-silent) second

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
      inner final-relation inner-transport

  first-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation inner-coherence

  combined-transport =
    weak-one-step-prepend-left-silent-preserves-transportᵀ
      (left-silent first first-silent) second
      first-transport
      (weak-one-step-keep-source-catchup-transportᵀ
        final-step second-relation)

  combined-coherence =
    weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
      (left-silent first first-silent) second
      first-coherence
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        final-step second-relation)
world-coherent-source-unseal-catchup-proofᵀ
    cancel prefix c↑ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final)
        inner-transport inner-coherence)
      coherent exclusive wfL)
    q
    | μ′ , α′ , X′ , final-conversion
    | applied-unseal coercion-eq source-eq target-eq
    | inj₂ refl =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-source-cast-blame-frameᵀ
      catchup framed refl first-silent
      first-transport first-coherence refl)
    coherent exclusive wfL
  where
  inner = weakIndexedResult indexed

  final-relation =
    conv↑⊑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first (relatedResults first)

  first-silent =
    weak-one-step-source-cast-frame-silentᵀ
      inner final-relation (left-silent-invariant refl refl)

  first-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation inner-transport

  first-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation inner-coherence
