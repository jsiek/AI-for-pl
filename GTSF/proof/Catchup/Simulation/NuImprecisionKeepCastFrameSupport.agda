module proof.Catchup.Simulation.NuImprecisionKeepCastFrameSupport where

-- File Charter:
--   * Composes source `keep` steps with universal catch-up results.
--   * Frames weak one-step results with target casts.
--   * Lifts indexed weak one-step results through source narrowing and
--     widening casts.
--   * Contains no polymorphic reduction case or allocation scheduling.

open import proof.Store.Prefix.NuImprecisionTermStorePrefixLemma using
  (term-imprecision-store-prefixᵀ)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import CastImprecisionShape using (_⊢ᶜ_⦂_)
import CastImprecisionShape as CastShape using (narrowing; widening)
open import ImprecisionComposition using (⌊_⌋; _；_≋_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_; ∀ⁱ_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuReduction using
  ( applyCoercion
  ; applyTy
  ; applyTyCtxs
  ; applyTys
  ; keep
  ; _—→[_]_
  )
open import NuTerms using (No•; Value; blame; _⟨_⟩)
open import QuotientedTermImprecision
open import TermTyping using (CastMode; SealModeStore★; _∣_∣_⊢_⦂_)
open import Types using (`∀)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  (cast-shape-applyCoercions; imprecision-composition-shape-transport)
open import proof.Core.Properties.NuNarrowingTransport using
  (apply-narrows-typing)
open import proof.Core.Properties.NuWideningTransport using
  (apply-widens-typing)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; cast-↠)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  (weak-one-step-prepend-left-silentᵀ)
open import
  proof.Catchup.Simulation.NuImprecisionWeakOneStepResultTransport
  using (weak-one-step-index-resultᵀ)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef
open import proof.OneStep.NuImprecisionWeakOneStepSourceCastFrame
open import proof.Catchup.Core.NuImprecisionCatchupComposition


left-catchup-all-keep-stepᵀ :
  ∀ {Φ Δᴸ Δᴿ M N V′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  M —→[ keep ] N →
  (Value N × No• N) ⊎ N ≡ blame →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  LeftCatchupAllResult {N = M} {V′ = V′} {ρ = ρ} q
left-catchup-all-keep-stepᵀ source→ final N⊑V′ =
  let result = weak-one-step-keep-source-catchupᵀ source→ N⊑V′ in
  left-all-catchup (weak-all-result result N⊑V′)
    (left-catchup-invariant
      (left-silent-invariant refl refl) final)

left-catchup-all-prepend-keepᵀ :
  ∀ {Φ Δᴸ Δᴿ M N V′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  M —→[ keep ] N →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q →
  LeftCatchupAllResult {N = M} {V′ = V′} {ρ = ρ} q
left-catchup-all-prepend-keepᵀ source→ N⊑V′
    (left-all-catchup second
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)) =
  let
    first = weak-one-step-keep-source-catchupᵀ source→ N⊑V′
    combined = weak-one-step-prepend-left-silentᵀ
      (left-silent first (left-silent-invariant refl refl))
      (weakResult second)
  in
  left-all-catchup
    (weak-all-result combined (canonicalAllResults second))
    (left-catchup-invariant
      (left-silent-invariant refl refl) final)

left-catchup-indexed-all-keep-stepᵀ :
  ∀ {Φ Δᴸ Δᴿ M N V′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (source→ : M —→[ keep ] N) →
  (final : (Value N × No• N) ⊎ N ≡ blame) →
  (N⊑V′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q) →
  LeftCatchupIndexedAllResult
    {N = M} {V′ = V′} {ρ = ρ} q
left-catchup-indexed-all-keep-stepᵀ source→ final N⊑V′ =
  left-indexed-all-catchup
    (weak-one-step-index-resultᵀ result refl transport coherence)
    (left-catchup-invariant
      (left-silent-invariant refl refl) final)
  where
  result = weak-one-step-keep-source-catchupᵀ source→ N⊑V′
  transport = weak-one-step-keep-source-catchup-transportᵀ source→ N⊑V′
  coherence =
    weak-one-step-keep-source-catchup-type-coherenceᵀ source→ N⊑V′

left-catchup-indexed-all-prefix-prepend-keepᵀ :
  ∀ {Φ Δᴸ Δᴿ M N V′ C C′ q}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  (source→ : M —→[ keep ] N) →
  (N⊑V′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q) →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ N ⦂ `∀ C →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ V′ ⦂ `∀ C′ →
  LeftCatchupIndexedAllResult
    {N = N} {V′ = V′} {ρ = ρ⁺} q →
  LeftCatchupIndexedAllResult
    {N = M} {V′ = V′} {ρ = ρ⁺} q
left-catchup-indexed-all-prefix-prepend-keepᵀ
    prefix source→ N⊑V′ N⊢ V′⊢ catchup =
  left-catchup-indexed-all-prepend-keepᵀ source→
    (term-imprecision-store-prefixᵀ prefix N⊑V′ N⊢ V′⊢) catchup

weak-one-step-target-cast-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c χ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (inner : WeakOneStepResult ρ M N′ A A′ χ) →
  (resultCtx inner
    ∣ resultLeftCtx inner
    ∣ resultRightCtx inner
    ∣ resultStore inner ∣ []
    ⊢ᴺ sourceResult inner ⊑
      (targetResult inner ⟨
        applyCoercions (targetTailChanges inner)
          (applyCoercion χ c) ⟩)
    ⦂ applyTys (sourceChanges inner) A
      ⊑ applyTys (targetTailChanges inner) (applyTy χ B′)
    ∶ transportType inner q) →
  WeakOneStepResult ρ M (N′ ⟨ applyCoercion χ c ⟩) A B′ χ
weak-one-step-target-cast-frameᵀ
    {A = A} {B′ = B′} {c = c} {χ = χ} inner result =
  record
    { sourceChanges = sourceChanges inner
    ; targetTailChanges = targetTailChanges inner
    ; sourceResult = sourceResult inner
    ; targetResult =
        targetResult inner ⟨
          applyCoercions (targetTailChanges inner)
            (applyCoercion χ c) ⟩
    ; resultCtx = resultCtx inner
    ; resultLeftCtx = resultLeftCtx inner
    ; resultRightCtx = resultRightCtx inner
    ; sourceCtxResult = sourceCtxResult inner
    ; targetCtxResult = targetCtxResult inner
    ; resultStore = resultStore inner
    ; resultSourceType = applyTys (sourceChanges inner) A
    ; resultTargetType =
        applyTys (targetTailChanges inner) (applyTy χ B′)
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = transportType inner
    ; transportAllBody = transportAllBody inner
    ; transportRightBody = transportRightBody inner
    ; transportSourceNu = transportSourceNu inner
    ; resultType = transportType inner _
    ; sourceCatchup = sourceCatchup inner
    ; targetTail = cast-↠ (targetTail inner)
    ; sourceStoreResult = sourceStoreResult inner
    ; targetStoreResult = targetStoreResult inner
    ; relatedResults = result
    }

weak-one-step-target-cast-frame-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c χ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (inner : WeakOneStepResult ρ M N′ A A′ χ)
    (result : resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ sourceResult inner ⊑
        (targetResult inner ⟨
          applyCoercions (targetTailChanges inner)
            (applyCoercion χ c) ⟩)
      ⦂ applyTys (sourceChanges inner) A
        ⊑ applyTys (targetTailChanges inner) (applyTy χ B′)
      ∶ transportType inner q) →
  WeakOneStepTransport inner →
  WeakOneStepTransport
    (weak-one-step-target-cast-frameᵀ inner result)
weak-one-step-target-cast-frame-transportᵀ
    inner result transport =
  weak-step-transport (transportNo•Terms transport)

weak-one-step-target-cast-frame-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c χ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (inner : WeakOneStepResult ρ M N′ A A′ χ)
    (result : resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ sourceResult inner ⊑
        (targetResult inner ⟨
          applyCoercions (targetTailChanges inner)
            (applyCoercion χ c) ⟩)
      ⦂ applyTys (sourceChanges inner) A
        ⊑ applyTys (targetTailChanges inner) (applyTy χ B′)
      ∶ transportType inner q) →
  WeakOneStepTypeCoherence inner →
  WeakOneStepTypeCoherence
    (weak-one-step-target-cast-frameᵀ inner result)
weak-one-step-target-cast-frame-coherenceᵀ
    inner result coherence =
  weak-step-type-coherence
    (transportArrowCoherent coherence)
    (transportAllCoherent coherence)
    (transportShapeCoherent coherence)
    (transportRightBodyShapeCoherent coherence)
    (transportLeftReplacementCoherent coherence)
    (transportRightReplacementCoherent coherence)
    (transportPairedReplacementCoherent coherence)
    (transportAllBodyPairedReplacementCoherent coherence)
    (transportSourceNuBodyLeftReplacementCoherent coherence)
    (transportRightBodyRightReplacementCoherent coherence)

weak-one-step-source-narrow-cast-indexed-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B c μ χ s}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  CastShape.narrowing ⊢ᶜ c ⦂ s →
  s ； ⌊ p ⌋ ≋ ⌊ q ⌋ →
  (indexed : WeakOneStepIndexedResult
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p) →
  WeakOneStepIndexedResult
    {M = M ⟨ c ⟩} {N′ = N′} {χ = χ} {ρ = ρ} q
weak-one-step-source-narrow-cast-indexed-frameᵀ
    {Δᴸ = Δᴸ} {B = B} {c = c} {p = p} {q = q}
    mode seal★ c⊒ c-shape comp indexed
    with apply-narrows-typing
      { χs = sourceChanges (weakIndexedResult indexed) }
      mode seal★ c⊒
weak-one-step-source-narrow-cast-indexed-frameᵀ
    {Δᴸ = Δᴸ} {B = B} {c = c} {p = p} {q = q}
    mode seal★ c⊒ c-shape comp indexed
    | μ′ , mode′ , seal★′ , c′⊒ =
  weak-indexed-result framed (relatedResults framed)
    framed-transport framed-coherence
  where
  inner = weakIndexedResult indexed

  final-seal :
    SealModeStore★ μ′ (leftStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ′)
      (sym (sourceStoreResult inner)) seal★′

  final-cast :
    μ′ ∣ resultLeftCtx inner
      ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) c
        ∶ applyTys (sourceChanges inner) _
          ⊒ applyTys (sourceChanges inner) B
  final-cast =
    subst
      (λ Δ → μ′ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) c
          ∶ applyTys (sourceChanges inner) _
            ⊒ applyTys (sourceChanges inner) B)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → μ′ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
          ⊢ applyCoercions (sourceChanges inner) c
            ∶ applyTys (sourceChanges inner) _
              ⊒ applyTys (sourceChanges inner) B)
        (sym (sourceStoreResult inner)) c′⊒)

  final-c-shape =
    cast-shape-applyCoercions
      (sourceChanges inner) c-shape

  final-comp =
    imprecision-composition-shape-transport
      refl
      (transportShapeCoherent
        (weakIndexedTypeCoherence indexed) p)
      (transportShapeCoherent
        (weakIndexedTypeCoherence indexed) q)
      comp

  final-relation =
    cast⊒⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner _)
      final-c-shape final-comp

  framed = weak-one-step-source-cast-frameᵀ inner final-relation
  framed-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)
  framed-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)

weak-one-step-source-widen-cast-indexed-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B c μ χ s}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  CastShape.widening ⊢ᶜ c ⦂ s →
  s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
  (indexed : WeakOneStepIndexedResult
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p) →
  WeakOneStepIndexedResult
    {M = M ⟨ c ⟩} {N′ = N′} {χ = χ} {ρ = ρ} q
weak-one-step-source-widen-cast-indexed-frameᵀ
    {Δᴸ = Δᴸ} {B = B} {c = c} {p = p} {q = q}
    mode seal★ c⊑ c-shape comp indexed
    with apply-widens-typing
      { χs = sourceChanges (weakIndexedResult indexed) }
      mode seal★ c⊑
weak-one-step-source-widen-cast-indexed-frameᵀ
    {Δᴸ = Δᴸ} {B = B} {c = c} {p = p} {q = q}
    mode seal★ c⊑ c-shape comp indexed
    | μ′ , mode′ , seal★′ , c′⊑ =
  weak-indexed-result framed (relatedResults framed)
    framed-transport framed-coherence
  where
  inner = weakIndexedResult indexed

  final-seal :
    SealModeStore★ μ′ (leftStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ′)
      (sym (sourceStoreResult inner)) seal★′

  final-cast :
    μ′ ∣ resultLeftCtx inner
      ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) c
        ∶ applyTys (sourceChanges inner) _
          ⊑ applyTys (sourceChanges inner) B
  final-cast =
    subst
      (λ Δ → μ′ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) c
          ∶ applyTys (sourceChanges inner) _
            ⊑ applyTys (sourceChanges inner) B)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → μ′ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
          ⊢ applyCoercions (sourceChanges inner) c
            ∶ applyTys (sourceChanges inner) _
              ⊑ applyTys (sourceChanges inner) B)
        (sym (sourceStoreResult inner)) c′⊑)

  final-c-shape =
    cast-shape-applyCoercions
      (sourceChanges inner) c-shape

  final-comp =
    imprecision-composition-shape-transport
      refl
      (transportShapeCoherent
        (weakIndexedTypeCoherence indexed) q)
      (transportShapeCoherent
        (weakIndexedTypeCoherence indexed) p)
      comp

  final-relation =
    cast⊑⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner _)
      final-c-shape final-comp

  framed = weak-one-step-source-cast-frameᵀ inner final-relation
  framed-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)
  framed-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)
