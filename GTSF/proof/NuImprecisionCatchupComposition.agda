module proof.NuImprecisionCatchupComposition where

-- File Charter:
--   * Composes a checked source `keep` step with a later catch-up result.
--   * Preserves indexed transport and type-coherence witnesses.
--   * Exports the indexed catch-up wrapper used by active cast dispatchers.
--   * Depends only on the stable weak-simulation core.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)
import Relation.Binary.HeterogeneousEquality as HE

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  (keep; _—→[_]_; ↠-refl; ↠-step)
open import NuTermImprecision using (StoreImp)
open import QuotientedTermImprecision
open import proof.NuImprecisionSimulationCore

weak-one-step-keep-source-catchupᵀ :
  ∀ {Φ Δᴸ Δᴿ M N N′ A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  M —→[ keep ] N →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p →
  WeakOneStepResult ρ M N′ A B keep
weak-one-step-keep-source-catchupᵀ source→ result =
  record
    { sourceChanges = keep ∷ []
    ; targetTailChanges = []
    ; sourceResult = _
    ; targetResult = _
    ; resultCtx = _
    ; resultLeftCtx = _
    ; resultRightCtx = _
    ; sourceCtxResult = refl
    ; targetCtxResult = refl
    ; resultStore = _
    ; resultSourceType = _
    ; resultTargetType = _
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = λ p → p
    ; transportAllBody = λ p → p
    ; transportRightBody = λ p → p
    ; resultType = _
    ; sourceCatchup = ↠-step source→ ↠-refl
    ; targetTail = ↠-refl
    ; sourceStoreResult = refl
    ; targetStoreResult = refl
    ; relatedResults = result
    }

weak-one-step-keep-source-catchup-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ M N N′ A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (source→ : M —→[ keep ] N) →
  (result : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p) →
  WeakOneStepTransport
    (weak-one-step-keep-source-catchupᵀ source→ result)
weak-one-step-keep-source-catchup-transportᵀ source→ result =
  weak-step-transport (λ noL noL′ L⊑L′ → L⊑L′)

weak-one-step-keep-source-catchup-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ M N N′ A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (source→ : M —→[ keep ] N) →
  (result : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p) →
  WeakOneStepTypeCoherence
    (weak-one-step-keep-source-catchupᵀ source→ result)
weak-one-step-keep-source-catchup-type-coherenceᵀ source→ result =
  weak-step-type-coherence
    (λ pC pD → HE.≅-to-≡
      (transportArrowType-to-raw≅ oneStep pC pD))
    (λ q → HE.≅-to-≡
      (transportAllType-to-raw≅ oneStep q))
  where
  oneStep = weak-one-step-keep-source-catchupᵀ source→ result

weak-one-step-prepend-source-keepᵀ :
  ∀ {Φ Δᴸ Δᴿ M N N′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  M —→[ keep ] N →
  WeakOneStepResult ρ N N′ A B χ →
  WeakOneStepResult ρ M N′ A B χ
weak-one-step-prepend-source-keepᵀ source→ second =
  record
    { sourceChanges = keep ∷ sourceChanges second
    ; targetTailChanges = targetTailChanges second
    ; sourceResult = sourceResult second
    ; targetResult = targetResult second
    ; resultCtx = resultCtx second
    ; resultLeftCtx = resultLeftCtx second
    ; resultRightCtx = resultRightCtx second
    ; sourceCtxResult = sourceCtxResult second
    ; targetCtxResult = targetCtxResult second
    ; resultStore = resultStore second
    ; resultSourceType = resultSourceType second
    ; resultTargetType = resultTargetType second
    ; sourceTypeResult = sourceTypeResult second
    ; targetTypeResult = targetTypeResult second
    ; transportType = transportType second
    ; transportAllBody = transportAllBody second
    ; transportRightBody = transportRightBody second
    ; resultType = resultType second
    ; sourceCatchup = ↠-step source→ (sourceCatchup second)
    ; targetTail = targetTail second
    ; sourceStoreResult = sourceStoreResult second
    ; targetStoreResult = targetStoreResult second
    ; relatedResults = relatedResults second
    }

weak-one-step-prepend-source-keep-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ M N N′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (source→ : M —→[ keep ] N)
    (second : WeakOneStepResult ρ N N′ A B χ) →
  WeakOneStepTransport second →
  WeakOneStepTransport
    (weak-one-step-prepend-source-keepᵀ source→ second)
weak-one-step-prepend-source-keep-transportᵀ
    source→ second transport =
  weak-step-transport (transportNo•Terms transport)

weak-one-step-prepend-source-keep-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ M N N′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (source→ : M —→[ keep ] N)
    (second : WeakOneStepResult ρ N N′ A B χ) →
  WeakOneStepTypeCoherence second →
  WeakOneStepTypeCoherence
    (weak-one-step-prepend-source-keepᵀ source→ second)
weak-one-step-prepend-source-keep-type-coherenceᵀ
    source→ second coherence =
  weak-step-type-coherence
    (λ pC pD → HE.≅-to-≡
      (HE.trans
        (transportArrowType-to-raw≅ combined pC pD)
        (HE.trans
          (HE.sym (transportArrowType-to-raw≅ second pC pD))
          (≡-to-≅ (transportArrowCoherent coherence pC pD)))))
    (λ q → HE.≅-to-≡
      (HE.trans
        (transportAllType-to-raw≅ combined q)
        (HE.trans
          (HE.sym (transportAllType-to-raw≅ second q))
          (≡-to-≅ (transportAllCoherent coherence q)))))
  where
  combined = weak-one-step-prepend-source-keepᵀ source→ second

left-catchup-indexed-prepend-keepᵀ :
  ∀ {Φ Δᴸ Δᴿ M N V′ A B}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (source→ : M —→[ keep ] N) →
  LeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ} p →
  LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p
left-catchup-indexed-prepend-keepᵀ source→
    (left-indexed-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      second-transport second-coherence) =
  left-indexed-catchup
    (weak-indexed-result combined (canonicalIndexedResults indexed))
    (left-catchup-invariant
      (left-silent-invariant refl refl) final)
    (weak-one-step-prepend-source-keep-transportᵀ
      source→ second second-transport)
    (weak-one-step-prepend-source-keep-type-coherenceᵀ
      source→ second second-coherence)
  where
  second = weakIndexedResult indexed
  combined = weak-one-step-prepend-source-keepᵀ source→ second
