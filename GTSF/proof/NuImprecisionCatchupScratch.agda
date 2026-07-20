{-# OPTIONS --allow-unsolved-metas --allow-incomplete-matches #-}

module proof.NuImprecisionCatchupScratch where

-- File Charter:
--   * Isolates active proof engineering for recursive universal catch-up.
--   * States arbitrary-type value catch-up and proves its terminal,
--     target-frame, and recursive quotient-dispatch clauses.
--   * Exposes source-∀ catch-up as a specialization of that recursion.
--   * Keeps the general indexed one-step dispatcher visibly incomplete while
--     its remaining structural clauses are developed.
--   * Exposes explicit quotient-instantiation residuals in that dispatcher.
--   * Depends only on the stable weak-simulation core; move a lemma to its
--     permanent module once its statement and proof are stable.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
import Relation.Binary.HeterogeneousEquality as HE

open import ImprecisionWf using (_∣_⊢_⊑_⊣_; ∀ⁱ_)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import Coercions using
  ( Inert
  ; genᵈ
  ; id-onlyᵈ
  ; instᵈ
  ; tag-or-idᵈ
  )
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import NarrowWiden using
  ( narrow-weaken
  ; widen-weaken
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using
  ( _—→[_]_
  ; _—↠[_]_
  ; applyStores
  ; applyTy
  ; applyTyCtxs
  ; applyTys
  ; blame-ν
  ; bind
  ; keep
  ; ξ-ν
  ; ν-step
  ; ↠-refl
  ; ↠-step
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Value
  ; no•-Λ
  ; no•-⟨⟩
  ; no•-blame
  ; ok-no
  ; ok-⟨⟩
  ; blame
  ; ν
  ; ƛ_
  ; Λ_
  ; `_
  ; _·_
  ; _•
  ; $
  ; _⊕[_]_
  ; _⟨_⟩
  ; ⇑ᵗᵐ
  )
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; lift-left-ctx-[]
  ; rightStoreⁱ
  )
open import QuotientedTermImprecision
open import TermTyping using
  (CastMode; SealModeStore★; _∣_∣_⊢_⦂_)
open import Types using (★; `∀; ⇑ᵗ; ⟰ᵗ)
open import NuStore using (StoreWf)
open import proof.MaximalLowerBoundsWf using (∀ᵢᶜ)
open import proof.CoercionProperties using (ModeRename)
open import proof.NuImprecisionAllocationSimulation using
  ( weak-one-step-matched-ν↑-indexed-catchup-outcomeᵀ
  ; weak-one-step-matched-νcast-indexed-catchup-outcomeᵀ
  ; weak-one-step-right-ν↑-indexed-outcomeᵀ
  ; weak-one-step-right-νcast-indexed-outcomeᵀ
  )
open import proof.NuImprecisionSimulationCore
open import proof.NuImprecisionQuotientValue using
  (left-catchup-indexed-final-quotientᵀ)
open import proof.NuImprecisionOneStepSourceCastFrames using
  ( weak-one-step-source-narrow-cast-indexed-frame-outcomeᵀ
  ; weak-one-step-source-widen-cast-indexed-frame-outcomeᵀ
  )
open import proof.NuImprecisionOneStepSourceConversionFrames using
  ( weak-one-step-source-conceal-conversion-indexed-frame-outcomeᵀ
  ; weak-one-step-source-reveal-conversion-indexed-frame-outcomeᵀ
  )
open import proof.NuImprecisionSimulation using
  ( left-catchup-indexed-prefix-α-Λᵀ
  ; weak-one-step-target-cast-frameᵀ
  ; weak-one-step-target-cast-frame-coherenceᵀ
  ; weak-one-step-target-cast-frame-transportᵀ
  )
open import proof.ReductionProperties using
  (applyCoercions; applyTy-★; applyTys-++; cast-↠)
open import proof.NuPreservation using (runtime-ν; runtime-⟨⟩)
open import proof.NuProgress using (runtime-value-no•)
open import proof.TypePreservation using
  (seal★-weaken; term-weaken)

left-catchup-indexed-resume-silentᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  (silent : LeftSilentIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p) →
  let first = weakIndexedResult (silentIndexedResult silent) in
  LeftCatchupIndexedResult
    {N = sourceResult first}
    {V′ = targetResult first}
    {ρ = resultStore first}
    (transportType first p) →
  LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p
left-catchup-indexed-resume-silentᵀ
    {A = A} {B = B} {p = p}
    (left-silent-indexed first-indexed
      (left-silent-invariant refl refl)
      first-runtime first-transport first-coherence)
    (left-indexed-catchup second-indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      second-transport second-coherence) =
  left-indexed-catchup
    (weak-indexed-result combined canonical)
    (left-catchup-invariant
      (left-silent-invariant refl refl) final)
    combined-transport combined-coherence
  where
  first-raw = weakIndexedResult first-indexed

  first = weak-one-step-reindexᵀ
    first-raw refl refl (canonicalIndexedResults first-indexed)

  first-transport′ =
    weak-one-step-reindex-preserves-transportᵀ
      first-raw refl refl (canonicalIndexedResults first-indexed)
      first-transport

  first-coherence′ =
    weak-one-step-reindex-preserves-type-coherenceᵀ
      first-raw refl refl (canonicalIndexedResults first-indexed)
      first-coherence

  second = weakIndexedResult second-indexed

  raw-combined =
    weak-one-step-prepend-left-silentᵀ
      (left-silent first (left-silent-invariant refl refl)) second

  source-eq :
    applyTys (sourceChanges second) (resultSourceType first) ≡
      applyTys
        (sourceChanges first ++ sourceChanges second) A
  source-eq =
    trans
      (cong (applyTys (sourceChanges second))
        (sourceTypeResult first))
      (sym (applyTys-++
        (sourceChanges first) (sourceChanges second) A))

  target-eq :
    applyTys (targetTailChanges second)
        (applyTy keep (resultTargetType first)) ≡
      applyTys (targetTailChanges second) (applyTy keep B)
  target-eq =
    cong
      (λ T → applyTys (targetTailChanges second) (applyTy keep T))
      (targetTypeResult first)

  index-eq = HE.≅-to-≡
    (HE.trans
      (subst²-to-≅
        {P = λ S T → resultCtx second ∣ resultLeftCtx second
          ⊢ S ⊑ T ⊣ resultRightCtx second}
        source-eq target-eq
        (transportType second (transportType first p)))
      (HE.sym
        (weak-one-step-compose-type-to-nested≅ first second p)))

  canonical =
    nu-term-imprecision-transport-typesᵀ
      source-eq target-eq index-eq
      (canonicalIndexedResults second-indexed)

  combined = weak-one-step-reindexᵀ
    raw-combined refl refl canonical

  raw-transport =
    weak-one-step-prepend-left-silent-preserves-transportᵀ
      (left-silent first (left-silent-invariant refl refl)) second
      first-transport′ second-transport

  combined-transport =
    weak-one-step-reindex-preserves-transportᵀ
      raw-combined refl refl canonical raw-transport

  raw-coherence =
    weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
      (left-silent first (left-silent-invariant refl refl)) second
      first-coherence′ second-coherence

  combined-coherence =
    weak-one-step-reindex-preserves-type-coherenceᵀ
      raw-combined refl refl canonical raw-coherence

left-catchup-indexed-target-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ W′ A A′ B B′}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p) →
  (framed : WeakOneStepIndexedResult
    {M = M} {N′ = W′} {χ = keep} {ρ = ρ} q) →
  let inner = weakIndexedResult (catchupIndexedResult catchup)
      first = weakIndexedResult framed
  in
  sourceResult first ≡ sourceResult inner →
  LeftSilentInvariant first →
  WeakOneStepTransport first →
  WeakOneStepTypeCoherence first →
  LeftCatchupIndexedResult
    {N = M} {V′ = W′} {ρ = ρ} q
left-catchup-indexed-target-frameᵀ
    (left-indexed-catchup indexed
      (left-catchup-invariant inner-silent final)
      inner-transport inner-coherence)
    framed refl first-silent first-transport first-coherence =
  left-indexed-catchup framed
    (left-catchup-invariant first-silent final)
    first-transport first-coherence

left-catchup-indexed-prefix-target-narrow-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B′ c μ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ A′ ⊒ B′ →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p) →
  LeftCatchupIndexedResult
    {N = M} {V′ = V′ ⟨ c ⟩} {ρ = ρ⁺} q
left-catchup-indexed-prefix-target-narrow-castᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c}
    prefix mode seal★ c⊒
    catchup@(left-indexed-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      inner-transport inner-coherence) =
  left-catchup-indexed-target-frameᵀ
    catchup framed refl (left-silent-invariant refl refl)
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation inner-transport)
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation inner-coherence)
  where
  inner = weakIndexedResult indexed

  seal★⁺ = seal★-weaken
    (rightStoreⁱ-prefix-inclusion prefix) seal★

  c⊒⁺ = narrow-weaken ≤-refl
    (rightStoreⁱ-prefix-inclusion prefix) c⊒

  final-seal =
    subst (SealModeStore★ _)
      (sym (targetStoreResult inner)) seal★⁺

  final-cast =
    subst
      (λ Δ → _ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ c ∶ A′ ⊒ B′)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → _ ∣ Δᴿ ∣ Σ ⊢ c ∶ A′ ⊒ B′)
        (sym (targetStoreResult inner)) c⊒⁺)

  final-relation =
    ⊑cast⊒ᵀ mode final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner _)

  first = weak-one-step-target-cast-frameᵀ
    inner final-relation

  framed = weak-indexed-result first (relatedResults first)

left-catchup-indexed-prefix-target-reveal-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B′ c μ β X′}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  RevealConversion μ Δᴿ (rightStoreⁱ ρ₀)
    β X′ c A′ B′ →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p) →
  LeftCatchupIndexedResult
    {N = M} {V′ = V′ ⟨ c ⟩} {ρ = ρ⁺} q
left-catchup-indexed-prefix-target-reveal-castᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c}
    prefix c↑
    catchup@(left-indexed-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      inner-transport inner-coherence) =
  left-catchup-indexed-target-frameᵀ
    catchup framed refl (left-silent-invariant refl refl)
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation inner-transport)
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation inner-coherence)
  where
  inner = weakIndexedResult indexed

  c↑⁺ = weaken-reveal-conversion
    (rightStoreⁱ-prefix-inclusion prefix) c↑

  final-conversion =
    subst
      (λ Δ → RevealConversion _ Δ
        (rightStoreⁱ (resultStore inner)) _ _ c A′ B′)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → RevealConversion _ Δᴿ Σ _ _ c A′ B′)
        (sym (targetStoreResult inner)) c↑⁺)

  final-relation =
    ⊑conv↑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner _)

  first = weak-one-step-target-cast-frameᵀ
    inner final-relation

  framed = weak-indexed-result first (relatedResults first)

left-catchup-indexed-prefix-target-conceal-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B′ c μ β X′}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  ConcealConversion μ Δᴿ (rightStoreⁱ ρ₀)
    β X′ c A′ B′ →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p) →
  LeftCatchupIndexedResult
    {N = M} {V′ = V′ ⟨ c ⟩} {ρ = ρ⁺} q
left-catchup-indexed-prefix-target-conceal-castᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c}
    prefix c↓
    catchup@(left-indexed-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      inner-transport inner-coherence) =
  left-catchup-indexed-target-frameᵀ
    catchup framed refl (left-silent-invariant refl refl)
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation inner-transport)
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation inner-coherence)
  where
  inner = weakIndexedResult indexed

  c↓⁺ = weaken-conceal-conversion
    (rightStoreⁱ-prefix-inclusion prefix) c↓

  final-conversion =
    subst
      (λ Δ → ConcealConversion _ Δ
        (rightStoreⁱ (resultStore inner)) _ _ c A′ B′)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → ConcealConversion _ Δᴿ Σ _ _ c A′ B′)
        (sym (targetStoreResult inner)) c↓⁺)

  final-relation =
    ⊑conv↓ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner _)

  first = weak-one-step-target-cast-frameᵀ
    inner final-relation

  framed = weak-indexed-result first (relatedResults first)

left-catchup-indexed-prefix-target-widen-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B′ c μ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ A′ ⊑ B′ →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p) →
  LeftCatchupIndexedResult
    {N = M} {V′ = V′ ⟨ c ⟩} {ρ = ρ⁺} q
left-catchup-indexed-prefix-target-widen-castᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c}
    prefix mode seal★ c⊑
    catchup@(left-indexed-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      inner-transport inner-coherence) =
  left-catchup-indexed-target-frameᵀ
    catchup framed refl (left-silent-invariant refl refl)
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation inner-transport)
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation inner-coherence)
  where
  inner = weakIndexedResult indexed

  seal★⁺ = seal★-weaken
    (rightStoreⁱ-prefix-inclusion prefix) seal★

  c⊑⁺ = widen-weaken ≤-refl
    (rightStoreⁱ-prefix-inclusion prefix) c⊑

  final-seal =
    subst (SealModeStore★ _)
      (sym (targetStoreResult inner)) seal★⁺

  final-cast =
    subst
      (λ Δ → _ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ c ∶ A′ ⊑ B′)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → _ ∣ Δᴿ ∣ Σ ⊢ c ∶ A′ ⊑ B′)
        (sym (targetStoreResult inner)) c⊑⁺)

  final-relation =
    ⊑cast⊑ᵀ mode final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner _)

  first = weak-one-step-target-cast-frameᵀ
    inner final-relation

  framed = weak-indexed-result first (relatedResults first)

left-catchup-indexed-prefix-target-widen-id-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B′ c}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ₀) →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ c ∶ A′ ⊑ B′ →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p) →
  LeftCatchupIndexedResult
    {N = M} {V′ = V′ ⟨ c ⟩} {ρ = ρ⁺} q
left-catchup-indexed-prefix-target-widen-id-castᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c}
    prefix seal★ c⊑
    catchup@(left-indexed-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      inner-transport inner-coherence) =
  left-catchup-indexed-target-frameᵀ
    catchup framed refl (left-silent-invariant refl refl)
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation inner-transport)
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation inner-coherence)
  where
  inner = weakIndexedResult indexed

  seal★⁺ = seal★-weaken {μ = id-onlyᵈ}
    (rightStoreⁱ-prefix-inclusion prefix) seal★

  c⊑⁺ = widen-weaken ≤-refl
    (rightStoreⁱ-prefix-inclusion prefix) c⊑

  final-seal =
    subst (SealModeStore★ id-onlyᵈ)
      (sym (targetStoreResult inner)) seal★⁺

  final-cast =
    subst
      (λ Δ → id-onlyᵈ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ c ∶ A′ ⊑ B′)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → id-onlyᵈ ∣ Δᴿ ∣ Σ ⊢ c ∶ A′ ⊑ B′)
        (sym (targetStoreResult inner)) c⊑⁺)

  final-relation =
    ⊑cast⊑idᵀ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner _)

  first = weak-one-step-target-cast-frameᵀ
    inner final-relation

  framed = weak-indexed-result first (relatedResults first)

------------------------------------------------------------------------
-- Active arbitrary-type value catch-up worker
------------------------------------------------------------------------

left-catchup-indexed-prefix-valueᵀ :
  ∀ {Φ Δᴸ Δᴿ V V′ A B}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  RuntimeOK V →
  Value V →
  No• V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ A ⊑ B ∶ p →
  LeftCatchupIndexedResult
    {N = V} {V′ = V′} {ρ = ρ⁺} p
left-catchup-indexed-prefix-valueᵀ
    prefix okV vV noV′ V⊑V′ =
  left-catchup-indexed-prefix-relatedᵀ
    prefix (inj₁ (vV , runtime-value-no• okV vV))
    V⊑V′ V⊢ V′⊢
  where
  V⊢ = term-weaken ≤-refl
    (leftStoreⁱ-prefix-inclusion prefix)
    (runtime-value-no• okV vV)
    (nu-term-imprecision-source-typing V⊑V′)
  V′⊢ = term-weaken ≤-refl
    (rightStoreⁱ-prefix-inclusion prefix) noV′
    (nu-term-imprecision-target-typing V⊑V′)

left-catchup-indexed-prefix-blameᵀ :
  ∀ {Φ Δᴸ Δᴿ V′ A B}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  No• V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ blame ⊑ V′ ⦂ A ⊑ B ∶ p →
  LeftCatchupIndexedResult
    {N = blame} {V′ = V′} {ρ = ρ⁺} p
left-catchup-indexed-prefix-blameᵀ prefix noV′ blame⊑V′ =
  left-catchup-indexed-prefix-relatedᵀ
    prefix (inj₂ refl) blame⊑V′ blame⊢ V′⊢
  where
  blame⊢ = term-weaken ≤-refl
    (leftStoreⁱ-prefix-inclusion prefix) no•-blame
    (nu-term-imprecision-source-typing blame⊑V′)
  V′⊢ = term-weaken ≤-refl
    (rightStoreⁱ-prefix-inclusion prefix) noV′
    (nu-term-imprecision-target-typing blame⊑V′)

weak-one-step-paired-double-cast-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ A A′ d d′ u u′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (inner : WeakOneStepResult ρ M M′ C C′ keep) →
  LeftSilentInvariant inner →
  (resultCtx inner
    ∣ resultLeftCtx inner
    ∣ resultRightCtx inner
    ∣ resultStore inner ∣ []
    ⊢ᴺ ((sourceResult inner ⟨
          applyCoercions (sourceChanges inner) d ⟩) ⟨
        applyCoercions (sourceChanges inner) u ⟩)
      ⊑ ((targetResult inner ⟨ d′ ⟩) ⟨ u′ ⟩)
    ⦂ applyTys (sourceChanges inner) A ⊑
        applyTys (targetTailChanges inner) (applyTy keep A′)
    ∶ transportType inner pA) →
  WeakOneStepResult ρ
    ((M ⟨ d ⟩) ⟨ u ⟩) ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩)
    A A′ keep
weak-one-step-paired-double-cast-frameᵀ
    {A = A} {A′ = A′}
    {d = d} {d′ = d′} {u = u} {u′ = u′}
    inner (left-silent-invariant refl refl) final =
  record
    { sourceChanges = sourceChanges inner
    ; targetTailChanges = []
    ; sourceResult = (sourceResult inner ⟨
        applyCoercions (sourceChanges inner) d ⟩) ⟨
          applyCoercions (sourceChanges inner) u ⟩
    ; targetResult = (targetResult inner ⟨ d′ ⟩) ⟨ u′ ⟩
    ; resultCtx = resultCtx inner
    ; resultLeftCtx = resultLeftCtx inner
    ; resultRightCtx = resultRightCtx inner
    ; sourceCtxResult = sourceCtxResult inner
    ; targetCtxResult = targetCtxResult inner
    ; resultStore = resultStore inner
    ; resultSourceType = applyTys (sourceChanges inner) A
    ; resultTargetType = A′
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = transportType inner
    ; transportAllBody = transportAllBody inner
    ; transportRightBody = transportRightBody inner
    ; resultType = transportType inner _
    ; sourceCatchup = cast-↠ (cast-↠ (sourceCatchup inner))
    ; targetTail = cast-↠ (cast-↠ (targetTail inner))
    ; sourceStoreResult = sourceStoreResult inner
    ; targetStoreResult = targetStoreResult inner
    ; relatedResults = final
    }

left-catchup-final-runtime :
  ∀ {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {result : WeakOneStepResult ρ M V′ A B keep} →
  LeftCatchupInvariant result →
  RuntimeOK (sourceResult result)
left-catchup-final-runtime
    (left-catchup-invariant silent
      (inj₁ (vV , noV))) =
  ok-no noV
left-catchup-final-runtime
    (left-catchup-invariant silent (inj₂ refl)) =
  ok-no no•-blame

weak-one-step-transport-source-fixed-narrowingᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ D μ d}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  ModeRename suc μ μ →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ d ∶ C ⊒ D →
  μ ∣ resultLeftCtx inner ∣ leftStoreⁱ (resultStore inner)
    ⊢ applyCoercions (sourceChanges inner) d
      ∶ applyTys (sourceChanges inner) C
      ⊒ applyTys (sourceChanges inner) D
weak-one-step-transport-source-fixed-narrowingᵀ
    {Δᴸ = Δᴸ} mode-suc prefix inner d⊒ =
  subst
    (λ Δ → _ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) _
        ∶ applyTys (sourceChanges inner) _
        ⊒ applyTys (sourceChanges inner) _)
    (sym (sourceCtxResult inner))
    (subst
      (λ Σ → _ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
        ⊢ applyCoercions (sourceChanges inner) _
          ∶ applyTys (sourceChanges inner) _
          ⊒ applyTys (sourceChanges inner) _)
      (sym (sourceStoreResult inner))
      (apply-fixed-narrows-typing mode-suc
        (narrow-weaken ≤-refl
          (leftStoreⁱ-prefix-inclusion prefix) d⊒)))

weak-one-step-transport-target-narrowing-silentᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ D′ μ d′}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  LeftSilentInvariant inner →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ d′ ∶ C′ ⊒ D′ →
  μ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
    ⊢ d′ ∶ C′ ⊒ D′
weak-one-step-transport-target-narrowing-silentᵀ
    {Δᴿ = Δᴿ} prefix inner
    (left-silent-invariant refl refl) d′⊒ =
  subst
    (λ Δ → _ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
      ⊢ _ ∶ _ ⊒ _)
    (sym (targetCtxResult inner))
    (subst
      (λ Σ → _ ∣ Δᴿ ∣ Σ ⊢ _ ∶ _ ⊒ _)
      (sym (targetStoreResult inner))
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) d′⊒))

weak-one-step-transport-id-downᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ D D′ d d′}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  (indexed : WeakOneStepIndexedResult
    {M = M} {N′ = M′} {χ = keep} {ρ = ρ⁺} pC) →
  let inner = weakIndexedResult indexed in
  LeftSilentInvariant inner →
  id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ d ∶ C ⊒ D →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ d′ ∶ C′ ⊒ D′ →
  resultCtx inner
    ∣ resultLeftCtx inner
    ∣ resultRightCtx inner
    ∣ resultStore inner ∣ []
    ⊢ᴺᵖ (sourceResult inner ⟨
        applyCoercions (sourceChanges inner) d ⟩)
      ⊑ (targetResult inner ⟨ d′ ⟩)
    ⦂ applyTys (sourceChanges inner) D ⊑ᵖ
      applyTys (targetTailChanges inner) (applyTy keep D′)
    ∶ weak-one-step-transport-quotientᵀ inner qD
weak-one-step-transport-id-downᵀ
    prefix indexed (left-silent-invariant refl refl) d⊒ d′⊒ =
  down⊑downᵀ
    (weak-one-step-transport-source-fixed-narrowingᵀ
      (modeRename-id-only suc) prefix inner d⊒)
    (weak-one-step-transport-target-narrowing-silentᵀ
      prefix inner (left-silent-invariant refl refl) d′⊒)
    (canonicalIndexedResults indexed)
    (weak-one-step-transport-quotientᵀ inner _)
  where
  inner = weakIndexedResult indexed

weak-one-step-transport-gen-downᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ D D′ d d′}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  (indexed : WeakOneStepIndexedResult
    {M = M} {N′ = M′} {χ = keep} {ρ = ρ⁺} pC) →
  let inner = weakIndexedResult indexed in
  LeftSilentInvariant inner →
  genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ d ∶ C ⊒ D →
  genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ d′ ∶ C′ ⊒ D′ →
  resultCtx inner
    ∣ resultLeftCtx inner
    ∣ resultRightCtx inner
    ∣ resultStore inner ∣ []
    ⊢ᴺᵖ (sourceResult inner ⟨
        applyCoercions (sourceChanges inner) d ⟩)
      ⊑ (targetResult inner ⟨ d′ ⟩)
    ⦂ applyTys (sourceChanges inner) D ⊑ᵖ
      applyTys (targetTailChanges inner) (applyTy keep D′)
    ∶ weak-one-step-transport-quotientᵀ inner qD
weak-one-step-transport-gen-downᵀ
    prefix indexed (left-silent-invariant refl refl) d⊒ d′⊒ =
  gen-down⊑gen-downᵀ
    (weak-one-step-transport-source-fixed-narrowingᵀ
      (modeRename-gen-tag-or-id suc) prefix inner d⊒)
    (weak-one-step-transport-target-narrowing-silentᵀ
      prefix inner (left-silent-invariant refl refl) d′⊒)
    (canonicalIndexedResults indexed)
    (weak-one-step-transport-quotientᵀ inner _)
  where
  inner = weakIndexedResult indexed

weak-one-step-transport-quotient-widening-pairᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ D D′ A A′ u u′}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  LeftSilentInvariant inner →
  QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
  QuotientWideningPair
    (resultLeftCtx inner) (resultRightCtx inner) (resultStore inner)
    (applyCoercions (sourceChanges inner) u) u′
    (applyTys (sourceChanges inner) D) D′
    (applyTys (sourceChanges inner) A) A′
weak-one-step-transport-quotient-widening-pairᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {D = D} {D′ = D′} {A = A} {A′ = A′}
    prefix inner (left-silent-invariant refl refl)
    (quotient-id-widening u⊑ u′⊑) =
  quotient-id-widening source-u target-u
  where
  source-u⁺ = widen-weaken ≤-refl
    (leftStoreⁱ-prefix-inclusion prefix) u⊑

  source-u⁺⁺ = apply-fixed-widens-typing
    (modeRename-id-only suc) source-u⁺

  source-u =
    subst
      (λ Δ → id-onlyᵈ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) _
          ∶ applyTys (sourceChanges inner) D
          ⊑ applyTys (sourceChanges inner) A)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → id-onlyᵈ ∣ applyTyCtxs (sourceChanges inner) Δᴸ
          ∣ Σ ⊢ applyCoercions (sourceChanges inner) _
          ∶ applyTys (sourceChanges inner) D
          ⊑ applyTys (sourceChanges inner) A)
        (sym (sourceStoreResult inner)) source-u⁺⁺)

  target-u⁺ = widen-weaken ≤-refl
    (rightStoreⁱ-prefix-inclusion prefix) u′⊑

  target-u =
    subst
      (λ Δ → id-onlyᵈ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ _ ∶ D′ ⊑ A′)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → id-onlyᵈ ∣ Δᴿ ∣ Σ ⊢ _ ∶ D′ ⊑ A′)
        (sym (targetStoreResult inner)) target-u⁺)
weak-one-step-transport-quotient-widening-pairᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {D = D} {D′ = D′} {A = A} {A′ = A′}
    prefix inner (left-silent-invariant refl refl)
    (quotient-cast-widening
      mode seal★ u⊑ mode′ seal★′ u′⊑)
    with apply-widens-typing
      { χs = sourceChanges inner }
      mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) u⊑)
weak-one-step-transport-quotient-widening-pairᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {D = D} {D′ = D′} {A = A} {A′ = A′}
    prefix inner (left-silent-invariant refl refl)
    (quotient-cast-widening
      mode seal★ u⊑ mode′ seal★′ u′⊑)
    | μˢ , modeˢ , seal★ˢ , uˢ⊑ =
  quotient-cast-widening
    modeˢ source-seal★ source-u
    mode′ target-seal★ target-u
  where
  source-seal★ =
    subst (SealModeStore★ μˢ)
      (sym (sourceStoreResult inner)) seal★ˢ

  source-u =
    subst
      (λ Δ → μˢ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) _
          ∶ applyTys (sourceChanges inner) D
          ⊑ applyTys (sourceChanges inner) A)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → μˢ ∣ applyTyCtxs (sourceChanges inner) Δᴸ
          ∣ Σ ⊢ applyCoercions (sourceChanges inner) _
          ∶ applyTys (sourceChanges inner) D
          ⊑ applyTys (sourceChanges inner) A)
        (sym (sourceStoreResult inner)) uˢ⊑)

  target-seal★⁺ = seal★-weaken
    (rightStoreⁱ-prefix-inclusion prefix) seal★′

  target-seal★ =
    subst (SealModeStore★ _)
      (sym (targetStoreResult inner)) target-seal★⁺

  target-u⁺ = widen-weaken ≤-refl
    (rightStoreⁱ-prefix-inclusion prefix) u′⊑

  target-u =
    subst
      (λ Δ → _ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ _ ∶ D′ ⊑ A′)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → _ ∣ Δᴿ ∣ Σ ⊢ _ ∶ D′ ⊑ A′)
        (sym (targetStoreResult inner)) target-u⁺)

left-silent-indexed-prefix-down-up-from-finalᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ D D′ A A′ d d′ u u′}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = M′} {ρ = ρ⁺} pC) →
  let indexed = catchupIndexedResult catchup
      inner = weakIndexedResult indexed
  in
  (resultCtx inner
    ∣ resultLeftCtx inner
    ∣ resultRightCtx inner
    ∣ resultStore inner ∣ []
    ⊢ᴺᵖ (sourceResult inner ⟨
        applyCoercions (sourceChanges inner) d ⟩)
      ⊑ (targetResult inner ⟨ d′ ⟩)
    ⦂ applyTys (sourceChanges inner) D ⊑ᵖ
      applyTys (targetTailChanges inner) (applyTy keep D′)
    ∶ weak-one-step-transport-quotientᵀ inner qD) →
  LeftSilentIndexedResult
    {N = (M ⟨ d ⟩) ⟨ u ⟩}
    {V′ = (M′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ⁺} pA
left-silent-indexed-prefix-down-up-from-finalᵀ
    {pA = pA} prefix widening
    (left-indexed-catchup indexed
      invariant@(left-catchup-invariant
        silent@(left-silent-invariant refl refl) final)
      transport coherence)
    down =
  left-silent-indexed
    (weak-indexed-result framed final-relation)
    (left-silent-invariant refl refl)
    (ok-⟨⟩ (ok-⟨⟩ (left-catchup-final-runtime invariant)))
    (weak-step-transport (transportNo•Terms transport))
    (weak-step-type-coherence
      (transportArrowCoherent coherence)
      (transportAllCoherent coherence))
  where
  inner = weakIndexedResult indexed

  final-widening =
    weak-one-step-transport-quotient-widening-pairᵀ
      prefix inner silent widening

  final-relation =
    up⊑upᵀ down final-widening (transportType inner pA)

  framed = weak-one-step-paired-double-cast-frameᵀ
    inner silent final-relation

left-catchup-indexed-prefix-down-upᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ D D′ A A′ d d′ u u′}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  RuntimeOK ((M ⟨ d ⟩) ⟨ u ⟩) →
  Value M′ →
  No• M′ →
  Inert d′ →
  Inert u′ →
  id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ d ∶ C ⊒ D →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ d′ ∶ C′ ⊒ D′ →
  QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = M′} {ρ = ρ⁺} pC) →
  LeftCatchupIndexedResult
    {N = (M ⟨ d ⟩) ⟨ u ⟩}
    {V′ = (M′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ⁺} pA
left-catchup-indexed-prefix-down-upᵀ
    prefix okM vM′ noM′ inert-d′ inert-u′
    d⊒ d′⊒ widening
    catchup@(left-indexed-catchup indexed
      invariant@(left-catchup-invariant
        silent@(left-silent-invariant refl refl) final)
      transport coherence)
    with left-catchup-indexed-final-quotientᵀ
      vM′ noM′ inert-d′ inert-u′
      (weak-one-step-transport-id-downᵀ
        prefix indexed silent d⊒ d′⊒)
      (weak-one-step-transport-quotient-widening-pairᵀ
        prefix (weakIndexedResult indexed) silent widening)
      (transportType (weakIndexedResult indexed) _)
      (sourceIsValueOrBlame invariant)
left-catchup-indexed-prefix-down-upᵀ
    prefix okM vM′ noM′ inert-d′ inert-u′
    d⊒ d′⊒ widening
    catchup@(left-indexed-catchup indexed
      invariant@(left-catchup-invariant
        silent@(left-silent-invariant refl refl) final)
      transport coherence)
    | inj₁ second =
  left-catchup-indexed-resume-silentᵀ
    (left-silent-indexed-prefix-down-up-from-finalᵀ
      prefix widening catchup
      (weak-one-step-transport-id-downᵀ
        prefix indexed silent d⊒ d′⊒))
    second
left-catchup-indexed-prefix-down-upᵀ
    prefix okM vM′ noM′ inert-d′ inert-u′
    d⊒ d′⊒ widening
    catchup@(left-indexed-catchup indexed
      invariant@(left-catchup-invariant
        silent@(left-silent-invariant refl refl) final)
      transport coherence)
    | inj₂ (B , s , u≡inst , source↠) =
  {!!}

left-catchup-indexed-prefix-gen-down-upᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ D D′ A A′ d d′ u u′}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  RuntimeOK ((M ⟨ d ⟩) ⟨ u ⟩) →
  Value M′ →
  No• M′ →
  Inert d′ →
  Inert u′ →
  genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ d ∶ C ⊒ D →
  genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ d′ ∶ C′ ⊒ D′ →
  QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = M′} {ρ = ρ⁺} pC) →
  LeftCatchupIndexedResult
    {N = (M ⟨ d ⟩) ⟨ u ⟩}
    {V′ = (M′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ⁺} pA
left-catchup-indexed-prefix-gen-down-upᵀ
    prefix okM vM′ noM′ inert-d′ inert-u′
    d⊒ d′⊒ widening
    catchup@(left-indexed-catchup indexed
      invariant@(left-catchup-invariant
        silent@(left-silent-invariant refl refl) final)
      transport coherence)
    with left-catchup-indexed-final-quotientᵀ
      vM′ noM′ inert-d′ inert-u′
      (weak-one-step-transport-gen-downᵀ
        prefix indexed silent d⊒ d′⊒)
      (weak-one-step-transport-quotient-widening-pairᵀ
        prefix (weakIndexedResult indexed) silent widening)
      (transportType (weakIndexedResult indexed) _)
      (sourceIsValueOrBlame invariant)
left-catchup-indexed-prefix-gen-down-upᵀ
    prefix okM vM′ noM′ inert-d′ inert-u′
    d⊒ d′⊒ widening
    catchup@(left-indexed-catchup indexed
      invariant@(left-catchup-invariant
        silent@(left-silent-invariant refl refl) final)
      transport coherence)
    | inj₁ second =
  left-catchup-indexed-resume-silentᵀ
    (left-silent-indexed-prefix-down-up-from-finalᵀ
      prefix widening catchup
      (weak-one-step-transport-gen-downᵀ
        prefix indexed silent d⊒ d′⊒))
    second
left-catchup-indexed-prefix-gen-down-upᵀ
    prefix okM vM′ noM′ inert-d′ inert-u′
    d⊒ d′⊒ widening
    catchup@(left-indexed-catchup indexed
      invariant@(left-catchup-invariant
        silent@(left-silent-invariant refl refl) final)
      transport coherence)
    | inj₂ (B , s , u≡inst , source↠) =
  {!!}

left-catchup-indexed-prefixᵀ :
  ∀ {Φ Δᴸ Δᴿ N V′ A B}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  RuntimeOK N →
  Value V′ →
  No• V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ A ⊑ B ∶ p →
  LeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺} p
left-catchup-indexed-prefixᵀ
    prefix okN vV′ noV′ rel@(blame⊑ᵀ V′⊢) =
  left-catchup-indexed-prefix-blameᵀ prefix noV′ rel
left-catchup-indexed-prefixᵀ
    prefix okN (vM′ ⟨ inert-d′ ⟩ ⟨ inert-u′ ⟩)
    (no•-⟨⟩ (no•-⟨⟩ noM′))
    (up⊑upᵀ
      (down⊑downᵀ d⊒ d′⊒ M⊑M′ qD) widening pA) =
  left-catchup-indexed-prefix-down-upᵀ
    prefix okN vM′ noM′ inert-d′ inert-u′
    d⊒ d′⊒ widening inner
  where
  inner = left-catchup-indexed-prefixᵀ prefix
    (runtime-⟨⟩ (runtime-⟨⟩ okN)) vM′ noM′ M⊑M′
left-catchup-indexed-prefixᵀ
    prefix okN (vM′ ⟨ inert-d′ ⟩ ⟨ inert-u′ ⟩)
    (no•-⟨⟩ (no•-⟨⟩ noM′))
    (up⊑upᵀ
      (gen-down⊑gen-downᵀ d⊒ d′⊒ M⊑M′ qD)
      widening pA) =
  left-catchup-indexed-prefix-gen-down-upᵀ
    prefix okN vM′ noM′ inert-d′ inert-u′
    d⊒ d′⊒ widening inner
  where
  inner = left-catchup-indexed-prefixᵀ prefix
    (runtime-⟨⟩ (runtime-⟨⟩ okN)) vM′ noM′ M⊑M′
left-catchup-indexed-prefixᵀ
    prefix okN vV′ noV′
    rel@(allocation-prefixᵀ prefix₀ inner N⊢ V′⊢) =
  left-catchup-indexed-prefixᵀ
    (store-imp-prefix-transⁱ prefix₀ prefix)
    okN vV′ noV′ inner
left-catchup-indexed-prefixᵀ
    prefix okN (vV′ ⟨ inert ⟩) (no•-⟨⟩ noV′)
    (⊑cast⊒ᵀ mode seal★ c⊒ rel q) =
  left-catchup-indexed-prefix-target-narrow-castᵀ
    prefix mode seal★ c⊒
    (left-catchup-indexed-prefixᵀ
      prefix okN vV′ noV′ rel)
left-catchup-indexed-prefixᵀ
    prefix okN (vV′ ⟨ inert ⟩) (no•-⟨⟩ noV′)
    (⊑cast⊑ᵀ mode seal★ c⊑ rel q) =
  left-catchup-indexed-prefix-target-widen-castᵀ
    prefix mode seal★ c⊑
    (left-catchup-indexed-prefixᵀ
      prefix okN vV′ noV′ rel)
left-catchup-indexed-prefixᵀ
    prefix okN (vV′ ⟨ inert ⟩) (no•-⟨⟩ noV′)
    (⊑cast⊑idᵀ seal★ c⊑ rel q) =
  left-catchup-indexed-prefix-target-widen-id-castᵀ
    prefix seal★ c⊑
    (left-catchup-indexed-prefixᵀ
      prefix okN vV′ noV′ rel)
left-catchup-indexed-prefixᵀ
    prefix okN (vV′ ⟨ inert ⟩) (no•-⟨⟩ noV′)
    (⊑conv↑ᵀ c↑ rel q) =
  left-catchup-indexed-prefix-target-reveal-castᵀ
    prefix c↑
    (left-catchup-indexed-prefixᵀ
      prefix okN vV′ noV′ rel)
left-catchup-indexed-prefixᵀ
    prefix okN (vV′ ⟨ inert ⟩) (no•-⟨⟩ noV′)
    (⊑conv↓ᵀ c↓ rel q) =
  left-catchup-indexed-prefix-target-conceal-castᵀ
    prefix c↓
    (left-catchup-indexed-prefixᵀ
      prefix okN vV′ noV′ rel)
left-catchup-indexed-prefixᵀ
    prefix okN () noV′ (x⊑xᵀ x∈)
left-catchup-indexed-prefixᵀ
    prefix okN vV′ noV′ rel@(ƛ⊑ƛᵀ hA hA′ body) =
  left-catchup-indexed-prefix-valueᵀ
    prefix okN (ƛ _) noV′ rel
left-catchup-indexed-prefixᵀ
    prefix okN () noV′ (·⊑·ᵀ L⊑L′ M⊑M′)
left-catchup-indexed-prefixᵀ
    prefix okN vV′ noV′
    rel@(Λ⊑Λᵀ liftρ liftγ vV vW′ body) =
  left-catchup-indexed-prefix-valueᵀ
    prefix okN (Λ vV) noV′ rel
left-catchup-indexed-prefixᵀ
    prefix okN vV′ noV′
    rel@(Λ⊑ᵀ occ liftρ liftγ vV body) =
  left-catchup-indexed-prefix-valueᵀ
    prefix okN (Λ vV) noV′ rel
left-catchup-indexed-prefixᵀ
    prefix okN () noV′
    (α⊑αᵀ vL noL vL′ noL′ pA liftρ liftγ
      L⊑L′ L•⊢ L′•⊢)
left-catchup-indexed-prefixᵀ
    prefix okN vV′ noV′
    (α⊑ᵀ vΛ (no•-Λ noW) h⇑A liftρᵃ lift-left-ctx-[]
      (Λ⊑ᵀ occ liftρᵇ lift-left-ctx-[] vW W⊑V′) L•⊢ V′⊢) =
  left-catchup-indexed-prefix-α-Λᵀ
    vW noW noV′ h⇑A liftρᵃ liftρᵇ prefix W⊑V′
left-catchup-indexed-prefixᵀ
    prefix okN vV′ noV′
    rel@(α⊑ᵀ vL noL h⇑A liftρ liftγ L⊑V′ L•⊢ V′⊢) =
  {!!}
left-catchup-indexed-prefixᵀ
    prefix okN () noV′
    (⊑αᵀ vL′ noL′ h⇑A liftρ liftγ N⊑L′ r N⊢ L′•⊢)
left-catchup-indexed-prefixᵀ
    prefix okN () noV′
    (ν⊑νᵀ hA hA′ s↑ s′↑ pA pA⇑ liftρ liftγ N⊑N′)
left-catchup-indexed-prefixᵀ
    prefix okN vV′ noV′
    rel@(ν⊑ᵀ hA h⇑A s↑ liftρ liftγ N⊑V′) =
  {!!}
left-catchup-indexed-prefixᵀ
    prefix okN () noV′
    (⊑νᵀ hA h⇑A s↑ liftρ liftγ pC N⊑N′)
left-catchup-indexed-prefixᵀ
    prefix okN () noV′
    (νcast⊑νcastᵀ mode seal★ mode′ seal★′
      s⊑ s′⊑ liftρ liftγ N⊑N′)
left-catchup-indexed-prefixᵀ
    prefix okN vV′ noV′
    rel@(νcast⊑ᵀ mode seal★ s⊑ liftρ liftγ N⊑V′) =
  {!!}
left-catchup-indexed-prefixᵀ
    prefix okN () noV′
    (⊑νcastᵀ mode seal★ s⊑ liftρ liftγ pC N⊑N′)
left-catchup-indexed-prefixᵀ
    prefix okN vV′ noV′ rel@κ⊑κᵀ =
  left-catchup-indexed-prefix-valueᵀ
    prefix okN ($ _) noV′ rel
left-catchup-indexed-prefixᵀ
    prefix okN () noV′ (⊕⊑⊕ᵀ L⊑L′ M⊑M′)
left-catchup-indexed-prefixᵀ
    prefix okN vV′ noV′
    rel@(cast⊒⊑ᵀ mode seal★ c⊒ N⊑V′ q) =
  {!!}
left-catchup-indexed-prefixᵀ
    prefix okN vV′ noV′
    rel@(cast⊑⊑ᵀ mode seal★ c⊑ N⊑V′ q) =
  {!!}
left-catchup-indexed-prefixᵀ
    prefix okN vV′ noV′
    rel@(conv⊑convᵀ conversion N⊑V′) =
  {!!}
left-catchup-indexed-prefixᵀ
    prefix okN vV′ noV′
    rel@(conv↑⊑ᵀ c↑ N⊑V′ q) =
  {!!}
left-catchup-indexed-prefixᵀ
    prefix okN vV′ noV′
    rel@(conv↓⊑ᵀ c↓ N⊑V′ q) =
  {!!}

left-catchup-indexed-source-all-prefixᵀ :
  ∀ {Φ Δᴸ Δᴿ N V′ C B}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  RuntimeOK N →
  Value V′ →
  No• V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ B ∶ p →
  LeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺} p
left-catchup-indexed-source-all-prefixᵀ
    prefix okN vV′ noV′ N⊑V′ =
  left-catchup-indexed-prefixᵀ
    prefix okN vV′ noV′ N⊑V′

left-catchup-indexed-source-allᵀ :
  ∀ {Φ Δᴸ Δᴿ N V′ C B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B ⊣ Δᴿ} →
  RuntimeOK N →
  Value V′ →
  No• V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ B ∶ p →
  LeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ} p
left-catchup-indexed-source-allᵀ okN vV′ noV′ N⊑V′ =
  left-catchup-indexed-source-all-prefixᵀ
    prefix-reflⁱ okN vV′ noV′ N⊑V′

left-catchup-indexed-all-prefixᵀ :
  ∀ {Φ Δᴸ Δᴿ N V′ C C′}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  RuntimeOK N →
  Value V′ →
  No• V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  LeftCatchupIndexedAllResult
    {N = N} {V′ = V′} {ρ = ρ⁺} q
left-catchup-indexed-all-prefixᵀ
    prefix okN vV′ noV′ N⊑V′ =
  specialize-left-indexed-all-catchup
    (left-catchup-indexed-source-all-prefixᵀ
      prefix okN vV′ noV′ N⊑V′)

left-catchup-indexed-allᵀ :
  ∀ {Φ Δᴸ Δᴿ N V′ C C′}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
  RuntimeOK N →
  Value V′ →
  No• V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  LeftCatchupIndexedAllResult
    {N = N} {V′ = V′} {ρ = ρ} q
left-catchup-indexed-allᵀ okN vV′ noV′ N⊑V′ =
  left-catchup-indexed-all-prefixᵀ
    prefix-reflⁱ okN vV′ noV′ N⊑V′

------------------------------------------------------------------------
-- Matched allocation leaves for the one-step dispatcher
------------------------------------------------------------------------

weak-one-step-matched-ν↑-source-allᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK (ν A N s) →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  ν A′ V′ s′ —→[ bind A′ ] ((⇑ᵗᵐ V′) •) ⟨ s′ ⟩ →
  WeakOneStepIndexedOutcome
    {M = ν A N s}
    {N′ = ((⇑ᵗᵐ V′) •) ⟨ s′ ⟩}
    {A = B} {B = B′} {χ = bind A′} {ρ = ρ} pB
weak-one-step-matched-ν↑-source-allᵀ
    wfΣ′ okν s↑ s′↑ N⊑V′ (ν-step vV′ noV′) =
  weak-one-step-matched-ν↑-indexed-catchup-outcomeᵀ
    wfΣ′ s↑ s′↑ _ _ vV′ noV′
    (left-catchup-indexed-allᵀ
      (runtime-ν okν) vV′ noV′ N⊑V′)

weak-one-step-matched-νcast-source-allᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK (ν ★ N s) →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ
    ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  CastMode μ′ →
  SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ′ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  ν ★ V′ s′ —→[ bind ★ ] ((⇑ᵗᵐ V′) •) ⟨ s′ ⟩ →
  WeakOneStepIndexedOutcome
    {M = ν ★ N s}
    {N′ = ((⇑ᵗᵐ V′) •) ⟨ s′ ⟩}
    {A = B} {B = B′} {χ = bind ★} {ρ = ρ} pB
weak-one-step-matched-νcast-source-allᵀ
    wfΣ′ okν mode seal★ s⊑ mode′ seal★′ s′⊑
    N⊑V′ (ν-step vV′ noV′) =
  weak-one-step-matched-νcast-indexed-catchup-outcomeᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ _
    vV′ noV′
    (left-catchup-indexed-allᵀ
      (runtime-ν okν) vV′ noV′ N⊑V′)

------------------------------------------------------------------------
-- Active indexed one-step dispatcher
------------------------------------------------------------------------

weak-one-step-indexed-simulationᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ N′ A B χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M →
  RuntimeOK M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  M′ —→[ χ ] N′ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′ (blame⊑ᵀ M′⊢) M′→N′ =
  indexed-outcome-source-blame ↠-refl
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (ν⊑νᵀ hA hA′ s↑ s′↑ pA pA⇑
      liftρ liftγ N⊑V′)
    red@(ν-step vV′ noV′) =
  weak-one-step-matched-ν↑-source-allᵀ
    {pA = pA} wfΣ′ okM s↑ s′↑ N⊑V′ red
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (ν⊑νᵀ hA hA′ s↑ s′↑ pA pA⇑
      liftρ liftγ N⊑N′)
    (ξ-ν N′→N₁′) =
  weak-one-step-matched-ν-indexed-frame-outcomeᵀ
    s↑ s′↑ pA _ inner
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ (runtime-ν okM) (runtime-ν okM′) N⊑N′ N′→N₁′
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (ν⊑νᵀ hA hA′ s↑ s′↑ pA pA⇑
      liftρ liftγ (blame⊑ᵀ blame⊢))
    blame-ν =
  indexed-outcome-source-blame
    (↠-step blame-ν ↠-refl)
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (νcast⊑νcastᵀ mode seal★ mode′ seal★′
      s⊑ s′⊑ liftρ liftγ N⊑V′)
    red@(ν-step vV′ noV′) =
  weak-one-step-matched-νcast-source-allᵀ
    wfΣ′ okM mode seal★ s⊑ mode′ seal★′ s′⊑ N⊑V′ red
weak-one-step-indexed-simulationᵀ {χ = χ}
    wfΣ′ okM okM′
    (νcast⊑νcastᵀ mode seal★ mode′ seal★′
      s⊑ s′⊑ liftρ liftγ N⊑N′)
    (ξ-ν N′→N₁′)
    rewrite applyTy-★ χ =
  weak-one-step-matched-νcast-indexed-frame-outcomeᵀ
    mode seal★ s⊑ mode′ seal★′ s′⊑ _ inner
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ (runtime-ν okM) (runtime-ν okM′) N⊑N′ N′→N₁′
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (νcast⊑νcastᵀ mode seal★ mode′ seal★′
      s⊑ s′⊑ liftρ liftγ (blame⊑ᵀ blame⊢))
    blame-ν =
  indexed-outcome-source-blame
    (↠-step blame-ν ↠-refl)
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (ν⊑ᵀ hA h⇑A s↑ liftρ liftγ N⊑N′)
    N′→N₁′ =
  weak-one-step-source-ν-indexed-frame-outcomeᵀ
    hA s↑ _ inner
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ (runtime-ν okM) okM′ N⊑N′ N′→N₁′
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (νcast⊑ᵀ mode seal★ s⊑ liftρ liftγ N⊑N′)
    N′→N₁′ =
  weak-one-step-source-νcast-indexed-frame-outcomeᵀ
    mode seal★ s⊑ _ inner
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ (runtime-ν okM) okM′ N⊑N′ N′→N₁′
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (⊑νᵀ hA h⇑A s↑ liftρ liftγ pC N⊑V′)
    (ν-step vV′ noV′) =
  weak-one-step-right-ν↑-indexed-outcomeᵀ
    vV′ noV′ h⇑A s↑ _ pC liftρ N⊑V′
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (⊑νᵀ hA h⇑A s↑ liftρ liftγ pC N⊑N′)
    (ξ-ν N′→N₁′) =
  weak-one-step-target-ν-indexed-frame-outcomeᵀ
    hA s↑ _ pC inner
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ okM (runtime-ν okM′) N⊑N′ N′→N₁′
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (⊑νᵀ hA h⇑A s↑ liftρ liftγ pC
      (blame⊑ᵀ blame⊢))
    blame-ν =
  indexed-outcome-source-blame ↠-refl
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (⊑νcastᵀ mode seal★ s⊑ liftρ liftγ pC N⊑V′)
    (ν-step vV′ noV′) =
  weak-one-step-right-νcast-indexed-outcomeᵀ
    vV′ noV′ mode seal★ s⊑ _ pC liftρ N⊑V′
weak-one-step-indexed-simulationᵀ {χ = χ}
    wfΣ′ okM okM′
    (⊑νcastᵀ mode seal★ s⊑ liftρ liftγ pC N⊑N′)
    (ξ-ν N′→N₁′)
    rewrite applyTy-★ χ =
  weak-one-step-target-νcast-indexed-frame-outcomeᵀ
    mode seal★ s⊑ _ pC inner
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ okM (runtime-ν okM′) N⊑N′ N′→N₁′
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (⊑νcastᵀ mode seal★ s⊑ liftρ liftγ pC
      (blame⊑ᵀ blame⊢))
    blame-ν =
  indexed-outcome-source-blame ↠-refl
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (cast⊒⊑ᵀ mode seal★ c⊒ M⊑M′ q)
    M′→N′ =
  weak-one-step-source-narrow-cast-indexed-frame-outcomeᵀ
    mode seal★ c⊒ inner
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ (runtime-⟨⟩ okM) okM′ M⊑M′ M′→N′
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ q)
    M′→N′ =
  weak-one-step-source-widen-cast-indexed-frame-outcomeᵀ
    mode seal★ c⊑ inner
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ (runtime-⟨⟩ okM) okM′ M⊑M′ M′→N′
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (conv↑⊑ᵀ c↑ M⊑M′ q)
    M′→N′ =
  weak-one-step-source-reveal-conversion-indexed-frame-outcomeᵀ
    c↑ inner q
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ (runtime-⟨⟩ okM) okM′ M⊑M′ M′→N′
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (conv↓⊑ᵀ c↓ M⊑M′ q)
    M′→N′ =
  weak-one-step-source-conceal-conversion-indexed-frame-outcomeᵀ
    c↓ inner q
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ (runtime-⟨⟩ okM) okM′ M⊑M′ M′→N′
