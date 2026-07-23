module proof.Catchup.Core.NuImprecisionCatchupPrefixSupport where

-- File Charter:
--   * Provides strict support for composing silent catch-up results.
--   * Lifts target casts and terminal source values across store prefixes.
--   * Excludes recursive catch-up dispatch and paired double-cast reasoning.
--   * Depends on the stable simulation core and target-cast frame boundary.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _++_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
import Relation.Binary.HeterogeneousEquality as HE

open import Coercions using (id-onlyᵈ)
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using
  ( narrow-weaken
  ; widen-weaken
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using (applyTy; applyTys; keep)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Value
  ; blame
  ; no•-blame
  ; _⟨_⟩
  )
open import QuotientedTermImprecision
open import TermTyping using
  (CastMode; SealModeStore★; _∣_∣_⊢_⦂_)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.Catchup.Simulation.NuImprecisionSimulation using
  ( weak-one-step-target-cast-frameᵀ
  ; weak-one-step-target-cast-frame-coherenceᵀ
  ; weak-one-step-target-cast-frame-transportᵀ
  )
open import proof.DGG.Core.NuProgress using (runtime-value-no•)
open import proof.Core.Properties.ReductionProperties using (applyTys-++)
open import proof.Core.Properties.TypePreservation using (seal★-weaken; term-weaken)

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
      first-runtime)
    (left-indexed-catchup second-indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)) =
  left-indexed-catchup
    (weak-indexed-result combined canonical
      combined-transport combined-coherence)
    (left-catchup-invariant
      (left-silent-invariant refl refl) final)
  where
  first-raw = weakIndexedResult first-indexed

  first = weak-one-step-reindexᵀ
    first-raw refl refl (canonicalIndexedResults first-indexed)

  first-transport′ =
    weak-one-step-reindex-preserves-transportᵀ
      first-raw refl refl (canonicalIndexedResults first-indexed)
      (weakIndexedTransport first-indexed)

  first-coherence′ =
    weak-one-step-reindex-preserves-type-coherenceᵀ
      first-raw refl refl (canonicalIndexedResults first-indexed)
      (weakIndexedTypeCoherence first-indexed)

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
      first-transport′ (weakIndexedTransport second-indexed)

  combined-transport =
    weak-one-step-reindex-preserves-transportᵀ
      raw-combined refl refl canonical raw-transport

  raw-coherence =
    weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
      (left-silent first (left-silent-invariant refl refl)) second
      first-coherence′ (weakIndexedTypeCoherence second-indexed)

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
      (left-catchup-invariant inner-silent final))
    framed refl first-silent first-transport first-coherence =
  left-indexed-catchup framed
    (left-catchup-invariant first-silent final)

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
      ) =
  left-catchup-indexed-target-frameᵀ
    catchup framed refl (left-silent-invariant refl refl)
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))
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
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

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
      ) =
  left-catchup-indexed-target-frameᵀ
    catchup framed refl (left-silent-invariant refl refl)
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))
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
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

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
      ) =
  left-catchup-indexed-target-frameᵀ
    catchup framed refl (left-silent-invariant refl refl)
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))
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
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

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
      ) =
  left-catchup-indexed-target-frameᵀ
    catchup framed refl (left-silent-invariant refl refl)
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))
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
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

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
      ) =
  left-catchup-indexed-target-frameᵀ
    catchup framed refl (left-silent-invariant refl refl)
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))
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
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

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
