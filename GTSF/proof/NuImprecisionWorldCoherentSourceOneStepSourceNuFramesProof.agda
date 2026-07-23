module
  proof.NuImprecisionWorldCoherentSourceOneStepSourceNuFramesProof
  where

-- File Charter:
--   * Implements matched and source-only ordinary/casted source-ν framing for
--     completed source steps.
--   * Prefix-weakens reveal, seal, and widening evidence to the completed
--     relational store, then delegates to the weak source-ν frame helpers.
--   * Preserves store lineage, exact source changes/results, final world
--     coherence, and source-name exclusivity.
--   * Contains no outcome wrapper, result alias, compatibility shim, hole,
--     postulate, permissive option, or incomplete match.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; instᵈ)
open import Conversion using (RevealConversion; weaken-reveal-conversion)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  ; ⇑ᵢ
  )
open import NarrowWiden using (widen-weaken; _∣_∣_⊢_∶_⊑_)
open import NuReduction using
  ( StoreChange
  ; applyCoercionUnderTyBinder
  ; applyTy
  ; applyTys
  ; keep
  )
open import NuStore using (StoreIncl-cons)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (Term; ν)
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; WfTy; ★; `∀; ⇑ᵗ; ⟰ᵗ)
open import proof.NuImprecisionSimulationCore using
  ( weak-indexed-all-resultᵀ
  ; weak-one-step-matched-ν-frameᵀ
  ; weak-one-step-matched-ν-frame-preserves-transportᵀ
  ; weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ
  ; weak-one-step-matched-νcast-frameᵀ
  ; weak-one-step-matched-νcast-frame-preserves-transportᵀ
  ; weak-one-step-matched-νcast-frame-preserves-type-coherenceᵀ
  ; weak-one-step-source-ν-frameᵀ
  ; weak-one-step-source-ν-frame-preserves-transportᵀ
  ; weak-one-step-source-ν-frame-preserves-type-coherenceᵀ
  ; weak-one-step-source-νcast-frameᵀ
  ; weak-one-step-source-νcast-frame-preserves-transportᵀ
  ; weak-one-step-source-νcast-frame-preserves-type-coherenceᵀ
  )
open import proof.NuImprecisionSimulationResultDef using
  ( WeakOneStepAllResult
  ; WeakOneStepResult
  ; relatedResults
  ; sourceChanges
  ; sourceResult
  ; weak-indexed-result
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  ( WorldCoherentSourceOneStepIndexedResult
  ; sourceStepChangesExact
  ; sourceStepIndexedResult
  ; sourceStepResultExact
  ; sourceStepSourceNameExclusive
  ; sourceStepAssumptionMembershipUnique
  ; sourceStepStoreLineage
  ; sourceStepWorldCoherent
  ; world-coherent-source-one-step-indexed
  )
open import
  proof.NuImprecisionWorldCoherentSourceOneStepSourceNuFramesDef
  using
  ( WorldCoherentSourceOneStepSourceNuFrames
  ; sourceStepMatchedNuCastFrame
  ; sourceStepMatchedNuFrame
  ; sourceStepSourceNuCastFrame
  ; sourceStepSourceNuFrame
  )
open import proof.ReductionProperties using
  ( applyCoercionUnderTyBinders
  ; applyTy-★
  )
open import proof.StoreProperties using (renameStoreᵗ-incl)
open import proof.TypePreservation using (seal★-weaken)


source-step-matched-ν-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N N′ L : Term} {A A′ B B′ C C′ : Ty}
    {s s′ : Coercion} {μ μ′} {χ : StoreChange}
    {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  WorldCoherentSourceOneStepIndexedResult
    {M = N} {M′ = N′} {L = L}
    {A = `∀ C} {B = `∀ C′} {χ = χ} {ρ = ρ⁺} (∀ⁱ q) →
  WorldCoherentSourceOneStepIndexedResult
    {M = ν A N s} {M′ = ν A′ N′ s′}
    {L = ν (applyTy χ A) L (applyCoercionUnderTyBinder χ s)}
    {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} pB
source-step-matched-ν-frameᵀ
    {ρ⁺ = ρ⁺} {N = N} {N′ = N′} {A = A} {A′ = A′}
    {B = B} {B′ = B′} {C = C} {C′ = C′} {s = s}
    {s′ = s′} {χ = χ} {q = q}
    {pA = pA} {pB = pB} prefix s↑ s′↑ complete =
  world-coherent-source-one-step-indexed
    framed-indexed
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepChangesExact complete)
    framed-result-exact
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
    (sourceStepAssumptionMembershipUnique complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀

  all : WeakOneStepAllResult
    {N = N} {N₁′ = N′} {C = C} {C′ = C′}
    {χ = keep} {ρ = ρ⁺} q
  all =
    weak-indexed-all-resultᵀ {q = q} indexed₀

  source-store-incl =
    StoreIncl-cons
      (renameStoreᵗ-incl suc (leftStoreⁱ-prefix-inclusion prefix))

  target-store-incl =
    StoreIncl-cons
      (renameStoreᵗ-incl suc (rightStoreⁱ-prefix-inclusion prefix))

  s↑⁺ = weaken-reveal-conversion source-store-incl s↑
  s′↑⁺ = weaken-reveal-conversion target-store-incl s′↑

  framed : WeakOneStepResult ρ⁺
    (ν A N s)
    (ν (applyTy keep A′) N′ (applyCoercionUnderTyBinder keep s′))
    B B′ keep
  framed =
    weak-one-step-matched-ν-frameᵀ {χ = keep} {q = q}
      s↑⁺ s′↑⁺ pA pB all
  framed-indexed = weak-indexed-result framed (relatedResults framed)
    (weak-one-step-matched-ν-frame-preserves-transportᵀ
      {χ = keep} {q = q}
      s↑⁺ s′↑⁺ pA pB all (weakIndexedTransport (sourceStepIndexedResult complete)))
    (weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ
      {χ = keep} {q = q}
      s↑⁺ s′↑⁺ pA pB all (weakIndexedTypeCoherence (sourceStepIndexedResult complete)))
  framed-transport =
    weak-one-step-matched-ν-frame-preserves-transportᵀ
      {χ = keep} {q = q}
      s↑⁺ s′↑⁺ pA pB all (weakIndexedTransport (sourceStepIndexedResult complete))
  framed-coherence =
    weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ
      {χ = keep} {q = q}
      s↑⁺ s′↑⁺ pA pB all (weakIndexedTypeCoherence (sourceStepIndexedResult complete))

  type-exact :
    applyTys (sourceChanges inner) A ≡ applyTy χ A
  type-exact =
    cong (λ χs → applyTys χs A) (sourceStepChangesExact complete)

  coercion-exact :
    applyCoercionUnderTyBinders (sourceChanges inner) s ≡
      applyCoercionUnderTyBinder χ s
  coercion-exact =
    cong (λ χs → applyCoercionUnderTyBinders χs s)
      (sourceStepChangesExact complete)

  framed-result-exact =
    trans
      (cong₂ (λ A₀ s₀ → ν A₀ (sourceResult inner) s₀)
        type-exact coercion-exact)
      (cong
        (λ L₀ → ν (applyTy χ A) L₀
          (applyCoercionUnderTyBinder χ s))
        (sourceStepResultExact complete))


source-step-matched-νcast-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N N′ L : Term} {B B′ C C′ : Ty}
    {s s′ : Coercion} {μ μ′} {χ : StoreChange}
    {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ₀)) →
  instᵈ μ ∣ suc Δᴸ
    ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ₀)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  CastMode μ′ →
  SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ₀)) →
  instᵈ μ′ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ₀)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′ →
  PairedWideningCompatible
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    (suc Δᴸ) (suc Δᴿ) s s′ (⇑ᵗ B) C′ →
  WorldCoherentSourceOneStepIndexedResult
    {M = N} {M′ = N′} {L = L}
    {A = `∀ C} {B = `∀ C′} {χ = χ} {ρ = ρ⁺} (∀ⁱ q) →
  WorldCoherentSourceOneStepIndexedResult
    {M = ν ★ N s} {M′ = ν ★ N′ s′}
    {L = ν (applyTy χ ★) L (applyCoercionUnderTyBinder χ s)}
    {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} pB
source-step-matched-νcast-frameᵀ {s = s} {χ = χ} {q = q} {pB = pB}
    prefix mode seal★ s⊑ mode′ seal★′ s′⊑ compat complete =
  world-coherent-source-one-step-indexed
    framed-indexed
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepChangesExact complete)
    framed-result-exact
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
    (sourceStepAssumptionMembershipUnique complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀
  all =
    weak-indexed-all-resultᵀ {q = q} indexed₀

  source-store-incl =
    StoreIncl-cons
      (renameStoreᵗ-incl suc (leftStoreⁱ-prefix-inclusion prefix))

  target-store-incl =
    StoreIncl-cons
      (renameStoreᵗ-incl suc (rightStoreⁱ-prefix-inclusion prefix))

  seal★⁺ = seal★-weaken source-store-incl seal★
  seal★′⁺ = seal★-weaken target-store-incl seal★′
  s⊑⁺ = widen-weaken ≤-refl source-store-incl s⊑
  s′⊑⁺ = widen-weaken ≤-refl target-store-incl s′⊑

  framed =
    weak-one-step-matched-νcast-frameᵀ
      {χ = keep} {q = q}
      mode seal★⁺ s⊑⁺ mode′ seal★′⁺ s′⊑⁺ compat pB all
  framed-indexed = weak-indexed-result framed (relatedResults framed)
    (weak-one-step-matched-νcast-frame-preserves-transportᵀ
      {χ = keep} {q = q}
      mode seal★⁺ s⊑⁺ mode′ seal★′⁺ s′⊑⁺ compat pB all
      (weakIndexedTransport (sourceStepIndexedResult complete)))
    (weak-one-step-matched-νcast-frame-preserves-type-coherenceᵀ
      {χ = keep} {q = q}
      mode seal★⁺ s⊑⁺ mode′ seal★′⁺ s′⊑⁺ compat pB all
      (weakIndexedTypeCoherence (sourceStepIndexedResult complete)))
  framed-transport =
    weak-one-step-matched-νcast-frame-preserves-transportᵀ
      {χ = keep} {q = q}
      mode seal★⁺ s⊑⁺ mode′ seal★′⁺ s′⊑⁺ compat pB all
      (weakIndexedTransport (sourceStepIndexedResult complete))
  framed-coherence =
    weak-one-step-matched-νcast-frame-preserves-type-coherenceᵀ
      {χ = keep} {q = q}
      mode seal★⁺ s⊑⁺ mode′ seal★′⁺ s′⊑⁺ compat pB all
      (weakIndexedTypeCoherence (sourceStepIndexedResult complete))

  star-exact : ★ ≡ applyTy χ ★
  star-exact = sym (applyTy-★ χ)

  coercion-exact :
    applyCoercionUnderTyBinders (sourceChanges inner) s ≡
      applyCoercionUnderTyBinder χ s
  coercion-exact =
    cong (λ χs → applyCoercionUnderTyBinders χs s)
      (sourceStepChangesExact complete)

  framed-result-exact =
    trans
      (cong₂ (λ A₀ s₀ → ν A₀ (sourceResult inner) s₀)
        star-exact coercion-exact)
      (cong
        (λ L₀ → ν (applyTy χ ★) L₀
          (applyCoercionUnderTyBinder χ s))
        (sourceStepResultExact complete))


source-step-source-ν-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N N′ L : Term} {A B B′ C : Ty}
    {s : Coercion} {μ} {χ : StoreChange}
    {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WfTy Δᴸ A →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  WorldCoherentSourceOneStepIndexedResult
    {M = N} {M′ = N′} {L = L}
    {A = `∀ C} {B = B′} {χ = χ} {ρ = ρ⁺} q →
  WorldCoherentSourceOneStepIndexedResult
    {M = ν A N s} {M′ = N′}
    {L = ν (applyTy χ A) L (applyCoercionUnderTyBinder χ s)}
    {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} pB
source-step-source-ν-frameᵀ {A = A} {s = s} {χ = χ} {pB = pB}
    prefix hA s↑ complete =
  world-coherent-source-one-step-indexed
    framed-indexed
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepChangesExact complete)
    framed-result-exact
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
    (sourceStepAssumptionMembershipUnique complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀

  source-store-incl =
    StoreIncl-cons
      (renameStoreᵗ-incl suc (leftStoreⁱ-prefix-inclusion prefix))

  s↑⁺ = weaken-reveal-conversion source-store-incl s↑

  framed = weak-one-step-source-ν-frameᵀ hA s↑⁺ pB inner
  framed-indexed = weak-indexed-result framed (relatedResults framed)
    (weak-one-step-source-ν-frame-preserves-transportᵀ
      hA s↑⁺ pB inner (weakIndexedTransport (sourceStepIndexedResult complete)))
    (weak-one-step-source-ν-frame-preserves-type-coherenceᵀ
      hA s↑⁺ pB inner (weakIndexedTypeCoherence (sourceStepIndexedResult complete)))
  framed-transport =
    weak-one-step-source-ν-frame-preserves-transportᵀ
      hA s↑⁺ pB inner (weakIndexedTransport (sourceStepIndexedResult complete))
  framed-coherence =
    weak-one-step-source-ν-frame-preserves-type-coherenceᵀ
      hA s↑⁺ pB inner (weakIndexedTypeCoherence (sourceStepIndexedResult complete))

  type-exact :
    applyTys (sourceChanges inner) A ≡ applyTy χ A
  type-exact =
    cong (λ χs → applyTys χs A) (sourceStepChangesExact complete)

  coercion-exact :
    applyCoercionUnderTyBinders (sourceChanges inner) s ≡
      applyCoercionUnderTyBinder χ s
  coercion-exact =
    cong (λ χs → applyCoercionUnderTyBinders χs s)
      (sourceStepChangesExact complete)

  framed-result-exact =
    trans
      (cong₂ (λ A₀ s₀ → ν A₀ (sourceResult inner) s₀)
        type-exact coercion-exact)
      (cong
        (λ L₀ → ν (applyTy χ A) L₀
          (applyCoercionUnderTyBinder χ s))
        (sourceStepResultExact complete))


source-step-source-νcast-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N N′ L : Term} {B B′ C : Ty}
    {s : Coercion} {μ} {χ : StoreChange}
    {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ₀)) →
  instᵈ μ ∣ suc Δᴸ
    ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ₀)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  WorldCoherentSourceOneStepIndexedResult
    {M = N} {M′ = N′} {L = L}
    {A = `∀ C} {B = B′} {χ = χ} {ρ = ρ⁺} q →
  WorldCoherentSourceOneStepIndexedResult
    {M = ν ★ N s} {M′ = N′}
    {L = ν (applyTy χ ★) L (applyCoercionUnderTyBinder χ s)}
    {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} pB
source-step-source-νcast-frameᵀ {s = s} {χ = χ} {pB = pB}
    prefix mode seal★ s⊑ complete =
  world-coherent-source-one-step-indexed
    framed-indexed
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepChangesExact complete)
    framed-result-exact
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
    (sourceStepAssumptionMembershipUnique complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀

  source-store-incl =
    StoreIncl-cons
      (renameStoreᵗ-incl suc (leftStoreⁱ-prefix-inclusion prefix))

  seal★⁺ = seal★-weaken source-store-incl seal★
  s⊑⁺ = widen-weaken ≤-refl source-store-incl s⊑

  framed = weak-one-step-source-νcast-frameᵀ mode seal★⁺ s⊑⁺ pB inner
  framed-indexed = weak-indexed-result framed (relatedResults framed)
    (weak-one-step-source-νcast-frame-preserves-transportᵀ
      mode seal★⁺ s⊑⁺ pB inner (weakIndexedTransport (sourceStepIndexedResult complete)))
    (weak-one-step-source-νcast-frame-preserves-type-coherenceᵀ
      mode seal★⁺ s⊑⁺ pB inner (weakIndexedTypeCoherence (sourceStepIndexedResult complete)))
  framed-transport =
    weak-one-step-source-νcast-frame-preserves-transportᵀ
      mode seal★⁺ s⊑⁺ pB inner (weakIndexedTransport (sourceStepIndexedResult complete))
  framed-coherence =
    weak-one-step-source-νcast-frame-preserves-type-coherenceᵀ
      mode seal★⁺ s⊑⁺ pB inner (weakIndexedTypeCoherence (sourceStepIndexedResult complete))

  star-exact : ★ ≡ applyTy χ ★
  star-exact = sym (applyTy-★ χ)

  coercion-exact :
    applyCoercionUnderTyBinders (sourceChanges inner) s ≡
      applyCoercionUnderTyBinder χ s
  coercion-exact =
    cong (λ χs → applyCoercionUnderTyBinders χs s)
      (sourceStepChangesExact complete)

  framed-result-exact =
    trans
      (cong₂ (λ A₀ s₀ → ν A₀ (sourceResult inner) s₀)
        star-exact coercion-exact)
      (cong
        (λ L₀ → ν (applyTy χ ★) L₀
          (applyCoercionUnderTyBinder χ s))
        (sourceStepResultExact complete))


world-coherent-source-one-step-source-nu-frames-proofᵀ :
  WorldCoherentSourceOneStepSourceNuFrames
world-coherent-source-one-step-source-nu-frames-proofᵀ = record
  { sourceStepMatchedNuFrame =
      λ {Φ} {Δᴸ} {Δᴿ} {ρ₀} {ρ⁺}
        {N} {N′} {L} {A} {A′} {B} {B′} {C} {C′}
        {s} {s′} {μ} {μ′} {χ} {q} {pA} {pB}
        prefix s↑ s′↑ complete →
        source-step-matched-ν-frameᵀ
          {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
          {ρ₀ = ρ₀} {ρ⁺ = ρ⁺}
          {N = N} {N′ = N′} {L = L}
          {A = A} {A′ = A′} {B = B} {B′ = B′}
          {C = C} {C′ = C′}
          {s = s} {s′ = s′} {μ = μ} {μ′ = μ′}
          {χ = χ} {q = q} {pA = pA} {pB = pB}
          prefix s↑ s′↑ complete
  ; sourceStepMatchedNuCastFrame = source-step-matched-νcast-frameᵀ
  ; sourceStepSourceNuFrame = source-step-source-ν-frameᵀ
  ; sourceStepSourceNuCastFrame = source-step-source-νcast-frameᵀ
  }
