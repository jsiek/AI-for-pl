module proof.NuImprecisionCatchupQuotientSupport where

-- File Charter:
--   * Provides strict support for quotient down-up catch-up assembly.
--   * Transports paired casts, narrowing, widening, and quotient evidence
--     through a completed silent catch-up result.
--   * Excludes the recursive down-up drivers and quotient-instantiation proof.
--   * Depends on stable simulation results, store prefixes, and transport.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([])
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import Coercions using (genᵈ; id-onlyᵈ; tag-or-idᵈ)
open import NarrowWiden using
  ( narrow-weaken
  ; widen-weaken
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using
  (applyTy; applyTyCtxs; applyTys; keep)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  (RuntimeOK; no•-blame; ok-no; ok-⟨⟩; _⟨_⟩)
open import QuotientedTermImprecision
open import TermTyping using (SealModeStore★)
open import proof.CoercionProperties using (ModeRename)
open import proof.NuImprecisionSimulationCore
open import proof.NuImprecisionSimulationResultDef
open import proof.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.ReductionProperties using
  (applyCoercions; cast-↠)
open import proof.TypePreservation using (seal★-weaken)

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
      (apply-fixed-narrows-typing
        {χs = sourceChanges inner} mode-suc
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
    {χs = sourceChanges inner}
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
