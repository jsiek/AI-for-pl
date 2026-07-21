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
  ; pure-step
  ; ξ-⟨⟩
  ; ξ-⊕₁
  ; ξ-⊕₂
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
  ; no•-⊕
  ; no•-⟨⟩
  ; no•-blame
  ; ok-no
  ; ok-⊕₁
  ; ok-⊕₂
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
open import proof.NuImprecisionSimulationResultDef
open import proof.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  ; store-imp-prefix-transⁱ
  )
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
open import proof.NuImprecisionOneStepTargetConversionFrames using
  ( weak-one-step-target-conceal-conversion-indexed-frame-outcomeᵀ
  ; weak-one-step-target-reveal-conversion-indexed-frame-outcomeᵀ
  )
open import proof.NuImprecisionOneStepTargetConversionRoots using
  ( weak-one-step-target-conceal-conversion-root-outcomeᵀ
  ; weak-one-step-target-reveal-conversion-root-outcomeᵀ
  )
open import proof.NuImprecisionOneStepTargetCastFrames using
  ( weak-one-step-target-narrow-cast-indexed-frame-outcomeᵀ
  ; weak-one-step-target-widen-cast-indexed-frame-outcomeᵀ
  ; weak-one-step-target-widen-id-cast-indexed-frame-outcomeᵀ
  )
open import proof.NuImprecisionOneStepTargetCastRoots using
  ( weak-one-step-target-narrow-cast-root-outcomeᵀ
  ; weak-one-step-target-widen-cast-root-outcomeᵀ
  ; weak-one-step-target-widen-id-cast-root-outcomeᵀ
  )
open import proof.NuImprecisionOneStepPrimitiveFrames using
  ( weak-one-step-⊕₁-indexed-frame-outcomeᵀ
  ; weak-one-step-⊕₂-indexed-frame-outcomeᵀ
  )
open import proof.NuImprecisionSimulation using
  ( left-catchup-indexed-prefix-α-Λᵀ
  ; weak-one-step-target-cast-frameᵀ
  ; weak-one-step-target-cast-frame-coherenceᵀ
  ; weak-one-step-target-cast-frame-transportᵀ
  )
open import proof.NuImprecisionCatchupPrefixSupport
open import proof.NuImprecisionCatchupQuotientSupport
open import proof.NuImprecisionQuotientWideningTransport using
  (weak-one-step-transport-quotient-widening-pairᵀ)
open import proof.ReductionProperties using
  (applyCoercions; applyTy-★; applyTys-++; cast-↠)
open import proof.NuPreservation using (runtime-ν; runtime-⟨⟩)
open import proof.NuProgress using (runtime-value-no•)
open import proof.TypePreservation using
  (seal★-weaken; term-weaken)

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
    wfΣ′ okM okM′ (x⊑xᵀ x∈) (pure-step ())
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′ (ƛ⊑ƛᵀ hA hA′ N⊑N′) (pure-step ())
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (Λ⊑Λᵀ liftρ liftγ vV vV′ V⊑V′) (pure-step ())
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′ κ⊑κᵀ (pure-step ())
weak-one-step-indexed-simulationᵀ
    wfΣ′
    (ok-no (no•-⊕ noL noM))
    (ok-no (no•-⊕ noL′ noM′))
    (⊕⊑⊕ᵀ L⊑L′ M⊑M′)
    (ξ-⊕₁ L′→L₁′ shiftM′) =
  weak-one-step-⊕₁-indexed-frame-outcomeᵀ
    noM noM′ M⊑M′ inner
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ (ok-no noL) (ok-no noL′) L⊑L′ L′→L₁′
weak-one-step-indexed-simulationᵀ
    wfΣ′
    (ok-no (no•-⊕ noL noM))
    (ok-⊕₁ okL′ noM′)
    (⊕⊑⊕ᵀ L⊑L′ M⊑M′)
    (ξ-⊕₁ L′→L₁′ shiftM′) =
  weak-one-step-⊕₁-indexed-frame-outcomeᵀ
    noM noM′ M⊑M′ inner
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ (ok-no noL) okL′ L⊑L′ L′→L₁′
weak-one-step-indexed-simulationᵀ
    wfΣ′
    (ok-⊕₁ okL noM)
    (ok-no (no•-⊕ noL′ noM′))
    (⊕⊑⊕ᵀ L⊑L′ M⊑M′)
    (ξ-⊕₁ L′→L₁′ shiftM′) =
  weak-one-step-⊕₁-indexed-frame-outcomeᵀ
    noM noM′ M⊑M′ inner
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ okL (ok-no noL′) L⊑L′ L′→L₁′
weak-one-step-indexed-simulationᵀ
    wfΣ′
    (ok-⊕₁ okL noM)
    (ok-⊕₁ okL′ noM′)
    (⊕⊑⊕ᵀ L⊑L′ M⊑M′)
    (ξ-⊕₁ L′→L₁′ shiftM′) =
  weak-one-step-⊕₁-indexed-frame-outcomeᵀ
    noM noM′ M⊑M′ inner
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ okL okL′ L⊑L′ L′→L₁′
weak-one-step-indexed-simulationᵀ
    wfΣ′
    (ok-⊕₂ vL noL okM)
    (ok-no (no•-⊕ noL′ noM′))
    (⊕⊑⊕ᵀ L⊑L′ M⊑M′)
    (ξ-⊕₂ vL′ shiftL′ M′→M₁′) =
  weak-one-step-⊕₂-indexed-frame-outcomeᵀ
    vL noL vL′ noL′ L⊑L′ inner
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ okM (ok-no noM′) M⊑M′ M′→M₁′
weak-one-step-indexed-simulationᵀ
    wfΣ′
    (ok-⊕₂ vL noL okM)
    (ok-⊕₁ okL′ noM′)
    (⊕⊑⊕ᵀ L⊑L′ M⊑M′)
    (ξ-⊕₂ vL′ shiftL′ M′→M₁′) =
  weak-one-step-⊕₂-indexed-frame-outcomeᵀ
    vL noL vL′ noL′ L⊑L′ inner
  where
  noL′ = runtime-value-no• okL′ vL′
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ okM (ok-no noM′) M⊑M′ M′→M₁′
weak-one-step-indexed-simulationᵀ
    wfΣ′
    (ok-⊕₂ vL noL okM)
    (ok-⊕₂ vL″ noL′ okM′)
    (⊕⊑⊕ᵀ L⊑L′ M⊑M′)
    (ξ-⊕₂ vL′ shiftL′ M′→M₁′) =
  weak-one-step-⊕₂-indexed-frame-outcomeᵀ
    vL noL vL′ noL′ L⊑L′ inner
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′ M⊑M′ M′→M₁′
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
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (⊑conv↑ᵀ c′↑ M⊑M′ q)
    (ξ-⟨⟩ M′→N′) =
  weak-one-step-target-reveal-conversion-indexed-frame-outcomeᵀ
    c′↑ inner q
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ okM (runtime-⟨⟩ okM′) M⊑M′ M′→N′
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (⊑conv↑ᵀ c′↑ M⊑M′ q)
    (pure-step root) =
  weak-one-step-target-reveal-conversion-root-outcomeᵀ
    wfΣ′ okM okM′ c′↑ M⊑M′ q root
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (⊑conv↓ᵀ c′↓ M⊑M′ q)
    (ξ-⟨⟩ M′→N′) =
  weak-one-step-target-conceal-conversion-indexed-frame-outcomeᵀ
    c′↓ inner q
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ okM (runtime-⟨⟩ okM′) M⊑M′ M′→N′
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (⊑conv↓ᵀ c′↓ M⊑M′ q)
    (pure-step root) =
  weak-one-step-target-conceal-conversion-root-outcomeᵀ
    wfΣ′ okM okM′ c′↓ M⊑M′ q root
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (⊑cast⊒ᵀ mode′ seal★′ c′⊒ M⊑M′ q)
    (ξ-⟨⟩ M′→N′) =
  weak-one-step-target-narrow-cast-indexed-frame-outcomeᵀ
    mode′ seal★′ c′⊒ inner q
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ okM (runtime-⟨⟩ okM′) M⊑M′ M′→N′
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (⊑cast⊒ᵀ mode′ seal★′ c′⊒ M⊑M′ q)
    (pure-step root) =
  weak-one-step-target-narrow-cast-root-outcomeᵀ
    wfΣ′ okM okM′ mode′ seal★′ c′⊒ M⊑M′ q root
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (⊑cast⊑ᵀ mode′ seal★′ c′⊑ M⊑M′ q)
    (ξ-⟨⟩ M′→N′) =
  weak-one-step-target-widen-cast-indexed-frame-outcomeᵀ
    mode′ seal★′ c′⊑ inner q
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ okM (runtime-⟨⟩ okM′) M⊑M′ M′→N′
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (⊑cast⊑ᵀ mode′ seal★′ c′⊑ M⊑M′ q)
    (pure-step root) =
  weak-one-step-target-widen-cast-root-outcomeᵀ
    wfΣ′ okM okM′ mode′ seal★′ c′⊑ M⊑M′ q root
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (⊑cast⊑idᵀ seal★′ c′⊑ M⊑M′ q)
    (ξ-⟨⟩ M′→N′) =
  weak-one-step-target-widen-id-cast-indexed-frame-outcomeᵀ
    seal★′ c′⊑ inner q
  where
  inner = weak-one-step-indexed-simulationᵀ
    wfΣ′ okM (runtime-⟨⟩ okM′) M⊑M′ M′→N′
weak-one-step-indexed-simulationᵀ
    wfΣ′ okM okM′
    (⊑cast⊑idᵀ seal★′ c′⊑ M⊑M′ q)
    (pure-step root) =
  weak-one-step-target-widen-id-cast-root-outcomeᵀ
    wfΣ′ okM okM′ seal★′ c′⊑ M⊑M′ q root
