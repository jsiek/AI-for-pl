{-# OPTIONS --allow-unsolved-metas #-}

module proof.NuImprecisionOneStepTargetCastRoots where

-- File Charter:
--   * Freezes the three root-only target-cast outcomes required by the
--     indexed one-step dispatcher.
--   * Excludes ξ-⟨⟩, which is handled by the target-cast frame module.
--   * Each helper owns exhaustive inversion of its ordinary cast redex while
--     retaining the explicit result index q from the quotient constructor.
--   * Keeps one visible hole for each feasible non-blame root form; impossible
--     grammar/mode combinations and the shared target-blame case are closed.

open import Coercions using (id-onlyᵈ)
import Coercions as C
open import Data.List using ([])
open import Data.Product using (_,_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
import NarrowWiden as NW
open import NuReduction using
  ( keep
  ; _—→_
  ; β-id
  ; β-seq
  ; β-inst
  ; tag-untag-ok
  ; tag-untag-bad
  ; seal-unseal
  ; blame-⟨⟩
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using (RuntimeOK; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (CastMode; SealModeStore★)
open import proof.NuImprecisionSimulationResultDef using
  (WeakOneStepIndexedOutcome)
open import proof.NuImprecisionOneStepTargetCastIdentityRoots using
  ( weak-one-step-target-narrow-cast-identity-root-outcomeᵀ
  ; weak-one-step-target-widen-cast-identity-root-outcomeᵀ
  ; weak-one-step-target-widen-id-cast-identity-root-outcomeᵀ
  )
open import proof.NuImprecisionOneStepTargetBlameRoots using
  (weak-one-step-target-blame-indexed-outcomeᵀ)


weak-one-step-target-narrow-cast-root-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ N′ A A′ B′ c′ μ′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M →
  RuntimeOK (M′ ⟨ c′ ⟩) →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  M′ ⟨ c′ ⟩ —→ N′ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q
weak-one-step-target-narrow-cast-root-outcomeᵀ
    wf okM okCast mode seal★ narrowing relation q (β-id vV) =
  weak-one-step-target-narrow-cast-identity-root-outcomeᵀ
    narrowing relation q vV
weak-one-step-target-narrow-cast-root-outcomeᵀ
    wf okM okCast mode seal★ narrowing relation q (β-seq vV) = {!!}
weak-one-step-target-narrow-cast-root-outcomeᵀ
    wf okM okCast mode seal★ (c′⊢ , NW.cross ()) relation q
    (β-inst vV)
weak-one-step-target-narrow-cast-root-outcomeᵀ
    wf okM okCast mode seal★ narrowing relation q (tag-untag-ok vV) = {!!}
weak-one-step-target-narrow-cast-root-outcomeᵀ
    wf okM okCast mode seal★ narrowing relation q
    (tag-untag-bad vV G≢H) = {!!}
weak-one-step-target-narrow-cast-root-outcomeᵀ
    wf okM okCast mode seal★ (c′⊢ , NW.cross ()) relation q
    (seal-unseal vV)
weak-one-step-target-narrow-cast-root-outcomeᵀ
    wf okM okCast mode seal★ narrowing relation q blame-⟨⟩ =
  weak-one-step-target-blame-indexed-outcomeᵀ okM relation q


weak-one-step-target-widen-cast-root-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ N′ A A′ B′ c′ μ′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M →
  RuntimeOK (M′ ⟨ c′ ⟩) →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  M′ ⟨ c′ ⟩ —→ N′ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q
weak-one-step-target-widen-cast-root-outcomeᵀ
    wf okM okCast mode seal★ widening relation q (β-id vV) =
  weak-one-step-target-widen-cast-identity-root-outcomeᵀ
    widening relation q vV
weak-one-step-target-widen-cast-root-outcomeᵀ
    wf okM okCast mode seal★ widening relation q (β-seq vV) = {!!}
weak-one-step-target-widen-cast-root-outcomeᵀ
    wf okM okCast mode seal★ widening relation q (β-inst vV) = {!!}
weak-one-step-target-widen-cast-root-outcomeᵀ
    wf okM okCast mode seal★ (c′⊢ , NW.cross ()) relation q
    (tag-untag-ok vV)
weak-one-step-target-widen-cast-root-outcomeᵀ
    wf okM okCast mode seal★ (c′⊢ , NW.cross ()) relation q
    (tag-untag-bad vV G≢H)
weak-one-step-target-widen-cast-root-outcomeᵀ
    wf okM okCast mode seal★ widening relation q (seal-unseal vV) = {!!}
weak-one-step-target-widen-cast-root-outcomeᵀ
    wf okM okCast mode seal★ widening relation q blame-⟨⟩ =
  weak-one-step-target-blame-indexed-outcomeᵀ okM relation q


weak-one-step-target-widen-id-cast-root-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ N′ A A′ B′ c′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M →
  RuntimeOK (M′ ⟨ c′ ⟩) →
  SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  M′ ⟨ c′ ⟩ —→ N′ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q
weak-one-step-target-widen-id-cast-root-outcomeᵀ
    wf okM okCast seal★ widening relation q (β-id vV) =
  weak-one-step-target-widen-id-cast-identity-root-outcomeᵀ
    widening relation q vV
weak-one-step-target-widen-id-cast-root-outcomeᵀ
    wf okM okCast seal★ widening relation q (β-seq vV) = {!!}
weak-one-step-target-widen-id-cast-root-outcomeᵀ
    wf okM okCast seal★ widening relation q (β-inst vV) = {!!}
weak-one-step-target-widen-id-cast-root-outcomeᵀ
    wf okM okCast seal★ (c′⊢ , NW.cross ()) relation q
    (tag-untag-ok vV)
weak-one-step-target-widen-id-cast-root-outcomeᵀ
    wf okM okCast seal★ (c′⊢ , NW.cross ()) relation q
    (tag-untag-bad vV G≢H)
weak-one-step-target-widen-id-cast-root-outcomeᵀ
    wf okM okCast seal★
    (C.cast-unseal hA α∈Σ () , NW.unsealʷ α A)
    relation q (seal-unseal vV)
weak-one-step-target-widen-id-cast-root-outcomeᵀ
    wf okM okCast seal★ widening relation q blame-⟨⟩ =
  weak-one-step-target-blame-indexed-outcomeᵀ okM relation q
