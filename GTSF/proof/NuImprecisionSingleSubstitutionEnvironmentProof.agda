module proof.NuImprecisionSingleSubstitutionEnvironmentProof where

-- File Charter:
--   * Builds the complete single-substitution environment family by recursion
--     on the genuine binder frame.
--   * Handles the identity and ordinary-lambda frames canonically and exposes
--     paired and source-only type lifting as the only hard leaves.
--   * Contains no postulate, hole, catch-all, or permissive option.

open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)

open import ImprecisionWf using (ImpCtx)
open import NuTermImprecision using (CtxImp; StoreImp)
open import NuTerms using (Substˣ; no•-`)
open import QuotientedTermImprecision using (x⊑xᵀ)
open import Types using (S; TyCtx; Z)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionAssumptionMembershipUniquenessProof using
  ( assumption-membership-unique-matched
  ; assumption-membership-unique-source
  )
open import proof.NuImprecisionLambdaSubstitutionEnvironmentProof using
  (quotiented-lambda-substitution-environment-proofᵀ)
open import proof.NuImprecisionSingleSubstitutionEnvironmentDef using
  (QuotientedSingleSubstitutionEnvironmentᵀ)
open import proof.NuImprecisionSubstitutionEnvironmentTypeLiftDef using
  ( QuotientedSubstitutionEnvironmentLeftTypeLiftᵀ
  ; QuotientedSubstitutionEnvironmentPairedTypeLiftᵀ
  )
open import proof.NuImprecisionSubstitutionFrame using
  ( QuotientedSubstitutionFrame
  ; substitution-frame-id
  ; substitution-frame-Λ
  ; substitution-frame-Λ-left
  ; substitution-frame-ƛ
  )
open import proof.NuImprecisionTermContextShiftDef using
  (QuotientedTermContextShiftᵀ)


substitution-frame-preserves-unique :
  ∀ {Φ₀ : ImpCtx} {Δ₀ᴸ Δ₀ᴿ : TyCtx}
    {ρ₀ : StoreImp Φ₀ Δ₀ᴸ Δ₀ᴿ}
    {γ₀ δ₀ : CtxImp Φ₀ Δ₀ᴸ Δ₀ᴿ}
    {τ₀ τ₀′ : Substˣ}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {γ δ : CtxImp Φ Δᴸ Δᴿ}
    {τ τ′ : Substˣ} →
  QuotientedSubstitutionFrame ρ₀ γ₀ δ₀ τ₀ τ₀′
    ρ γ δ τ τ′ →
  AssumptionMembershipUnique Φ₀ →
  AssumptionMembershipUnique Φ
substitution-frame-preserves-unique substitution-frame-id unique = unique
substitution-frame-preserves-unique
    (substitution-frame-ƛ frame) unique =
  substitution-frame-preserves-unique frame unique
substitution-frame-preserves-unique
    (substitution-frame-Λ frame liftρ liftγ liftδ) unique =
  assumption-membership-unique-matched
    (substitution-frame-preserves-unique frame unique)
substitution-frame-preserves-unique
    (substitution-frame-Λ-left frame liftρ liftγ liftδ) unique =
  assumption-membership-unique-source
    (substitution-frame-preserves-unique frame unique)


quotiented-single-substitution-environment-proofᵀ :
  QuotientedTermContextShiftᵀ →
  QuotientedSubstitutionEnvironmentPairedTypeLiftᵀ →
  QuotientedSubstitutionEnvironmentLeftTypeLiftᵀ →
  QuotientedSingleSubstitutionEnvironmentᵀ
quotiented-single-substitution-environment-proofᵀ
    shift paired-lift left-lift unique noV noV′ argument
    substitution-frame-id =
  (λ { Z → argument; (S x∈) → x⊑xᵀ x∈ }) ,
  (λ { zero → noV; (suc x) → no•-` }) ,
  λ { zero → noV′; (suc x) → no•-` }
quotiented-single-substitution-environment-proofᵀ
    shift paired-lift left-lift unique noV noV′ argument
    (substitution-frame-ƛ frame)
    with quotiented-single-substitution-environment-proofᵀ
      shift paired-lift left-lift unique noV noV′ argument frame
quotiented-single-substitution-environment-proofᵀ
    shift paired-lift left-lift unique noV noV′ argument
    (substitution-frame-ƛ frame)
    | related , noτ , noτ′ =
  quotiented-lambda-substitution-environment-proofᵀ
    shift related noτ noτ′
quotiented-single-substitution-environment-proofᵀ
    shift paired-lift left-lift unique noV noV′ argument
    (substitution-frame-Λ frame liftρ liftγ liftδ)
    with quotiented-single-substitution-environment-proofᵀ
      shift paired-lift left-lift unique noV noV′ argument frame
quotiented-single-substitution-environment-proofᵀ
    shift paired-lift left-lift unique noV noV′ argument
    (substitution-frame-Λ frame liftρ liftγ liftδ)
    | related , noτ , noτ′ =
  paired-lift
    (substitution-frame-preserves-unique frame unique)
    liftρ liftγ liftδ related noτ noτ′
quotiented-single-substitution-environment-proofᵀ
    shift paired-lift left-lift unique noV noV′ argument
    (substitution-frame-Λ-left frame liftρ liftγ liftδ)
    with quotiented-single-substitution-environment-proofᵀ
      shift paired-lift left-lift unique noV noV′ argument frame
quotiented-single-substitution-environment-proofᵀ
    shift paired-lift left-lift unique noV noV′ argument
    (substitution-frame-Λ-left frame liftρ liftγ liftδ)
    | related , noτ , noτ′ =
  left-lift
    (substitution-frame-preserves-unique frame unique)
    liftρ liftγ liftδ related noτ noτ′
