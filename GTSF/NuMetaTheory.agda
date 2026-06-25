module NuMetaTheory where

-- File Charter:
--   * Public metatheory statements for the Nu variant of GTSF.
--   * Exposes progress and preservation at the top level while keeping proof
--     scripts and helper infrastructure under `proof/`.
--   * The theorem statements are restated here explicitly; this module is not
--     a compatibility re-export of the proof modules.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Types
open import Ctx
open import Coercions
open import NarrowWiden
  using (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_; dualⁿ; dualʷ)
open import NuStore using (StoreWf)
open import NuTerms
open import NuReduction

import proof.CoercionProperties as CoercionProof
import proof.NarrowWidenProperties as NarrowWidenProof
import proof.NuProgress as ProgressProof
import proof.NuPreservation as PreservationProof

progress :
  ∀ {Δ : TyCtx}{Σ : Store}{M : Term}{A : Ty} →
  RuntimeOK M →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  ProgressProof.Progress {Δ = Δ} {Σ = Σ} M
progress = ProgressProof.progress

preservation :
  ∀ {Δ : TyCtx}{Σ : Store}{M N : Term}{A : Ty}
    {χ : StoreChange} →
  StoreWf Δ Σ →
  RuntimeOK M →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  M —→[ χ ] N →
  applyTyCtx χ Δ ∣ applyStore χ Σ ∣ [] ⊢ N ⦂ applyTy χ A
preservation = PreservationProof.preservation

multi-preservation :
  ∀ {Δ : TyCtx}{Σ : Store}{M N : Term}{A : Ty}
    {χs : StoreChanges} →
  StoreWf Δ Σ →
  RuntimeOK M →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  M —↠[ χs ] N →
  applyTyCtxs χs Δ ∣ applyStores χs Σ ∣ [] ⊢ N ⦂ applyTys χs A
multi-preservation = PreservationProof.multi-preservation

narrowing-determinedᵐ :
  ∀ {μ Δ Σ A B s t} →
  NarrowWidenProof.StoreDetWf Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊒ B →
  μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ B →
  s ≡ t
narrowing-determinedᵐ =
  NarrowWidenProof.narrowing-determinedᵐ

widening-determinedᵐ :
  ∀ {μ Δ Σ A B s t} →
  NarrowWidenProof.StoreDetWf Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊑ B →
  μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊑ B →
  s ≡ t
widening-determinedᵐ =
  NarrowWidenProof.widening-determinedᵐ

coercion-endpoints-unique :
  ∀ {Δ Σ c A B A′ B′} →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  Δ ∣ Σ ⊢ c ∶ A′ =⇒ B′ →
  A ≡ A′ × B ≡ B′
coercion-endpoints-unique =
  CoercionProof.coercion-endpoints-unique
