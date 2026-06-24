module NuMetaTheory where

-- File Charter:
--   * Public metatheory statements for the Nu variant of GTSF.
--   * Exposes progress and preservation at the top level while keeping proof
--     scripts and helper infrastructure under `proof/`.
--   * The theorem statements are restated here explicitly; this module is not
--     a compatibility re-export of the proof modules.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Types
open import Ctx
open import Coercions
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreIncl; StoreWf)
open import NuTerms
open import NuReduction

import NuStore as NuStore
import proof.CoercionProperties as CoercionProof
import proof.NarrowWidenProperties as NarrowWidenProof
import proof.NuProgress as ProgressProof
import proof.NuPreservation as PreservationProof

progress :
  ∀ {Δ : TyCtx}{Σ : Store}{M : Term}{A : Ty} →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  ProgressProof.Progress {Δ = Δ} {Σ = Σ} M
progress = ProgressProof.progress

preservation :
  ∀ {Δ Δ′ : TyCtx}{Σ Σ′ : Store}{Γ : Ctx}{M N : Term}{A : Ty} →
  StoreWf Δ Σ →
  CtxWf Δ Γ →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ∣ M —→ Δ′ ∣ Σ′ ∣ N →
  StoreWf Δ′ Σ′ × Δ ≤ Δ′ × StoreIncl Σ Σ′ ×
  CtxWf Δ′ Γ × Δ′ ∣ Σ′ ∣ Γ ⊢ N ⦂ A
preservation wfΣ hΓ M⊢ red
    with PreservationProof.preservation wfΣ hΓ M⊢ red
preservation wfΣ hΓ M⊢ red
    | PreservationProof.preserve wfΣ′ Δ≤Δ′ incl hΓ′ N⊢ =
  wfΣ′ , Δ≤Δ′ , incl , hΓ′ , N⊢

nuStoreWf⇒det :
  ∀ {Δ Σ} →
  StoreWf Δ Σ →
  NarrowWidenProof.StoreDetWf Δ Σ
nuStoreWf⇒det wfΣ =
  record
    { at = NuStore.at wfΣ
    ; wfOlder = NuStore.wfOlder wfΣ
    ; unique = NuStore.unique wfΣ
    }

narrowing-determinedᵐ :
  ∀ {μ Δ Σ A B s t} →
  StoreWf Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊒ B →
  μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ B →
  s ≡ t
narrowing-determinedᵐ wfΣ =
  NarrowWidenProof.narrowing-determinedᵐ-det (nuStoreWf⇒det wfΣ)

widening-determinedᵐ :
  ∀ {μ Δ Σ A B s t} →
  StoreWf Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊑ B →
  μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊑ B →
  s ≡ t
widening-determinedᵐ wfΣ =
  NarrowWidenProof.widening-determinedᵐ-det (nuStoreWf⇒det wfΣ)

coercion-endpoints-unique :
  ∀ {Δ Σ c A B A′ B′} →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  Δ ∣ Σ ⊢ c ∶ A′ =⇒ B′ →
  A ≡ A′ × B ≡ B′
coercion-endpoints-unique =
  CoercionProof.coercion-endpoints-unique
