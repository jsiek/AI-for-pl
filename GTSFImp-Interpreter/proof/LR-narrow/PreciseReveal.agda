module proof.LR-narrow.PreciseReveal where

-- File Charter:
--   * The one-sided structural reveal and conceal: when a paired slot's
--     precise variable does not occur in the precise type, the reveal
--     conversion contains no unseal, the imprecise endpoint carries no
--     conversion at all, and wrapping the precise endpoint preserves the
--     relation at the same imprecision.
--   * Needed for the `⇒⊑★` case of the paired structural reveal, where
--     the imprecise conversion degenerates to `id↑ ★`.
--   * Restricted to universal-free precise types; see
--     FUNDAMENTAL-PROPERTY-PLAN.md, Finding C.

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (n≤1+n; ≤-trans; ≤-refl; <-cmp)
open import Data.Nat.Induction using () renaming (<-wellFounded to wf)
open import Induction.WellFounded using (Acc; acc)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
open import Conversion using
  (Conv↑; Conv↓; id↑; id↓; _↦↑_; _↦↓_; replaceTy; 〖_,_↑_〗;
   makeConceal)
open import Consistency using (toRenameᵗ)
import Imprecision as I
open import Reduction
import Eval as E
open import Interpreter
open import proof.ImprecisionConsistency using
  (toRenameᵗ-injective; renameᵗ-injective)
open import proof.TypeSafety.Preservation using
  (structural-reveal-typing; structural-conceal-typing)
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.Closure using (value-imprecision-downward-to)
import proof.LR-narrow.Closure as ClosureProof
open import proof.LR-narrow.ImmediateReturn using
  (related-values-return)
open import proof.LR-narrow.KeepStepExpansion using
  (related-precise-keep-step-expand)
open import proof.LR-narrow.RevealSteps
open import proof.LR-narrow.RevealLifting using
  (PairedSlot; paired-slot; center; atom; entry-eq; mode-eq)
open import proof.LR-narrow.RevealStructural using
  (slotXᴾ; slotXᴵ; slotRᴾ; slotRᴵ; no-precise-bottom-value)
open import proof.LR-narrow.StarNoOccurrence using (replaceTy-absent)

------------------------------------------------------------------------
-- Universal-free types
------------------------------------------------------------------------

data NoUniversal {Δ : TyCtx} : Ty Δ → Set where
  nu-var : ∀ {X} → NoUniversal (＇ X)
  nu-base : ∀ {ι} → NoUniversal (‵ ι)
  nu-star : NoUniversal ★
  nu-fun : ∀ {A B} → NoUniversal A → NoUniversal B
    → NoUniversal (A ⇒ B)

renameᵗ-reflects-NoUniversal : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) (A : Ty Δ)
  → NoUniversal (renameᵗ ρ A) → NoUniversal A
renameᵗ-reflects-NoUniversal ρ (＇ X) nu = nu-var
renameᵗ-reflects-NoUniversal ρ (‵ ι) nu = nu-base
renameᵗ-reflects-NoUniversal ρ ★ nu = nu-star
renameᵗ-reflects-NoUniversal ρ (A ⇒ B) (nu-fun nuA nuB) =
  nu-fun (renameᵗ-reflects-NoUniversal ρ A nuA)
    (renameᵗ-reflects-NoUniversal ρ B nuB)
renameᵗ-reflects-NoUniversal ρ (`∀ A) ()

------------------------------------------------------------------------
-- Statements
------------------------------------------------------------------------

PreciseRevealAt : ℕ → Set₁
PreciseRevealAt k = ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W) {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → NoUniversal Bᴾ
  → slotXᴾ s ∉ᵗ Bᴾ
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k
      Vᴵ (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗)

PreciseConcealAt : ℕ → Set₁
PreciseConcealAt k = ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W) {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → NoUniversal Bᴾ
  → slotXᴾ s ∉ᵗ Bᴾ
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k
      Vᴵ (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ)

------------------------------------------------------------------------
-- Endpoint typings of a one-sided wrapper
------------------------------------------------------------------------

precise-endpoint-type : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → (related : ValueImprecision W p k Vᴵ Vᴾ)
  → ⟨ Δᴾ , preciseStore (core W) , [] ⟩ ⊢ Vᴾ ⦂ Bᴾ
precise-endpoint-type W {Bᴾ = Bᴾ} sourceᴾ related =
  subst≡ (λ A → ⟨ _ , preciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    (renameᵗ-injective (toRenameᵗ-injective (preciseEmbedding (core W)))
      (trans (preciseEmbedded endpoints) (sym sourceᴾ)))
    (precise-typed endpoints)
  where
  endpoints = ClosureProof.value-imprecision-endpoints related

precise-reveal-endpoints : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W) {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → slotXᴾ s ∉ᵗ Bᴾ
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → Value (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗)
  → TypedEndpoints W p Vᴵ (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗)
precise-reveal-endpoints W s {Bᴾ = Bᴾ} p no-occur sourceᴾ
    {Vᴾ = Vᴾ} related vᴾ =
  typed-endpoints (impreciseType endpoints) Bᴾ
    (impreciseEmbedded endpoints) sourceᴾ
    (imprecise-value endpoints) vᴾ (imprecise-typed endpoints)
    (subst≡
      (λ A → ⟨ _ , preciseStore (core W) , [] ⟩
        ⊢ Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗 ⦂ A)
      (replaceTy-absent (slotXᴾ s) (slotRᴾ s) no-occur)
      (⊢reveal (structural-reveal-typing Bᴾ (preciseBound (atom s)))
        (precise-endpoint-type W sourceᴾ related)))
  where
  endpoints = ClosureProof.value-imprecision-endpoints related

precise-conceal-endpoints : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W) {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → slotXᴾ s ∉ᵗ Bᴾ
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → Value (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ)
  → TypedEndpoints W p Vᴵ (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ)
precise-conceal-endpoints W s {Bᴾ = Bᴾ} p no-occur sourceᴾ
    {Vᴾ = Vᴾ} related vᴾ =
  typed-endpoints (impreciseType endpoints) Bᴾ
    (impreciseEmbedded endpoints) sourceᴾ
    (imprecise-value endpoints) vᴾ (imprecise-typed endpoints)
    (⊢conceal (structural-conceal-typing Bᴾ (preciseBound (atom s)))
      (subst≡
        (λ A → ⟨ _ , preciseStore (core W) , [] ⟩ ⊢ Vᴾ ⦂ A)
        (sym (replaceTy-absent (slotXᴾ s) (slotRᴾ s) no-occur))
        (precise-endpoint-type W sourceᴾ related)))
  where
  endpoints = ClosureProof.value-imprecision-endpoints related
