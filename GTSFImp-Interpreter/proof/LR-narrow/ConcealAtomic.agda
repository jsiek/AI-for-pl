module proof.LR-narrow.ConcealAtomic where

-- File Charter:
--   * Conceal compatibility at a paired semantic slot for the atomic
--     imprecision forms: both endpoints carry an identity conversion,
--     except at the slot's own variable where related payloads are sealed
--     into the canonical slot relation.
--   * Parameterized like proof.LR-narrow.RevealAtomic.

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _∸_)
open import Data.Nat.Properties using (n≤1+n; ≤-trans; ≤-refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)
open import Data.Fin.Properties using (_≟_)

open import Types
open import TyStore
open import CastTerms
open import Conversion using
  (Conv↓; unseal; seal; id↓; replaceTy; makeConceal; ⊢↓-seal)
open import Consistency using (toRenameᵗ)
import Imprecision as I
open import Reduction
import Eval as E
open import Interpreter
open import proof.ImprecisionConsistency using
  (toRenameᵗ-injective; renameᵗ-injective)
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.Closure using (value-imprecision-downward-to)
import proof.LR-narrow.Closure as ClosureProof
open import proof.LR-narrow.ImmediateReturn using
  (related-values-return)
open import proof.LR-narrow.StepExpansion using
  (related-pure-step-expand)
open import proof.LR-narrow.RevealSteps
open import proof.LR-narrow.RevealAtomic using
  (rename-base-injective; rename-star-injective;
   rename-variable-inversion; AtomicReveal; atomic-★; atomic-ι; atomic-X;
   atomic-ι★; atomic-X★)

------------------------------------------------------------------------
-- Identity conceals on both endpoints
------------------------------------------------------------------------

conceal-id-not-blame : ∀ {Δ} {V : Term Δ} (A : Ty Δ)
  → V ↓ id↓ A ≢ blame
conceal-id-not-blame A ()

related-conceal-identities : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    (Bᴾ : Ty Δᴾ) (Bᴵ : Ty Δᴵ)
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k
      (Vᴵ ↓ id↓ Bᴵ) (Vᴾ ↓ id↓ Bᴾ)
related-conceal-identities {W = W} p Bᴾ Bᴵ {k = zero} related =
  ClosureProof.computations-related-zero
related-conceal-identities {W = W} p Bᴾ Bᴵ {k = suc k} related
    with conceal-id-step-question {Σ = impreciseStore (core W)} Bᴵ
           (imprecise-value (ClosureProof.value-imprecision-endpoints
             related))
       | conceal-id-step-question {Σ = preciseStore (core W)} Bᴾ
           (precise-value (ClosureProof.value-imprecision-endpoints
             related))
related-conceal-identities {W = W} p Bᴾ Bᴵ {k = suc k} related
    | vVᴵ , stepᴵ | vVᴾ , stepᴾ =
  related-pure-step-expand (conceal-id-not-blame Bᴵ)
    (conceal-id-not-blame Bᴾ)
    (conceal-id-value-none Bᴵ vVᴵ) (conceal-id-value-none Bᴾ vVᴾ)
    (id-conceal vVᴵ) (id-conceal vVᴾ) stepᴵ stepᴾ
    (related-values-return vVᴵ vVᴾ
      (λ j j≤k → value-imprecision-downward-to
        (≤-trans j≤k (n≤1+n k)) related))

------------------------------------------------------------------------
-- At a paired slot
------------------------------------------------------------------------

module AtSlot {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) {Z : TyVar Δᶜ}
    (a : SemanticAtom (core W) Z)
    (entry-eq : semanticEntry W Z ≡ paired-entry a)
    (mode-eq : impEnv (core W) Z ≡ I.X⊑X) where

  Xᴾ = preciseVariable a
  Xᴵ = impreciseVariable a
  Rᴾ = preciseRep a
  Rᴵ = impreciseRep a

  -- Sealing related payloads at the slot's own variable produces values
  -- related at the slot.

  sealed-endpoints : ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W (rep-related a) k Vᴵ Vᴾ
    → TypedEndpoints W (I.X⊑X {X = Z})
        (Vᴵ ↓ seal Xᴵ Rᴵ) (Vᴾ ↓ seal Xᴾ Rᴾ)
  sealed-endpoints related =
    typed-endpoints (＇ Xᴵ) (＇ Xᴾ)
      (cong ＇_ (impreciseAligned a)) (cong ＇_ (preciseAligned a))
      (imprecise-value endpoints ↓ seal) (precise-value endpoints ↓ seal)
      (⊢conceal (⊢↓-seal (impreciseBound a)) Vᴵ⊢Rᴵ)
      (⊢conceal (⊢↓-seal (preciseBound a)) Vᴾ⊢Rᴾ)
    where
    endpoints = ClosureProof.value-imprecision-endpoints related

    Vᴾ⊢Rᴾ = subst≡
      (λ A → ⟨ _ , preciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
      (renameᵗ-injective (toRenameᵗ-injective (preciseEmbedding (core W)))
        (preciseEmbedded endpoints))
      (precise-typed endpoints)

    Vᴵ⊢Rᴵ = subst≡
      (λ A → ⟨ _ , impreciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
      (renameᵗ-injective
        (toRenameᵗ-injective (impreciseEmbedding (core W)))
        (impreciseEmbedded endpoints))
      (imprecise-typed endpoints)

  sealed-related : ∀ (k : ℕ) {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W (rep-related a) k Vᴵ Vᴾ
    → ValueImprecision W (I.X⊑X {X = Z}) k
        (Vᴵ ↓ seal Xᴵ Rᴵ) (Vᴾ ↓ seal Xᴾ Rᴾ)
  sealed-related zero related = sealed-endpoints {k = zero} related
  sealed-related (suc k) {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related =
    sealed-endpoints related ,
    subst≡
      (λ e → PairedAtomHolds (ValueImprecisionᵏ k W) e
        (Vᴵ ↓ seal Xᴵ Rᴵ) (Vᴾ ↓ seal Xᴾ Rᴾ))
      (sym entry-eq)
      (atom-holds Vᴵ Vᴾ refl refl
        (value-imprecision-downward-to (n≤1+n k) related))

  conceal-own-variable : ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
      (s : impEnv (core W) I.⊢ embedPrecise (core W) Rᴾ
        ⊑ embedImprecise (core W) Rᴵ)
    → ValueImprecision W s k Vᴵ Vᴾ
    → ComputationsRelated W (FutureValueRelation (I.X⊑X {X = Z})) k
        (Vᴵ ↓ seal Xᴵ Rᴵ) (Vᴾ ↓ seal Xᴾ Rᴾ)
  conceal-own-variable {k = k} s related =
    related-values-return
      (imprecise-value endpoints ↓ seal) (precise-value endpoints ↓ seal)
      (λ j j≤k → sealed-related j
        (ClosureProof.value-imprecision-reindex (rep-related a) s
          refl refl (value-imprecision-downward-to j≤k related)))
    where
    endpoints = ClosureProof.value-imprecision-endpoints related

  other-variable-not-slot : ∀ {Y : TyVar Δᴾ}
    → Xᴾ ≢ Y
    → toRenameᵗ (preciseEmbedding (core W)) Y ≢ Z
  other-variable-not-slot Xᴾ≢Y eq =
    Xᴾ≢Y (toRenameᵗ-injective (preciseEmbedding (core W))
      (trans (preciseAligned a) (sym eq)))

  -- The atomic conceal cases.  The source values are related at the
  -- replaced types; the result is related at the original types.

  conceal-atomic : ∀ {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → AtomicReveal p
    → (sourceᴾ : embedPrecise (core W) Bᴾ ≡ Aᴾ)
    → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Aᴵ)
    → {Cᴾ Cᴵ : Ty Δᶜ} (s : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
    → (targetᴾ : embedPrecise (core W) (replaceTy Xᴾ Rᴾ Bᴾ) ≡ Cᴾ)
    → (targetᴵ : embedImprecise (core W) (replaceTy Xᴵ Rᴵ Bᴵ) ≡ Cᴵ)
    → {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W s k Vᴵ Vᴾ
    → ComputationsRelated W (FutureValueRelation p) k
        (Vᴵ ↓ makeConceal Xᴵ Rᴵ Bᴵ) (Vᴾ ↓ makeConceal Xᴾ Rᴾ Bᴾ)
  conceal-atomic {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} I.★⊑★ atomic-★
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      with rename-star-injective _ sourceᴾ
         | rename-star-injective _ sourceᴵ
  conceal-atomic I.★⊑★ atomic-★ sourceᴾ sourceᴵ s targetᴾ targetᴵ
      related | refl | refl =
    ClosureProof.computations-related-reindex s I.★⊑★
      (trans (sym targetᴾ) sourceᴾ) (trans (sym targetᴵ) sourceᴵ)
      refl refl (related-conceal-identities s ★ ★ related)
  conceal-atomic {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} I.ι⊑ι atomic-ι
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      with rename-base-injective _ sourceᴾ
         | rename-base-injective _ sourceᴵ
  conceal-atomic (I.ι⊑ι {ι = ι}) atomic-ι
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | refl | refl =
    ClosureProof.computations-related-reindex s I.ι⊑ι
      (trans (sym targetᴾ) sourceᴾ) (trans (sym targetᴵ) sourceᴵ)
      refl refl (related-conceal-identities s (‵ ι) (‵ ι) related)
  conceal-atomic {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} (I.X⊑X {X = X}) atomic-X
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      with rename-variable-inversion _ sourceᴾ
         | rename-variable-inversion _ sourceᴵ
  conceal-atomic (I.X⊑X {X = X}) atomic-X
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | Y′ , refl , centerᴵ
      with Xᴾ ≟ Y
  conceal-atomic (I.X⊑X {X = X}) atomic-X
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | Y′ , refl , centerᴵ
      | yes refl
      with toRenameᵗ-injective (impreciseEmbedding (core W))
             (trans centerᴵ (trans (sym centerᴾ)
               (trans (preciseAligned a) (sym (impreciseAligned a)))))
  conceal-atomic (I.X⊑X {X = X}) atomic-X
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | Y′ , refl , centerᴵ
      | yes refl | Y′≡Xᴵ
      rewrite Y′≡Xᴵ with Xᴵ ≟ Xᴵ
  conceal-atomic (I.X⊑X {X = X}) atomic-X
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | Y′ , refl , centerᴵ
      | yes refl | Y′≡Xᴵ | no Xᴵ≢Xᴵ = ⊥-elim (Xᴵ≢Xᴵ refl)
  conceal-atomic (I.X⊑X {X = X}) atomic-X
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | Y′ , refl , centerᴵ
      | yes refl | Y′≡Xᴵ | yes refl =
    ClosureProof.computations-related-reindex
      (I.X⊑X {X = Z}) (I.X⊑X {X = X})
      (cong ＇_ (trans (sym (preciseAligned a)) centerᴾ))
      (cong ＇_ (trans (sym (preciseAligned a)) centerᴾ))
      refl refl
      (conceal-own-variable s′
        (ClosureProof.value-imprecision-reindex s′ s
          targetᴾ targetᴵ related))
    where
    s′ : impEnv (core W) I.⊢ embedPrecise (core W) Rᴾ
      ⊑ embedImprecise (core W) Rᴵ
    s′ = subst≡ (λ T → impEnv (core W) I.⊢ T ⊑ _) (sym targetᴾ)
      (subst≡ (λ T → impEnv (core W) I.⊢ _ ⊑ T) (sym targetᴵ) s)
  conceal-atomic (I.X⊑X {X = X}) atomic-X
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | Y′ , refl , centerᴵ
      | no Xᴾ≢Y
      with Xᴵ ≟ Y′
  conceal-atomic (I.X⊑X {X = X}) atomic-X
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | Y′ , refl , centerᴵ
      | no Xᴾ≢Y | yes refl =
    ⊥-elim (other-variable-not-slot Xᴾ≢Y
      (trans centerᴾ (trans (sym centerᴵ) (impreciseAligned a))))
  conceal-atomic (I.X⊑X {X = X}) atomic-X
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | Y′ , refl , centerᴵ
      | no Xᴾ≢Y | no Xᴵ≢Y′ =
    ClosureProof.computations-related-reindex s (I.X⊑X {X = X})
      (trans (sym targetᴾ) sourceᴾ) (trans (sym targetᴵ) sourceᴵ)
      refl refl
      (related-conceal-identities s (＇ Y) (＇ Y′) related)
  conceal-atomic {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} I.ι⊑★ atomic-ι★
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      with rename-base-injective _ sourceᴾ
         | rename-star-injective _ sourceᴵ
  conceal-atomic (I.ι⊑★ {ι = ι}) atomic-ι★
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | refl | refl =
    ClosureProof.computations-related-reindex s I.ι⊑★
      (trans (sym targetᴾ) sourceᴾ) (trans (sym targetᴵ) sourceᴵ)
      refl refl (related-conceal-identities s (‵ ι) ★ related)
  conceal-atomic {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} (I.X⊑★ {X = X} eq) (atomic-X★ .eq)
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      with rename-variable-inversion _ sourceᴾ
         | rename-star-injective _ sourceᴵ
  conceal-atomic (I.X⊑★ {X = X} eq) (atomic-X★ .eq)
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | refl
      with Xᴾ ≟ Y
  conceal-atomic (I.X⊑★ {X = X} eq) (atomic-X★ .eq)
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | refl | yes refl
      with trans (sym mode-eq) (trans (cong (impEnv (core W))
             (trans (sym (preciseAligned a)) centerᴾ)) eq)
  conceal-atomic (I.X⊑★ {X = X} eq) (atomic-X★ .eq)
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | refl | yes refl | ()
  conceal-atomic (I.X⊑★ {X = X} eq) (atomic-X★ .eq)
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | refl | no Xᴾ≢Y =
    ClosureProof.computations-related-reindex s (I.X⊑★ eq)
      (trans (sym targetᴾ) sourceᴾ) (trans (sym targetᴵ) sourceᴵ)
      refl refl
      (related-conceal-identities s (＇ Y) ★ related)
