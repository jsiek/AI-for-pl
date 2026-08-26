module proof.LR-narrow.RevealAtomic where

-- File Charter:
--   * Reveal compatibility at a paired semantic slot for the atomic
--     imprecision forms: both endpoints carry an identity conversion,
--     except at the slot's own variable where a matching unseal cancels
--     the canonical seal.
--   * Parameterized by the world, the slot, and the proof that the slot
--     is the paired entry at its center in X⊑X mode.
--   * Contains the zero-index and identity-step helpers shared by the
--     structural reveal cases.

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _∸_)
open import Data.Nat.Properties using (n≤1+n; ≤-trans; ≤-refl)
open import Data.Empty using (⊥; ⊥-elim)
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
  (Conv↑; unseal; seal; id↑; replaceTy; 〖_,_↑_〗)
open import Consistency using (toRenameᵗ)
import Imprecision as I
open import Reduction
import Eval as E
open import Interpreter
open import proof.ImprecisionConsistency using (toRenameᵗ-injective)
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.Closure using (value-imprecision-downward-to)
import proof.LR-narrow.Closure as ClosureProof
open import proof.LR-narrow.ImmediateReturn using
  (related-values-return)
open import proof.LR-narrow.StepExpansion using
  (related-pure-step-expand; nonvalue-zero-timed)
open import proof.LR-narrow.RevealSteps

------------------------------------------------------------------------
-- Shape inversion of embedded endpoint types
------------------------------------------------------------------------

rename-base-injective : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) {A : Ty Δ} {ι}
  → renameᵗ ρ A ≡ ‵ ι
  → A ≡ ‵ ι
rename-base-injective ρ {A = ＇ X} ()
rename-base-injective ρ {A = ‵ ι} refl = refl
rename-base-injective ρ {A = ★} ()
rename-base-injective ρ {A = A ⇒ B} ()
rename-base-injective ρ {A = `∀ A} ()

rename-star-injective : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) {A : Ty Δ}
  → renameᵗ ρ A ≡ ★
  → A ≡ ★
rename-star-injective ρ {A = ＇ X} ()
rename-star-injective ρ {A = ‵ ι} ()
rename-star-injective ρ {A = ★} refl = refl
rename-star-injective ρ {A = A ⇒ B} ()
rename-star-injective ρ {A = `∀ A} ()

rename-variable-inversion : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) {A : Ty Δ} {X}
  → renameᵗ ρ A ≡ ＇ X
  → Σ[ Y ∈ TyVar Δ ] (A ≡ ＇ Y) × (ρ Y ≡ X)
rename-variable-inversion ρ {A = ＇ Y} refl = Y , refl , refl
rename-variable-inversion ρ {A = ‵ ι} ()
rename-variable-inversion ρ {A = ★} ()
rename-variable-inversion ρ {A = A ⇒ B} ()
rename-variable-inversion ρ {A = `∀ A} ()

------------------------------------------------------------------------
-- Computations at index zero
------------------------------------------------------------------------

-- Two non-blame non-values are vacuously related at index zero: no
-- evaluation with zero gas returns or blames.

nonvalue-computations-zero : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W}
    {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
  → Mᴵ ≢ blame
  → Mᴾ ≢ blame
  → E.value? Mᴵ ≡ nothing
  → E.value? Mᴾ ≡ nothing
  → ComputationsRelated W R zero Mᴵ Mᴾ
nonvalue-computations-zero _ _ _ _ = ClosureProof.computations-related-zero

reveal-id-not-blame : ∀ {Δ} {V : Term Δ} (A : Ty Δ)
  → V ↑ id↑ A ≢ blame
reveal-id-not-blame A ()

-- Both endpoints step through an identity reveal to the related values.

related-reveal-identities : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    (Bᴾ : Ty Δᴾ) (Bᴵ : Ty Δᴵ)
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k
      (Vᴵ ↑ id↑ Bᴵ) (Vᴾ ↑ id↑ Bᴾ)
related-reveal-identities {W = W} p Bᴾ Bᴵ {k = zero} related =
  ClosureProof.computations-related-zero
related-reveal-identities {W = W} p Bᴾ Bᴵ {k = suc k} related
    with reveal-id-step-question {Σ = impreciseStore (core W)} Bᴵ
           (imprecise-value (ClosureProof.value-imprecision-endpoints
             related))
       | reveal-id-step-question {Σ = preciseStore (core W)} Bᴾ
           (precise-value (ClosureProof.value-imprecision-endpoints
             related))
related-reveal-identities {W = W} p Bᴾ Bᴵ {k = suc k} related
    | vVᴵ , stepᴵ | vVᴾ , stepᴾ =
  related-pure-step-expand (reveal-id-not-blame Bᴵ)
    (reveal-id-not-blame Bᴾ)
    (reveal-id-value-none Bᴵ vVᴵ) (reveal-id-value-none Bᴾ vVᴾ)
    (id-reveal vVᴵ) (id-reveal vVᴾ) stepᴵ stepᴾ
    (related-values-return vVᴵ vVᴾ
      (λ j j≤k → value-imprecision-downward-to
        (≤-trans j≤k (n≤1+n k)) related))

------------------------------------------------------------------------
-- Atomic reveal at a paired slot
------------------------------------------------------------------------

data AtomicReveal {Δ} {μ : I.ImpEnv Δ} :
    ∀ {A B : Ty Δ} → μ I.⊢ A ⊑ B → Set where
  atomic-★ : AtomicReveal I.★⊑★
  atomic-ι : ∀ {ι} → AtomicReveal (I.ι⊑ι {ι = ι})
  atomic-X : ∀ {X} → AtomicReveal (I.X⊑X {X = X})
  atomic-ι★ : ∀ {ι} → AtomicReveal (I.ι⊑★ {ι = ι})
  atomic-X★ : ∀ {X} (eq : μ X ≡ I.X⊑★) → AtomicReveal (I.X⊑★ eq)

module AtSlot {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) {Z : TyVar Δᶜ}
    (a : SemanticAtom (core W) Z)
    (entry-eq : semanticEntry W Z ≡ paired-entry a)
    (mode-eq : impEnv (core W) Z ≡ I.X⊑X) where

  Xᴾ = preciseVariable a
  Xᴵ = impreciseVariable a
  Rᴾ = preciseRep a
  Rᴵ = impreciseRep a

  -- The reveal at the slot's own variable unseals the canonical seal and
  -- returns the related payloads.

  reveal-own-variable : ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
      (s : impEnv (core W) I.⊢ embedPrecise (core W) Rᴾ
        ⊑ embedImprecise (core W) Rᴵ)
    → ValueImprecision W (I.X⊑X {X = Z}) k Vᴵ Vᴾ
    → ComputationsRelated W (FutureValueRelation s) k
        (Vᴵ ↑ unseal Xᴵ Rᴵ) (Vᴾ ↑ unseal Xᴾ Rᴾ)
  reveal-own-variable {k = zero} s endpoints =
    nonvalue-computations-zero (λ ()) (λ ())
      (unseal-value-none′ (imprecise-value endpoints))
      (unseal-value-none′ (precise-value endpoints))
    where
    unseal-value-none′ : ∀ {Δ} {V : Term Δ} {X : TyVar Δ} {R : Ty Δ}
      → Value V
      → E.value? (V ↑ unseal X R) ≡ nothing
    unseal-value-none′ vV
        with proof.LR-narrow.ImmediateReturn.value-question-complete vV
    unseal-value-none′ vV | vV′ , eq rewrite eq = refl
  reveal-own-variable {k = suc k} s (endpoints , holds)
      rewrite entry-eq
      with holds
  reveal-own-variable {k = suc k} s (endpoints , holds)
      | atom-holds Uᴵ Uᴾ refl refl payloads
      with unseal-step-question {Σ = impreciseStore (core W)} Xᴵ Rᴵ
             (imprecise-value payload-endpoints)
         | unseal-step-question {Σ = preciseStore (core W)} Xᴾ Rᴾ
             (precise-value payload-endpoints)
    where
    payload-endpoints = ClosureProof.value-imprecision-endpoints payloads
  reveal-own-variable {k = suc k} s (endpoints , holds)
      | atom-holds Uᴵ Uᴾ refl refl payloads
      | vUᴵ , stepᴵ | vUᴾ , stepᴾ =
    related-pure-step-expand (λ ()) (λ ())
      (unseal-value-none Xᴵ Rᴵ vUᴵ) (unseal-value-none Xᴾ Rᴾ vUᴾ)
      (conceal-reveal vUᴵ) (conceal-reveal vUᴾ) stepᴵ stepᴾ
      (related-values-return vUᴵ vUᴾ
        (λ j j≤k → ClosureProof.value-imprecision-reindex
          s (rep-related a) refl refl
          (value-imprecision-downward-to j≤k payloads)))

  -- Variables other than the slot's own reveal by identities.

  other-variable-not-slot : ∀ {Y : TyVar Δᴾ}
    → Xᴾ ≢ Y
    → toRenameᵗ (preciseEmbedding (core W)) Y ≢ Z
  other-variable-not-slot Xᴾ≢Y eq =
    Xᴾ≢Y (toRenameᵗ-injective (preciseEmbedding (core W))
      (trans (preciseAligned a) (sym eq)))

  reveal-atomic : ∀ {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → AtomicReveal p
    → (sourceᴾ : embedPrecise (core W) Bᴾ ≡ Aᴾ)
    → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Aᴵ)
    → {Cᴾ Cᴵ : Ty Δᶜ} (s : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
    → (targetᴾ : embedPrecise (core W) (replaceTy Xᴾ Rᴾ Bᴾ) ≡ Cᴾ)
    → (targetᴵ : embedImprecise (core W) (replaceTy Xᴵ Rᴵ Bᴵ) ≡ Cᴵ)
    → {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W p k Vᴵ Vᴾ
    → ComputationsRelated W (FutureValueRelation s) k
        (Vᴵ ↑ 〖 Xᴵ , Rᴵ ↑ Bᴵ 〗) (Vᴾ ↑ 〖 Xᴾ , Rᴾ ↑ Bᴾ 〗)
  reveal-atomic {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} I.★⊑★ atomic-★
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      with rename-star-injective _ sourceᴾ
         | rename-star-injective _ sourceᴵ
  reveal-atomic I.★⊑★ atomic-★ sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | refl | refl =
    ClosureProof.computations-related-reindex I.★⊑★ s
      (trans (sym sourceᴾ) targetᴾ) (trans (sym sourceᴵ) targetᴵ)
      refl refl (related-reveal-identities I.★⊑★ ★ ★ related)
  reveal-atomic {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} I.ι⊑ι atomic-ι
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      with rename-base-injective _ sourceᴾ
         | rename-base-injective _ sourceᴵ
  reveal-atomic (I.ι⊑ι {ι = ι}) atomic-ι
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | refl | refl =
    ClosureProof.computations-related-reindex I.ι⊑ι s
      (trans (sym sourceᴾ) targetᴾ) (trans (sym sourceᴵ) targetᴵ)
      refl refl (related-reveal-identities I.ι⊑ι (‵ ι) (‵ ι) related)
  reveal-atomic {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} (I.X⊑X {X = X}) atomic-X
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      with rename-variable-inversion _ sourceᴾ
         | rename-variable-inversion _ sourceᴵ
  reveal-atomic (I.X⊑X {X = X}) atomic-X
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | Y′ , refl , centerᴵ
      with Xᴾ ≟ Y
  reveal-atomic (I.X⊑X {X = X}) atomic-X
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | Y′ , refl , centerᴵ
      | yes refl
      with toRenameᵗ-injective (impreciseEmbedding (core W))
             (trans centerᴵ (trans (sym centerᴾ)
               (trans (preciseAligned a) (sym (impreciseAligned a)))))
  reveal-atomic (I.X⊑X {X = X}) atomic-X
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | Y′ , refl , centerᴵ
      | yes refl | Y′≡Xᴵ
      rewrite Y′≡Xᴵ with Xᴵ ≟ Xᴵ
  reveal-atomic (I.X⊑X {X = X}) atomic-X
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | Y′ , refl , centerᴵ
      | yes refl | Y′≡Xᴵ | no Xᴵ≢Xᴵ = ⊥-elim (Xᴵ≢Xᴵ refl)
  reveal-atomic (I.X⊑X {X = X}) atomic-X
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | Y′ , refl , centerᴵ
      | yes refl | Y′≡Xᴵ | yes refl =
    ClosureProof.computations-related-reindex s′ s
      targetᴾ targetᴵ refl refl
      (reveal-own-variable s′
        (ClosureProof.value-imprecision-reindex
          (I.X⊑X {X = Z}) (I.X⊑X {X = X})
          (cong ＇_ (trans (sym (preciseAligned a)) centerᴾ))
          (cong ＇_ (trans (sym (preciseAligned a)) centerᴾ)) related))
    where
    s′ : impEnv (core W) I.⊢ embedPrecise (core W) Rᴾ
      ⊑ embedImprecise (core W) Rᴵ
    s′ = subst≡ (λ T → impEnv (core W) I.⊢ T ⊑ _) (sym targetᴾ)
      (subst≡ (λ T → impEnv (core W) I.⊢ _ ⊑ T) (sym targetᴵ) s)
  reveal-atomic (I.X⊑X {X = X}) atomic-X
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | Y′ , refl , centerᴵ
      | no Xᴾ≢Y
      with Xᴵ ≟ Y′
  reveal-atomic (I.X⊑X {X = X}) atomic-X
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | Y′ , refl , centerᴵ
      | no Xᴾ≢Y | yes refl =
    ⊥-elim (other-variable-not-slot Xᴾ≢Y
      (trans centerᴾ (trans (sym centerᴵ) (impreciseAligned a))))
  reveal-atomic (I.X⊑X {X = X}) atomic-X
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | Y′ , refl , centerᴵ
      | no Xᴾ≢Y | no Xᴵ≢Y′ =
    ClosureProof.computations-related-reindex (I.X⊑X {X = X}) s
      (trans (sym sourceᴾ) targetᴾ) (trans (sym sourceᴵ) targetᴵ)
      refl refl
      (related-reveal-identities (I.X⊑X {X = X}) (＇ Y) (＇ Y′) related)
  reveal-atomic {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} I.ι⊑★ atomic-ι★
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      with rename-base-injective _ sourceᴾ
         | rename-star-injective _ sourceᴵ
  reveal-atomic (I.ι⊑★ {ι = ι}) atomic-ι★
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | refl | refl =
    ClosureProof.computations-related-reindex I.ι⊑★ s
      (trans (sym sourceᴾ) targetᴾ) (trans (sym sourceᴵ) targetᴵ)
      refl refl (related-reveal-identities I.ι⊑★ (‵ ι) ★ related)
  reveal-atomic {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} (I.X⊑★ {X = X} eq) (atomic-X★ .eq)
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      with rename-variable-inversion _ sourceᴾ
         | rename-star-injective _ sourceᴵ
  reveal-atomic (I.X⊑★ {X = X} eq) (atomic-X★ .eq)
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | refl
      with Xᴾ ≟ Y
  reveal-atomic (I.X⊑★ {X = X} eq) (atomic-X★ .eq)
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | refl | yes refl
      with trans (sym mode-eq) (trans (cong (impEnv (core W))
             (trans (sym (preciseAligned a)) centerᴾ)) eq)
  reveal-atomic (I.X⊑★ {X = X} eq) (atomic-X★ .eq)
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | refl | yes refl | ()
  reveal-atomic (I.X⊑★ {X = X} eq) (atomic-X★ .eq)
      sourceᴾ sourceᴵ s targetᴾ targetᴵ related
      | Y , refl , centerᴾ | refl | no Xᴾ≢Y =
    ClosureProof.computations-related-reindex (I.X⊑★ eq) s
      (trans (sym sourceᴾ) targetᴾ) (trans (sym sourceᴵ) targetᴵ)
      refl refl
      (related-reveal-identities (I.X⊑★ eq) (＇ Y) ★ related)
