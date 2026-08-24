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

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using
  (n≤1+n; ≤-trans; ≤-refl; m≤m+n; m≤n+m)
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
open import Relation.Nullary using (yes; no)
open import Data.Fin.Properties using (_≟_)

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
  (toRenameᵗ-injective; renameᵗ-injective; ext-injective;
   fin-suc-injective)
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
open import proof.LR-narrow.StarNoOccurrence using
  (replaceTy-absent; renameᵗ-∉ᵗ; renameᵗ-reflects-∉ᵗ)
open import proof.LR-narrow.CastComposition using
  (computations-related-future-compose)
open import proof.LR-narrow.FramePhases using (Frame)
open import proof.LR-narrow.FrameComposition
open import proof.LR-narrow.RevealFrames using
  (revealFrame; concealFrame; RevealFrm; reveal-frm; ConcealFrm;
   conceal-frm)
open import proof.LR-narrow.ArgumentFrame using
  (related-application-computation)
open import proof.LR-narrow.RevealLifting using
  (slot-future; liftPreciseTerm-reveal; liftPreciseTerm-conceal)
open import proof.LR-narrow.SlotLifting using
  (slotXᴾ; slotXᴵ; slotRᴾ; slotRᴵ;
   transported-reveal-eq; transported-conceal-eq;
   lifted-reveal-precise; lifted-conceal-precise;
   liftPreciseTy-arrow; slot-precise-variable-lift)

open PreciseComposition revealFrame using () renaming
  (precise-frame-computations-related to reveal-precise-composition;
   PrecisePlugValues to RevealPrecisePlugValues)
open PreciseComposition concealFrame using () renaming
  (precise-frame-computations-related to conceal-precise-composition;
   PrecisePlugValues to ConcealPrecisePlugValues)

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

------------------------------------------------------------------------
-- Both hypotheses survive renaming and future lifting
------------------------------------------------------------------------

renameᵗ-NoUniversal : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) {A : Ty Δ}
  → NoUniversal A → NoUniversal (renameᵗ ρ A)
renameᵗ-NoUniversal ρ nu-var = nu-var
renameᵗ-NoUniversal ρ nu-base = nu-base
renameᵗ-NoUniversal ρ nu-star = nu-star
renameᵗ-NoUniversal ρ (nu-fun nuA nuB) =
  nu-fun (renameᵗ-NoUniversal ρ nuA) (renameᵗ-NoUniversal ρ nuB)

lift-NoUniversal : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {A : Ty Δᴾ}
  → NoUniversal A → NoUniversal (liftPreciseTy W≼W′ A)
lift-NoUniversal future-refl nu = nu
lift-NoUniversal (future-paired W≼W′ r) nu =
  renameᵗ-NoUniversal Fin.suc (lift-NoUniversal W≼W′ nu)
lift-NoUniversal (future-precise W≼W′ r) nu =
  renameᵗ-NoUniversal Fin.suc (lift-NoUniversal W≼W′ nu)
lift-NoUniversal (future-imprecise W≼W′) nu = lift-NoUniversal W≼W′ nu

lift-∉ᵗ : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {X : TyVar Δᴾ} {A : Ty Δᴾ}
  → X ∉ᵗ A
  → liftPreciseVariable W≼W′ X ∉ᵗ liftPreciseTy W≼W′ A
lift-∉ᵗ future-refl no-occur = no-occur
lift-∉ᵗ (future-paired W≼W′ r) no-occur =
  renameᵗ-∉ᵗ Fin.suc fin-suc-injective (lift-∉ᵗ W≼W′ no-occur)
lift-∉ᵗ (future-precise W≼W′ r) no-occur =
  renameᵗ-∉ᵗ Fin.suc fin-suc-injective (lift-∉ᵗ W≼W′ no-occur)
lift-∉ᵗ (future-imprecise W≼W′) no-occur = lift-∉ᵗ W≼W′ no-occur

------------------------------------------------------------------------
-- Type size, as the structural measure of the inner recursion
------------------------------------------------------------------------

sizeᵗ : ∀ {Δ} → Ty Δ → ℕ
sizeᵗ (＇ X) = suc zero
sizeᵗ (‵ ι) = suc zero
sizeᵗ ★ = suc zero
sizeᵗ (A ⇒ B) = suc (sizeᵗ A + sizeᵗ B)
sizeᵗ (`∀ A) = suc (sizeᵗ A)

renameᵗ-sizeᵗ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) (A : Ty Δ)
  → sizeᵗ (renameᵗ ρ A) ≡ sizeᵗ A
renameᵗ-sizeᵗ ρ (＇ X) = refl
renameᵗ-sizeᵗ ρ (‵ ι) = refl
renameᵗ-sizeᵗ ρ ★ = refl
renameᵗ-sizeᵗ ρ (A ⇒ B) =
  cong suc (cong₂ _+_ (renameᵗ-sizeᵗ ρ A) (renameᵗ-sizeᵗ ρ B))
renameᵗ-sizeᵗ ρ (`∀ A) = cong suc (renameᵗ-sizeᵗ (extᵗ ρ) A)

lift-sizeᵗ : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (A : Ty Δᴾ)
  → sizeᵗ (liftPreciseTy W≼W′ A) ≡ sizeᵗ A
lift-sizeᵗ future-refl A = refl
lift-sizeᵗ (future-paired W≼W′ r) A =
  trans (renameᵗ-sizeᵗ Fin.suc (liftPreciseTy W≼W′ A))
    (lift-sizeᵗ W≼W′ A)
lift-sizeᵗ (future-precise W≼W′ r) A =
  trans (renameᵗ-sizeᵗ Fin.suc (liftPreciseTy W≼W′ A))
    (lift-sizeᵗ W≼W′ A)
lift-sizeᵗ (future-imprecise W≼W′) A = lift-sizeᵗ W≼W′ A

size-bound-left : ∀ {a b n} → suc (a + b) ≤ suc n → a ≤ n
size-bound-left {a} {b} {n} (s≤s a+b≤n) =
  ≤-trans (m≤m+n a b) a+b≤n

size-bound-right : ∀ {a b n} → suc (a + b) ≤ suc n → b ≤ n
size-bound-right {a} {b} {n} (s≤s a+b≤n) =
  ≤-trans (m≤n+m b a) a+b≤n

------------------------------------------------------------------------
-- The two imprecision forms with a function type on the left
------------------------------------------------------------------------

data ArrowSource {Δ} {μ : I.ImpEnv Δ} {A₁ A₂ : Ty Δ} :
    ∀ {B : Ty Δ} → μ I.⊢ A₁ ⇒ A₂ ⊑ B → Set where
  arrow-arrow : ∀ {B₁ B₂} (q₁ : μ I.⊢ A₁ ⊑ B₁) (q₂ : μ I.⊢ A₂ ⊑ B₂)
    → ArrowSource (I.⇒⊑⇒ q₁ q₂)
  arrow-star : (q₁ : μ I.⊢ A₁ ⊑ ★) (q₂ : μ I.⊢ A₂ ⊑ ★)
    → ArrowSource (I.⇒⊑★ q₁ q₂)

arrow-source-view : ∀ {Δ} {μ : I.ImpEnv Δ} {A₁ A₂ B : Ty Δ}
    (p : μ I.⊢ A₁ ⇒ A₂ ⊑ B) → ArrowSource p
arrow-source-view (I.⇒⊑⇒ q₁ q₂) = arrow-arrow q₁ q₂
arrow-source-view (I.⇒⊑★ q₁ q₂) = arrow-star q₁ q₂

------------------------------------------------------------------------
-- The one-sided reveal and conceal
------------------------------------------------------------------------

-- Lexicographic recursion: the type size decreases at a function type,
-- and the index decreases when a dynamic tag is unfolded.

mutual
  reveal-go : ∀ (fuel : ℕ) (j : ℕ) {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
      (s : PairedSlot W) {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → NoUniversal Bᴾ
    → sizeᵗ Bᴾ ≤ fuel
    → slotXᴾ s ∉ᵗ Bᴾ
    → embedPrecise (core W) Bᴾ ≡ Aᴾ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W p j Vᴵ Vᴾ
    → ComputationsRelated W (FutureValueRelation p) j
        Vᴵ (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗)
  reveal-go fuel j W s p (nu-var {X = Y}) size no-occur sourceᴾ related
      with slotXᴾ s ≟ Y
  reveal-go fuel j W s p (nu-var {X = Y}) size (∉-var X≢Y) sourceᴾ
      related | yes refl = ⊥-elim (≢ᶠ→≢ X≢Y refl)
  reveal-go fuel j W s p (nu-var {X = Y}) size no-occur sourceᴾ related
      | no _ = identity-reveal W p (＇ Y) related
  reveal-go fuel j W s p (nu-base {ι = ι}) size no-occur sourceᴾ
      related = identity-reveal W p (‵ ι) related
  reveal-go fuel j W s p nu-star size no-occur sourceᴾ related =
    identity-reveal W p ★ related
  reveal-go zero j W s p (nu-fun nuA nuB) () no-occur sourceᴾ related
  reveal-go (suc fuel) j W s p (nu-fun nuA nuB) size
      (∉-fun absentA absentB) sourceᴾ related =
    related-values-return
      (imprecise-value endpoints) (precise-value endpoints ↑ fun)
      (λ i i≤j → reveal-arrow fuel i W s p nuA nuB
        (size-bound-left size) (size-bound-right size)
        absentA absentB sourceᴾ
        (value-imprecision-downward-to i≤j related))
    where
    endpoints = ClosureProof.value-imprecision-endpoints related

  conceal-go : ∀ (fuel : ℕ) (j : ℕ) {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
      (s : PairedSlot W) {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → NoUniversal Bᴾ
    → sizeᵗ Bᴾ ≤ fuel
    → slotXᴾ s ∉ᵗ Bᴾ
    → embedPrecise (core W) Bᴾ ≡ Aᴾ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W p j Vᴵ Vᴾ
    → ComputationsRelated W (FutureValueRelation p) j
        Vᴵ (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ)
  conceal-go fuel j W s p (nu-var {X = Y}) size no-occur sourceᴾ
      related with slotXᴾ s ≟ Y
  conceal-go fuel j W s p (nu-var {X = Y}) size (∉-var X≢Y) sourceᴾ
      related | yes refl = ⊥-elim (≢ᶠ→≢ X≢Y refl)
  conceal-go fuel j W s p (nu-var {X = Y}) size no-occur sourceᴾ
      related | no _ = identity-conceal W p (＇ Y) related
  conceal-go fuel j W s p (nu-base {ι = ι}) size no-occur sourceᴾ
      related = identity-conceal W p (‵ ι) related
  conceal-go fuel j W s p nu-star size no-occur sourceᴾ related =
    identity-conceal W p ★ related
  conceal-go zero j W s p (nu-fun nuA nuB) () no-occur sourceᴾ related
  conceal-go (suc fuel) j W s p (nu-fun nuA nuB) size
      (∉-fun absentA absentB) sourceᴾ related =
    related-values-return
      (imprecise-value endpoints) (precise-value endpoints ↓ fun)
      (λ i i≤j → conceal-arrow fuel i W s p nuA nuB
        (size-bound-left size) (size-bound-right size)
        absentA absentB sourceᴾ
        (value-imprecision-downward-to i≤j related))
    where
    endpoints = ClosureProof.value-imprecision-endpoints related

  -- Identity wrappers step away on the precise endpoint.

  identity-reveal : ∀ {j} {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
      {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ) (Bᴾ : Ty Δᴾ)
      {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W p j Vᴵ Vᴾ
    → ComputationsRelated W (FutureValueRelation p) j
        Vᴵ (Vᴾ ↑ id↑ Bᴾ)
  identity-reveal {j = j} W p Bᴾ related
      with reveal-id-step-question {Σ = preciseStore (core W)} Bᴾ
             (precise-value
               (ClosureProof.value-imprecision-endpoints related))
  identity-reveal {j = j} W p Bᴾ related | vVᴾ , step-eq =
    related-precise-keep-step-expand (λ ())
      (reveal-id-value-none Bᴾ vVᴾ) (pure-step (id-reveal vVᴾ)) step-eq
      (related-values-return
        (imprecise-value
          (ClosureProof.value-imprecision-endpoints related))
        vVᴾ
        (λ i i≤j → value-imprecision-downward-to i≤j related))

  identity-conceal : ∀ {j} {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
      {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ) (Bᴾ : Ty Δᴾ)
      {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W p j Vᴵ Vᴾ
    → ComputationsRelated W (FutureValueRelation p) j
        Vᴵ (Vᴾ ↓ id↓ Bᴾ)
  identity-conceal {j = j} W p Bᴾ related
      with conceal-id-step-question {Σ = preciseStore (core W)} Bᴾ
             (precise-value
               (ClosureProof.value-imprecision-endpoints related))
  identity-conceal {j = j} W p Bᴾ related | vVᴾ , step-eq =
    related-precise-keep-step-expand (λ ())
      (conceal-id-value-none Bᴾ vVᴾ) (pure-step (id-conceal vVᴾ)) step-eq
      (related-values-return
        (imprecise-value
          (ClosureProof.value-imprecision-endpoints related))
        vVᴾ
        (λ i i≤j → value-imprecision-downward-to i≤j related))

  -- Wrapping a related computation on the precise endpoint.

  precise-revealed-computations : ∀ (fuel : ℕ) (j : ℕ)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
      {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → NoUniversal Bᴾ
    → sizeᵗ Bᴾ ≤ fuel
    → slotXᴾ s ∉ᵗ Bᴾ
    → embedPrecise (core W) Bᴾ ≡ Aᴾ
    → ∀ {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
    → ComputationsRelated W (FutureValueRelation p) j Mᴵ Mᴾ
    → ComputationsRelated W (FutureValueRelation p) j
        Mᴵ (Mᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗)
  precise-revealed-computations fuel j W s {Bᴾ = Bᴾ} p nu size
      no-occur sourceᴾ {Mᴵ = Mᴵ} {Mᴾ = Mᴾ} related =
    reveal-precise-composition
      {R = FutureValueRelation p} {S = FutureValueRelation p}
      (reveal-frm 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗) j Mᴵ Mᴾ
      plug-values related
    where
    plug-values : RevealPrecisePlugValues W (FutureValueRelation p)
        (FutureValueRelation p) j
        (reveal-frm 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗)
    plug-values {W′ = W′} W≼W′ {χsᴾ = χsᴾ} {χsᴵ = χsᴵ}
        storeᴵ storeᴾ termsᴵ termsᴾ {j = i} i≤j {Vᴵ = Uᴵ} {Vᴾ = Uᴾ}
        value-related =
      computations-related-future-compose W≼W′ p
        (ClosureProof.computations-related-reindex
          (liftCenterImprecision W≼W′ p) (liftCenterImprecision W≼W′ p)
          refl refl refl
          (sym (transported-reveal-eq χsᴾ Mᴾ (slotXᴾ s) (slotRᴾ s) Bᴾ
            (trans (termsᴾ (Mᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗))
              (trans (lifted-reveal-precise s W≼W′ Mᴾ Bᴾ)
                (cong (λ M → M ↑ _) (sym (termsᴾ Mᴾ))))) Uᴾ))
          (reveal-go fuel i W′ (slot-future s W≼W′)
            (liftCenterImprecision W≼W′ p)
            (lift-NoUniversal W≼W′ nu)
            (subst≡ (_≤ fuel) (sym (lift-sizeᵗ W≼W′ Bᴾ)) size)
            (subst≡ (_∉ᵗ liftPreciseTy W≼W′ Bᴾ)
              (sym (slot-precise-variable-lift s W≼W′))
              (lift-∉ᵗ W≼W′ no-occur))
            (trans (embedPrecise-lift W≼W′ Bᴾ)
              (cong (liftCenterTy W≼W′) sourceᴾ))
            value-related))

  precise-concealed-computations : ∀ (fuel : ℕ) (j : ℕ)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
      {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → NoUniversal Bᴾ
    → sizeᵗ Bᴾ ≤ fuel
    → slotXᴾ s ∉ᵗ Bᴾ
    → embedPrecise (core W) Bᴾ ≡ Aᴾ
    → ∀ {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
    → ComputationsRelated W (FutureValueRelation p) j Mᴵ Mᴾ
    → ComputationsRelated W (FutureValueRelation p) j
        Mᴵ (Mᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ)
  precise-concealed-computations fuel j W s {Bᴾ = Bᴾ} p nu size
      no-occur sourceᴾ {Mᴵ = Mᴵ} {Mᴾ = Mᴾ} related =
    conceal-precise-composition
      {R = FutureValueRelation p} {S = FutureValueRelation p}
      (conceal-frm (makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ)) j Mᴵ Mᴾ
      plug-values related
    where
    plug-values : ConcealPrecisePlugValues W (FutureValueRelation p)
        (FutureValueRelation p) j
        (conceal-frm (makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ))
    plug-values {W′ = W′} W≼W′ {χsᴾ = χsᴾ} {χsᴵ = χsᴵ}
        storeᴵ storeᴾ termsᴵ termsᴾ {j = i} i≤j {Vᴵ = Uᴵ} {Vᴾ = Uᴾ}
        value-related =
      computations-related-future-compose W≼W′ p
        (ClosureProof.computations-related-reindex
          (liftCenterImprecision W≼W′ p) (liftCenterImprecision W≼W′ p)
          refl refl refl
          (sym (transported-conceal-eq χsᴾ Mᴾ (slotXᴾ s) (slotRᴾ s) Bᴾ
            (trans
              (termsᴾ (Mᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ))
              (trans (lifted-conceal-precise s W≼W′ Mᴾ Bᴾ)
                (cong (λ M → M ↓ _) (sym (termsᴾ Mᴾ))))) Uᴾ))
          (conceal-go fuel i W′ (slot-future s W≼W′)
            (liftCenterImprecision W≼W′ p)
            (lift-NoUniversal W≼W′ nu)
            (subst≡ (_≤ fuel) (sym (lift-sizeᵗ W≼W′ Bᴾ)) size)
            (subst≡ (_∉ᵗ liftPreciseTy W≼W′ Bᴾ)
              (sym (slot-precise-variable-lift s W≼W′))
              (lift-∉ᵗ W≼W′ no-occur))
            (trans (embedPrecise-lift W≼W′ Bᴾ)
              (cong (liftCenterTy W≼W′) sourceᴾ))
            value-related))

  -- One head of the wrapped function value: the precise endpoint
  -- redistributes the wrapper over the application.

  reveal-arrow-head : ∀ (fuel : ℕ) (m : ℕ) {Δᴾ Δᴵ Δᶜ}
      (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
      {A₀ B₀ : Ty Δᴾ} {Pᴵ Qᴵ : Ty Δᶜ}
      (q₁ : impEnv (core W) I.⊢ embedPrecise (core W) A₀ ⊑ Pᴵ)
      (q₂ : impEnv (core W) I.⊢ embedPrecise (core W) B₀ ⊑ Qᴵ)
    → NoUniversal A₀ → NoUniversal B₀
    → sizeᵗ A₀ ≤ fuel → sizeᵗ B₀ ≤ fuel
    → slotXᴾ s ∉ᵗ A₀ → slotXᴾ s ∉ᵗ B₀
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W (I.⇒⊑⇒ q₁ q₂) (suc m) Vᴵ Vᴾ
    → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′) (W≼W′ : Future W W′)
        {Uᴵ : Term Δᴵ′} {Uᴾ : Term Δᴾ′}
    → ValueImprecision W′ (liftCenterImprecision W≼W′ q₁) (suc m) Uᴵ Uᴾ
    → ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc m)
        (liftImpreciseTerm W≼W′ Vᴵ · Uᴵ)
        (liftPreciseTerm W≼W′
          (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ A₀ ⇒ B₀ 〗) · Uᴾ)
  reveal-arrow-head fuel m W s {A₀ = A₀} {B₀ = B₀} q₁ q₂ nuA nuB
      sizeA sizeB absentA absentB {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} function-related
      W′ W≼W′ {Uᴵ = Uᴵ} {Uᴾ = Uᴾ} argument-related =
    ClosureProof.computations-related-reindex
      (liftCenterImprecision W≼W′ q₂) (liftCenterImprecision W≼W′ q₂)
      refl refl refl (sym precise-redex-eq) expanded
    where
    s′ = slot-future s W≼W′
    A′ = liftPreciseTy W≼W′ A₀
    B′ = liftPreciseTy W≼W′ B₀
    cᴾ = makeConceal (slotXᴾ s′) (slotRᴾ s′) A′
    dᴾ = 〖 slotXᴾ s′ , slotRᴾ s′ ↑ B′ 〗
    Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ
    Vᴵ′ = liftImpreciseTerm W≼W′ Vᴵ

    precise-redex-eq :
        liftPreciseTerm W≼W′ (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ A₀ ⇒ B₀ 〗)
          · Uᴾ
        ≡ (Vᴾ′ ↑ (cᴾ ↦↑ dᴾ)) · Uᴾ
    precise-redex-eq
        rewrite lifted-reveal-precise s W≼W′ Vᴾ (A₀ ⇒ B₀)
              | liftPreciseTy-arrow W≼W′ A₀ B₀ = refl

    sourceA′ : embedPrecise (core W′) A′
        ≡ liftCenterTy W≼W′ (embedPrecise (core W) A₀)
    sourceA′ = embedPrecise-lift W≼W′ A₀

    sourceB′ : embedPrecise (core W′) B′
        ≡ liftCenterTy W≼W′ (embedPrecise (core W) B₀)
    sourceB′ = embedPrecise-lift W≼W′ B₀

    absentA′ : slotXᴾ s′ ∉ᵗ A′
    absentA′ = subst≡ (_∉ᵗ A′) (sym (slot-precise-variable-lift s W≼W′))
      (lift-∉ᵗ W≼W′ absentA)

    absentB′ : slotXᴾ s′ ∉ᵗ B′
    absentB′ = subst≡ (_∉ᵗ B′) (sym (slot-precise-variable-lift s W≼W′))
      (lift-∉ᵗ W≼W′ absentB)

    argument-endpoints =
      ClosureProof.value-imprecision-endpoints argument-related

    lifted-function : ValueImprecision W′
        (I.⇒⊑⇒ (liftCenterImprecision W≼W′ q₁)
          (liftCenterImprecision W≼W′ q₂)) (suc m) Vᴵ′ Vᴾ′
    lifted-function = ClosureProof.value-imprecision-reindex
      (I.⇒⊑⇒ (liftCenterImprecision W≼W′ q₁)
        (liftCenterImprecision W≼W′ q₂))
      (liftCenterImprecision W≼W′ (I.⇒⊑⇒ q₁ q₂))
      (sym (liftCenterTy-arrow W≼W′ _ _))
      (sym (liftCenterTy-arrow W≼W′ _ _))
      (ClosureProof.value-imprecision-future
        {W = W} {p = I.⇒⊑⇒ q₁ q₂} {k = suc m} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
        W≼W′ function-related)

    concealed : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₁)) (suc m)
        Uᴵ (Uᴾ ↓ cᴾ)
    concealed = conceal-go fuel (suc m) W′ s′
      (liftCenterImprecision W≼W′ q₁) (lift-NoUniversal W≼W′ nuA)
      (subst≡ (_≤ fuel) (sym (lift-sizeᵗ W≼W′ A₀)) sizeA)
      absentA′ sourceA′ argument-related

    applied : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc m)
        (Vᴵ′ · Uᴵ) (Vᴾ′ · (Uᴾ ↓ cᴾ))
    applied = related-application-computation lifted-function concealed

    contracted : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc m)
        (Vᴵ′ · Uᴵ) ((Vᴾ′ · (Uᴾ ↓ cᴾ)) ↑ dᴾ)
    contracted = precise-revealed-computations fuel (suc m) W′ s′
      (liftCenterImprecision W≼W′ q₂) (lift-NoUniversal W≼W′ nuB)
      (subst≡ (_≤ fuel) (sym (lift-sizeᵗ W≼W′ B₀)) sizeB)
      absentB′ sourceB′ applied

    expanded : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc m)
        (Vᴵ′ · Uᴵ) ((Vᴾ′ ↑ (cᴾ ↦↑ dᴾ)) · Uᴾ)
    expanded
        with reveal-fun-app-step-question
               {Σ = preciseStore (core W′)} cᴾ dᴾ
               (precise-value function-endpoints)
               (precise-value argument-endpoints)
      where
      function-endpoints = ClosureProof.value-imprecision-endpoints
        {W = W′}
        {p = I.⇒⊑⇒ (liftCenterImprecision W≼W′ q₁)
          (liftCenterImprecision W≼W′ q₂)}
        {k = suc m} {Vᴵ = Vᴵ′} {Vᴾ = Vᴾ′} lifted-function
    expanded | vVᴾ , vUᴾ , step-eqᴾ =
      related-precise-keep-step-expand (λ ())
        (reveal-fun-app-value-none cᴾ dᴾ)
        (pure-step (β-reveal-⇒ vVᴾ vUᴾ)) step-eqᴾ contracted

  conceal-arrow-head : ∀ (fuel : ℕ) (m : ℕ) {Δᴾ Δᴵ Δᶜ}
      (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
      {A₀ B₀ : Ty Δᴾ} {Pᴵ Qᴵ : Ty Δᶜ}
      (q₁ : impEnv (core W) I.⊢ embedPrecise (core W) A₀ ⊑ Pᴵ)
      (q₂ : impEnv (core W) I.⊢ embedPrecise (core W) B₀ ⊑ Qᴵ)
    → NoUniversal A₀ → NoUniversal B₀
    → sizeᵗ A₀ ≤ fuel → sizeᵗ B₀ ≤ fuel
    → slotXᴾ s ∉ᵗ A₀ → slotXᴾ s ∉ᵗ B₀
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W (I.⇒⊑⇒ q₁ q₂) (suc m) Vᴵ Vᴾ
    → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′) (W≼W′ : Future W W′)
        {Uᴵ : Term Δᴵ′} {Uᴾ : Term Δᴾ′}
    → ValueImprecision W′ (liftCenterImprecision W≼W′ q₁) (suc m) Uᴵ Uᴾ
    → ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc m)
        (liftImpreciseTerm W≼W′ Vᴵ · Uᴵ)
        (liftPreciseTerm W≼W′
          (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (A₀ ⇒ B₀)) · Uᴾ)
  conceal-arrow-head fuel m W s {A₀ = A₀} {B₀ = B₀} q₁ q₂ nuA nuB
      sizeA sizeB absentA absentB {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} function-related
      W′ W≼W′ {Uᴵ = Uᴵ} {Uᴾ = Uᴾ} argument-related =
    ClosureProof.computations-related-reindex
      (liftCenterImprecision W≼W′ q₂) (liftCenterImprecision W≼W′ q₂)
      refl refl refl (sym precise-redex-eq) expanded
    where
    s′ = slot-future s W≼W′
    A′ = liftPreciseTy W≼W′ A₀
    B′ = liftPreciseTy W≼W′ B₀
    cᴾ = 〖 slotXᴾ s′ , slotRᴾ s′ ↑ A′ 〗
    dᴾ = makeConceal (slotXᴾ s′) (slotRᴾ s′) B′
    Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ
    Vᴵ′ = liftImpreciseTerm W≼W′ Vᴵ

    precise-redex-eq :
        liftPreciseTerm W≼W′
          (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (A₀ ⇒ B₀)) · Uᴾ
        ≡ (Vᴾ′ ↓ (cᴾ ↦↓ dᴾ)) · Uᴾ
    precise-redex-eq
        rewrite lifted-conceal-precise s W≼W′ Vᴾ (A₀ ⇒ B₀)
              | liftPreciseTy-arrow W≼W′ A₀ B₀ = refl

    sourceA′ : embedPrecise (core W′) A′
        ≡ liftCenterTy W≼W′ (embedPrecise (core W) A₀)
    sourceA′ = embedPrecise-lift W≼W′ A₀

    sourceB′ : embedPrecise (core W′) B′
        ≡ liftCenterTy W≼W′ (embedPrecise (core W) B₀)
    sourceB′ = embedPrecise-lift W≼W′ B₀

    absentA′ : slotXᴾ s′ ∉ᵗ A′
    absentA′ = subst≡ (_∉ᵗ A′) (sym (slot-precise-variable-lift s W≼W′))
      (lift-∉ᵗ W≼W′ absentA)

    absentB′ : slotXᴾ s′ ∉ᵗ B′
    absentB′ = subst≡ (_∉ᵗ B′) (sym (slot-precise-variable-lift s W≼W′))
      (lift-∉ᵗ W≼W′ absentB)

    argument-endpoints =
      ClosureProof.value-imprecision-endpoints argument-related

    lifted-function : ValueImprecision W′
        (I.⇒⊑⇒ (liftCenterImprecision W≼W′ q₁)
          (liftCenterImprecision W≼W′ q₂)) (suc m) Vᴵ′ Vᴾ′
    lifted-function = ClosureProof.value-imprecision-reindex
      (I.⇒⊑⇒ (liftCenterImprecision W≼W′ q₁)
        (liftCenterImprecision W≼W′ q₂))
      (liftCenterImprecision W≼W′ (I.⇒⊑⇒ q₁ q₂))
      (sym (liftCenterTy-arrow W≼W′ _ _))
      (sym (liftCenterTy-arrow W≼W′ _ _))
      (ClosureProof.value-imprecision-future
        {W = W} {p = I.⇒⊑⇒ q₁ q₂} {k = suc m} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
        W≼W′ function-related)

    revealed : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₁)) (suc m)
        Uᴵ (Uᴾ ↑ cᴾ)
    revealed = reveal-go fuel (suc m) W′ s′
      (liftCenterImprecision W≼W′ q₁) (lift-NoUniversal W≼W′ nuA)
      (subst≡ (_≤ fuel) (sym (lift-sizeᵗ W≼W′ A₀)) sizeA)
      absentA′ sourceA′ argument-related

    applied : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc m)
        (Vᴵ′ · Uᴵ) (Vᴾ′ · (Uᴾ ↑ cᴾ))
    applied = related-application-computation lifted-function revealed

    contracted : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc m)
        (Vᴵ′ · Uᴵ) ((Vᴾ′ · (Uᴾ ↑ cᴾ)) ↓ dᴾ)
    contracted = precise-concealed-computations fuel (suc m) W′ s′
      (liftCenterImprecision W≼W′ q₂) (lift-NoUniversal W≼W′ nuB)
      (subst≡ (_≤ fuel) (sym (lift-sizeᵗ W≼W′ B₀)) sizeB)
      absentB′ sourceB′ applied

    expanded : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc m)
        (Vᴵ′ · Uᴵ) ((Vᴾ′ ↓ (cᴾ ↦↓ dᴾ)) · Uᴾ)
    expanded
        with conceal-fun-app-step-question
               {Σ = preciseStore (core W′)} cᴾ dᴾ
               (precise-value function-endpoints)
               (precise-value argument-endpoints)
      where
      function-endpoints = ClosureProof.value-imprecision-endpoints
        {W = W′}
        {p = I.⇒⊑⇒ (liftCenterImprecision W≼W′ q₁)
          (liftCenterImprecision W≼W′ q₂)}
        {k = suc m} {Vᴵ = Vᴵ′} {Vᴾ = Vᴾ′} lifted-function
    expanded | vVᴾ , vUᴾ , step-eqᴾ =
      related-precise-keep-step-expand (λ ())
        (conceal-fun-app-value-none cᴾ dᴾ)
        (pure-step (β-conceal-⇒ vVᴾ vUᴾ)) step-eqᴾ contracted

  -- The value relation of a wrapped function value.

  reveal-arrow : ∀ (fuel : ℕ) (j : ℕ) {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
      (s : PairedSlot W) {A₀ B₀ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → NoUniversal A₀ → NoUniversal B₀
    → sizeᵗ A₀ ≤ fuel → sizeᵗ B₀ ≤ fuel
    → slotXᴾ s ∉ᵗ A₀ → slotXᴾ s ∉ᵗ B₀
    → embedPrecise (core W) (A₀ ⇒ B₀) ≡ Aᴾ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W p j Vᴵ Vᴾ
    → ValueImprecision W p j
        Vᴵ (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ A₀ ⇒ B₀ 〗)
  reveal-arrow fuel zero W s p nuA nuB sizeA sizeB absentA absentB
      sourceᴾ related =
    precise-reveal-endpoints W s p (∉-fun absentA absentB) sourceᴾ
      {k = zero} related (precise-value endpoints ↑ fun)
    where
    endpoints = ClosureProof.value-imprecision-endpoints
      {k = zero} related
  reveal-arrow fuel (suc i) W s p nuA nuB sizeA sizeB absentA absentB
      sourceᴾ related with sourceᴾ
  reveal-arrow fuel (suc i) W s p nuA nuB sizeA sizeB absentA absentB
      sourceᴾ related | refl with arrow-source-view p
  reveal-arrow fuel (suc i) W s {A₀ = A₀} {B₀ = B₀} .(I.⇒⊑⇒ q₁ q₂)
      nuA nuB sizeA sizeB
      absentA absentB sourceᴾ {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
      | refl | arrow-arrow q₁ q₂ =
    precise-reveal-endpoints W s (I.⇒⊑⇒ q₁ q₂)
      (∉-fun absentA absentB) sourceᴾ {k = suc i} related
      (precise-value endpoints ↑ fun) ,
    functions (suc i) ≤-refl related
    where
    endpoints = ClosureProof.value-imprecision-endpoints
      {W = W} {p = I.⇒⊑⇒ q₁ q₂} {k = suc i} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related

    functions : ∀ (m : ℕ) → m ≤ suc i
      → ValueImprecision W (I.⇒⊑⇒ q₁ q₂) m Vᴵ Vᴾ
      → FunctionsRelated W q₁ q₂ m Vᴵ
          (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ A₀ ⇒ B₀ 〗)
    functions zero m≤ rel = tt
    functions (suc m) sm≤ rel =
      (λ W′ W≼W′ argument-related →
        reveal-arrow-head fuel m W s q₁ q₂ nuA nuB sizeA sizeB
          absentA absentB rel W′ W≼W′ argument-related) ,
      functions m (≤-trans (n≤1+n m) sm≤)
        (value-imprecision-downward-to
          {W = W} {p = I.⇒⊑⇒ q₁ q₂} {j = m} {k = suc m}
          {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (n≤1+n m) rel)
  reveal-arrow fuel (suc i) W s {A₀ = A₀} {B₀ = B₀} .(I.⇒⊑★ q₁ q₂)
      nuA nuB sizeA sizeB
      absentA absentB sourceᴾ {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
      | refl | arrow-star q₁ q₂ =
    precise-reveal-endpoints W s (I.⇒⊑★ q₁ q₂)
      (∉-fun absentA absentB) sourceᴾ {k = suc i} related
      (precise-value endpoints ↑ fun) ,
    shape ,
    reveal-arrow fuel i W s (right-payload-imprecision shape)
      nuA nuB sizeA sizeB absentA absentB refl payload-related
    where
    endpoints = ClosureProof.value-imprecision-endpoints
      {W = W} {p = I.⇒⊑★ q₁ q₂} {k = suc i} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related

    shape : RightDynamicPayloadShape W
        (embedPrecise (core W) A₀ ⇒ embedPrecise (core W) B₀) Vᴵ
    shape = proj₁ (proj₂ related)

    payload-related : ValueImprecision W
        (right-payload-imprecision shape) i
        (right-dynamic-imprecise-payload shape) Vᴾ
    payload-related = proj₂ (proj₂ related)

  conceal-arrow : ∀ (fuel : ℕ) (j : ℕ) {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
      (s : PairedSlot W) {A₀ B₀ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → NoUniversal A₀ → NoUniversal B₀
    → sizeᵗ A₀ ≤ fuel → sizeᵗ B₀ ≤ fuel
    → slotXᴾ s ∉ᵗ A₀ → slotXᴾ s ∉ᵗ B₀
    → embedPrecise (core W) (A₀ ⇒ B₀) ≡ Aᴾ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W p j Vᴵ Vᴾ
    → ValueImprecision W p j
        Vᴵ (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (A₀ ⇒ B₀))
  conceal-arrow fuel zero W s p nuA nuB sizeA sizeB absentA absentB
      sourceᴾ related =
    precise-conceal-endpoints W s p (∉-fun absentA absentB) sourceᴾ
      {k = zero} related (precise-value endpoints ↓ fun)
    where
    endpoints = ClosureProof.value-imprecision-endpoints
      {k = zero} related
  conceal-arrow fuel (suc i) W s p nuA nuB sizeA sizeB absentA absentB
      sourceᴾ related with sourceᴾ
  conceal-arrow fuel (suc i) W s p nuA nuB sizeA sizeB absentA absentB
      sourceᴾ related | refl with arrow-source-view p
  conceal-arrow fuel (suc i) W s {A₀ = A₀} {B₀ = B₀} .(I.⇒⊑⇒ q₁ q₂)
      nuA nuB sizeA sizeB
      absentA absentB sourceᴾ {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
      | refl | arrow-arrow q₁ q₂ =
    precise-conceal-endpoints W s (I.⇒⊑⇒ q₁ q₂)
      (∉-fun absentA absentB) sourceᴾ {k = suc i} related
      (precise-value endpoints ↓ fun) ,
    functions (suc i) ≤-refl related
    where
    endpoints = ClosureProof.value-imprecision-endpoints
      {W = W} {p = I.⇒⊑⇒ q₁ q₂} {k = suc i} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related

    functions : ∀ (m : ℕ) → m ≤ suc i
      → ValueImprecision W (I.⇒⊑⇒ q₁ q₂) m Vᴵ Vᴾ
      → FunctionsRelated W q₁ q₂ m Vᴵ
          (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (A₀ ⇒ B₀))
    functions zero m≤ rel = tt
    functions (suc m) sm≤ rel =
      (λ W′ W≼W′ argument-related →
        conceal-arrow-head fuel m W s q₁ q₂ nuA nuB sizeA sizeB
          absentA absentB rel W′ W≼W′ argument-related) ,
      functions m (≤-trans (n≤1+n m) sm≤)
        (value-imprecision-downward-to
          {W = W} {p = I.⇒⊑⇒ q₁ q₂} {j = m} {k = suc m}
          {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (n≤1+n m) rel)
  conceal-arrow fuel (suc i) W s {A₀ = A₀} {B₀ = B₀} .(I.⇒⊑★ q₁ q₂)
      nuA nuB sizeA sizeB
      absentA absentB sourceᴾ {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
      | refl | arrow-star q₁ q₂ =
    precise-conceal-endpoints W s (I.⇒⊑★ q₁ q₂)
      (∉-fun absentA absentB) sourceᴾ {k = suc i} related
      (precise-value endpoints ↓ fun) ,
    shape ,
    conceal-arrow fuel i W s (right-payload-imprecision shape)
      nuA nuB sizeA sizeB absentA absentB refl payload-related
    where
    endpoints = ClosureProof.value-imprecision-endpoints
      {W = W} {p = I.⇒⊑★ q₁ q₂} {k = suc i} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related

    shape : RightDynamicPayloadShape W
        (embedPrecise (core W) A₀ ⇒ embedPrecise (core W) B₀) Vᴵ
    shape = proj₁ (proj₂ related)

    payload-related : ValueImprecision W
        (right-payload-imprecision shape) i
        (right-dynamic-imprecise-payload shape) Vᴾ
    payload-related = proj₂ (proj₂ related)

------------------------------------------------------------------------
-- The one-sided reveal and conceal, with the fuel instantiated
------------------------------------------------------------------------

precise-reveal : ∀ {k : ℕ} → PreciseRevealAt k
precise-reveal {k = k} W s {Bᴾ = Bᴾ} p nu no-occur sourceᴾ related =
  reveal-go (sizeᵗ Bᴾ) k W s p nu ≤-refl no-occur sourceᴾ related

precise-conceal : ∀ {k : ℕ} → PreciseConcealAt k
precise-conceal {k = k} W s {Bᴾ = Bᴾ} p nu no-occur sourceᴾ related =
  conceal-go (sizeᵗ Bᴾ) k W s p nu ≤-refl no-occur sourceᴾ related
