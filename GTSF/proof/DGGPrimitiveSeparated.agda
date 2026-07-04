module proof.DGGPrimitiveSeparated where

-- File Charter:
--   * Primitive/nat helper lemmas for the separated dynamic gradual guarantee.
--   * Provides the `ℕ` identity coercion facts and constant-shape inversions
--     used by the arithmetic congruence and delta cases.
--   * Keeps primitive-specific proof plumbing out of the main separated DGG
--     module.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (_+_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

open import Types
open import Coercions
open import NarrowWiden using
  ( cross
  ; id-‵
  ; _∣_∣_⊢_∶_⊒_
  )
open import Primitives using (addℕ; κℕ)
open import NuTerms
open import NuReduction
open import StoreCorrespondence
open import TermNarrowingSeparated
open import proof.NuProgress using (canonical-ℕ; nv-const)
open import proof.ReductionProperties using
  ( applyCoercions
  ; applyTerms-const
  )

id-ℕ-narrowingᶜ :
  ∀ {ΔL ΔR ρ} →
  StoreCorr ΔL ΔR ρ →
  ΔL ∣ ΔR ∣ ρ ⊢ id (‵ `ℕ) ∶ᶜ ‵ `ℕ ⊒ ‵ `ℕ
id-ℕ-narrowingᶜ stores =
  stores ,
  refl ,
  refl ,
  wfBase ,
  wfBase ,
  (cast-id wfBase refl , cross (id-‵ `ℕ)) ,
  (cast-id wfBase refl , cross (id-‵ `ℕ))

applyCoercion-id-ℕ :
  ∀ χ →
  applyCoercion χ (id (‵ `ℕ)) ≡ id (‵ `ℕ)
applyCoercion-id-ℕ keep = refl
applyCoercion-id-ℕ (bind A) = refl

applyCoercions-id-ℕ :
  ∀ χs →
  applyCoercions χs (id (‵ `ℕ)) ≡ id (‵ `ℕ)
applyCoercions-id-ℕ [] = refl
applyCoercions-id-ℕ (χ ∷ χs) rewrite applyCoercion-id-ℕ χ =
  applyCoercions-id-ℕ χs

applyCoercions-id-ℕ-applyCoercions :
  ∀ χs χs′ →
  applyCoercions χs′ (applyCoercions χs (id (‵ `ℕ))) ≡ id (‵ `ℕ)
applyCoercions-id-ℕ-applyCoercions χs χs′ =
  trans (cong (applyCoercions χs′) (applyCoercions-id-ℕ χs))
    (applyCoercions-id-ℕ χs′)

source-nat-typingᶜ :
  ∀ {ΔL ΔR ρ W V p A B} →
  A ≡ ‵ `ℕ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ W ⊒ V ∶ p ⦂ A ⊒ B →
  ΔL ∣ leftStore ρ ∣ [] ⊢ W ⦂ ‵ `ℕ
source-nat-typingᶜ A≡ℕ W⊒V =
  subst (λ A → _ ∣ _ ∣ [] ⊢ _ ⦂ A) A≡ℕ
    (typed-term-narrowing-source-typingᶜ W⊒V)

typed-term-narrowing-endpointsᶜ :
  ∀ {ΔL ΔR ρ γ M M′ p A B A′ B′} →
  A ≡ A′ →
  B ≡ B′ →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A′ ⊒ B′
typed-term-narrowing-endpointsᶜ refl refl M⊒M′ = M⊒M′

typed-term-narrowing-coercion-endpointsᶜ :
  ∀ {ΔL ΔR ρ γ M M′ p A B A′ B′} →
  ΔL ∣ ΔR ∣ ρ ⊢ p ∶ᶜ A′ ⊒ B′ →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A′ ⊒ B′
typed-term-narrowing-coercion-endpointsᶜ
    (_ , src′ , tgt′ , _ , _ , _ , _) M⊒M′ =
  let
    _ , (_ , src , tgt , _ , _ , _ , _) =
      typed-term-narrowing-coercion M⊒M′
  in
  typed-term-narrowing-endpointsᶜ
    (trans (sym src) src′)
    (trans (sym tgt) tgt′)
    M⊒M′

constant-⊕-δ-step :
  ∀ {χsL χsR L R m n} →
  L ≡ $ (κℕ m) →
  R ≡ $ (κℕ n) →
  applyTerms χsL L ⊕[ addℕ ] applyTerms χsR R
    —↠[ keep ∷ [] ] $ (κℕ (m + n))
constant-⊕-δ-step {χsL = χsL} {χsR = χsR} {m = m} {n = n}
    L≡ R≡
    rewrite L≡ | applyTerms-const χsL (κℕ m)
          | R≡ | applyTerms-const χsR (κℕ n) =
  ↠-step (pure-step δ-⊕) ↠-refl

const-narrowing-targetᶜ :
  ∀ {ΔL ΔR ρ γ M M′ p A B m n} →
  M ≡ $ (κℕ m) →
  M′ ≡ $ (κℕ n) →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  m ≡ n
const-narrowing-targetᶜ eqM () (⊒blameᵗ M⊢ pᶜ)
const-narrowing-targetᶜ () eqM′ (x⊒xᵗ pᶜ x∋p)
const-narrowing-targetᶜ () eqM′ (ƛ⊒ƛᵗ p↦qᶜ N⊒N′)
const-narrowing-targetᶜ () eqM′ (·⊒·ᵗ p↦qᶜ L⊒L′ M⊒M′)
const-narrowing-targetᶜ () eqM′ (Λ⊒Λᵗ allᶜ vV vV′ V⊒V′)
const-narrowing-targetᶜ refl refl (κ⊒κᵗ (κℕ n) pᶜ) = refl
const-narrowing-targetᶜ () eqM′ (⊕⊒⊕ᵗ pᶜ M⊒M′ N⊒N′)
const-narrowing-targetᶜ eqM () (⊒cast+ᵗ pᶜ rᶜ t⊒ M⊒M′)
const-narrowing-targetᶜ eqM () (⊒cast-ᵗ pᶜ rᶜ t⊒ M⊒M′)
const-narrowing-targetᶜ () eqM′ (cast+⊒ᵗ qᶜ rᶜ s⊒ M⊒M′)
const-narrowing-targetᶜ () eqM′ (cast-⊒ᵗ qᶜ rᶜ s⊒ M⊒M′)

value-id-ℕ-narrowing-target-constᶜ :
  ∀ {ΔL ΔR ρ W n} →
  Value W →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ W ⊒ $ (κℕ n)
    ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ →
  W ≡ $ (κℕ n)
value-id-ℕ-narrowing-target-constᶜ {W = W} vW W⊒
    with canonical-ℕ vW (typed-term-narrowing-source-typingᶜ W⊒)
value-id-ℕ-narrowing-target-constᶜ {W = W} vW W⊒
    | nv-const {n = m} W≡
    rewrite W≡ | const-narrowing-targetᶜ refl refl W⊒ =
  refl

value-normalized-id-ℕ-target-constᶜ :
  ∀ {ΔL ΔR ρ W T p A B n} →
  Value W →
  T ≡ $ (κℕ n) →
  p ≡ id (‵ `ℕ) →
  A ≡ ‵ `ℕ →
  B ≡ ‵ `ℕ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ W ⊒ T ∶ p ⦂ A ⊒ B →
  W ≡ $ (κℕ n)
value-normalized-id-ℕ-target-constᶜ target-value T≡ p≡ A≡ B≡ W⊒ =
  value-id-ℕ-narrowing-target-constᶜ target-value
    (subst
      (λ T → _ ∣ _ ∣ _ ∣ [] ⊢ _ ⊒ T
        ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ)
      T≡
      (subst
        (λ p → _ ∣ _ ∣ _ ∣ [] ⊢ _ ⊒ _ ∶ p ⦂ ‵ `ℕ ⊒ ‵ `ℕ)
        p≡
        (subst
          (λ A → _ ∣ _ ∣ _ ∣ [] ⊢ _ ⊒ _ ∶ _ ⦂ A ⊒ ‵ `ℕ)
          A≡
          (subst
            (λ B → _ ∣ _ ∣ _ ∣ [] ⊢ _ ⊒ _ ∶ _ ⦂ _ ⊒ B)
            B≡
            W⊒))))
