module proof.ImprecisionConsistent where

-- File Charter:
--   * Properties that involve Imprecisoin and Consistency

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; _+_; _<_; _≤_; zero; suc; z<s; s<s; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import Imprecision
open import Consistency

leftICtx-boths[] : ∀ Δ → leftICtx (boths Δ []) ≡ plains Δ []
leftICtx-boths[] zero = refl
leftICtx-boths[] (suc Δ) = cong (plain ∷_) (leftICtx-boths[] Δ)

rightICtx-boths[] : ∀ Δ → rightICtx (boths Δ []) ≡ plains Δ []
rightICtx-boths[] zero = refl
rightICtx-boths[] (suc Δ) = cong (plain ∷_) (rightICtx-boths[] Δ)

left-lookup-left :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ left →
  leftICtx Γ ∋ X ∶ plain
left-lookup-left here = here
left-lookup-left (there x∈) = there (left-lookup-left x∈)

right-lookup-left :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ left →
  rightICtx Γ ∋ X ∶ ν-bound
right-lookup-left here = here
right-lookup-left (there x∈) = there (right-lookup-left x∈)

left-lookup-right :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ right →
  leftICtx Γ ∋ X ∶ ν-bound
left-lookup-right here = here
left-lookup-right (there x∈) = there (left-lookup-right x∈)

right-lookup-right :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ right →
  rightICtx Γ ∋ X ∶ plain
right-lookup-right here = here
right-lookup-right (there x∈) = there (right-lookup-right x∈)

left-lookup-both :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ both →
  leftICtx Γ ∋ X ∶ plain
left-lookup-both here = here
left-lookup-both (there x∈) = there (left-lookup-both x∈)

right-lookup-both :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ both →
  rightICtx Γ ∋ X ∶ plain
right-lookup-both here = here
right-lookup-both (there x∈) = there (right-lookup-both x∈)
