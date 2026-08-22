module LR-narrow.Examples.Cambridge26.Specification where

-- File Charter:
--   * Defines the checked, reduction-free format of a Cambridge26 example.
--   * Stores endpoints in the LR orientation: imprecise-left, precise-right.
--   * Retains the source-to-target `Aᴾ ⊑ Aᴵ` proof as the relation index.
--   * Reorders proof-oriented builder inputs at the record boundary.

open import Data.List using ([])
open import Data.Nat using (ℕ; zero)

open import Coercions using (Coercion; id-onlyᵈ)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import LR-narrow.Context.TermRelation using (TermRelation)
open import LR-narrow.World using (Interpretation; World)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuTerms using (Term; _∣_∣_⊢_⦂_)
open import TypeCheck using (IsJust; fromJust; type-check-expect)
open import Types using (Ty)

record ClosedExample : Set₁ where
  constructor closed-example
  field
    imprecise-type : Ty
    precise-type : Ty
    type-imprecision :
      [] ∣ zero ⊢ precise-type ⊑ imprecise-type ⊣ zero
    narrowing-coercion : Coercion
    narrowing :
      id-onlyᵈ ∣ zero ∣ [] ⊢ narrowing-coercion
        ∶ imprecise-type ⊒ precise-type
    imprecise-term : Term
    precise-term : Term
    imprecise-typing :
      zero ∣ [] ∣ [] ⊢ imprecise-term ⦂ imprecise-type
    precise-typing :
      zero ∣ [] ∣ [] ⊢ precise-term ⦂ precise-type

open ClosedExample public

checked-example :
    (Aᴾ Aᴵ : Ty)
  → [] ∣ zero ⊢ Aᴾ ⊑ Aᴵ ⊣ zero
  → (c : Coercion)
  → id-onlyᵈ ∣ zero ∣ [] ⊢ c ∶ Aᴵ ⊒ Aᴾ
  → (Mᴾ Mᴵ : Term)
  → IsJust (type-check-expect zero [] [] Mᴾ Aᴾ)
  → IsJust (type-check-expect zero [] [] Mᴵ Aᴵ)
  → ClosedExample
checked-example Aᴾ Aᴵ p c c⊒ Mᴾ Mᴵ right-ok left-ok =
  closed-example Aᴵ Aᴾ p c c⊒ Mᴵ Mᴾ
    (fromJust (type-check-expect zero [] [] Mᴵ Aᴵ) left-ok)
    (fromJust (type-check-expect zero [] [] Mᴾ Aᴾ) right-ok)

Membership : ClosedExample → Set₁
Membership example =
  ∀ {w : World}
  → (I : Interpretation {[]} {zero} {zero} w)
  → (k : ℕ)
  → TermRelation (type-imprecision example) I k
      [] []
      (imprecise-term example) (precise-term example)

record TypeExample : Set where
  constructor type-example
  field
    imprecise-type : Ty
    precise-type : Ty
    type-imprecision :
      [] ∣ zero ⊢ precise-type ⊑ imprecise-type ⊣ zero
    narrowing-coercion : Coercion
    narrowing :
      id-onlyᵈ ∣ zero ∣ [] ⊢ narrowing-coercion
        ∶ imprecise-type ⊒ precise-type

record CheckedProgram : Set₁ where
  constructor checked-program
  field
    result-type : Ty
    term : Term
    typing : zero ∣ [] ∣ [] ⊢ term ⦂ result-type

checked-programᵐ :
    (A : Ty)
  → (M : Term)
  → IsJust (type-check-expect zero [] [] M A)
  → CheckedProgram
checked-programᵐ A M ok =
  checked-program A M (fromJust (type-check-expect zero [] [] M A) ok)
