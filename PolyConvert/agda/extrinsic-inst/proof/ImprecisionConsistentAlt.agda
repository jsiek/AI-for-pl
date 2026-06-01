module proof.ImprecisionConsistentAlt where

-- File Charter:
--   * Properties that involve Imprecision and Consistency (alternative definitions)

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (_∨_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat using (ℕ; _+_; _<_; _≤_; zero; suc; z<s; s<s; z≤n; s≤s)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import ImprecisionAlt
open import ConsistencyAlt
open import Types

leftAssm : CAssm → ImpAssm
leftAssm (X ~ᶜ★) = X ˣ⊑ˣ X
leftAssm (★~ᶜ X) = X ˣ⊑★
leftAssm (X ~ᶜ Y) = X ˣ⊑ˣ Y

rightAssm : CAssm → ImpAssm
rightAssm (X ~ᶜ★) = X ˣ⊑★
rightAssm (★~ᶜ X) = X ˣ⊑ˣ X
rightAssm (X ~ᶜ Y) = X ˣ⊑ˣ Y

leftImpCtx : CCtx → ImpCtx
leftImpCtx [] = []
leftImpCtx (m ∷ Γ) = leftAssm m ∷ leftImpCtx Γ

rightImpCtx : CCtx → ImpCtx
rightImpCtx [] = []
rightImpCtx (m ∷ Γ) = rightAssm m ∷ rightImpCtx Γ

{-
lower-bounds-consistent : ∀ {Γ A B C}
  → 0 ∣ leftImpCtx Γ ⊢ A ⊑ B
  → 0 ∣ rightImpCtx Γ ⊢ A ⊑ C
  → Γ ⊢ B ~ C
lower-bounds-consistent AB AC = {!!}

consistent-glb : ∀ {Γ B C}
  → Γ ⊢ B ~ C
-}
