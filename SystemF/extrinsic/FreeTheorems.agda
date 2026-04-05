{-# OPTIONS --cumulativity --omega-in-omega #-}
module extrinsic.FreeTheorems where

-- File Charter:
--   * Ports the intrinsic free-theorem statements to the extrinsic setting.
--   * Reuses the extrinsic logical relation to state relation witnesses.

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.List using ([])
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import extrinsic.ProductOmega using (Σ-syntax; ∃-syntax; _×_)
  renaming (_,_ to ⟨_,_⟩)

open import extrinsic.Types
open import extrinsic.Terms
open import extrinsic.Reduction
open import extrinsic.LogicalRelation
open import extrinsic.Parametricity

--------------------------------------------------------------------------------
-- Free theorem (identity)
--------------------------------------------------------------------------------

-- R = {(V, V)}
idR : ∀ {A} → (V : Term) → Rel A A
idR V V′ W′ _ _ = V ≡ V′ × V ≡ W′

postulate
  free-theorem-id : ∀ {A : Ty}
    → (M V : Term)
    → 0 ⊢ [] ⊢ M ⦂ `∀ (` 0 ⇒ ` 0)
    → 0 ⊢ [] ⊢ V ⦂ A
    → Value V
      ------------------------
    → ((M ·[]) · V) —↠ V

--------------------------------------------------------------------------------
-- Free theorem (representation independence)
--------------------------------------------------------------------------------

neg : Term
neg = ƛ (`if_then_else (` 0) `false `true)

flip : Term
flip = ƛ (case_[zero⇒_|suc⇒_] (` 0) (`suc `zero) `zero)

-- R = {(true, 1), (false, 0)}
R : Rel `Bool `ℕ
R `true (`suc `zero) vTrue (vSuc vZero) = ⊤
R `false `zero vFalse vZero = ⊤
R _ _ _ _ = ⊥

neg-flip-related : 𝒱 (` 0 ⇒ ` 0) (∅ρ ,⟨ `Bool , `ℕ , R ⟩) neg flip vLam vLam
neg-flip-related {V = `true} {W = `zero} vTrue vZero ()
neg-flip-related {V = `true} {W = `suc `zero} vTrue (vSuc vZero) tt =
  ⟨ `false , ⟨ `zero , ⟨ vFalse , ⟨ vZero ,
    ⟨ (`if_then_else `true `false `true) —→⟨ β-true ⟩ (`false ∎) ,
      ⟨ (case_[zero⇒_|suc⇒_] (`suc `zero) (`suc `zero) `zero) —→⟨ β-suc vZero ⟩ (`zero ∎) ,
        tt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
neg-flip-related {V = `true} {W = `suc (`suc W)} vTrue (vSuc (vSuc w)) ()
neg-flip-related {V = `false} {W = `zero} vFalse vZero tt =
  ⟨ `true , ⟨ `suc `zero , ⟨ vTrue , ⟨ vSuc vZero ,
    ⟨ (`if_then_else `false `false `true) —→⟨ β-false ⟩ (`true ∎) ,
      ⟨ (case_[zero⇒_|suc⇒_] `zero (`suc `zero) `zero) —→⟨ β-zero ⟩ ((`suc `zero) ∎) ,
        tt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
neg-flip-related {V = `false} {W = `suc W} vFalse (vSuc w) ()

-- If 0 ⊢ [] ⊢ M : ∀ α. α -> (α -> α) -> α,
-- then M [ Bool ] true neg —↠ V
-- and  M [ Nat  ] 1   flip —↠ W
-- and  (V, W) ∈ R.
postulate
  free-theorem-rep :
    ∀ (M : Term)
    → 0 ⊢ [] ⊢ M ⦂ `∀ (` 0 ⇒ (` 0 ⇒ ` 0) ⇒ ` 0)
      ------------------------------------------------------
    → ∃[ V ] ∃[ W ] ∃[ v ] ∃[ w ]
          (((M ·[]) · `true)        · neg  —↠ V)
        × (((M ·[]) · (`suc `zero)) · flip —↠ W)
        × R V W v w
