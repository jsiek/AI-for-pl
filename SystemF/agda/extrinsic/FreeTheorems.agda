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
idR V V′ W′ _ _ _ _ = V ≡ V′ × V ≡ W′

postulate
  free-theorem-id : ∀ {A : Ty}
    → (M V : Term)
    → 0 ∣ [] ⊢ M ⦂ `∀ (` 0 ⇒ ` 0)
    → 0 ∣ [] ⊢ V ⦂ A
    → Value V
      ------------------------
    → ((M ·[ A ]) · V) —↠ V

--------------------------------------------------------------------------------
-- Free theorem (representation independence)
--------------------------------------------------------------------------------

neg : Term
neg = ƛ `Bool ⇒ (`if_then_else (` 0) `false `true)

flip : Term
flip = ƛ `ℕ ⇒ (case_[zero⇒_|suc⇒_] (` 0) (`suc `zero) `zero)

-- R = {(true, 1), (false, 0)}
R : Rel `Bool `ℕ
R `true (`suc `zero) vTrue (vSuc vZero) ⊢V ⊢W = ⊤
R `false `zero vFalse vZero ⊢V ⊢W = ⊤
R _ _ _ _ ⊢V ⊢W = ⊥

neg-flip-related : 𝒱 (` 0 ⇒ ` 0) (∅ρ ,⟨ `Bool , `ℕ , wf`Bool , wf`ℕ , R ⟩) neg flip vLam vLam
neg-flip-related = ⟨ ⊢neg , ⟨ ⊢flip , body ⟩ ⟩
  where
  ⊢neg : 0 ∣ [] ⊢ neg ⦂ substᵗ (left (∅ρ ,⟨ `Bool , `ℕ , wf`Bool , wf`ℕ , R ⟩)) (` 0 ⇒ ` 0)
  ⊢neg = ⊢ƛ wf`Bool (⊢if (⊢` Z) ⊢false ⊢true)

  ⊢flip : 0 ∣ [] ⊢ flip ⦂ substᵗ (right (∅ρ ,⟨ `Bool , `ℕ , wf`Bool , wf`ℕ , R ⟩)) (` 0 ⇒ ` 0)
  ⊢flip = ⊢ƛ wf`ℕ (⊢case (⊢` Z) (⊢suc ⊢zero) ⊢zero)

  body : ∀ {V W} (v : Value V) (w : Value W)
    → 𝒱 (` 0) (∅ρ ,⟨ `Bool , `ℕ , wf`Bool , wf`ℕ , R ⟩) V W v w
    → ℰ (` 0) (∅ρ ,⟨ `Bool , `ℕ , wf`Bool , wf`ℕ , R ⟩)
        ((`if_then_else (` 0) `false `true) [ V ])
        ((case_[zero⇒_|suc⇒_] (` 0) (`suc `zero) `zero) [ W ])
  body {V = `true} {W = `zero} vTrue vZero ()
  body {V = `true} {W = `suc `zero} vTrue (vSuc vZero) ⟨ _ , ⟨ _ , tt ⟩ ⟩ =
    ⟨ ⊢L
    , ⟨ ⊢R
      , ⟨ `false
        , ⟨ `zero
          , ⟨ vFalse
            , ⟨ vZero
              , ⟨ redL
                , ⟨ redR
                  , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where
    ⊢L : 0 ∣ [] ⊢ (`if_then_else `true `false `true) ⦂ `Bool
    ⊢L = ⊢if ⊢true ⊢false ⊢true

    ⊢R : 0 ∣ [] ⊢ (case_[zero⇒_|suc⇒_] (`suc `zero) (`suc `zero) `zero) ⦂ `ℕ
    ⊢R = ⊢case (⊢suc ⊢zero) (⊢suc ⊢zero) ⊢zero

    redL : (`if_then_else `true `false `true) —↠ `false
    redL = (`if_then_else `true `false `true) —→⟨ β-true ⟩ (`false ∎)

    redR : (case_[zero⇒_|suc⇒_] (`suc `zero) (`suc `zero) `zero) —↠ `zero
    redR = (case_[zero⇒_|suc⇒_] (`suc `zero) (`suc `zero) `zero) —→⟨ β-suc vZero ⟩ (`zero ∎)

    rel : 𝒱 (` 0) (∅ρ ,⟨ `Bool , `ℕ , wf`Bool , wf`ℕ , R ⟩) `false `zero vFalse vZero
    rel = ⟨ ⊢false , ⟨ ⊢zero , tt ⟩ ⟩
  body {V = `true} {W = `suc (`suc W)} vTrue (vSuc (vSuc w)) ()
  body {V = `false} {W = `zero} vFalse vZero ⟨ _ , ⟨ _ , tt ⟩ ⟩ =
    ⟨ ⊢L
    , ⟨ ⊢R
      , ⟨ `true
        , ⟨ `suc `zero
          , ⟨ vTrue
            , ⟨ vSuc vZero
              , ⟨ redL
                , ⟨ redR
                  , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where
    ⊢L : 0 ∣ [] ⊢ (`if_then_else `false `false `true) ⦂ `Bool
    ⊢L = ⊢if ⊢false ⊢false ⊢true

    ⊢R : 0 ∣ [] ⊢ (case_[zero⇒_|suc⇒_] `zero (`suc `zero) `zero) ⦂ `ℕ
    ⊢R = ⊢case ⊢zero (⊢suc ⊢zero) ⊢zero

    redL : (`if_then_else `false `false `true) —↠ `true
    redL = (`if_then_else `false `false `true) —→⟨ β-false ⟩ (`true ∎)

    redR : (case_[zero⇒_|suc⇒_] `zero (`suc `zero) `zero) —↠ (`suc `zero)
    redR = (case_[zero⇒_|suc⇒_] `zero (`suc `zero) `zero) —→⟨ β-zero ⟩ ((`suc `zero) ∎)

    rel : 𝒱 (` 0) (∅ρ ,⟨ `Bool , `ℕ , wf`Bool , wf`ℕ , R ⟩) `true (`suc `zero) vTrue (vSuc vZero)
    rel = ⟨ ⊢true , ⟨ ⊢suc ⊢zero , tt ⟩ ⟩
  body {V = `false} {W = `suc W} vFalse (vSuc w) ()

-- If 0 ⊢ [] ⊢ M : ∀ α. α -> (α -> α) -> α,
-- then M [ Bool ] true neg —↠ V
-- and  M [ Nat  ] 1   flip —↠ W
-- and  (V, W) ∈ R.
postulate
  free-theorem-rep :
    ∀ (M : Term)
    → 0 ∣ [] ⊢ M ⦂ `∀ (` 0 ⇒ (` 0 ⇒ ` 0) ⇒ ` 0)
      ------------------------------------------------------
    → ∃[ V ] ∃[ W ] ∃[ v ] ∃[ w ]
          (((M ·[ `Bool ]) · `true)        · neg  —↠ V)
        × (((M ·[ `ℕ ]) · (`suc `zero)) · flip —↠ W)
        × (∃[ ⊢V ] ∃[ ⊢W ] R V W v w ⊢V ⊢W)
