{-# OPTIONS --rewriting #-}

module FreeTheorems where

open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Level using (Lift; lift; zero)

open import Types
open import Ctx
open import Terms
open import Reduction
open import Parametricity

-- | Free theorem (identity):

-- R = {(V, V)}
idR : ∀ {A} → (V : ∅ ; ∅ ⊢ A) → Rel {ℓ = zero} {Ξ = ∅} A A
idR V V′ W′ _ _ = Lift _ (V ≡ V′ × V ≡ W′)

postulate
  free-theorem-id : ∀ {A : Type ∅}
    → (M : ∅ ; ∅ ⊢ `∀ (` Z ⇒ ` Z))
    → (V : ∅ ; ∅ ⊢ A)
    → Value V
      ------------------------
    → (closedInst M ∙ A) · V —↠ V

-- | Free theorem (representation independence):

neg : ∅ ; ∅ ⊢ (`Bool ⇒ `Bool)
neg = ƛ `Bool ˙ `if ` Z then `false else `true

flip : ∅ ; ∅ ⊢ (`Nat ⇒ `Nat)
flip = ƛ `Nat ˙ `case-nat (` Z) (`suc `zero) `zero

-- R = {(true, 1), (false, 0)}
R : Rel {ℓ = zero} {Ξ = ∅} `Bool `Nat
R `true `zero V-true V-zero = ⊥
R `true (`suc `zero) V-true (V-suc V-zero) = ⊤
R `true (`suc (`suc W)) V-true (V-suc (V-suc w)) = ⊥
R `false `zero V-false V-zero = ⊤
R `false (`suc W) V-false (V-suc w) = ⊥

neg-flip-related : 𝒱 (` Z ⇒ ` Z) (extendRelSub emptyRelSub `Bool `Nat R) neg flip V-ƛ V-ƛ
neg-flip-related {V = `true} {W = `zero} V-true V-zero (lift ())
neg-flip-related {V = `true} {W = `suc `zero} V-true (V-suc V-zero) (lift tt) =
  ⟨ `false , ⟨ `zero , ⟨ V-false , ⟨ V-zero ,
    ⟨ (`if `true then `false else `true) —→⟨ β-true ⟩ (`false ∎) ,
      ⟨ (`case-nat (`suc `zero) (`suc `zero) `zero) —→⟨ β-suc V-zero ⟩ (`zero ∎) ,
        lift tt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
neg-flip-related {V = `true} {W = `suc (`suc W)} V-true (V-suc (V-suc w)) (lift ())
neg-flip-related {V = `false} {W = `zero} V-false V-zero (lift tt) =
  ⟨ `true , ⟨ `suc `zero , ⟨ V-true , ⟨ V-suc V-zero ,
    ⟨ (`if `false then `false else `true) —→⟨ β-false ⟩ (`true ∎) ,
      ⟨ (`case-nat `zero (`suc `zero) `zero) —→⟨ β-zero ⟩ ((`suc `zero) ∎) ,
        lift tt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
neg-flip-related {V = `false} {W = `suc W} V-false (V-suc w) (lift ())

-- If ∅ ; ∅ ⊢ M : ∀ α. α -> (α -> α) -> α,
-- then M [ Bool ] true neg —↠ V
-- and  M [ Nat  ] 1   flip —↠ W
-- and  (V, W) ∈ R.
postulate
  free-theorem-rep :
    ∀ (M : ∅ ; ∅ ⊢ `∀ (` Z ⇒ (` Z ⇒ ` Z) ⇒ ` Z))
      ------------------------------------------------------
    → ∃[ V ] ∃[ W ] ∃[ v ] ∃[ w ]
          ((closedInst M ∙ `Bool · `true)        · neg  —↠ V)
        × ((closedInst M ∙ `Nat  · (`suc `zero)) · flip —↠ W)
        × R V W v w
