module intrinsic-subst.FreeTheorems where

-- File Charter:
--   * The programs and the relation in the statements of the free
--     theorems (MetaTheory.agda): boolean negation `neg`, its counterpart
--     `flip` on the naturals 0 and 1, and the relation `R` that pairs
--     `true` with 1 and `false` with 0.
--   * Definitions only; the proofs are in intrinsic-subst/proof/.

open import Level using (zero)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic using (⊤)

open import intrinsic-subst.Types
open import intrinsic-subst.Ctx
open import intrinsic-subst.Terms
open import intrinsic-subst.Reduction
open import intrinsic-subst.Parametricity

neg : ∅ ∣ ∅ ⊢ `Bool ⇒ `Bool
neg = ƛ `Bool ˙ (`if ` Z then `false else `true)

flip : ∅ ∣ ∅ ⊢ `Nat ⇒ `Nat
flip = ƛ `Nat ˙ `case-nat (` Z) (`suc `zero) `zero

-- R = {(true, 1), (false, 0)}
R : Rel zero `Bool `Nat
R _ _ V-true V-zero = ⊥
R _ _ V-true (V-suc V-zero) = ⊤
R _ _ V-true (V-suc (V-suc w)) = ⊥
R _ _ V-false V-zero = ⊤
R _ _ V-false (V-suc w) = ⊥
