module strong.proof.CloseTy where

-- Strong System F v7 — the index arithmetic of `closeAt`.
--
-- `revTy X α S A` targets `closeAt X S A`: the source type `A` with the
-- revealed variable `X` replaced by its reading `S` and every deeper
-- variable shifted down into the slot `X` vacates.  `closeEnv` decides that
-- with `_≟_` and `_<?_`; the structural `closeIdx` below is the same
-- function on the `X ≢ Y` branch, and is what the typing proofs case on.

open import Data.Nat using (ℕ; zero; suc; _<_; _∸_; s≤s; z≤n)
open import Data.Nat.Properties using (_≟_; _<?_; <-irrefl; ≮⇒≥; ≤∧≢⇒<)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)

open import strong.Types
open import strong.Conversion using (closeEnv; closeAt)

infix 4 _≢ᴺ_
_≢ᴺ_ : ℕ → ℕ → Set
X ≢ᴺ Y = ¬ (X ≡ Y)

------------------------------------------------------------------------
-- The structural index map
------------------------------------------------------------------------

closeIdx : ℕ → ℕ → ℕ
closeIdx zero    zero    = zero
closeIdx zero    (suc Y) = Y
closeIdx (suc X) zero    = zero
closeIdx (suc X) (suc Y) = suc (closeIdx X Y)

closeIdx-gt : ∀ X Y → X < Y → closeIdx X Y ≡ Y ∸ 1
closeIdx-gt zero (suc Y) lt = refl
closeIdx-gt (suc X) (suc (suc Y)) (s≤s lt) =
  cong suc (closeIdx-gt X (suc Y) lt)

closeIdx-lt : ∀ X Y → Y < X → closeIdx X Y ≡ Y
closeIdx-lt (suc X) zero lt = refl
closeIdx-lt (suc X) (suc Y) (s≤s lt) = cong suc (closeIdx-lt X Y lt)

------------------------------------------------------------------------
-- `closeEnv`, pointwise
------------------------------------------------------------------------

closeEnv-hit : ∀ X S → closeEnv X S X ≡ S
closeEnv-hit X S with X ≟ X
closeEnv-hit X S | yes _ = refl
closeEnv-hit X S | no ne = ⊥-elim (ne refl)

closeEnv-miss : ∀ X S Y → X ≢ᴺ Y → closeEnv X S Y ≡ ` (closeIdx X Y)
closeEnv-miss X S Y ne with X ≟ Y
closeEnv-miss X S Y ne | yes eq = ⊥-elim (ne eq)
closeEnv-miss X S Y ne | no _ with X <? Y
closeEnv-miss X S Y ne | no _ | yes lt = cong `_ (sym (closeIdx-gt X Y lt))
closeEnv-miss X S Y ne | no _ | no ¬lt =
  cong `_ (sym (closeIdx-lt X Y (≤∧≢⇒< (≮⇒≥ ¬lt) (λ eq → ne (sym eq)))))

------------------------------------------------------------------------
-- Going under a binder
------------------------------------------------------------------------

closeEnv-ext : ∀ X S Y
  → extsᵗ (closeEnv X S) Y ≡ closeEnv (suc X) (⇑ᵗ S) Y
closeEnv-ext X S zero = sym (closeEnv-miss (suc X) (⇑ᵗ S) zero (λ ()))
closeEnv-ext X S (suc Y) = go (X ≟ Y)
  where
  -- The decision is taken OUTSIDE the goal: a `with` here would abstract
  -- `closeEnv`'s own internal `with`, and `closeEnv-miss` would no longer
  -- apply to the abstracted form.
  go : Dec (X ≡ Y)
     → extsᵗ (closeEnv X S) (suc Y) ≡ closeEnv (suc X) (⇑ᵗ S) (suc Y)
  go (yes refl) =
    trans (cong ⇑ᵗ (closeEnv-hit X S))
          (sym (closeEnv-hit (suc X) (⇑ᵗ S)))
  go (no ne) =
    trans (cong ⇑ᵗ (closeEnv-miss X S Y ne))
          (sym (closeEnv-miss (suc X) (⇑ᵗ S) (suc Y)
                 (λ { refl → ne refl })))

closeAt-∀ : ∀ X S A → closeAt X S (`∀ A) ≡ `∀ (closeAt (suc X) (⇑ᵗ S) A)
closeAt-∀ X S A = cong `∀ (substᵗ-cong (closeEnv-ext X S) A)

closeAt-hit : ∀ X S → closeAt X S (` X) ≡ S
closeAt-hit = closeEnv-hit

closeAt-miss : ∀ X S Y → X ≢ᴺ Y → closeAt X S (` Y) ≡ ` (closeIdx X Y)
closeAt-miss = closeEnv-miss

-- `closeAt zero` IS the type-level action of a type application: `revTy`'s
-- target at the outermost variable is exactly `⊢•[]`'s result type.
closeEnv-single : ∀ S Y → closeEnv zero S Y ≡ singleTyEnv S Y
closeEnv-single S zero = closeEnv-hit zero S
closeEnv-single S (suc Y) = closeEnv-miss zero S (suc Y) (λ ())

closeAt-single : ∀ S A → closeAt zero S A ≡ A [ S ]ᵗ
closeAt-single S A = substᵗ-cong (closeEnv-single S) A
