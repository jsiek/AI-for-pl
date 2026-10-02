module proof.TypeSafety.CoercionTyping where

-- File Charter:
--   * Connects a coercion typing derivation to its computed endpoints.
--   * Records that closing a shifted type at `★` restores that type.

open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

open import Types
open import proof.TypeSubst
open import Ctx
open import Coercion

lower-⇑ : (A : Ty) → lowerᵗ (⇑ᵗ A) ≡ A
lower-⇑ A =
  trans (rename-subst-commute suc (singleTyEnv ★) A)
        (trans (subst-cong (λ X → refl) A) (subst-id A))

mutual
  coercion-src : ∀ {Δ μ p A B}
    → Δ ∣ μ ⊢ᵖ p ∶ A ⟹ B
    → srcᵖ p ≡ A
  coercion-src (⊢id wA) = refl
  coercion-src (⊢tag g) = refl
  coercion-src (⊢tag-var tv mode ok) = refl
  coercion-src (⊢check g) = refl
  coercion-src (⊢check-var tv mode ok) = refl
  coercion-src (⊢fun ⊢p ⊢q) =
    cong₂ _⇒_ (coercion-trg ⊢p) (coercion-src ⊢q)
  coercion-src (⊢all ⊢p) = cong `∀ (coercion-src ⊢p)
  coercion-src (⊢inst ⊢p wB nv occ ns) = cong `∀ (coercion-src ⊢p)
  coercion-src {p = genᵖ p} (⊢gen ⊢p wA nv occ ns safe) =
    trans (cong lowerᵗ (coercion-src ⊢p)) (lower-⇑ _)
  coercion-src (⊢seq ⊢p ⊢q) = coercion-src ⊢p
  coercion-src ⊢bot-elim = refl
  coercion-src ⊢bot-intro = refl

  coercion-trg : ∀ {Δ μ p A B}
    → Δ ∣ μ ⊢ᵖ p ∶ A ⟹ B
    → trgᵖ p ≡ B
  coercion-trg (⊢id wA) = refl
  coercion-trg (⊢tag g) = refl
  coercion-trg (⊢tag-var tv mode ok) = refl
  coercion-trg (⊢check g) = refl
  coercion-trg (⊢check-var tv mode ok) = refl
  coercion-trg (⊢fun ⊢p ⊢q) =
    cong₂ _⇒_ (coercion-src ⊢p) (coercion-trg ⊢q)
  coercion-trg (⊢all ⊢p) = cong `∀ (coercion-trg ⊢p)
  coercion-trg {p = instᵖ p} (⊢inst ⊢p wB nv occ ns) =
    trans (cong lowerᵗ (coercion-trg ⊢p)) (lower-⇑ _)
  coercion-trg (⊢gen ⊢p wA nv occ ns safe) =
    cong `∀ (coercion-trg ⊢p)
  coercion-trg (⊢seq ⊢p ⊢q) = coercion-trg ⊢q
  coercion-trg ⊢bot-elim = refl
  coercion-trg ⊢bot-intro = refl
