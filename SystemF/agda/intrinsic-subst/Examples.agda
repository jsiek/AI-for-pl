module intrinsic-subst.Examples where

-- File Charter:
--   * Example System F programs with reduction sequences that end at
--     natural-number constants.
--   * They check that type instantiation `N [ B ]ᵀ` and term substitution
--     `N [ M ]`, defined by the kit library, compute: in particular
--     `apply-id` instantiates a term that contains a type application, so
--     its reduction goes through the cast in the `_∙_` clause of `travᵀ`.

open import intrinsic-subst.Types
open import intrinsic-subst.Ctx
open import intrinsic-subst.Terms
open import intrinsic-subst.Reduction

-- the polymorphic identity: Λα. λ(x : α). x
id : ∅ ∣ ∅ ⊢ `∀ (` Z ⇒ ` Z)
id = Λ (ƛ (` Z) ˙ (` Z))

id-zero : ∅ ∣ ∅ ⊢ `Nat
id-zero = id ∙ `Nat · `zero

id-zero-↠ : id-zero —↠ `zero
id-zero-↠ =
    id ∙ `Nat · `zero
  —→⟨ ξ-·₁ β-Λ ⟩
    (ƛ `Nat ˙ ` Z) · `zero
  —→⟨ β-ƛ V-zero ⟩
    `zero
  ∎

-- Λα. λ(f : ∀β. β → β). f [α]
apply-id : ∅ ∣ ∅ ⊢ `∀ (`∀ (` Z ⇒ ` Z) ⇒ (` Z ⇒ ` Z))
apply-id = Λ (ƛ (`∀ (` Z ⇒ ` Z)) ˙ (` Z ∙ ` Z))

apply-id-suc : ∅ ∣ ∅ ⊢ `Nat
apply-id-suc = apply-id ∙ `Nat · id · `suc `zero

apply-id-suc-↠ : apply-id-suc —↠ `suc `zero
apply-id-suc-↠ =
    apply-id ∙ `Nat · id · `suc `zero
  —→⟨ ξ-·₁ (ξ-·₁ β-Λ) ⟩
    (ƛ (`∀ (` Z ⇒ ` Z)) ˙ (` Z ∙ `Nat)) · id · `suc `zero
  —→⟨ ξ-·₁ (β-ƛ V-Λ) ⟩
    id ∙ `Nat · `suc `zero
  —→⟨ ξ-·₁ β-Λ ⟩
    (ƛ `Nat ˙ ` Z) · `suc `zero
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc `zero
  ∎

-- case analysis under a binder: λ(n : ℕ). case n [zero ⇒ true | suc m ⇒
-- false], applied to 1
is-zero : ∅ ∣ ∅ ⊢ `Nat ⇒ `Bool
is-zero = ƛ `Nat ˙ `case-nat (` Z) `true `false

is-zero-one : ∅ ∣ ∅ ⊢ `Bool
is-zero-one = is-zero · `suc `zero

is-zero-one-↠ : is-zero-one —↠ `false
is-zero-one-↠ =
    is-zero · `suc `zero
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    `case-nat (`suc `zero) `true `false
  —→⟨ β-suc V-zero ⟩
    `false
  ∎
