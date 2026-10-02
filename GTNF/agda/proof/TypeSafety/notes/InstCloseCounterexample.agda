module proof.TypeSafety.notes.InstCloseCounterexample where

-- File Charter:
--   * COUNTEREXAMPLE TO PRESERVATION found in M1 (2026-10-02): the cast
--     rule `Inst` closes its coercion at ★ with the syntactic `closeᵖ 0`,
--     and design.md §3's lemma "if Δ, X:=α ; μ, X:m ⊢ p : A ⇒ B then
--     Δ ; μ ⊢ p[★/X] : A[★/X] ⇒ B[★/X]" is FALSE.  A nested
--     `inst Y. q` whose target is X itself becomes `inst Y. q[★/X]`
--     with target ★, which `⊢inst`'s side condition `NonStar B` (design
--     "B ≠ ★") rejects; no other rule types an `instᵖ`.  The dual case
--     (a nested `gen Y. q` whose SOURCE is X, `NonStar A`) breaks the
--     same way.
--   * THE EXAMPLE (names; de Bruijn below).  Under the outer binder X
--     (mode X∼★), the domain of `p` is flipped, so X has mode ★∼X there
--     and may be checked:
--         q = (Y?ℓ → id(ℕ)) ; (id(★) → ℕ!) ; (★→★)! ; X?ℓ
--           : (Y → ℕ) ⇒ X                         (Y : X∼★, X : ★∼X)
--         r = inst Y. q : ∀Y. (Y → ℕ) ⇒ X
--         p = r → id(ℕ) : (X → ℕ) ⇒ (∀Y. (Y → ℕ)) → ℕ
--         V = ΛX. λx:X. 1 : ∀X. X → ℕ
--     `V ⟨inst X. p⟩` is well typed at `(∀Y. (Y → ℕ)) → ℕ` in the empty
--     context and steps by `Inst` to `(ν X:=★. …) ⟨p[★/X]⟩`, where
--     `p[★/X] = inst Y. (… ; id(★)) → id(ℕ)` has no typing at all.
--   * GTSFImp does not have the bug: its `subst∼` (Consistency.agda) is
--     type-directed and re-factors an `inst` whose target became ★
--     (`factor-inst-star`, `factor-gen-star`); its coercions are normal
--     forms, so the offending `inst` there ends in a tag `G!`, which it
--     pulls out of the `inst`.
--   * `preservation-false : ¬ Preservation` below is the checked claim.

open import Data.Nat using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Types
open import Ctx
open import proof.Ctx using (wf-empty)
open import Conversion using (reveal)
open import Coercion
open import Terms hiding (`_)
open import Reduction
open import TypeSafety using (Preservation)

ℓ : Label
ℓ = 0

-- under Y (index 0) and X (index 1)
q : Coercion
q = ((((` 0) ？ ℓ) ↦ᵖ idᵖ `ℕ) ︔ (idᵖ ★ ↦ᵖ (`ℕ !))) ︔ ((★ ⇒ ★) !)
      ︔ ((` 1) ？ ℓ)

-- under X (index 0)
p : Coercion
p = (instᵖ q) ↦ᵖ idᵖ `ℕ

V : Term
V = Λ (ƛ (` 0) ∙ ($ 1))

A B : Ty
A = ` 0 ⇒ `ℕ
B = `∀ (` 0 ⇒ `ℕ) ⇒ `ℕ

M : Term
M = V ⟨ [] ∣ instᵖ p ⟩

------------------------------------------------------------------------
-- The redex is well typed
------------------------------------------------------------------------

Δ₁ Δ₂ : Ctxᵗ
Δ₁ = underΛ empty
Δ₂ = underΛ Δ₁

tv₁-0 : Δ₁ ∋tv 0
tv₁-0 = zero , here

tv₂-0 : Δ₂ ∋tv 0
tv₂-0 = zero , here

tv₂-1 : Δ₂ ∋tv 1
tv₂-1 = suc zero , there here

⊢q : Δ₂ ∣ X∼★ ∷ ★∼X ∷ [] ⊢ᵖ q ∶ ` 0 ⇒ `ℕ ⟹ ` 1
⊢q = ⊢seq (⊢seq (⊢seq
        (⊢fun (⊢check-var tv₂-0 here check-dyn) (⊢id wf-ℕ))
        (⊢fun (⊢id wf-★) (⊢tag g-ℕ)))
        (⊢tag g-⇒))
        (⊢check-var tv₂-1 (there here) check-dyn)

⊢r : Δ₁ ∣ ★∼X ∷ [] ⊢ᵖ instᵖ q ∶ `∀ (` 0 ⇒ `ℕ) ⟹ ` 0
⊢r = ⊢inst ⊢q (wf-var tv₁-0) nv-⇒ (∈-⇒ˡ ∈-var) ns-var

⊢p : Δ₁ ∣ X∼★ ∷ [] ⊢ᵖ p ∶ A ⟹ ⇑ᵗ B
⊢p = ⊢fun ⊢r (⊢id wf-ℕ)

wf-B : empty ⊢ᵗ B
wf-B = wf-⇒ (wf-∀ (wf-⇒ (wf-var tv₁-0) wf-ℕ)) wf-ℕ

⊢V : empty ∣ [] ⊢ V ⦂ `∀ A
⊢V = ⊢Λ (V-simple S-ƛ) (⊢ƛ (wf-var tv₁-0) ⊢$)

⊢M : empty ∣ [] ⊢ M ⦂ B
⊢M = ⊢cast ⊢V (⊢inst ⊢p wf-B nv-⇒ (∈-⇒ˡ ∈-var) ns-⇒) refl

------------------------------------------------------------------------
-- It steps by Inst
------------------------------------------------------------------------

M′ : Term
M′ = (ν ★ · V ⟨ reveal 0 (srcᵖ p) ⟩) ⟨ [] ∣ closeᵖ 0 p ⟩

step : empty ⊢ M -→ M′ ∣ none
step = Inst (V-simple (S-Λ (V-simple S-ƛ)))

------------------------------------------------------------------------
-- The closed coercion has no typing
------------------------------------------------------------------------

-- the nested inst's body now ENDS in id(★)
_ : closeᵖ 0 p
    ≡ (instᵖ (((((` 0) ？ ℓ ↦ᵖ idᵖ `ℕ) ︔ (idᵖ ★ ↦ᵖ (`ℕ !))) ︔ ((★ ⇒ ★) !))
              ︔ idᵖ ★)) ↦ᵖ idᵖ `ℕ
_ = refl

seq-id★-target : ∀ {Δ μ c C D}
  → Δ ∣ μ ⊢ᵖ c ︔ idᵖ ★ ∶ C ⟹ D → D ≡ ★
seq-id★-target (⊢seq _ (⊢id _)) = refl

⇑-★ : ∀ {C} → ⇑ᵗ C ≡ ★ → C ≡ ★
⇑-★ {★} refl = refl
⇑-★ {` _} ()
⇑-★ {`ℕ} ()
⇑-★ {`𝔹} ()
⇑-★ {_ ⇒ _} ()
⇑-★ {`∀ _} ()

nonstar-★ : ¬ NonStar ★
nonstar-★ ()

closed-untyped : ∀ {Δ μ C D} → ¬ (Δ ∣ μ ⊢ᵖ closeᵖ 0 p ∶ C ⟹ D)
closed-untyped (⊢fun (⊢inst {B = E} ⊢q′ _ _ _ ns) _)
  with ⇑-★ {E} (seq-id★-target ⊢q′)
closed-untyped (⊢fun (⊢inst {B = E} ⊢q′ _ _ _ ns) _) | refl =
  nonstar-★ ns

M′-untyped : ∀ {Δ C} → ¬ (Δ ∣ [] ⊢ M′ ⦂ C)
M′-untyped (⊢cast _ ⊢c _) = closed-untyped ⊢c

preservation-false : ¬ Preservation
preservation-false pres = M′-untyped (pres wf-empty ⊢M step)
