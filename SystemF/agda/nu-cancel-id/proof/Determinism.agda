module nu-cancel-id.proof.Determinism where

-- File Charter:
--   * THE PROOF OF DETERMINISM of νF₁ᶜ: a term has at most one step, and
--     the step's allocation is unique too.  Unlike strong-rep-nu's `det`
--     it needs no typing derivation: the left-hand sides are disjoint on
--     the syntax alone (Design.md §8).
--   * §1 values do not step (`value-¬step`), with `fun-¬sealed`, which
--     keeps Swap off a hide over a reveal of a functional value.  §2
--     TyBeta's instantiation is a function.  §3 `det`.
--   * The public statements are nu-cancel-id.Determinism.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)

open import nu-cancel-id.Types
open import nu-cancel-id.Ctx
open import nu-cancel-id.Terms
open import nu-cancel-id.Reduction
open import nu-cancel-id.proof.Flags using (⇝-unique)

private
  variable
    Γ : Ctx
    s : Sign
    α : ℕ
    a a′ : Alloc
    c : Conv
    M M₁ M₂ N N′ V F : Term

------------------------------------------------------------------------
-- 1. Values do not step
------------------------------------------------------------------------

fun-¬sealed : Fun F → Sealed F → ⊥
fun-¬sealed F-ƛ          ()
fun-¬sealed F-Λ          ()
fun-¬sealed (F-↦ v)      ()
fun-¬sealed (F-∀ v)      ()
fun-¬sealed (F-id⁺ F)    (S-rev s) = fun-¬sealed F s
fun-¬sealed (F-id⁻ F nr) ()

value-¬step : Value V → ¬ (Γ ⊢ V ⟶ N ∣ a)
fun-¬step : Fun F → ¬ (Γ ⊢ F ⟶ N ∣ a)
sealed-¬step : Sealed V → ¬ (Γ ⊢ V ⟶ N ∣ a)

value-¬step V-$          ()
value-¬step (V-fun F)    st = fun-¬step F st
value-¬step (V-sealed s) st = sealed-¬step s st

fun-¬step F-ƛ          ()
fun-¬step F-Λ          ()
fun-¬step (F-↦ v)      (ξ-[] st)       = value-¬step v st
fun-¬step (F-∀ v)      (ξ-[] st)       = value-¬step v st
fun-¬step (F-id⁺ ())   id-$
fun-¬step (F-id⁺ F)    (ξ-[] st)       = fun-¬step F st
fun-¬step (F-id⁻ () _) id-$
fun-¬step (F-id⁻ F nr) (cancel-id u)   = nr refl
fun-¬step (F-id⁻ () _) (sink _ _)
fun-¬step (F-id⁻ (F-id⁺ F) nr) (swap _ s) = fun-¬sealed F s
fun-¬step (F-id⁻ F nr) (ξ-[] st)       = fun-¬step F st

sealed-¬step (S-seal w) (ξ-[] st) = value-¬step w st
sealed-¬step (S-rev ()) id-$
sealed-¬step (S-rev s)  (ξ-[] st) = sealed-¬step s st

------------------------------------------------------------------------
-- 2. TyBeta's instantiation is a function
------------------------------------------------------------------------

•⟶-unique : V •⟶ N → V •⟶ N′ → N ≡ N′
•⟶-unique inst-Λ       inst-Λ        = refl
•⟶-unique (inst-∀ i)  (inst-∀ i′)  = cong (λ N → [ _ , _ ] N ⟨ _ ⟩)
                                          (•⟶-unique i i′)
•⟶-unique (inst-id i) (inst-id i′) = cong (λ N → [ _ , _ ] N ⟨ _ ⟩)
                                          (•⟶-unique i i′)

------------------------------------------------------------------------
-- 3. Determinism
------------------------------------------------------------------------

det : Γ ⊢ M ⟶ M₁ ∣ a → Γ ⊢ M ⟶ M₂ ∣ a′ → M₁ ≡ M₂ × a ≡ a′

-- Beta
det (β-ƛ w)     (β-ƛ w′)     = refl , refl
det (β-ƛ w)     (ξ-·₂ v st)  = ⊥-elim (value-¬step w st)
det (ξ-·₂ v st) (β-ƛ w)      = ⊥-elim (value-¬step w st)

-- Wrap, Wrap-id
det (wrap v w)     (wrap v′ w′)    = refl , refl
det (wrap v w)     (ξ-·₁ st)       = ⊥-elim (value-¬step (V-fun (F-↦ v)) st)
det (wrap v w)     (ξ-·₂ u st)     = ⊥-elim (value-¬step w st)
det (ξ-·₁ st)      (wrap v w)      = ⊥-elim (value-¬step (V-fun (F-↦ v)) st)
det (ξ-·₂ u st)    (wrap v w)      = ⊥-elim (value-¬step w st)
det (wrap-id u w)  (wrap-id u′ w′) = refl , refl
det (wrap-id u w)  (ξ-·₁ st)       = ⊥-elim (value-¬step u st)
det (wrap-id u w)  (ξ-·₂ u′ st)    = ⊥-elim (value-¬step w st)
det (ξ-·₁ st)      (wrap-id u w)   = ⊥-elim (value-¬step u st)
det (ξ-·₂ u′ st)   (wrap-id u w)   = ⊥-elim (value-¬step w st)

-- TyBeta: the payload's spelling and the instantiation are functions
det (tyβ sp v i) (tyβ sp′ v′ i′)
  with ⇝-unique sp sp′ | •⟶-unique i i′
... | refl | refl = refl , refl
det (tyβ sp v i) (ξ-ν st) = ⊥-elim (value-¬step v st)
det (ξ-ν st) (tyβ sp v i) = ⊥-elim (value-¬step v st)

-- Id
det id-$ id-$ = refl , refl
det id-$ (ξ-[] ())
det (ξ-[] ()) id-$

-- Cancel-□ and Push: the unseal is over a seal, or over a reveal
det (cancel-□ w) (cancel-□ w′) = refl , refl
det (cancel-□ w) (ξ-[] st) = ⊥-elim (value-¬step (V-sealed (S-seal w)) st)
det (ξ-[] st) (cancel-□ w) = ⊥-elim (value-¬step (V-sealed (S-seal w)) st)
det (push s) (push s′) = refl , refl
det (push s) (ξ-[] st) = ⊥-elim (sealed-¬step (S-rev s) st)
det (ξ-[] st) (push s) = ⊥-elim (sealed-¬step (S-rev s) st)

-- CancelId, Sink and Swap: the hide is over a reveal of its own cell,
-- a seal, or a reveal of another cell
det (cancel-id u)  (cancel-id u′) = refl , refl
det (cancel-id u)  (swap α≢α s)   = ⊥-elim (α≢α refl)
det (swap α≢α s)   (cancel-id u)  = ⊥-elim (α≢α refl)
det (cancel-id u)  (ξ-[] st)      = ⊥-elim (value-¬step u st)
det (ξ-[] st)      (cancel-id u)  = ⊥-elim (value-¬step u st)
det (sink α≢β v)   (sink α≢β′ v′) = refl , refl
det (sink α≢β v)   (ξ-[] st) =
  ⊥-elim (value-¬step (V-sealed (S-seal v)) st)
det (ξ-[] st)      (sink α≢β v) =
  ⊥-elim (value-¬step (V-sealed (S-seal v)) st)
det (swap α≢β s)   (swap α≢β′ s′) = refl , refl
det (swap α≢β s)   (ξ-[] st)      = ⊥-elim (sealed-¬step (S-rev s) st)
det (ξ-[] st)      (swap α≢β s)   = ⊥-elim (sealed-¬step (S-rev s) st)

-- the congruences: the sibling shift is a function of the allocation
det (ξ-·₁ st) (ξ-·₁ st′) with det st st′
... | refl , refl = refl , refl
det (ξ-·₁ st) (ξ-·₂ v st′) = ⊥-elim (value-¬step v st)
det (ξ-·₂ v st) (ξ-·₁ st′) = ⊥-elim (value-¬step v st′)
det (ξ-·₂ v st) (ξ-·₂ v′ st′) with det st st′
... | refl , refl = refl , refl
det (ξ-ν st) (ξ-ν st′) with det st st′
... | refl , refl = refl , refl
det (ξ-[] st) (ξ-[] st′) with det st st′
... | refl , refl = refl , refl
