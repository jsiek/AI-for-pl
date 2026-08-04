module
  proof.Right.Core.NuImprecisionRightOpenedInstantiationIndexCounterexample
  where

-- File Charter:
--   * Refutes the uniform right-opened index proposed for target
--     instantiation.
--   * Exhibits compatible initial and final type-imprecision indices and a
--     well-typed InstSafe widening whose matched target binder cannot be
--     reopened as an independent right-only binder.
--   * Contains no term relation, result carrier, postulate, hole, permissive
--     option, or termination bypass.

open import Agda.Builtin.Equality using (refl)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (suc; zero; z<s)
open import Data.Product using (_×_; _,_)

import Coercions as C
open import Imprecision using (_ˣ⊑★; _ˣ⊑ˣ_)
open import ImprecisionWf using
  ( _↦_
  ; _∣_⊢_⊑_⊣_
  ; idˣ
  ; tagˣ
  ; ∀ⁱ_
  ; ν
  )
import NarrowWiden as NW
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import Types using (wf★; wf⇒; ★; ＇_; _⇒_; `∀)


private
  no-matched-variable :
    ((zero ˣ⊑★) ∷ []) ∣ suc zero
      ⊢ ＇ zero ⊑ ＇ zero ⊣ suc zero →
    ⊥
  no-matched-variable (idˣ (here ()) source-bound target-bound)
  no-matched-variable (idˣ (there ()) source-bound target-bound)

  no-independent-right-opening :
    [] ∣ zero
      ⊢ `∀ (＇ zero ⇒ ＇ zero)
        ⊑ (＇ zero ⇒ ＇ zero) ⊣ suc zero →
    ⊥
  no-independent-right-opening
      (ν nonvar occurrence (domain ↦ codomain)) =
    no-matched-variable domain


right-opened-instantiation-index-counterexample :
  ([] ∣ zero
      ⊢ `∀ (＇ zero ⇒ ＇ zero)
        ⊑ `∀ (＇ zero ⇒ ＇ zero) ⊣ zero) ×
  ([] ∣ zero
      ⊢ `∀ (＇ zero ⇒ ＇ zero)
        ⊑ (★ ⇒ ★) ⊣ zero) ×
  (C.tag-or-idᵈ ∣ zero ∣ []
      ⊢ C.inst (★ ⇒ ★)
          (C.seal ★ zero C.↦ C.unseal zero ★)
        ∶ `∀ (＇ zero ⇒ ＇ zero) ⊑ (★ ⇒ ★)) ×
  (([] ∣ zero
      ⊢ `∀ (＇ zero ⇒ ＇ zero)
        ⊑ (＇ zero ⇒ ＇ zero) ⊣ suc zero) →
    ⊥)
right-opened-instantiation-index-counterexample =
  ∀ⁱ
    (idˣ (here refl) z<s z<s ↦
     idˣ (here refl) z<s z<s) ,
  ν Imprecision.nonvar-fun refl
    (tagˣ (here refl) z<s ↦
     tagˣ (here refl) z<s) ,
  (C.cast-inst (wf⇒ wf★ wf★) refl
    (C.cast-fun
      (C.cast-seal wf★ (here refl) refl)
      (C.cast-unseal wf★ (here refl) refl)) ,
   NW.inst
     (NW.safe-fun
       (NW.sealⁿ ★ zero)
       (NW.unsealʷ zero ★))) ,
  no-independent-right-opening
