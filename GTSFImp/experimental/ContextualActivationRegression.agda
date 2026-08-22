module experimental.ContextualActivationRegression where

-- File Charter:
--   * Retains the former nested-generalization counterexample as a positive
--     regression test for automatic activation.
--   * Shows that removing raw `gen` and `inst` endpoint annotations lets the
--     existing `inst` side conditions support the phase change.
--   * Leaves the live GTSFImp development unchanged.

open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types renaming (`∀ to `∀ᵗ)
import Consistency as C
import experimental.ContextualCoercion as CC
import experimental.ContextualCoercionActivation as CCA

------------------------------------------------------------------------
-- A pending body satisfying all `inst` side conditions
------------------------------------------------------------------------

A : Ty 1
A = ＇ zero ⇒ ★

B-body : Ty 1
B-body = ★ ⇒ ＇ zero

B : Ty 0
B = `∀ᵗ B-body

inner : CC.Coercion 2
inner = CC.inst-in (suc zero) CC.↦ CC.？ CC.id

body : CC.Coercion 1
body = CC.gen inner

focus-in-pending :
  CC.flipCtx (CC.genCtx CC.pending0) (suc zero)
    ≡ CC.inst-in-bound CC.pending
focus-in-pending = refl

gen-variable-ordinary :
  CC.genCtx CC.pending0 zero ≡ CC.ordinary C.★∼X
gen-variable-ordinary = refl

inner-pending :
  CC.genCtx CC.pending0 CC.⊢ inner
    ∶ (＇ suc zero ⇒ ★) ⇒ (★ ⇒ ＇ zero)
inner-pending =
  CC.⊢↦
    (CC.⊢inst-in-pending focus-in-pending)
    (CC.⊢proj
      (CC.generic-X
        (CC.ordinary-entry C.★∼X gen-variable-ordinary))
      (C.★∼Xᵍ refl)
      (CC.⊢id (＇ zero))
      nonstar-X)

body-pending :
  CC.pending0 CC.⊢ body ∶ A ⇒ ⇑ᵗ B
body-pending =
  CC.⊢gen nonvar-fun
    (∈-fun-right ∉-star var-∈)
    inner-pending
    (λ ())

inst-side-conditions :
  CC.ordinaryCtx CC.⊢ CC.inst body ∶ (`∀ᵗ A) ⇒ B
inst-side-conditions =
  CC.⊢inst nonvar-fun (∈-fun-left var-∈) body-pending (λ ())

------------------------------------------------------------------------
-- The unchanged raw body receives the active source type
------------------------------------------------------------------------

body-active :
  CC.active0 CC.⊢ body ∶ (★ ⇒ ★) ⇒ ⇑ᵗ B
body-active = CCA.activate-newest-typing body-pending
