module CBNBigStep where

open import Lambda
open import CBNReduction

------------------------------------------------------------------------
-- Big-step call-by-name evaluation
------------------------------------------------------------------------

data Eval : Term → Term → Set where
  ev-var : ∀ {i} → Eval (var i) (var i)
  ev-lam : ∀ {n} → Eval (lam n) (lam n)
  ev-app : ∀ {l m n v} → Eval l (lam n) → Eval (single-subst n m) v → Eval (app l m) v

eval-to-multistep : ∀ {m n} → Eval m n → CbnMultiStep m n
eval-to-multistep ev-var = cbn-refl _
eval-to-multistep ev-lam = cbn-refl _
eval-to-multistep (ev-app {l} {m} {n} {v} hl hbody) =
  cbn-multi-trans hsL (cbn-multi-trans hsBeta (eval-to-multistep hbody))
  where
    hsL : CbnMultiStep (app l m) (app (lam n) m)
    hsL = cbn-appL-cong (eval-to-multistep hl)

    hsBeta : CbnMultiStep (app (lam n) m) (single-subst n m)
    hsBeta = cbn-step _ cbn-beta-lam (cbn-refl _)

cbn-step-bigstep-value : ∀ {m n v} → CbnStep m n → Eval n v → Value v → Eval m v
cbn-step-bigstep-value (cbn-xi-app1 s) (ev-app hl hbody) _ =
  ev-app (cbn-step-bigstep-value s hl v-lam) hbody
cbn-step-bigstep-value cbn-beta-lam hev _ = ev-app ev-lam hev

eval-value : ∀ {m v} → Eval m v → Value v
eval-value ev-var = v-var
eval-value ev-lam = v-lam
eval-value (ev-app _ hbody) = eval-value hbody

value-eval : ∀ {v} → Value v → Eval v v
value-eval v-var = ev-var
value-eval v-lam = ev-lam

cbn-multistep-bigstep : ∀ {m n v} → CbnMultiStep m n → Eval n v → Eval m v
cbn-multistep-bigstep (cbn-refl _) hev = hev
cbn-multistep-bigstep (cbn-step _ s ms) hev =
  cbn-step-bigstep-value s hmid (eval-value hmid)
  where
    hmid = cbn-multistep-bigstep ms hev

cbn-multistep-to-value-bigstep : ∀ {m v} → CbnMultiStep m v → Value v → Eval m v
cbn-multistep-to-value-bigstep hsteps hval = cbn-multistep-bigstep hsteps (value-eval hval)
