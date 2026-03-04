module CBNReduction where

open import Lambda

------------------------------------------------------------------------
-- Call-by-name one-step and multi-step reduction
------------------------------------------------------------------------

data CbnStep : Term → Term → Set where
  cbn-xi-app1 : ∀ {l l' m} → CbnStep l l' → CbnStep (app l m) (app l' m)
  cbn-beta-lam : ∀ {n w} → CbnStep (app (lam n) w) (single-subst n w)

data CbnMultiStep : Term → Term → Set where
  cbn-refl : ∀ (m : Term) → CbnMultiStep m m
  cbn-step : ∀ (l : Term) {m n : Term} → CbnStep l m → CbnMultiStep m n → CbnMultiStep l n

cbn-multi-trans : ∀ {m n l} → CbnMultiStep m n → CbnMultiStep n l → CbnMultiStep m l
cbn-multi-trans (cbn-refl _) ms2 = ms2
cbn-multi-trans (cbn-step _ s ms1') ms2 = cbn-step _ s (cbn-multi-trans ms1' ms2)

cbn-appL-cong : ∀ {l l' m} → CbnMultiStep l l' → CbnMultiStep (app l m) (app l' m)
cbn-appL-cong (cbn-refl _) = cbn-refl _
cbn-appL-cong (cbn-step _ r rs) = cbn-step _ (cbn-xi-app1 r) (cbn-appL-cong rs)
