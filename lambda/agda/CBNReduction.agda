module CBNReduction where

open import Lambda

------------------------------------------------------------------------
-- Call-by-name one-step and multi-step reduction
------------------------------------------------------------------------

infix  2 _—→_
infix  2 _—↠_

data _—→_ : Term → Term → Set where
  cbn-xi-app1 : ∀ {l l' m} → l —→ l' → (l · m) —→ (l' · m)
  cbn-beta-lam : ∀ {n w} → ((ƛ n) · w) —→ (single-subst n w)

data _—↠_ : Term → Term → Set where
  cbn-refl : ∀ (m : Term) → m —↠ m
  cbn-step : ∀ (l : Term) {m n : Term} → l —→ m → m —↠ n → l —↠ n

cbn-multi-trans : ∀ {m n l} → m —↠ n → n —↠ l → m —↠ l
cbn-multi-trans (cbn-refl _) ms2 = ms2
cbn-multi-trans (cbn-step _ s ms1') ms2 = cbn-step _ s (cbn-multi-trans ms1' ms2)

cbn-appL-cong : ∀ {l l' m} → l —↠ l' → (l · m) —↠ (l' · m)
cbn-appL-cong (cbn-refl _) = cbn-refl _
cbn-appL-cong (cbn-step _ r rs) = cbn-step _ (cbn-xi-app1 r) (cbn-appL-cong rs)
