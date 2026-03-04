module FullBetaReduction where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Lambda

------------------------------------------------------------------------
-- 1. Neutral and normal terms
------------------------------------------------------------------------

mutual
  data Neutral : Term → Set where
    neu-var : ∀ {i} → Neutral (var i)
    neu-app : ∀ {l m} → Neutral l → Normal m → Neutral (app l m)

  data Normal : Term → Set where
    norm-neu : ∀ {m} → Neutral m → Normal m
    norm-lam : ∀ {n} → Normal n → Normal (lam n)

------------------------------------------------------------------------
-- 2. Full-beta reduction
------------------------------------------------------------------------

data Step : Term → Term → Set where
  xi-lam  : ∀ {n n'} → Step n n' → Step (lam n) (lam n')
  xi-app1 : ∀ {l l' m} → Step l l' → Step (app l m) (app l' m)
  xi-app2 : ∀ {l m m'} → Step m m' → Step (app l m) (app l m')
  beta-lam : ∀ {n w} → Step (app (lam n) w) (single-subst n w)

------------------------------------------------------------------------
-- 3. Progress
------------------------------------------------------------------------

progress : (m : Term) → (Normal m) ⊎ (Σ Term (λ n → Step m n))
progress (var i) = inj₁ (norm-neu neu-var)
progress (lam n) with progress n
... | inj₁ hn = inj₁ (norm-lam hn)
... | inj₂ (n' , s) = inj₂ (lam n' , xi-lam s)
progress (app l r) with progress l
... | inj₂ (l' , sl) = inj₂ (app l' r , xi-app1 sl)
... | inj₁ hl with progress r
...   | inj₂ (r' , sr) = inj₂ (app l r' , xi-app2 sr)
...   | inj₁ hr with hl
...     | norm-neu hneu = inj₁ (norm-neu (neu-app hneu hr))
...     | norm-lam {n} hn = inj₂ (single-subst n r , beta-lam)

------------------------------------------------------------------------
-- 4. Multi-step reduction
------------------------------------------------------------------------

data MultiStep : Term → Term → Set where
  ms-refl : ∀ (m : Term) → MultiStep m m
  ms-step : ∀ (l : Term) {m n : Term} → Step l m → MultiStep m n → MultiStep l n

multi-trans : ∀ {m n l} → MultiStep m n → MultiStep n l → MultiStep m l
multi-trans (ms-refl _) ms2 = ms2
multi-trans (ms-step _ s ms1') ms2 = ms-step _ s (multi-trans ms1' ms2)

appL-cong : ∀ {l l' m} → MultiStep l l' → MultiStep (app l m) (app l' m)
appL-cong (ms-refl _) = ms-refl _
appL-cong (ms-step _ r rs) = ms-step _ (xi-app1 r) (appL-cong rs)

appR-cong : ∀ {l m m'} → MultiStep m m' → MultiStep (app l m) (app l m')
appR-cong (ms-refl _) = ms-refl _
appR-cong (ms-step _ r rs) = ms-step _ (xi-app2 r) (appR-cong rs)

app-cong : ∀ {l l' m m'} → MultiStep l l' → MultiStep m m' → MultiStep (app l m) (app l' m')
app-cong l2l' m2m' = multi-trans (appL-cong l2l') (appR-cong m2m')

lam-cong : ∀ {n n'} → MultiStep n n' → MultiStep (lam n) (lam n')
lam-cong (ms-refl _) = ms-refl _
lam-cong (ms-step _ r rs) = ms-step _ (xi-lam r) (lam-cong rs)

