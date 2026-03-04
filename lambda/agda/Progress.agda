module Progress where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Lambda
open import FullBetaReduction

progress : (m : Term) → (Normal m) ⊎ (Σ Term (λ n → Step m n))
progress (var i) = inj1 (norm-neu neu-var)
progress (lam n) with progress n
... | inj1 hn = inj1 (norm-lam hn)
... | inj2 (n' , s) = inj2 (lam n' , xi-lam s)
progress (app l r) with progress l
... | inj2 (l' , sl) = inj2 (app l' r , xi-app1 sl)
... | inj1 hl with progress r
...   | inj2 (r' , sr) = inj2 (app l r' , xi-app2 sr)
...   | inj1 hr with hl
...     | norm-neu hneu = inj1 (norm-neu (neu-app hneu hr))
...     | norm-lam {n} hn = inj2 (single-subst n r , beta-lam)
