module FullBetaReduction where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Lambda

------------------------------------------------------------------------
-- Neutral and normal terms
------------------------------------------------------------------------

mutual
  data Neutral : Term → Set where
    neu-var : ∀ {x} → Neutral (′ x)
    neu-app : ∀ {l m} → Neutral l → Normal m → Neutral (l · m)

  data Normal : Term → Set where
    norm-neu : ∀ {m} → Neutral m → Normal m
    norm-lam : ∀ {N} → Normal N → Normal (ƛ N)

------------------------------------------------------------------------
-- Full-beta reduction
------------------------------------------------------------------------

infix  2 _—→_
infix  2 _—↠_

data Step : Term → Term → Set where
  xi-lam  : ∀ {N N'} → Step N N' → Step (ƛ N) (ƛ N')
  xi-app1 : ∀ {L L' M} → Step L L' → Step (L · M) (L' · M)
  xi-app2 : ∀ {L M M'} → Step M M' → Step (L · M) (L · M')
  beta-lam : ∀ {N M} → Step ((ƛ N) · M) (N [ M ])

_—→_ : Term → Term → Set
L —→ L' = Step L L'

------------------------------------------------------------------------
-- Normal and Neutral terms are not reducible
------------------------------------------------------------------------

NeutralIsNotReducible : (M : Term) → (Neutral M) → ¬ (Σ Term (λ N → Step M N))
NormalIsNotReducible : (M : Term) → (Normal M) → ¬ (Σ Term (λ N → Step M N))

NormalIsNotReducible (′ x) n = λ ()
NormalIsNotReducible (ƛ M) (norm-lam n) = λ { (N , xi-lam r) → let IH = NormalIsNotReducible M n in IH (_ , r)}
NormalIsNotReducible (L · M) (norm-neu (neu-app l m)) (N , xi-app1 L→N) =
  let IH1 = NeutralIsNotReducible L l in
  IH1 (_ , L→N)  
NormalIsNotReducible (L · M) (norm-neu (neu-app l m)) (N , xi-app2 M→N) =
  let IH2 = NormalIsNotReducible M m in
  IH2 (_ , M→N)

NeutralIsNotReducible (′ x) neu-var = λ ()
NeutralIsNotReducible (L · M) (neu-app l m) (N , xi-app1 L→L') =
  NeutralIsNotReducible L l (_ , L→L')
NeutralIsNotReducible (L · M) (neu-app l m) (N , xi-app2 M→M') =
  NormalIsNotReducible M m (_ , M→M')

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

progress : (m : Term) → (Normal m) ⊎ (Σ Term (λ n → Step m n))
progress (′ i) = inj₁ (norm-neu neu-var)
progress (ƛ n) with progress n
... | inj₁ hn = inj₁ (norm-lam hn)
... | inj₂ (n' , s) = inj₂ (ƛ n' , xi-lam s)
progress (l · r) with progress l
... | inj₂ (l' , sl) = inj₂ (l' · r , xi-app1 sl)
... | inj₁ hl with progress r
...   | inj₂ (r' , sr) = inj₂ (l · r' , xi-app2 sr)
...   | inj₁ hr with hl
...     | norm-neu hneu = inj₁ (norm-neu (neu-app hneu hr))
...     | norm-lam {n} hn = inj₂ (n [ r ] , beta-lam)

------------------------------------------------------------------------
-- Multi-step reduction
------------------------------------------------------------------------

data MultiStep : Term → Term → Set where
  ms-refl : ∀ (M : Term) → MultiStep M M
  ms-step : ∀ (L : Term) {M N : Term} → Step L M → MultiStep M N → MultiStep L N

_—↠_ : Term → Term → Set
L —↠ L' = MultiStep L L'

infix 3 _∎
pattern _∎ M = ms-refl M

infixr 2 _—→⟨_⟩_
pattern _—→⟨_⟩_ L L—→M M—↠N = ms-step L L—→M M—↠N

multi-trans : ∀ {M N L} → M —↠ N → N —↠ L → M —↠ L
multi-trans (ms-refl _) MS2 = MS2
multi-trans (ms-step M S MS1') MS2 = ms-step M S (multi-trans MS1' MS2)

infixr 2 _—↠⟨_⟩_
_—↠⟨_⟩_ : ∀ (L : Term) {M N : Term}
    → L —↠ M
    → M —↠ N
      ---------
    → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N = multi-trans L—↠M M—↠N

appL-cong : ∀ {L L' M} → L —↠ L' → (L · M) —↠ (L' · M)
appL-cong {M = M} (ms-refl L) = (L · M) ∎
appL-cong {M = M} (ms-step L {M = L1} {N = L2} R RS) =
  (L · M)
    —→⟨ xi-app1 R ⟩
  (L1 · M)
    —↠⟨ appL-cong RS ⟩
  (L2 · M) ∎

appR-cong : ∀ {L M M'} → M —↠ M' → (L · M) —↠ (L · M')
appR-cong {L = L} (ms-refl M) = (L · M) ∎
appR-cong {L = L} (ms-step M {M = M1} {N = M2} R RS) =
  (L · M)
    —→⟨ xi-app2 R ⟩
  (L · M1)
    —↠⟨ appR-cong RS ⟩
  (L · M2) ∎

app-cong : ∀ {L L' M M'} → L —↠ L' → M —↠ M' → (L · M) —↠ (L' · M')
app-cong {L = L} {L' = L'} {M = M} {M' = M'} L—↠L' M—↠M' =
  (L · M)
    —↠⟨ appL-cong L—↠L' ⟩
  (L' · M)
    —↠⟨ appR-cong M—↠M' ⟩
  (L' · M') ∎

lam-cong : ∀ {N N'} → N —↠ N' → (ƛ N) —↠ (ƛ N')
lam-cong (ms-refl N) = (ƛ N) ∎
lam-cong (ms-step N {M = N1} {N = N2} R RS) =
  (ƛ N)
    —→⟨ xi-lam R ⟩
  (ƛ N1)
    —↠⟨ lam-cong RS ⟩
  (ƛ N2) ∎
