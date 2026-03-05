module FullBetaConfluence where

------------------------------------------------------------------------
-- Proof roadmap
--
-- Goal: (Confluence of full beta reduction)
--   If M —↠ N and M —↠ P then ∃ Q, N —↠ Q and P —↠ Q.
--
--                   M
--                  / \
--              —↠ /   \ —↠
--                /     \
--               N       P
--                \     /
--            —↠   \   /   —↠
--                  \ /
--                   Q
--
-- Strategy:
--   1) Define parallel reduction (_⇛_) and its reflexive-transitive
--      closure (_⇛*_).
--   2) Relate ordinary reduction and parallel sequences:
--      M ⇛* N  iff  M —↠ N
--   3) Prove local diamond for parallel reduction via complete
--      development (_⁺) and triangle:
--        par-triangle : M ⇛ N  implies  N ⇛ M⁺
--                   M
--                  /
--               ⇛ /
--                /
--               N
--                \
--               ⇛ \
--                  \ 
--                   M⁺
--      giving:
--        ⇛-diamond : M ⇛ N and M ⇛ P implies ∃ Q, N ⇛ Q and P ⇛ Q
--
--                   M
--                  / \
--               ⇛ /   \ ⇛
--                /     \
--               N       P
--                \     /
--             ⇛   \   /   ⇛
--                  \ /
--                   Q
--
--
--   4) Lift local diamond to sequences:
--        strip
--        pars-confluent
--
--                   M
--                  / \
--             ⇛*  /   \  ⇛*
--                /     \
--               N       P
--                \     /
--            ⇛*   \   /   ⇛*
--                  \ /
--                   Q
--
--   5) Transport confluence back to ordinary multi-step reduction
--
--                   M
--                  / \
--              —↠ /   \ —↠
--                /     \
--               N       P
--                \     /
--            —↠   \   /   —↠
--                  \ /
--                   Q
--
------------------------------------------------------------------------

open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_)
open import Lambda
open import FullBetaReduction
open import Subst using
  (single-subst-def; rename-subst; rename-subst-commute; subst-cong;
   seq; cons-sub; sub-sub; exts-sub-cons)

------------------------------------------------------------------------
-- Confluence statement
------------------------------------------------------------------------

Confluent : Set
Confluent =
  ∀ {M N P} → M —↠ N → M —↠ P →
    Σ[ Q ∈ Term ] (N —↠ Q) × (P —↠ Q)

------------------------------------------------------------------------
-- Parallel Reduction
-- M ⇛ N
-- if N is the result of contracting zero or more of the redexes in M 
------------------------------------------------------------------------

infix 2 _⇛_
infix  2 _⇛*_
infixr 2 _⇛⟨_⟩_
infix  3 _■

data _⇛_ : Term → Term → Set where
  par-var  : ∀ {x} → (′ x) ⇛ (′ x)
  par-lam  : ∀ {N N'} → N ⇛ N' → (ƛ N) ⇛ (ƛ N')
  par-app  : ∀ {L L' M M'} → L ⇛ L' → M ⇛ M' → (L · M) ⇛ (L' · M')
  par-beta : ∀ {N N' M M'} → N ⇛ N' → M ⇛ M' → ((ƛ N) · M) ⇛ (N' [ M' ])

data _⇛*_ : Term → Term → Set where
  _■ : (M : Term) → M ⇛* M
  _⇛⟨_⟩_ : (L : Term) {M N : Term}
    → L ⇛ M
    → M ⇛* N
    → L ⇛* N

------------------------------------------------------------------------
-- Parallel multi-reduction is equivalent to arrow-star reduction
-- M ⇛* N  iff  M —↠ N
------------------------------------------------------------------------

⇛-refl : ∀ {M} → M ⇛ M
⇛-refl {M = ′ I} = par-var
⇛-refl {M = ƛ N} = par-lam ⇛-refl
⇛-refl {M = L · M} = par-app ⇛-refl ⇛-refl

⇛*-trans : ∀ {L M N} → L ⇛* M → M ⇛* N → L ⇛* N
⇛*-trans (L ■) M⇛*N = M⇛*N
⇛*-trans (L ⇛⟨ L⇛M ⟩ M⇛*N) M⇛*P = L ⇛⟨ L⇛M ⟩ ⇛*-trans M⇛*N M⇛*P

→-to-⇛ : ∀ {M N} → M —→ N → M ⇛ N
→-to-⇛ (xi-lam S) = par-lam (→-to-⇛ S)
→-to-⇛ (xi-app1 S) = par-app (→-to-⇛ S) ⇛-refl
→-to-⇛ (xi-app2 S) = par-app ⇛-refl (→-to-⇛ S)
→-to-⇛ beta-lam = par-beta ⇛-refl ⇛-refl

betas-pars : ∀ {M N} → M —↠ N → M ⇛* N
betas-pars (ms-refl M) = M ■
betas-pars (ms-step L S MS) = L ⇛⟨ →-to-⇛ S ⟩ betas-pars MS

par-betas : ∀{M N : Term}
  → M ⇛ N
    ------
  → M —↠ N
par-betas {′ x} (par-var) = (′ x) ∎
par-betas {ƛ N} (par-lam p) = lam-cong (par-betas p)
par-betas {L · M} (par-app {L = L}{L′}{M}{M′} p₁ p₂) =
    L · M   —↠⟨ appL-cong{M = M} (par-betas p₁) ⟩
    L′ · M  —↠⟨ appR-cong (par-betas p₂) ⟩
    L′ · M′
    ∎
par-betas {(ƛ N) · M} (par-beta{N' = N′}{M' = M′} p₁ p₂) =
    (ƛ N) · M                    —↠⟨ appL-cong{M = M} (lam-cong (par-betas p₁)) ⟩
    (ƛ N′) · M                   —↠⟨ appR-cong{L = ƛ N′} (par-betas p₂)  ⟩
    (ƛ N′) · M′                  —→⟨ beta-lam ⟩
     N′ [ M′ ]
    ∎

pars-betas : ∀ {M N} → M ⇛* N → M —↠ N
pars-betas (M ■) = ms-refl M
pars-betas (L ⇛⟨ L⇛M ⟩ M⇛*N) = multi-trans (par-betas L⇛M) (pars-betas M⇛*N)

------------------------------------------------------------------------
-- Substitution and Parallel Reduction
-- If N ⇛ N′ and M ⇛ M′ then N [ M ] ⇛ N′ [ M′ ].
------------------------------------------------------------------------

rename-[] : ∀ {ρ : Rename} {N M : Term} →
  rename ρ (N [ M ]) ≡ (rename (ext ρ) N) [ rename ρ M ]
rename-[] {ρ} {N} {M} =
  trans
    (cong (rename ρ) (single-subst-def N M))
    (trans
      (rename-subst ρ (single-env M) N)
      (trans
        (subst-cong env-eq N)
        (trans
          (sym (rename-subst-commute (ext ρ) (single-env (rename ρ M)) N))
          (sym (single-subst-def (rename (ext ρ) N) (rename ρ M))))))
  where
    env-eq : ∀ i → rename ρ (single-env M i) ≡ single-env (rename ρ M) (ext ρ i)
    env-eq zero = refl
    env-eq (suc i) = refl

par-rename : ∀ {ρ : Rename} {M M′ : Term}
  → M ⇛ M′
  → rename ρ M ⇛ rename ρ M′
par-rename {ρ} par-var = par-var
par-rename {ρ} (par-lam p) = par-lam (par-rename {ρ = ext ρ} p)
par-rename {ρ} (par-app p₁ p₂) =
  par-app (par-rename {ρ = ρ} p₁) (par-rename {ρ = ρ} p₂)
par-rename {ρ} (par-beta {N' = N′} {M' = M′} p₁ p₂)
  rewrite rename-[] {ρ = ρ} {N = N′} {M = M′} =
  par-beta (par-rename {ρ = ext ρ} p₁) (par-rename {ρ = ρ} p₂)

par-subst : Subst → Subst → Set
par-subst σ τ = ∀ i → σ i ⇛ τ i

par-subst-exts : ∀ {σ τ : Subst}
  → par-subst σ τ
  → par-subst (exts σ) (exts τ)
par-subst-exts s zero = par-var
par-subst-exts s (suc i) = par-rename {ρ = suc} (s i)

subst-[] : ∀ {σ : Subst} {N M : Term} →
  subst σ (N [ M ]) ≡ (subst (exts σ) N) [ subst σ M ]
subst-[] {σ} {N} {M} =
  trans
    (cong (subst σ) (single-subst-def N M))
    (trans
      (sub-sub (single-env M) σ N)
      (trans
        (subst-cong env-eq N)
        (sym (exts-sub-cons {sigma = σ} {n = N} {v = subst σ M}))))
  where
    env-eq : ∀ i → seq (single-env M) σ i ≡ cons-sub (subst σ M) σ i
    env-eq zero = refl
    env-eq (suc i) = refl

subst-par : ∀ {σ τ : Subst} {M M′ : Term}
  → par-subst σ τ
  → M ⇛ M′
  → subst σ M ⇛ subst τ M′
subst-par {M = ′ i} s par-var = s i
subst-par {σ = σ} {τ = τ} {M = ƛ N} s (par-lam p) =
  par-lam (subst-par {σ = exts σ} {τ = exts τ} (par-subst-exts s) p)
subst-par s (par-app p₁ p₂) = par-app (subst-par s p₁) (subst-par s p₂)
subst-par {σ = σ} {τ = τ} (s) (par-beta {N' = N′} {M' = M′} p₁ p₂)
  rewrite subst-[] {σ = τ} {N = N′} {M = M′} =
  par-beta
    (subst-par {σ = exts σ} {τ = exts τ} (par-subst-exts s) p₁)
    (subst-par {σ = σ} {τ = τ} s p₂)

par-subst-zero : ∀ {M M′ : Term}
  → M ⇛ M′
  → par-subst (single-env M) (single-env M′)
par-subst-zero p zero = p
par-subst-zero p (suc i) = par-var

sub-par : ∀ {N N′ M M′ : Term}
  → N ⇛ N′
  → M ⇛ M′
  → N [ M ] ⇛ N′ [ M′ ]
sub-par pN pM = subst-par (par-subst-zero pM) pN

------------------------------------------------------------------------
-- Diamond Property
-- If M ⇛ N and M ⇛ P then N ⇛ Q and P ⇛ Q for some Q.
------------------------------------------------------------------------

-- The complete development function _⁺ maps a term to the result of
-- contracting all beta-redexes in parallel in one recursive sweep.

_⁺ : Term → Term
(′ x) ⁺ = ′ x
(ƛ N) ⁺ = ƛ (N ⁺)
((ƛ N) · M) ⁺ = N ⁺ [ M ⁺ ]
(L · M) ⁺ = L ⁺ · M ⁺

par-triangle : ∀ {M N : Term}
  → M ⇛ N
  → N ⇛ M ⁺
par-triangle par-var = par-var
par-triangle (par-lam {N = N} {N' = N′} p) =
  let ih : N′ ⇛ N ⁺
      ih = par-triangle p

      goal : (ƛ N′) ⇛ ƛ (N ⁺)
      goal = par-lam ih
  in goal
par-triangle (par-beta {N = N} {N' = N′} {M = M} {M' = M′} p1 p2) =
  let ihN : N′ ⇛ N ⁺
      ihN = par-triangle p1

      ihM : M′ ⇛ M ⁺
      ihM = par-triangle p2

      goal : (N′ [ M′ ]) ⇛ (N ⁺ [ M ⁺ ])
      goal = sub-par ihN ihM
  in goal
par-triangle (par-app {L = ƛ N} {L' = ƛ N′} {M = M} {M' = M′} (par-lam p1) p2) =
  let ihN : N′ ⇛ N ⁺
      ihN = par-triangle p1

      ihM : M′ ⇛ M ⁺
      ihM = par-triangle p2

      goal : ((ƛ N′) · M′) ⇛ (N ⁺ [ (M ⁺) ])
      goal = par-beta ihN ihM
  in goal
par-triangle (par-app {L = ′ I} {L' = L′} {M = M} {M' = M′} p1 p2) =
  let ihL : L′ ⇛ ′ I
      ihL = par-triangle p1

      ihM : M′ ⇛ M ⁺
      ihM = par-triangle p2

      goal : (L′ · M′) ⇛ ((′ I) · (M ⁺))
      goal = par-app ihL ihM
  in goal
par-triangle (par-app {L = L · L₁} {L' = L′} {M = M} {M' = M′} p1 p2) =
  let ihL : L′ ⇛ ((L · L₁) ⁺)
      ihL = par-triangle p1

      ihM : M′ ⇛ M ⁺
      ihM = par-triangle p2

      goal : (L′ · M′) ⇛ (((L · L₁) ⁺) · (M ⁺))
      goal = par-app ihL ihM
  in goal

⇛-diamond : ∀ {M N P} → M ⇛ N → M ⇛ P →
  Σ[ Q ∈ Term ] (N ⇛ Q) × (P ⇛ Q)
⇛-diamond {M} M⇛N M⇛P = (M ⁺) , par-triangle M⇛N , par-triangle M⇛P

strip : ∀ {L M N} → L ⇛ M → L ⇛* N →
  Σ[ Q ∈ Term ] (M ⇛* Q) × (N ⇛* Q)
strip {L} {M} {N} L⇛M (L' ■) =
  let M⇛*M : M ⇛* M
      M⇛*M = M ■

      L⇛*M : L ⇛* M
      L⇛*M = L ⇛⟨ L⇛M ⟩ M ■

      goal : Σ[ Q ∈ Term ] (M ⇛* Q) × (L ⇛* Q)
      goal = M , M⇛*M , L⇛*M
  in goal
strip {L} {M} {N} L⇛M (L' ⇛⟨ L⇛N1 ⟩ N1⇛*N) with ⇛-diamond L⇛M L⇛N1
... | R , M⇛R , N1⇛R with strip N1⇛R N1⇛*N
... | Q , R⇛*Q , N⇛*Q =
  let M⇛*Q : M ⇛* Q
      M⇛*Q = M ⇛⟨ M⇛R ⟩ R⇛*Q

      goal : Σ[ Q' ∈ Term ] (M ⇛* Q') × (N ⇛* Q')
      goal = Q , M⇛*Q , N⇛*Q
  in goal

pars-confluent : ∀ {M N P} → M ⇛* N → M ⇛* P →
  Σ[ Q ∈ Term ] (N ⇛* Q) × (P ⇛* Q)
pars-confluent {N = N} {P = P} (M ■) M⇛*P =
  let P⇛*P : P ⇛* P
      P⇛*P = P ■

      goal : Σ[ Q ∈ Term ] (M ⇛* Q) × (P ⇛* Q)
      goal = P , M⇛*P , P⇛*P
  in goal
pars-confluent {N = N} {P = P} (M ⇛⟨ M⇛M1 ⟩ M1⇛*N) M⇛*P with strip M⇛M1 M⇛*P
... | R , M1⇛*R , P⇛*R with pars-confluent M1⇛*N M1⇛*R
... | Q , N⇛*Q , R⇛*Q =
  let P⇛*Q : P ⇛* Q
      P⇛*Q = ⇛*-trans P⇛*R R⇛*Q

      goal : Σ[ Q' ∈ Term ] (N ⇛* Q') × (P ⇛* Q')
      goal = Q , N⇛*Q , P⇛*Q
  in goal

------------------------------------------------------------------------
-- Final theorem: confluence of full-beta reduction
------------------------------------------------------------------------

full-beta-confluent : Confluent
full-beta-confluent {M} {N} {P} M—↠N M—↠P =
  let M⇛*N : M ⇛* N
      M⇛*N = betas-pars M—↠N

      M⇛*P : M ⇛* P
      M⇛*P = betas-pars M—↠P
  in helper M⇛*N M⇛*P
  where
    helper : M ⇛* N → M ⇛* P → Σ[ Q' ∈ Term ] (N —↠ Q') × (P —↠ Q')
    helper M⇛*N M⇛*P with pars-confluent M⇛*N M⇛*P
    ... | Q , N⇛*Q , P⇛*Q =
      let N—↠Q : N —↠ Q
          N—↠Q = pars-betas N⇛*Q

          P—↠Q : P —↠ Q
          P—↠Q = pars-betas P⇛*Q

          goal : Σ[ Q' ∈ Term ] (N —↠ Q') × (P —↠ Q')
          goal = Q , N—↠Q , P—↠Q
      in goal
