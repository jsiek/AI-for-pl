module STLC where

-- File Charter:
--   * Core STLC language definition: syntax, typing, values, and reduction.
--   * Exports only definitional material used by trusted theorem statements.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_)

infixr 7 _⇒_

data Ty : Set where
  nat : Ty
  _⇒_ : Ty -> Ty -> Ty

infix  5 ƛ_⇒_
infixl 7 _·_
infix  8 `suc_
infix  9 `_

Var : Set
Var = ℕ

data Term : Set where
  `_ : ℕ -> Term
  ƛ_⇒_ : Ty -> Term -> Term
  _·_ : Term -> Term -> Term
  `zero : Term
  `suc_ : Term -> Term
  case_[zero⇒_|suc⇒_] : Term -> Term -> Term -> Term

Rename : Set
Rename = ℕ -> ℕ

Subst : Set
Subst = ℕ -> Term

ext : Rename -> Rename
ext ρ zero = zero
ext ρ (suc i) = suc (ρ i)

rename : Rename -> Term -> Term
rename ρ (` i) = ` (ρ i)
rename ρ (ƛ A ⇒ N) = ƛ A ⇒ rename (ext ρ) N
rename ρ (L · M) = rename ρ L · rename ρ M
rename ρ `zero = `zero
rename ρ (`suc M) = `suc rename ρ M
rename ρ (case_[zero⇒_|suc⇒_] L M N) =
  case_[zero⇒_|suc⇒_] (rename ρ L) (rename ρ M) (rename (ext ρ) N)

exts : Subst -> Subst
exts σ zero = ` zero
exts σ (suc i) = rename suc (σ i)

subst : Subst -> Term -> Term
subst σ (` i) = σ i
subst σ (ƛ A ⇒ N) = ƛ A ⇒ subst (exts σ) N
subst σ (L · M) = subst σ L · subst σ M
subst σ `zero = `zero
subst σ (`suc M) = `suc subst σ M
subst σ (case_[zero⇒_|suc⇒_] L M N) =
  case_[zero⇒_|suc⇒_] (subst σ L) (subst σ M) (subst (exts σ) N)

singleEnv : Term -> Subst
singleEnv M zero = M
singleEnv M (suc i) = ` i

infixl 8 _[_]
_[_] : Term -> Term -> Term
N [ M ] = subst (singleEnv M) N

Ctx : Set
Ctx = List Ty

infix 4 _∋_⦂_
data _∋_⦂_ : Ctx -> ℕ -> Ty -> Set where
  Z : {Γ : Ctx} {A : Ty} -> (A ∷ Γ) ∋ zero ⦂ A
  S : {Γ : Ctx} {A B : Ty} {i : ℕ} ->
      Γ ∋ i ⦂ A ->
      (B ∷ Γ) ∋ suc i ⦂ A

infix 4 _⊢_⦂_
data _⊢_⦂_ (Γ : Ctx) : Term -> Ty -> Set where
  ⊢` : {i : ℕ} {A : Ty} ->
       Γ ∋ i ⦂ A ->
       Γ ⊢ (` i) ⦂ A

  ⊢ƛ : {A B : Ty} {N : Term} ->
       (A ∷ Γ) ⊢ N ⦂ B ->
       Γ ⊢ (ƛ A ⇒ N) ⦂ (A ⇒ B)

  ⊢· : {A B : Ty} {L M : Term} ->
       Γ ⊢ L ⦂ (A ⇒ B) ->
       Γ ⊢ M ⦂ A ->
       Γ ⊢ (L · M) ⦂ B

  ⊢zero : Γ ⊢ `zero ⦂ nat

  ⊢suc : {M : Term} ->
         Γ ⊢ M ⦂ nat ->
         Γ ⊢ (`suc M) ⦂ nat

  ⊢case : {A : Ty} {L M N : Term} ->
          Γ ⊢ L ⦂ nat ->
          Γ ⊢ M ⦂ A ->
          (nat ∷ Γ) ⊢ N ⦂ A ->
          Γ ⊢ (case_[zero⇒_|suc⇒_] L M N) ⦂ A

data Value : Term -> Set where
  ƛ_⇒_ : (A : Ty) (N : Term) -> Value (ƛ A ⇒ N)
  `zero : Value `zero
  `suc_ : {V : Term} -> Value V -> Value (`suc V)

infix 2 _—→_
data _—→_ : Term -> Term -> Set where
  ξ-·₁ : {L L' M : Term} ->
         L —→ L' ->
         (L · M) —→ (L' · M)

  ξ-·₂ : {V M M' : Term} ->
         Σ (Value V) (λ _ -> M —→ M') ->
         (V · M) —→ (V · M')

  β-ƛ : {A : Ty} {N W : Term} ->
        Value W ->
        ((ƛ A ⇒ N) · W) —→ (N [ W ])

  ξ-suc : {M M' : Term} ->
          M —→ M' ->
          (`suc M) —→ (`suc M')

  ξ-case : {L L' M N : Term} ->
           L —→ L' ->
           (case_[zero⇒_|suc⇒_] L M N) —→ (case_[zero⇒_|suc⇒_] L' M N)

  β-zero : {M N : Term} ->
           (case_[zero⇒_|suc⇒_] `zero M N) —→ M

  β-suc : {V M N : Term} ->
          Value V ->
          (case_[zero⇒_|suc⇒_] (`suc V) M N) —→ (N [ V ])

infix 3 _∎
infixr 2 _—→⟨_⟩_
infix 2 _—↠_
data _—↠_ : Term -> Term -> Set where
  _∎ : (M : Term) -> M —↠ M
  _—→⟨_⟩_ : (L : Term) {M N : Term} ->
            L —→ M ->
            M —↠ N ->
            L —↠ N
