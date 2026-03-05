module STLC where

open import Agda.Builtin.Nat renaming (Nat to ℕ; zero to zeroℕ; suc to sucℕ)
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma using (Σ)

data Ty : Set where
  nat : Ty
  fn  : Ty -> Ty -> Ty

infixr 70 _⇒_
_⇒_ : Ty -> Ty -> Ty
_⇒_ = fn

infix  5 ƛ_⇒_
infixl 7 _·_
infix  8 `suc_
infix  9 `_

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
ext ρ zeroℕ    = zeroℕ
ext ρ (sucℕ i) = sucℕ (ρ i)

rename : Rename -> Term -> Term
rename ρ (` i)                      = ` (ρ i)
rename ρ (ƛ A ⇒ N)                  = ƛ A ⇒ rename (ext ρ) N
rename ρ (L · M)                    = rename ρ L · rename ρ M
rename ρ `zero                      = `zero
rename ρ (`suc M)                   = `suc rename ρ M
rename ρ (case_[zero⇒_|suc⇒_] L M N) = case_[zero⇒_|suc⇒_] (rename ρ L) (rename ρ M) (rename (ext ρ) N)

exts : Subst -> Subst
exts σ zeroℕ    = ` zeroℕ
exts σ (sucℕ i) = rename sucℕ (σ i)

subst : Subst -> Term -> Term
subst σ (` i)                      = σ i
subst σ (ƛ A ⇒ N)                  = ƛ A ⇒ subst (exts σ) N
subst σ (L · M)                    = subst σ L · subst σ M
subst σ `zero                      = `zero
subst σ (`suc M)                   = `suc subst σ M
subst σ (case_[zero⇒_|suc⇒_] L M N) = case_[zero⇒_|suc⇒_] (subst σ L) (subst σ M) (subst (exts σ) N)

singleEnv : Term -> Subst
singleEnv M zeroℕ    = M
singleEnv M (sucℕ i) = ` i

singleSubst : Term -> Term -> Term
singleSubst N M = subst (singleEnv M) N

Context : Set
Context = List Ty

data HasTypeVar : Context -> ℕ -> Ty -> Set where
  Z : {Γ : Context} {A : Ty} -> HasTypeVar (A ∷ Γ) zeroℕ A
  S : {Γ : Context} {A B : Ty} {i : ℕ} ->
      HasTypeVar Γ i A -> HasTypeVar (B ∷ Γ) (sucℕ i) A

data HasType : Context -> Term -> Ty -> Set where
  tVar  : {Γ : Context} {i : ℕ} {A : Ty} ->
           HasTypeVar Γ i A -> HasType Γ (` i) A
  tLam  : {Γ : Context} {A B : Ty} {N : Term} ->
           HasType (A ∷ Γ) N B -> HasType Γ (ƛ A ⇒ N) (A ⇒ B)
  tApp  : {Γ : Context} {A B : Ty} {L M : Term} ->
           HasType Γ L (A ⇒ B) -> HasType Γ M A -> HasType Γ (L · M) B
  tZero : {Γ : Context} -> HasType Γ `zero nat
  tSuc  : {Γ : Context} {M : Term} ->
           HasType Γ M nat -> HasType Γ (`suc M) nat
  tCase : {Γ : Context} {A : Ty} {L M N : Term} ->
           HasType Γ L nat ->
           HasType Γ M A ->
           HasType (nat ∷ Γ) N A ->
           HasType Γ (case_[zero⇒_|suc⇒_] L M N) A

data Value : Term -> Set where
  vLam  : {A : Ty} {N : Term} -> Value (ƛ A ⇒ N)
  vZero : Value `zero
  vSuc  : {V : Term} -> Value V -> Value (`suc V)

data Step : Term -> Term -> Set where
  xiAppLeft : {L L' M : Term} -> Step L L' -> Step (L · M) (L' · M)
  xiAppRight : {V M M' : Term} -> Σ (Value V) (λ _ -> Step M M') -> Step (V · M) (V · M')
  betaLam : {A : Ty} {N W : Term} -> Value W -> Step ((ƛ A ⇒ N) · W) (singleSubst N W)
  xiSuc : {M M' : Term} -> Step M M' -> Step (`suc M) (`suc M')
  xiCase : {L L' M N : Term} -> Step L L' -> Step (case_[zero⇒_|suc⇒_] L M N) (case_[zero⇒_|suc⇒_] L' M N)
  betaZero : {M N : Term} -> Step (case_[zero⇒_|suc⇒_] `zero M N) M
  betaSuc : {V M N : Term} -> Value V -> Step (case_[zero⇒_|suc⇒_] (`suc V) M N) (singleSubst N V)

infix 20 _—→_
_—→_ : Term -> Term -> Set
_—→_ = Step

data MultiStep : Term -> Term -> Set where
  ms-refl : (M : Term) -> MultiStep M M
  ms-step : (L : Term) {M N : Term} -> Step L M -> MultiStep M N -> MultiStep L N

infix 20 _—↠_
_—↠_ : Term -> Term -> Set
_—↠_ = MultiStep

multi-trans : {M N L : Term} -> M —↠ N -> N —↠ L -> M —↠ L
multi-trans (ms-refl _) ms2           = ms2
multi-trans (ms-step _ s ms1') ms2    = ms-step _ s (multi-trans ms1' ms2)
