module STLC where

open import Data.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma using (Σ)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Product using (Σ; Σ-syntax; ∃; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (sym; refl; cong; cong₂; trans; _≡_)

infixr 7 _⇒_

data Ty : Set where
  nat : Ty
  _⇒_  : Ty -> Ty -> Ty

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
ext ρ 0    = 0
ext ρ (suc i) = suc (ρ i)

rename : Rename -> Term -> Term
rename ρ (` i)                      = ` (ρ i)
rename ρ (ƛ A ⇒ N)                  = ƛ A ⇒ rename (ext ρ) N
rename ρ (L · M)                    = rename ρ L · rename ρ M
rename ρ `zero                      = `zero
rename ρ (`suc M)                   = `suc rename ρ M
rename ρ (case_[zero⇒_|suc⇒_] L M N) = case_[zero⇒_|suc⇒_] (rename ρ L) (rename ρ M) (rename (ext ρ) N)

exts : Subst -> Subst
exts σ 0    = ` 0
exts σ (suc i) = rename suc (σ i)

subst : Subst -> Term -> Term
subst σ (` i)                      = σ i
subst σ (ƛ A ⇒ N)                  = ƛ A ⇒ subst (exts σ) N
subst σ (L · M)                    = subst σ L · subst σ M
subst σ `zero                      = `zero
subst σ (`suc M)                   = `suc subst σ M
subst σ (case_[zero⇒_|suc⇒_] L M N) = case_[zero⇒_|suc⇒_] (subst σ L) (subst σ M) (subst (exts σ) N)

singleEnv : Term -> Subst
singleEnv M 0    = M
singleEnv M (suc i) = ` i

singleSubst : Term -> Term -> Term
singleSubst N M = subst (singleEnv M) N

Context : Set
Context = List Ty

data HasTypeVar : Context -> ℕ -> Ty -> Set where
  Z : {Γ : Context} {A : Ty} -> HasTypeVar (A ∷ Γ) 0 A
  S : {Γ : Context} {A B : Ty} {i : ℕ} ->
      HasTypeVar Γ i A -> HasTypeVar (B ∷ Γ) (suc i) A

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

infix 4 _≟Ty_
_≟Ty_ : (A B : Ty) → Dec (A ≡ B)
nat ≟Ty nat = yes refl
nat ≟Ty (B ⇒ B₁) = no λ ()
(A ⇒ A₁) ≟Ty nat = no (λ ())
(A₁ ⇒ A₂) ≟Ty (B₁ ⇒ B₂)
    with A₁ ≟Ty B₁ | A₂ ≟Ty B₂
... | yes refl | yes refl = yes refl
... | no neq | _ = no λ { refl → neq refl}
... | _ | no neq = no λ { refl → neq refl}
    
hasTypeVar-unique : {Γ : Context} {x : Var} {A B : Ty}
    → HasTypeVar Γ x A → HasTypeVar Γ x B
    → A ≡ B
hasTypeVar-unique Z Z = refl
hasTypeVar-unique (S x:A) (S x:B) = hasTypeVar-unique x:A x:B

lookup : (Γ : Context) (x : Var) → Dec (∃[ A ] HasTypeVar Γ x A)
lookup [] x = no λ { ()}
lookup (A ∷ Γ) zero = yes (A , Z)
lookup (A ∷ Γ) (suc x)
    with lookup Γ x
... | yes (B , x:B) = yes (B , (S x:B))
... | no nxx = no λ { (B , S sx:B) → nxx (B , sx:B)}


nat-fun : ∀{A B} → nat ≡ A ⇒ B → ⊥
nat-fun ()

fun-inv1 : ∀{A B C D} → A ⇒ B ≡ C ⇒ D → A ≡ C
fun-inv1 refl = refl

fun-inv2 : ∀{A B C D} → A ⇒ B ≡ C ⇒ D → B ≡ D
fun-inv2 refl = refl

typing-unique : (Γ : Context) (M : Term) (A B : Ty)
    → HasType Γ M A → HasType Γ M B
    → A ≡ B
typing-unique Γ _ _ _ (tVar x:A) (tVar x:B) =
  hasTypeVar-unique x:A x:B
typing-unique Γ _ _ _ (tLam {A = A} {B = B₁} {N = N} N:B₁) (tLam {B = B₂} N:B₂) =
  cong (A ⇒_) (typing-unique (A ∷ Γ) N B₁ B₂ N:B₁ N:B₂)
typing-unique Γ _ _ _ (tApp {A = A₁} {B = B₁} {L = L} L:AB M:A)
                      (tApp {A = A₂} {B = B₂} L:CD M:C) =
  fun-inv2 (typing-unique Γ L (A₁ ⇒ B₁) (A₂ ⇒ B₂) L:AB L:CD)
typing-unique Γ _ _ _ tZero tZero = refl
typing-unique Γ _ _ _ (tSuc M:nat) (tSuc M:nat′) = refl
typing-unique Γ _ _ _ (tCase {M = M} L:nat M:A N:A) (tCase L:nat′ M:B N:B) =
  typing-unique Γ M _ _ M:A M:B

