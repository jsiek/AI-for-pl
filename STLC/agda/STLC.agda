module STLC where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; ∃; ∃-syntax; _,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

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
  V-ƛ : {A : Ty} {N : Term} -> Value (ƛ A ⇒ N)
  V-zero : Value `zero
  V-suc : {V : Term} -> Value V -> Value (`suc V)

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

multi-trans : {M N L : Term} -> M —↠ N -> N —↠ L -> M —↠ L
multi-trans (_ ∎) ms2 = ms2
multi-trans (_ —→⟨ s ⟩ ms1') ms2 = _ —→⟨ s ⟩ (multi-trans ms1' ms2)

infix 4 _≟Ty_
_≟Ty_ : (A B : Ty) → Dec (A ≡ B)
nat ≟Ty nat = yes refl
nat ≟Ty (B ⇒ B₁) = no λ ()
(A ⇒ A₁) ≟Ty nat = no (λ ())
(A₁ ⇒ A₂) ≟Ty (B₁ ⇒ B₂)
    with A₁ ≟Ty B₁ | A₂ ≟Ty B₂
... | yes refl | yes refl = yes refl
... | no neq | _ = no λ { refl → neq refl }
... | _ | no neq = no λ { refl → neq refl }

∋-unique : {Γ : Ctx} {x : Var} {A B : Ty}
    → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B
    → A ≡ B
∋-unique Z Z = refl
∋-unique (S x:A) (S x:B) = ∋-unique x:A x:B

lookup : (Γ : Ctx) (x : Var) → Dec (∃[ A ] Γ ∋ x ⦂ A)
lookup [] x = no λ { () }
lookup (A ∷ Γ) zero = yes (A , Z)
lookup (A ∷ Γ) (suc x)
    with lookup Γ x
... | yes (B , x:B) = yes (B , (S x:B))
... | no nxx = no λ { (B , S sx:B) → nxx (B , sx:B) }

nat-fun : ∀ {A B} → nat ≡ A ⇒ B → ⊥
nat-fun ()

fun-inv1 : ∀ {A B C D} → A ⇒ B ≡ C ⇒ D → A ≡ C
fun-inv1 refl = refl

fun-inv2 : ∀ {A B C D} → A ⇒ B ≡ C ⇒ D → B ≡ D
fun-inv2 refl = refl

typing-unique : (Γ : Ctx) (M : Term) (A B : Ty)
    → Γ ⊢ M ⦂ A → Γ ⊢ M ⦂ B
    → A ≡ B
typing-unique Γ _ _ _ (⊢` x:A) (⊢` x:B) =
  ∋-unique x:A x:B
typing-unique Γ _ _ _ (⊢ƛ {A = A} {B = B₁} {N = N} N:B₁) (⊢ƛ {B = B₂} N:B₂) =
  cong (A ⇒_) (typing-unique (A ∷ Γ) N B₁ B₂ N:B₁ N:B₂)
typing-unique Γ _ _ _ (⊢· {A = A₁} {B = B₁} {L = L} L:AB M:A)
                      (⊢· {A = A₂} {B = B₂} L:CD M:C) =
  fun-inv2 (typing-unique Γ L (A₁ ⇒ B₁) (A₂ ⇒ B₂) L:AB L:CD)
typing-unique Γ _ _ _ ⊢zero ⊢zero = refl
typing-unique Γ _ _ _ (⊢suc M:nat) (⊢suc M:nat′) = refl
typing-unique Γ _ _ _ (⊢case {M = M} L:nat M:A N:A) (⊢case L:nat′ M:B N:B) =
  typing-unique Γ M _ _ M:A M:B
