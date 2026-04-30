module STLCMore where

-- File Charter:
--   * Core STLCMore language definition: syntax, typing, values, and reduction.
--   * Exports only definitional material used by trusted theorem statements.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_)

infixr 7 _⇒_
infixr 6 _`×_
infixr 5 _`+_

data Ty : Set where
  nat : Ty
  unit : Ty
  _⇒_ : Ty -> Ty -> Ty
  _`×_ : Ty -> Ty -> Ty
  _`+_ : Ty -> Ty -> Ty

infix  5 ƛ_⇒_
infixl 7 _·_
infixr 6 pair_,_
infix  8 `suc_
infix  8 _as_
infix  8 fst_
infix  8 snd_
infix  8 inl_`to_
infix  8 inr_`to_
infix  6 let'_`in_
infix  6 case⊎_[inl⇒_|inr⇒_]
infix  9 `_

Var : Set
Var = ℕ

data Term : Set where
  `_ : ℕ -> Term
  ƛ_⇒_ : Ty -> Term -> Term
  _·_ : Term -> Term -> Term
  _as_ : Term -> Ty -> Term
  let'_`in_ : Term -> Term -> Term
  `zero : Term
  `suc_ : Term -> Term
  case_[zero⇒_|suc⇒_] : Term -> Term -> Term -> Term
  `unit : Term
  pair_,_ : Term -> Term -> Term
  fst_ : Term -> Term
  snd_ : Term -> Term
  inl_`to_ : Term -> Ty -> Term
  inr_`to_ : Term -> Ty -> Term
  case⊎_[inl⇒_|inr⇒_] : Term -> Term -> Term -> Term

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
rename ρ (M as A) = rename ρ M as A
rename ρ (let' M `in N) = let' (rename ρ M) `in rename (ext ρ) N
rename ρ `zero = `zero
rename ρ (`suc M) = `suc (rename ρ M)
rename ρ (case_[zero⇒_|suc⇒_] L M N) =
  case_[zero⇒_|suc⇒_] (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ `unit = `unit
rename ρ (pair M , N) = pair (rename ρ M) , rename ρ N
rename ρ (fst M) = fst (rename ρ M)
rename ρ (snd M) = snd (rename ρ M)
rename ρ (inl M `to A) = inl (rename ρ M) `to A
rename ρ (inr M `to A) = inr (rename ρ M) `to A
rename ρ (case⊎_[inl⇒_|inr⇒_] L M N) =
  case⊎_[inl⇒_|inr⇒_] (rename ρ L) (rename (ext ρ) M) (rename (ext ρ) N)

exts : Subst -> Subst
exts σ zero = ` zero
exts σ (suc i) = rename suc (σ i)

subst : Subst -> Term -> Term
subst σ (` i) = σ i
subst σ (ƛ A ⇒ N) = ƛ A ⇒ subst (exts σ) N
subst σ (L · M) = subst σ L · subst σ M
subst σ (M as A) = subst σ M as A
subst σ (let' M `in N) = let' (subst σ M) `in subst (exts σ) N
subst σ `zero = `zero
subst σ (`suc M) = `suc (subst σ M)
subst σ (case_[zero⇒_|suc⇒_] L M N) =
  case_[zero⇒_|suc⇒_] (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ `unit = `unit
subst σ (pair M , N) = pair (subst σ M) , subst σ N
subst σ (fst M) = fst (subst σ M)
subst σ (snd M) = snd (subst σ M)
subst σ (inl M `to A) = inl (subst σ M) `to A
subst σ (inr M `to A) = inr (subst σ M) `to A
subst σ (case⊎_[inl⇒_|inr⇒_] L M N) =
  case⊎_[inl⇒_|inr⇒_] (subst σ L) (subst (exts σ) M) (subst (exts σ) N)

singleEnv : Term -> Subst
singleEnv M zero = M
singleEnv M (suc i) = ` i

infixl 8 _[_]
_[_] : Term -> Term -> Term
N [ M ] = subst (singleEnv M) N

infixl 6 _；_
_；_ : Term -> Term -> Term
M ； N = (ƛ unit ⇒ rename suc N) · M

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

  ⊢as : {A : Ty} {M : Term} ->
        Γ ⊢ M ⦂ A ->
        Γ ⊢ (M as A) ⦂ A

  ⊢let : {A B : Ty} {M N : Term} ->
         Γ ⊢ M ⦂ A ->
         (A ∷ Γ) ⊢ N ⦂ B ->
         Γ ⊢ (let' M `in N) ⦂ B

  ⊢zero : Γ ⊢ `zero ⦂ nat

  ⊢suc : {M : Term} ->
         Γ ⊢ M ⦂ nat ->
         Γ ⊢ (`suc M) ⦂ nat

  ⊢case : {A : Ty} {L M N : Term} ->
          Γ ⊢ L ⦂ nat ->
          Γ ⊢ M ⦂ A ->
          (nat ∷ Γ) ⊢ N ⦂ A ->
          Γ ⊢ (case_[zero⇒_|suc⇒_] L M N) ⦂ A

  ⊢unit : Γ ⊢ `unit ⦂ unit

  ⊢pair : {A B : Ty} {M N : Term} ->
          Γ ⊢ M ⦂ A ->
          Γ ⊢ N ⦂ B ->
          Γ ⊢ (pair M , N) ⦂ (A `× B)

  ⊢fst : {A B : Ty} {M : Term} ->
         Γ ⊢ M ⦂ (A `× B) ->
         Γ ⊢ (fst M) ⦂ A

  ⊢snd : {A B : Ty} {M : Term} ->
         Γ ⊢ M ⦂ (A `× B) ->
         Γ ⊢ (snd M) ⦂ B

  ⊢inl : {A B : Ty} {M : Term} ->
         Γ ⊢ M ⦂ A ->
         Γ ⊢ (inl M `to (A `+ B)) ⦂ (A `+ B)

  ⊢inr : {A B : Ty} {M : Term} ->
         Γ ⊢ M ⦂ B ->
         Γ ⊢ (inr M `to (A `+ B)) ⦂ (A `+ B)

  ⊢case⊎ : {A B C : Ty} {L M N : Term} ->
           Γ ⊢ L ⦂ (A `+ B) ->
           (A ∷ Γ) ⊢ M ⦂ C ->
           (B ∷ Γ) ⊢ N ⦂ C ->
           Γ ⊢ (case⊎_[inl⇒_|inr⇒_] L M N) ⦂ C

data Value : Term -> Set where
  ƛ_⇒_ : (A : Ty) (N : Term) -> Value (ƛ A ⇒ N)
  `zero : Value `zero
  `suc_ : {V : Term} -> Value V -> Value (`suc V)
  `unit : Value `unit
  pair_,_ : {V W : Term} -> Value V -> Value W -> Value (pair V , W)
  inl_`to_ : {V : Term} -> Value V -> (A : Ty) -> Value (inl V `to A)
  inr_`to_ : {V : Term} -> Value V -> (A : Ty) -> Value (inr V `to A)

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

  ξ-as : {M M' : Term} {A : Ty} ->
         M —→ M' ->
         (M as A) —→ (M' as A)

  β-as : {V : Term} {A : Ty} ->
         Value V ->
         (V as A) —→ V

  ξ-let : {M M' N : Term} ->
          M —→ M' ->
          (let' M `in N) —→ (let' M' `in N)

  β-let : {V N : Term} ->
          Value V ->
          (let' V `in N) —→ (N [ V ])

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

  ξ-pair₁ : {M M' N : Term} ->
            M —→ M' ->
            (pair M , N) —→ (pair M' , N)

  ξ-pair₂ : {V N N' : Term} ->
            Σ (Value V) (λ _ -> N —→ N') ->
            (pair V , N) —→ (pair V , N')

  ξ-fst : {M M' : Term} ->
          M —→ M' ->
          (fst M) —→ (fst M')

  β-fst : {V W : Term} ->
          Value V ->
          Value W ->
          (fst (pair V , W)) —→ V

  ξ-snd : {M M' : Term} ->
          M —→ M' ->
          (snd M) —→ (snd M')

  β-snd : {V W : Term} ->
          Value V ->
          Value W ->
          (snd (pair V , W)) —→ W

  ξ-inl : {M M' : Term} {A : Ty} ->
          M —→ M' ->
          (inl M `to A) —→ (inl M' `to A)

  ξ-inr : {M M' : Term} {A : Ty} ->
          M —→ M' ->
          (inr M `to A) —→ (inr M' `to A)

  ξ-case⊎ : {L L' M N : Term} ->
            L —→ L' ->
            (case⊎_[inl⇒_|inr⇒_] L M N) —→ (case⊎_[inl⇒_|inr⇒_] L' M N)

  β-inl : {V M N : Term} {A : Ty} ->
          Value V ->
          (case⊎_[inl⇒_|inr⇒_] (inl V `to A) M N) —→ (M [ V ])

  β-inr : {V M N : Term} {A : Ty} ->
          Value V ->
          (case⊎_[inl⇒_|inr⇒_] (inr V `to A) M N) —→ (N [ V ])

infix 3 _∎
infixr 2 _—→⟨_⟩_
infix 2 _—↠_
data _—↠_ : Term -> Term -> Set where
  _∎ : (M : Term) -> M —↠ M
  _—→⟨_⟩_ : (L : Term) {M N : Term} ->
            L —→ M ->
            M —↠ N ->
            L —↠ N
