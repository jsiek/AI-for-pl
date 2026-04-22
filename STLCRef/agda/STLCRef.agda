module STLCRef where

-- File Charter:
--   * Core STLC+references language definition in TAPL style.
--   * Defines syntax, parallel renaming/substitution, typing with store typing,
--     values, and one-step/multi-step reduction on configurations.
--   * Exports only definitional material (no metatheory proofs yet).

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (_×_; _,_)

infixr 7 _⇒_

data Ty : Set where
  nat : Ty
  unit : Ty
  _⇒_ : Ty -> Ty -> Ty
  ref_ : Ty -> Ty

infix 5 ƛ_⇒_
infixl 7 _·_
infix 8 `suc_
infix 8 ref_
infix 8 !_
infix 6 _:=_
infix 9 `_
infix 9 `loc_

data Term : Set where
  `_ : ℕ -> Term
  ƛ_⇒_ : Ty -> Term -> Term
  _·_ : Term -> Term -> Term
  `zero : Term
  `suc_ : Term -> Term
  case_[zero⇒_|suc⇒_] : Term -> Term -> Term -> Term
  `unit : Term
  ref_ : Term -> Term
  !_ : Term -> Term
  _:=_ : Term -> Term -> Term
  `loc_ : ℕ -> Term

Var : Set
Var = ℕ

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
rename ρ `unit = `unit
rename ρ (ref M) = ref (rename ρ M)
rename ρ (! M) = ! (rename ρ M)
rename ρ (L := M) = rename ρ L := rename ρ M
rename ρ (`loc l) = `loc l

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
subst σ `unit = `unit
subst σ (ref M) = ref (subst σ M)
subst σ (! M) = ! (subst σ M)
subst σ (L := M) = subst σ L := subst σ M
subst σ (`loc l) = `loc l

singleEnv : Term -> Subst
singleEnv M zero = M
singleEnv M (suc i) = ` i

infixl 8 _[_]
_[_] : Term -> Term -> Term
N [ M ] = subst (singleEnv M) N

Ctx : Set
Ctx = List Ty

StoreTy : Set
StoreTy = List Ty

infix 4 _∋_⦂_
data _∋_⦂_ : List Ty -> ℕ -> Ty -> Set where
  Z : {Γ : List Ty} {A : Ty} -> (A ∷ Γ) ∋ zero ⦂ A
  S : {Γ : List Ty} {A B : Ty} {i : ℕ} ->
      Γ ∋ i ⦂ A ->
      (B ∷ Γ) ∋ suc i ⦂ A

infix 4 _∣_⊢_⦂_
data _∣_⊢_⦂_ (Γ : Ctx) (Σ : StoreTy) : Term -> Ty -> Set where
  ⊢` : {i : ℕ} {A : Ty} ->
       Γ ∋ i ⦂ A ->
       Γ ∣ Σ ⊢ (` i) ⦂ A

  ⊢ƛ : {A B : Ty} {N : Term} ->
       (A ∷ Γ) ∣ Σ ⊢ N ⦂ B ->
       Γ ∣ Σ ⊢ (ƛ A ⇒ N) ⦂ (A ⇒ B)

  ⊢· : {A B : Ty} {L M : Term} ->
       Γ ∣ Σ ⊢ L ⦂ (A ⇒ B) ->
       Γ ∣ Σ ⊢ M ⦂ A ->
       Γ ∣ Σ ⊢ (L · M) ⦂ B

  ⊢zero : Γ ∣ Σ ⊢ `zero ⦂ nat

  ⊢suc : {M : Term} ->
         Γ ∣ Σ ⊢ M ⦂ nat ->
         Γ ∣ Σ ⊢ (`suc M) ⦂ nat

  ⊢case : {A : Ty} {L M N : Term} ->
          Γ ∣ Σ ⊢ L ⦂ nat ->
          Γ ∣ Σ ⊢ M ⦂ A ->
          (nat ∷ Γ) ∣ Σ ⊢ N ⦂ A ->
          Γ ∣ Σ ⊢ (case_[zero⇒_|suc⇒_] L M N) ⦂ A

  ⊢unit : Γ ∣ Σ ⊢ `unit ⦂ unit

  ⊢ref : {A : Ty} {M : Term} ->
         Γ ∣ Σ ⊢ M ⦂ A ->
         Γ ∣ Σ ⊢ (ref M) ⦂ ref A

  ⊢! : {A : Ty} {M : Term} ->
       Γ ∣ Σ ⊢ M ⦂ ref A ->
       Γ ∣ Σ ⊢ (! M) ⦂ A

  ⊢:= : {A : Ty} {L M : Term} ->
        Γ ∣ Σ ⊢ L ⦂ ref A ->
        Γ ∣ Σ ⊢ M ⦂ A ->
        Γ ∣ Σ ⊢ (L := M) ⦂ unit

  ⊢loc : {l : ℕ} {A : Ty} ->
         Σ ∋ l ⦂ A ->
         Γ ∣ Σ ⊢ (`loc l) ⦂ ref A

data Value : Term -> Set where
  ƛ_⇒_ : (A : Ty) (N : Term) -> Value (ƛ A ⇒ N)
  `zero : Value `zero
  `suc_ : {V : Term} -> Value V -> Value (`suc V)
  `unit : Value `unit
  `loc_ : (l : ℕ) -> Value (`loc l)

Store : Set
Store = List Term

lookupStore : Store -> ℕ -> Maybe Term
lookupStore [] i = nothing
lookupStore (V ∷ μ) zero = just V
lookupStore (V ∷ μ) (suc i) = lookupStore μ i

updateStore : Store -> ℕ -> Term -> Maybe Store
updateStore [] i W = nothing
updateStore (V ∷ μ) zero W = just (W ∷ μ)
updateStore (V ∷ μ) (suc i) W with updateStore μ i W
... | just μ′ = just (V ∷ μ′)
... | nothing = nothing

Config : Set
Config = Term × Store

infix 2 _—→_
data _—→_ : Config -> Config -> Set where
  ξ-·₁ : {L L' M : Term} {μ μ' : Store} ->
         (L , μ) —→ (L' , μ') ->
         (L · M , μ) —→ (L' · M , μ')

  ξ-·₂ : {V M M' : Term} {μ μ' : Store} ->
         Value V ->
         (M , μ) —→ (M' , μ') ->
         (V · M , μ) —→ (V · M' , μ')

  β-ƛ : {A : Ty} {N W : Term} {μ : Store} ->
        Value W ->
        ((ƛ A ⇒ N) · W , μ) —→ (N [ W ] , μ)

  ξ-suc : {M M' : Term} {μ μ' : Store} ->
          (M , μ) —→ (M' , μ') ->
          (`suc M , μ) —→ (`suc M' , μ')

  ξ-case : {L L' M N : Term} {μ μ' : Store} ->
           (L , μ) —→ (L' , μ') ->
           (case_[zero⇒_|suc⇒_] L M N , μ) —→
           (case_[zero⇒_|suc⇒_] L' M N , μ')

  β-zero : {M N : Term} {μ : Store} ->
           (case_[zero⇒_|suc⇒_] `zero M N , μ) —→ (M , μ)

  β-suc : {V M N : Term} {μ : Store} ->
          Value V ->
          (case_[zero⇒_|suc⇒_] (`suc V) M N , μ) —→ (N [ V ] , μ)

  ξ-ref : {M M' : Term} {μ μ' : Store} ->
          (M , μ) —→ (M' , μ') ->
          (ref M , μ) —→ (ref M' , μ')

  β-ref : {V : Term} {μ : Store} ->
          Value V ->
          (ref V , μ) —→ (`loc (length μ) , μ ++ (V ∷ []))

  ξ-! : {M M' : Term} {μ μ' : Store} ->
        (M , μ) —→ (M' , μ') ->
        (! M , μ) —→ (! M' , μ')

  β-! : {l : ℕ} {V : Term} {μ : Store} ->
        lookupStore μ l ≡ just V ->
        (! (`loc l) , μ) —→ (V , μ)

  ξ-:=₁ : {L L' M : Term} {μ μ' : Store} ->
          (L , μ) —→ (L' , μ') ->
          (L := M , μ) —→ (L' := M , μ')

  ξ-:=₂ : {V M M' : Term} {μ μ' : Store} ->
          Value V ->
          (M , μ) —→ (M' , μ') ->
          (V := M , μ) —→ (V := M' , μ')

  β-:= : {l : ℕ} {V : Term} {μ μ' : Store} ->
         Value V ->
         updateStore μ l V ≡ just μ' ->
         (`loc l := V , μ) —→ (`unit , μ')

infix 3 _∎
infixr 2 _—→⟨_⟩_
infix 2 _—↠_
data _—↠_ : Config -> Config -> Set where
  _∎ : (c : Config) -> c —↠ c
  _—→⟨_⟩_ : (c₁ : Config) {c₂ c₃ : Config} ->
            c₁ —→ c₂ ->
            c₂ —↠ c₃ ->
            c₁ —↠ c₃
