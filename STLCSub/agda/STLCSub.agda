module STLCSub where

-- File Charter:
--   * Core STLC with subtyping and records.
--   * Defines syntax, record-field lookup, declarative subtyping, typing,
--     de Bruijn renaming/substitution, values, small-step reduction, and
--     multi-step closure.
--   * Follows the local STLC family conventions while keeping the trusted
--     language surface in this top-level module.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≢_)

Label : Set
Label = ℕ

infixr 7 _⇒_
infix  6 _⦂ᶠ_

mutual
  data Ty : Set where
    top : Ty
    nat : Ty
    _⇒_ : Ty -> Ty -> Ty
    `⟨_⟩ : List FieldTy -> Ty

  data FieldTy : Set where
    _⦂ᶠ_ : Label -> Ty -> FieldTy

infix 4 HasTy
data HasTy : List FieldTy -> Label -> Ty -> Set where
  ty-here : {ℓ : Label} {A : Ty} {Fs : List FieldTy} ->
            HasTy ((ℓ ⦂ᶠ A) ∷ Fs) ℓ A
  ty-there : {ℓ ℓ′ : Label} {A B : Ty} {Fs : List FieldTy} ->
             ℓ′ ≢ ℓ ->
             HasTy Fs ℓ A ->
             HasTy ((ℓ′ ⦂ᶠ B) ∷ Fs) ℓ A

infix 4 _<:_

mutual
  data _<:_ : Ty -> Ty -> Set where
    S-refl : {A : Ty} -> A <: A
    S-top : {A : Ty} -> A <: top
    S-arrow : {A₁ A₂ B₁ B₂ : Ty} ->
              B₁ <: A₁ ->
              A₂ <: B₂ ->
              (A₁ ⇒ A₂) <: (B₁ ⇒ B₂)
    S-record : {Fs Gs : List FieldTy} ->
               FieldsSub Fs Gs ->
               `⟨ Fs ⟩ <: `⟨ Gs ⟩

  data FieldsSub : List FieldTy -> List FieldTy -> Set where
    fs[] : {Fs : List FieldTy} -> FieldsSub Fs []
    fs∷ : {Fs Gs : List FieldTy} {ℓ : Label} {A B : Ty} ->
          HasTy Fs ℓ A ->
          A <: B ->
          FieldsSub Fs Gs ->
          FieldsSub Fs ((ℓ ⦂ᶠ B) ∷ Gs)

infix  5 ƛ_⇒_
infixl 7 _·_
infix  8 `suc_
infix  8 _‼_
infix  9 `_
infix  6 _≔_

Var : Set
Var = ℕ

mutual
  data Term : Set where
    `_ : Var -> Term
    ƛ_⇒_ : Ty -> Term -> Term
    _·_ : Term -> Term -> Term
    `zero : Term
    `suc_ : Term -> Term
    case_[zero⇒_|suc⇒_] : Term -> Term -> Term -> Term
    `record : List FieldTerm -> Term
    _‼_ : Term -> Label -> Term

  data FieldTerm : Set where
    _≔_ : Label -> Term -> FieldTerm

infix 4 HasTerm
data HasTerm : List FieldTerm -> Label -> Term -> Set where
  tm-here : {ℓ : Label} {M : Term} {fs : List FieldTerm} ->
            HasTerm ((ℓ ≔ M) ∷ fs) ℓ M
  tm-there : {ℓ ℓ′ : Label} {M N : Term} {fs : List FieldTerm} ->
             ℓ′ ≢ ℓ ->
             HasTerm fs ℓ M ->
             HasTerm ((ℓ′ ≔ N) ∷ fs) ℓ M

Rename : Set
Rename = Var -> Var

Subst : Set
Subst = Var -> Term

ext : Rename -> Rename
ext ρ zero = zero
ext ρ (suc i) = suc (ρ i)

mutual
  rename : Rename -> Term -> Term
  rename ρ (` i) = ` (ρ i)
  rename ρ (ƛ A ⇒ N) = ƛ A ⇒ rename (ext ρ) N
  rename ρ (L · M) = rename ρ L · rename ρ M
  rename ρ `zero = `zero
  rename ρ (`suc M) = `suc rename ρ M
  rename ρ (case_[zero⇒_|suc⇒_] L M N) =
    case_[zero⇒_|suc⇒_] (rename ρ L) (rename ρ M) (rename (ext ρ) N)
  rename ρ (`record fs) = `record (renameFields ρ fs)
  rename ρ (M ‼ ℓ) = rename ρ M ‼ ℓ

  renameField : Rename -> FieldTerm -> FieldTerm
  renameField ρ (ℓ ≔ M) = ℓ ≔ rename ρ M

  renameFields : Rename -> List FieldTerm -> List FieldTerm
  renameFields ρ [] = []
  renameFields ρ (f ∷ fs) = renameField ρ f ∷ renameFields ρ fs

exts : Subst -> Subst
exts σ zero = ` zero
exts σ (suc i) = rename suc (σ i)

mutual
  subst : Subst -> Term -> Term
  subst σ (` i) = σ i
  subst σ (ƛ A ⇒ N) = ƛ A ⇒ subst (exts σ) N
  subst σ (L · M) = subst σ L · subst σ M
  subst σ `zero = `zero
  subst σ (`suc M) = `suc subst σ M
  subst σ (case_[zero⇒_|suc⇒_] L M N) =
    case_[zero⇒_|suc⇒_] (subst σ L) (subst σ M) (subst (exts σ) N)
  subst σ (`record fs) = `record (substFields σ fs)
  subst σ (M ‼ ℓ) = subst σ M ‼ ℓ

  substField : Subst -> FieldTerm -> FieldTerm
  substField σ (ℓ ≔ M) = ℓ ≔ subst σ M

  substFields : Subst -> List FieldTerm -> List FieldTerm
  substFields σ [] = []
  substFields σ (f ∷ fs) = substField σ f ∷ substFields σ fs

singleEnv : Term -> Subst
singleEnv M zero = M
singleEnv M (suc i) = ` i

infixl 8 _[_]
_[_] : Term -> Term -> Term
N [ M ] = subst (singleEnv M) N

Ctx : Set
Ctx = List Ty

infix 4 _∋_⦂_
data _∋_⦂_ : Ctx -> Var -> Ty -> Set where
  Z : {Γ : Ctx} {A : Ty} -> (A ∷ Γ) ∋ zero ⦂ A
  S : {Γ : Ctx} {A B : Ty} {i : Var} ->
      Γ ∋ i ⦂ A ->
      (B ∷ Γ) ∋ suc i ⦂ A

mutual
  infix 4 _⊢_⦂_
  data _⊢_⦂_ (Γ : Ctx) : Term -> Ty -> Set where
    ⊢` : {i : Var} {A : Ty} ->
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

    ⊢record : {fs : List FieldTerm} {Fs : List FieldTy} ->
              Γ ⊢ᶠˢ fs ⦂ Fs ->
              Γ ⊢ (`record fs) ⦂ `⟨ Fs ⟩

    ⊢proj : {M : Term} {Fs : List FieldTy} {ℓ : Label} {A : Ty} ->
            Γ ⊢ M ⦂ `⟨ Fs ⟩ ->
            HasTy Fs ℓ A ->
            Γ ⊢ (M ‼ ℓ) ⦂ A

    ⊢sub : {M : Term} {A B : Ty} ->
           Γ ⊢ M ⦂ A ->
           A <: B ->
           Γ ⊢ M ⦂ B

  infix 4 _⊢ᶠˢ_⦂_
  data _⊢ᶠˢ_⦂_ (Γ : Ctx) : List FieldTerm -> List FieldTy -> Set where
    ⊢[] : Γ ⊢ᶠˢ [] ⦂ []
    ⊢∷ : {fs : List FieldTerm} {Fs : List FieldTy}
         {ℓ : Label} {M : Term} {A : Ty} ->
         Γ ⊢ M ⦂ A ->
         Γ ⊢ᶠˢ fs ⦂ Fs ->
         Γ ⊢ᶠˢ ((ℓ ≔ M) ∷ fs) ⦂ ((ℓ ⦂ᶠ A) ∷ Fs)

data Value : Term -> Set where
  ƛ_⇒_ : (A : Ty) (N : Term) -> Value (ƛ A ⇒ N)
  `zero : Value `zero
  `suc_ : {V : Term} -> Value V -> Value (`suc V)
  `record : (fs : List FieldTerm) -> Value (`record fs)

infix 2 _—→_
data _—→_ : Term -> Term -> Set where
  ξ-·₁ : {L L′ M : Term} ->
         L —→ L′ ->
         (L · M) —→ (L′ · M)

  ξ-·₂ : {V M M′ : Term} ->
         Σ (Value V) (λ _ -> M —→ M′) ->
         (V · M) —→ (V · M′)

  β-ƛ : {A : Ty} {N W : Term} ->
        Value W ->
        ((ƛ A ⇒ N) · W) —→ (N [ W ])

  ξ-suc : {M M′ : Term} ->
          M —→ M′ ->
          (`suc M) —→ (`suc M′)

  ξ-case : {L L′ M N : Term} ->
           L —→ L′ ->
           (case_[zero⇒_|suc⇒_] L M N) —→
           (case_[zero⇒_|suc⇒_] L′ M N)

  β-zero : {M N : Term} ->
           (case_[zero⇒_|suc⇒_] `zero M N) —→ M

  β-suc : {V M N : Term} ->
          Value V ->
          (case_[zero⇒_|suc⇒_] (`suc V) M N) —→ (N [ V ])

  ξ-proj : {M M′ : Term} {ℓ : Label} ->
           M —→ M′ ->
           (M ‼ ℓ) —→ (M′ ‼ ℓ)

  β-proj : {fs : List FieldTerm} {ℓ : Label} {M : Term} ->
           HasTerm fs ℓ M ->
           (`record fs ‼ ℓ) —→ M

infix 3 _∎
infixr 2 _—→⟨_⟩_
infix 2 _—↠_
data _—↠_ : Term -> Term -> Set where
  _∎ : (M : Term) -> M —↠ M
  _—→⟨_⟩_ : (L : Term) {M N : Term} ->
            L —→ M ->
            M —↠ N ->
            L —↠ N
