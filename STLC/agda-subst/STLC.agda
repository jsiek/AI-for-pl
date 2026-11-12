module STLC where

-- File Charter:
--   * Core STLC language definition: syntax, typing, values, and reduction.
--   * Renaming and substitution come from the kit library (Subst/Kit.agda):
--     this file gives the one traversal `trav` (one clause per term
--     constructor); renaming `ren` and substitution `sub` are `trav` with
--     the kit of variables and the kit of terms, and single substitution
--     `N [ M ]` is `sub (M • ids) N`.
--   * Terms are raw de Bruijn terms (variables are numbers), so the library
--     is used with the scope structure `ℕScope` (one scope, one sort).
--   * Exports only definitional material used by trusted theorem statements.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤)

open import Subst.Scope using (ℕScope)

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

------------------------------------------------------------------------
-- Renaming and substitution
------------------------------------------------------------------------

-- Raw terms: the scope and the sort of a variable are both trivial.
Tm : ⊤ -> ⊤ -> Set
Tm _ _ = Term

open import Subst.Kit ℕScope Tm `_ public

-- The one traversal: with the kit of variables it renames, with the kit of
-- terms it substitutes.
trav : (𝒦 : Kit) -> ∀ {Γ Δ A} -> Sub 𝒦 Γ Δ -> Tm Γ A -> Tm Δ A
trav 𝒦 σ (` i) = Kit.tm 𝒦 (σ i)
trav 𝒦 σ (ƛ A ⇒ N) = ƛ A ⇒ trav 𝒦 (exts 𝒦 σ) N
trav 𝒦 σ (L · M) = trav 𝒦 σ L · trav 𝒦 σ M
trav 𝒦 σ `zero = `zero
trav 𝒦 σ (`suc M) = `suc trav 𝒦 σ M
trav 𝒦 σ (case_[zero⇒_|suc⇒_] L M N) =
  case_[zero⇒_|suc⇒_] (trav 𝒦 σ L) (trav 𝒦 σ M) (trav 𝒦 (exts 𝒦 σ) N)

open Substitution trav public

-- Renamings and substitutions of raw terms, as plain functions on indices.
Rename : Set
Rename = ℕ -> ℕ

Subst : Set
Subst = ℕ -> Term

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Values and reduction
------------------------------------------------------------------------

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
