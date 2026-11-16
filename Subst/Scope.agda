{-

  File Charter:
    * Scopes of variables, abstractly: what the substitution library
      (Subst/Kit.agda) needs to know about a language's variables.
    * A scope structure gives scopes `Sc`, sorts `Sort` (the types of
      the variables, or `⊤` for an untyped or unisorted language),
      variables `Var Γ A`, extension of a scope by a variable `Γ ▷ A`,
      the variable bound last (`here`), weakening of a variable past a
      binder (`there`), and induction on the variables of an extended
      scope (`var-ind`) with its two computation laws.
    * Instances: `ℕScope` (raw de Bruijn indices, unscoped and untyped,
      e.g. for an extrinsically typed language) and `ctxScope T`
      (typed de Bruijn indices `Γ ∋ A` into a context `Ctx T` of
      sorts `T`, e.g. for an intrinsically typed language).

-}

module Subst.Scope where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record Scope : Set₁ where
  infixl 5 _▷_
  field
    Sc : Set
    Sort : Set
    Var : Sc → Sort → Set
    _▷_ : Sc → Sort → Sc
    here : ∀ {Γ A} → Var (Γ ▷ A) A
    there : ∀ {Γ A B} → Var Γ A → Var (Γ ▷ B) A
    var-ind : ∀ {Γ B} (P : ∀ {A} → Var (Γ ▷ B) A → Set)
      → P here
      → (∀ {A} (x : Var Γ A) → P (there x))
      → ∀ {A} (x : Var (Γ ▷ B) A) → P x
    var-ind-here : ∀ {Γ B} (P : ∀ {A} → Var (Γ ▷ B) A → Set)
      (p : P here) (f : ∀ {A} (x : Var Γ A) → P (there x))
      → var-ind P p f here ≡ p
    var-ind-there : ∀ {Γ B} (P : ∀ {A} → Var (Γ ▷ B) A → Set)
      (p : P here) (f : ∀ {A} (x : Var Γ A) → P (there x))
      → ∀ {A} (x : Var Γ A) → var-ind P p f (there x) ≡ f x

------------------------------------------------------------------------
-- Raw de Bruijn indices: one scope, one sort, variables are numbers
------------------------------------------------------------------------

private
  ℕ-ind : ∀ {Γ B : ⊤} (P : ∀ {A : ⊤} → ℕ → Set)
    → P {B} zero
    → (∀ {A : ⊤} (x : ℕ) → P {A} (suc x))
    → ∀ {A : ⊤} (x : ℕ) → P {A} x
  ℕ-ind P p f zero = p
  ℕ-ind P p f (suc x) = f x

ℕScope : Scope
ℕScope = record
  { Sc = ⊤
  ; Sort = ⊤
  ; Var = λ _ _ → ℕ
  ; _▷_ = λ _ _ → tt
  ; here = zero
  ; there = suc
  ; var-ind = λ {Γ} {B} → ℕ-ind {Γ} {B}
  ; var-ind-here = λ P p f → refl
  ; var-ind-there = λ P p f x → refl
  }

------------------------------------------------------------------------
-- Typed de Bruijn indices into a context
------------------------------------------------------------------------

infixl 5 _,_
infix 4 _∋_

data Ctx (T : Set) : Set where
  ∅ : Ctx T
  _,_ : Ctx T → T → Ctx T

data _∋_ {T : Set} : Ctx T → T → Set where
  Z : ∀ {Γ A} → Γ , A ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A

private
  ∋-ind : ∀ {T : Set} {Γ : Ctx T} {B : T} (P : ∀ {A} → Γ , B ∋ A → Set)
    → P Z
    → (∀ {A} (x : Γ ∋ A) → P (S x))
    → ∀ {A} (x : Γ , B ∋ A) → P x
  ∋-ind P p f Z = p
  ∋-ind P p f (S x) = f x

ctxScope : Set → Scope
ctxScope T = record
  { Sc = Ctx T
  ; Sort = T
  ; Var = _∋_
  ; _▷_ = _,_
  ; here = Z
  ; there = S_
  ; var-ind = ∋-ind
  ; var-ind-here = λ P p f → refl
  ; var-ind-there = λ P p f x → refl
  }
