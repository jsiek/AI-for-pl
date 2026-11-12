module intrinsic-subst.Types where

-- File Charter:
--   * Types of System F, intrinsically scoped: type variable contexts
--     `TyCtx`, type variables `TyVar Δ`, and types `Type Δ`.
--   * Renaming and substitution of types come from the kit library
--     (Subst/Kit.agda): this file gives the one traversal `travᵗ` of types;
--     `renameᵗ` and `substᵗ` are `travᵗ` with the kit of type variables
--     and with the kit of types.
--   * Substitutions are functions on type variables, and all laws about
--     them (intrinsic-subst/proof/TypeSubst.agda) are pointwise, so no
--     function extensionality is assumed.

open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Subst.Scope using (Scope)
import Subst.Kit

infixr 7 _⇒_
infix  9 `_
infixl 5 _,α

---------------------------------------------------
-- | Type variable contexts and type variables | --
---------------------------------------------------

data TyCtx : Set where
  ∅    : TyCtx
  _,α  : TyCtx → TyCtx

data TyVar : (Δ : TyCtx) → Set where
  Z  : ∀ {Δ} → TyVar (Δ ,α)
  S_ : ∀ {Δ} → TyVar Δ → TyVar (Δ ,α)

---------------
-- | Types | --
---------------

data Type : TyCtx → Set where
  `_     : ∀ {Δ} → TyVar Δ → Type Δ
  `Nat   : ∀ {Δ} → Type Δ
  `Bool  : ∀ {Δ} → Type Δ
  _⇒_   : ∀ {Δ} → Type Δ → Type Δ → Type Δ
  `∀_    : ∀ {Δ} → Type (Δ ,α) → Type Δ

`ℕ : ∀ {Δ} → Type Δ
`ℕ = `Nat

---------------------------------------------------
-- | Type variables as a scope structure       | --
---------------------------------------------------

-- All type variables have the one kind, so the sort of a type variable is
-- trivial.

private
  TyVar-ind : ∀ {Δ : TyCtx} {B : ⊤} (P : ∀ {A : ⊤} → TyVar (Δ ,α) → Set)
    → P {B} Z
    → (∀ {A : ⊤} (α : TyVar Δ) → P {A} (S α))
    → ∀ {A : ⊤} (α : TyVar (Δ ,α)) → P {A} α
  TyVar-ind P p f Z = p
  TyVar-ind P p f (S α) = f α

tyScope : Scope
tyScope = record
  { Sc = TyCtx
  ; Sort = ⊤
  ; Var = λ Δ _ → TyVar Δ
  ; _▷_ = λ Δ _ → Δ ,α
  ; here = Z
  ; there = S_
  ; var-ind = λ {Δ} {B} → TyVar-ind {Δ} {B}
  ; var-ind-here = λ P p f → refl
  ; var-ind-there = λ P p f α → refl
  }

Typ : TyCtx → ⊤ → Set
Typ Δ _ = Type Δ

module TK = Subst.Kit tyScope Typ `_

------------------------------------------
-- | Renaming and substitution of types | --
------------------------------------------

-- The one traversal of types.
travᵗ : (𝒦 : TK.Kit) → ∀ {Δ Δ' s} → TK.Sub 𝒦 Δ Δ' → Typ Δ s → Typ Δ' s
travᵗ 𝒦 σ (` α)   = TK.Kit.tm 𝒦 (σ α)
travᵗ 𝒦 σ `Nat    = `Nat
travᵗ 𝒦 σ `Bool   = `Bool
travᵗ 𝒦 σ (A ⇒ B) = travᵗ 𝒦 σ A ⇒ travᵗ 𝒦 σ B
travᵗ 𝒦 σ (`∀ A)  = `∀ (travᵗ 𝒦 (TK.exts 𝒦 σ) A)

module TS = TK.Substitution travᵗ

infixr 7 _⇒ʳ_
infixr 7 _⇒ˢ_
infixr 6 _•ᵗ_
infixr 5 _⨟ᵗ_
infixl 8 _[_]ᵗ

-- Renamings and substitutions of types.
_⇒ʳ_ : TyCtx → TyCtx → Set
Δ ⇒ʳ Δ' = TK.Sub TK.varK Δ Δ'

_⇒ˢ_ : TyCtx → TyCtx → Set
Δ ⇒ˢ Δ' = TK.Sub TS.tmK Δ Δ'

renameᵗ : ∀ {Δ Δ'} → Δ ⇒ʳ Δ' → Type Δ → Type Δ'
renameᵗ ρ = TS.ren ρ

substᵗ : ∀ {Δ Δ'} → Δ ⇒ˢ Δ' → Type Δ → Type Δ'
substᵗ σ = TS.sub σ

extᵗ : ∀ {Δ Δ'} → Δ ⇒ʳ Δ' → (Δ ,α) ⇒ʳ (Δ' ,α)
extᵗ ρ = TK.exts TK.varK ρ

extsᵗ : ∀ {Δ Δ'} → Δ ⇒ˢ Δ' → (Δ ,α) ⇒ˢ (Δ' ,α)
extsᵗ σ = TK.exts TS.tmK σ

idᵗ : ∀ {Δ} → Δ ⇒ˢ Δ
idᵗ = TK.ids

↑ᵗ : ∀ {Δ} → Δ ⇒ˢ (Δ ,α)
↑ᵗ = TS.↑

_•ᵗ_ : ∀ {Δ Δ'} → Type Δ' → Δ ⇒ˢ Δ' → (Δ ,α) ⇒ˢ Δ'
A •ᵗ σ = A TK.• σ

_⨟ᵗ_ : ∀ {Δ₁ Δ₂ Δ₃} → Δ₁ ⇒ˢ Δ₂ → Δ₂ ⇒ˢ Δ₃ → Δ₁ ⇒ˢ Δ₃
σ ⨟ᵗ τ = σ TS.⨟ τ

-- weakening past a type variable
⇑ᵗ : ∀ {Δ} → Type Δ → Type (Δ ,α)
⇑ᵗ = TS.⇑

σ₀ᵗ : ∀ {Δ} → Type Δ → (Δ ,α) ⇒ˢ Δ
σ₀ᵗ B = B •ᵗ idᵗ

-- instantiating the type variable bound last
_[_]ᵗ : ∀ {Δ} → Type (Δ ,α) → Type Δ → Type Δ
A [ B ]ᵗ = A TS.[ B ]
