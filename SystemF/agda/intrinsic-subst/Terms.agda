module intrinsic-subst.Terms where

-- File Charter:
--   * Intrinsically typed terms of System F (with naturals and booleans)
--     and their renaming and substitution, from the library for
--     polymorphic languages (Subst/Poly.agda).
--   * This file gives the two traversals of terms, one clause per term
--     constructor:
--       - `travᵀ` renames or substitutes the type variables of a term
--         (a type-level kit, a map `θ` of types, and a map `ρ` of the term
--         variables along `θ`); from it, `renᵀ`, `subᵀ`, the weakening
--         `⇑ᵀ` past a type variable, and type instantiation `N [ B ]ᵀ`;
--       - `trav` renames or substitutes the term variables of a term (a
--         term-level kit); from it, `ren`, `sub`, `⇑`, and `N [ M ]`.
--   * The only cast on terms is in the `_∙_` clause of `travᵀ`, by the
--     equation that commutes a type substitution with instantiation.
--   * The laws are in intrinsic-subst/proof/TermSubst.agda.  No function
--     extensionality is assumed.

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import intrinsic-subst.Types
open import intrinsic-subst.Ctx
open import intrinsic-subst.proof.TypeSubst using (module TL)

infix  4 _∣_⊢_
infix  9 `_
infix  5 ƛ_˙_
infixl 7 _·_
infixl 7 _∙_
infix  8 `suc_

data _∣_⊢_ (Δ : TyCtx) (Γ : Ctx Δ) : Type Δ → Set where

  `true :
      --------------- (T-True)
    Δ ∣ Γ ⊢ `Bool

  `false :
      ---------------- (T-False)
    Δ ∣ Γ ⊢ `Bool

  `zero :
      --------------- (T-Zero)
    Δ ∣ Γ ⊢ `Nat

  `suc_ :
    Δ ∣ Γ ⊢ `Nat
      ----------------- (T-Suc)
    → Δ ∣ Γ ⊢ `Nat

  `case-nat : ∀ {A}
    → Δ ∣ Γ ⊢ `Nat
    → Δ ∣ Γ ⊢ A
    → Δ ∣ Γ , `Nat ⊢ A
      ---------------------- (T-CaseNat)
    → Δ ∣ Γ ⊢ A

  `if_then_else : ∀ {A}
    → Δ ∣ Γ ⊢ `Bool
    → Δ ∣ Γ ⊢ A
    → Δ ∣ Γ ⊢ A
      ---------------------- (T-If)
    → Δ ∣ Γ ⊢ A

  `_ : ∀ {A}
    → Γ ∋ A
      --------------- (T-Var)
    → Δ ∣ Γ ⊢ A

  ƛ_˙_ : ∀ {B}
    → (A : Type Δ)
    → Δ ∣ Γ , A ⊢ B
      ------------------ (T-Abs)
    → Δ ∣ Γ ⊢ A ⇒ B

  _·_ : ∀ {A B}
    → Δ ∣ Γ ⊢ A ⇒ B
    → Δ ∣ Γ ⊢ A
      ------------------ (T-App)
    → Δ ∣ Γ ⊢ B

  -- | New rules for System F | --
  Λ_ : ∀ {A}
    → Δ ,α ∣ ⇑ᶜ Γ ⊢ A
      --------------------- (T-TAbs)
    → Δ ∣ Γ ⊢ `∀ A

  _∙_    : ∀ {A : Type (Δ ,α)}
    → Δ ∣ Γ ⊢ (`∀ A)
    → (B : Type Δ)
      --------------------- (T-TApp)
    → Δ ∣ Γ ⊢ A [ B ]ᵗ

Tm : ∀ {Δ} → Ctx Δ → Type Δ → Set
Tm {Δ} Γ A = Δ ∣ Γ ⊢ A

open Terms Tm (λ x → ` x) public

---------------------------------------------------------
-- | Renaming and substituting the types of terms    | --
---------------------------------------------------------

-- a type-level map commutes with instantiation
act-[] : ∀ (𝒯 : TyKit) {Δ Δ'} (θ : TK.Sub (TyKit.kit 𝒯) Δ Δ')
  (A : Type (Δ ,α)) (B : Type Δ)
  → act 𝒯 θ (A [ B ]ᵗ)
    ≡ act 𝒯 (TK.exts (TyKit.kit 𝒯) θ) A [ act 𝒯 θ B ]ᵗ
act-[] 𝒯 θ A B = TL.trav-[] (TyKit.laws 𝒯) θ A B

travᵀ : ∀ (𝒯 : TyKit) {Δ Δ'} (θ : TK.Sub (TyKit.kit 𝒯) Δ Δ')
  {Γ : Ctx Δ} {Γ' : Ctx Δ'} {A}
  → TyRen 𝒯 θ Γ Γ' → Δ ∣ Γ ⊢ A → Δ' ∣ Γ' ⊢ act 𝒯 θ A
travᵀ 𝒯 θ ρ `true = `true
travᵀ 𝒯 θ ρ `false = `false
travᵀ 𝒯 θ ρ `zero = `zero
travᵀ 𝒯 θ ρ (`suc M) = `suc (travᵀ 𝒯 θ ρ M)
travᵀ 𝒯 θ ρ (`case-nat L M N) =
  `case-nat (travᵀ 𝒯 θ ρ L) (travᵀ 𝒯 θ ρ M) (travᵀ 𝒯 θ (extρ 𝒯 θ ρ) N)
travᵀ 𝒯 θ ρ (`if_then_else L M N) =
  `if_then_else (travᵀ 𝒯 θ ρ L) (travᵀ 𝒯 θ ρ M) (travᵀ 𝒯 θ ρ N)
travᵀ 𝒯 θ ρ (` x) = ` (ρ x)
travᵀ 𝒯 θ ρ (ƛ A ˙ N) = ƛ act 𝒯 θ A ˙ travᵀ 𝒯 θ (extρ 𝒯 θ ρ) N
travᵀ 𝒯 θ ρ (L · M) = travᵀ 𝒯 θ ρ L · travᵀ 𝒯 θ ρ M
travᵀ 𝒯 θ ρ (Λ N) =
  Λ (travᵀ 𝒯 (TK.exts (TyKit.kit 𝒯) θ) (⇑ρ 𝒯 θ ρ) N)
travᵀ 𝒯 θ ρ (_∙_ {A = A} M B) =
  convᵀ (sym (act-[] 𝒯 θ A B)) (travᵀ 𝒯 θ ρ M ∙ act 𝒯 θ B)

open TypeSubstitution travᵀ public

---------------------------------------------------------
-- | Renaming and substituting the variables of terms | --
---------------------------------------------------------

trav : ∀ (𝒦 : Kit) {Δ} {Γ Γ' : Ctx Δ} {A}
  → Sub 𝒦 Γ Γ' → Δ ∣ Γ ⊢ A → Δ ∣ Γ' ⊢ A
trav 𝒦 σ `true = `true
trav 𝒦 σ `false = `false
trav 𝒦 σ `zero = `zero
trav 𝒦 σ (`suc M) = `suc (trav 𝒦 σ M)
trav 𝒦 σ (`case-nat L M N) =
  `case-nat (trav 𝒦 σ L) (trav 𝒦 σ M) (trav 𝒦 (exts 𝒦 σ) N)
trav 𝒦 σ (`if_then_else L M N) =
  `if_then_else (trav 𝒦 σ L) (trav 𝒦 σ M) (trav 𝒦 σ N)
trav 𝒦 σ (` x) = Kit.tm 𝒦 (σ x)
trav 𝒦 σ (ƛ A ˙ N) = ƛ A ˙ trav 𝒦 (exts 𝒦 σ) N
trav 𝒦 σ (L · M) = trav 𝒦 σ L · trav 𝒦 σ M
trav 𝒦 σ (Λ N) = Λ (trav 𝒦 (⇑s 𝒦 σ) N)
trav 𝒦 σ (M ∙ B) = trav 𝒦 σ M ∙ B

open Substitution trav public
