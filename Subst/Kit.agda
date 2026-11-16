{-

  File Charter:
    * Renaming and substitution by one traversal with a kit (McBride,
      "Type-preserving renaming and substitution"), for any language
      whose variables form a scope structure (Subst/Scope.agda).
      Generalized from the framework of the denotational_semantics
      repository (Framework/Syntax/{Kit,TypedSubst}.agda) from typed de
      Bruijn indices to any representation of variables.
    * A kit says what a variable is mapped to (`K`), how a variable is
      one (`vr`), how one is a term (`tm`), and how one is moved under a
      binder (`wk`).  Renaming is the traversal with the kit of variables
      (`varK`), substitution the one with the kit of terms (`tmK`).
    * The language supplies its terms `Tm`, its variable constructor
      `` `_ ``, and (to the module `Substitution`) its traversal `trav`,
      one clause per term constructor, which goes under a binder by
      `exts`.
    * Exports: `Kit`, `Sub`, `cons`, `exts`, `varK`, `_•_`, `ids`, and,
      given the traversal, `ren`, `tmK`, `sub`, `↑`, `⇑`, `_⨟_`,
      `_[_]`, and the statements of the laws: `Fuse` and `SubId` (what a
      language proves by induction) and `Laws` (what a kit satisfies).
    * The proofs of the laws are in Subst/proof/Kit.agda.  Only
      statements are here, so a client's definitions can be audited
      without reading any proof.

-}

open import Subst.Scope using (Scope)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Subst.Kit (𝒮 : Scope) (let open Scope 𝒮)
  (Tm : Sc → Sort → Set) (`_ : ∀ {Γ A} → Var Γ A → Tm Γ A) where

record Kit : Set₁ where
  field
    K : Sc → Sort → Set
    vr : ∀ {Γ A} → Var Γ A → K Γ A
    tm : ∀ {Γ A} → K Γ A → Tm Γ A
    wk : ∀ {Γ A B} → K Γ A → K (Γ ▷ B) A

{- a map of the variables of Γ to things of the kit in Δ -}
Sub : Kit → Sc → Sc → Set
Sub 𝒦 Γ Δ = ∀ {A} → Var Γ A → Kit.K 𝒦 Δ A

{- `cons a f` maps the variable bound last to `a` and the others as `f`
   does -}
cons : ∀ {Γ B} {F : Sort → Set}
  → F B
  → (∀ {A} → Var Γ A → F A)
  → ∀ {A} → Var (Γ ▷ B) A → F A
cons {F = F} a f = var-ind (λ {A} _ → F A) a f

{- `exts σ` lifts `σ` under a binder: the bound variable maps to itself,
   the others as under `σ`, weakened past the binder. -}
exts : ∀ (𝒦 : Kit) {Γ Δ B} → Sub 𝒦 Γ Δ → Sub 𝒦 (Γ ▷ B) (Δ ▷ B)
exts 𝒦 {Δ = Δ} σ =
  cons {F = Kit.K 𝒦 (Δ ▷ _)} (Kit.vr 𝒦 here) (λ x → Kit.wk 𝒦 (σ x))

{- The kit of variables.  Its traversal is renaming. -}
varK : Kit
varK = record { K = Var ; vr = λ x → x ; tm = `_ ; wk = there }

{- The identity substitution and the cons of a term onto a substitution.
   (Their types are spelled out because `tmK` is defined below.) -}
ids : ∀ {Γ A} → Var Γ A → Tm Γ A
ids = `_

infixr 6 _•_
_•_ : ∀ {Γ Δ B}
  → Tm Δ B
  → (∀ {A} → Var Γ A → Tm Δ A)
  → ∀ {A} → Var (Γ ▷ B) A → Tm Δ A
_•_ {Δ = Δ} M σ = cons {F = Tm Δ} M σ

{- Renaming and substitution: the traversal with `varK` and with `tmK`.
   The traversal is a parameter because `tmK` weakens a term by renaming
   it. -}
module Substitution
  (trav : (𝒦 : Kit) → ∀ {Γ Δ A} → Sub 𝒦 Γ Δ → Tm Γ A → Tm Δ A) where

  ren : ∀ {Γ Δ A} → (∀ {B} → Var Γ B → Var Δ B) → Tm Γ A → Tm Δ A
  ren r = trav varK r

  {- weakening past one binder -}
  ⇑ : ∀ {Γ A B} → Tm Γ A → Tm (Γ ▷ B) A
  ⇑ = ren there

  {- The kit of terms.  Its traversal is substitution. -}
  tmK : Kit
  tmK = record { K = Tm ; vr = `_ ; tm = λ M → M ; wk = ⇑ }

  sub : ∀ {Γ Δ A} → (∀ {B} → Var Γ B → Tm Δ B) → Tm Γ A → Tm Δ A
  sub σ = trav tmK σ

  {- the substitution that weakens past one binder -}
  ↑ : ∀ {Γ B} → Sub tmK Γ (Γ ▷ B)
  ↑ x = ` (there x)

  {- composition: first σ, then τ -}
  infixr 5 _⨟_
  _⨟_ : ∀ {Γ Δ Θ} → Sub tmK Γ Δ → Sub tmK Δ Θ → Sub tmK Γ Θ
  (σ ⨟ τ) x = sub τ (σ x)

  {- `N [ M ]` substitutes `M` for the variable bound last in `N` -}
  infixl 8 _[_]
  _[_] : ∀ {Γ A B} → Tm (Γ ▷ B) A → Tm Γ B → Tm Γ A
  N [ M ] = sub (M • ids) N

  {- The statements of the laws (proofs in Subst/proof/Kit.agda) ---------}

  {- What a language proves by induction on its terms: two traversals fuse
     into one, for a relation between the two substitutions and the one
     that is kept under a binder and agrees on variables -}
  Fuse : Set₁
  Fuse =
    ∀ (𝒦₁ 𝒦₂ 𝒦₃ : Kit)
    (R : ∀ {Γ Δ Θ} → Sub 𝒦₁ Γ Δ → Sub 𝒦₂ Δ Θ → Sub 𝒦₃ Γ Θ → Set)
    → (∀ {Γ Δ Θ B} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ}
        → R σ₁ σ₂ σ₃ → R (exts 𝒦₁ {B = B} σ₁) (exts 𝒦₂ σ₂) (exts 𝒦₃ σ₃))
    → (∀ {Γ Δ Θ} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ}
        → R σ₁ σ₂ σ₃ → ∀ {A} (x : Var Γ A)
        → trav 𝒦₂ σ₂ (Kit.tm 𝒦₁ (σ₁ x)) ≡ Kit.tm 𝒦₃ (σ₃ x))
    → ∀ {Γ Δ Θ} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ}
      → R σ₁ σ₂ σ₃ → ∀ {A} (M : Tm Γ A)
      → trav 𝒦₂ σ₂ (trav 𝒦₁ σ₁ M) ≡ trav 𝒦₃ σ₃ M

  {- and substituting variables for themselves is the identity -}
  SubId : Set
  SubId =
    ∀ {Γ A} {σ : Sub tmK Γ Γ}
    → (∀ {B} (x : Var Γ B) → σ x ≡ ` x)
    → (M : Tm Γ A)
    → sub σ M ≡ M

  {- what both kits satisfy -}
  record Laws (𝒦 : Kit) : Set where
    field
      tm-vr : ∀ {Γ A} (x : Var Γ A) → Kit.tm 𝒦 (Kit.vr 𝒦 x) ≡ ` x
      tm-wk : ∀ {Γ A B} (k : Kit.K 𝒦 Γ A)
        → Kit.tm 𝒦 (Kit.wk 𝒦 {B = B} k) ≡ ⇑ (Kit.tm 𝒦 k)
      exts-ren : ∀ {Γ Δ A B} (τ : Sub 𝒦 Γ Δ) (M : Tm Γ A)
        → trav 𝒦 (exts 𝒦 {B = B} τ) (⇑ M) ≡ ⇑ (trav 𝒦 τ M)
