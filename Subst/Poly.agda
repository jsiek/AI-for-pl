{-

  File Charter:
    * Renaming and substitution for a polymorphic language (System F
      style): terms whose types contain type variables, and a binder of
      type variables in terms (`Λ`), on top of the one-level kit library
      (Subst/Kit.agda) used for the types.
    * Term contexts are contexts `Ctx (Ty Δ)` (Subst/Scope.agda) of types
      with type variables in `Δ`; the body of a type abstraction is in the
      context `⇑ᶜ Γ`, the weakening of `Γ` past the new type variable.
    * There are two traversals of terms, both supplied by the language:
        - `travᵀ` acts on the type variables of a term, by a type-level
          kit `𝒯` (a renaming or a substitution of types `θ`), with a map
          `ρ : TyRen 𝒯 θ Γ Γ'` of the term variables along `θ`;
        - `trav` acts on the term variables of a term, by a term-level
          kit `𝒦` (a renaming or a substitution of terms), and goes under
          a type binder by `⇑s`, which needs the term-level kit to weaken
          past a type variable (`wkα`); for the kit of terms that is `⇑ᵀ`,
          the type weakening of terms by `travᵀ`.
      The term-level traversal keeps the types fixed, so a term renaming
      or substitution has exactly the type of the term it acts on.
    * The only casts are by equations between types, at a type binder
      (`⇑ρ`, `instᵛ`, on variables only) and wherever the language needs
      them in `travᵀ`.
    * Exports: `Ty`, `Cx`, `⇑ᵗ`, `_[_]ᵗ`, `TyKit`, `renKᵗ`, `subKᵗ`,
      `act`, `TyRen`, `mapᶜ`, `mapᵛ`, `⇑ᶜ`, `⇑ᵛ`, `extρ`, `⇑ρ`, `instᵛ`;
      and, in the module `Terms`, `Kit`, `Sub`, `exts`, `⇑s`, `varK`,
      `ids`, `_•_`, given `travᵀ`: `renᵀ`, `subᵀ`, `⇑ᵀ`, `_[_]ᵀ`, and
      given also `trav`: `ren`, `⇑`, `tmK`, `sub`, `_[_]`.
    * The laws are in Subst/proof/Poly.agda.

-}

open import Subst.Scope using (Scope; Ctx; ∅; _,_; _∋_; Z; S_)
import Subst.Kit
import Subst.proof.Kit
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
  renaming (subst to substEq)

module Subst.Poly
  (𝒮 : Scope) (let open Scope 𝒮)
  (⋆ : Sort)
  (Typ : Sc → Sort → Set)
  (`ᵗ_ : ∀ {Δ s} → Var Δ s → Typ Δ s)
  (let module TK = Subst.Kit 𝒮 Typ `ᵗ_)
  (travᵗ : (𝒦 : TK.Kit) → ∀ {Δ Δ' s} → TK.Sub 𝒦 Δ Δ' → Typ Δ s → Typ Δ' s)
  (travᵗ-var : ∀ 𝒦 {Δ Δ' s} (σ : TK.Sub 𝒦 Δ Δ') (α : Var Δ s)
    → travᵗ 𝒦 σ (`ᵗ α) ≡ TK.Kit.tm 𝒦 (σ α))
  (let module TP = Subst.proof.Kit.Traversal 𝒮 Typ `ᵗ_ travᵗ travᵗ-var)
  (fuseᵗ : TP.Fuse) (sub-idᵗ : TP.SubId)
  where

module TL = TP.Lemmas fuseᵗ sub-idᵗ

{- Types and contexts -------------------------------------------------------}

{- the types: the syntax of the sort of the type variables -}
Ty : Sc → Set
Ty Δ = Typ Δ ⋆

{- weakening a type past a type variable, and instantiating the type
   variable bound last -}
⇑ᵗ : ∀ {Δ} → Ty Δ → Ty (Δ ▷ ⋆)
⇑ᵗ = TP.⇑

infixl 8 _[_]ᵗ
_[_]ᵗ : ∀ {Δ} → Ty (Δ ▷ ⋆) → Ty Δ → Ty Δ
A [ B ]ᵗ = A TP.[ B ]

{- term contexts -}
Cx : Sc → Set
Cx Δ = Ctx (Ty Δ)

{- A type-level kit, with its laws: the renamings or the substitutions of
   types. -}
record TyKit : Set₁ where
  field
    kit : TK.Kit
    laws : TP.Laws kit

renKᵗ : TyKit
renKᵗ = record { kit = TK.varK ; laws = TL.varL }

subKᵗ : TyKit
subKᵗ = record { kit = TP.tmK ; laws = TL.tmL }

{- the action of a type-level kit on types -}
act : ∀ (𝒯 : TyKit) {Δ Δ'} → TK.Sub (TyKit.kit 𝒯) Δ Δ' → Ty Δ → Ty Δ'
act 𝒯 θ A = travᵗ (TyKit.kit 𝒯) θ A

{- Term variables along a map of types --------------------------------------}

{- a map of the term variables of Γ to the term variables of Γ' along the
   map θ of types -}
TyRen : ∀ (𝒯 : TyKit) {Δ Δ'} → TK.Sub (TyKit.kit 𝒯) Δ Δ' → Cx Δ → Cx Δ'
  → Set
TyRen 𝒯 θ Γ Γ' = ∀ {A} → Γ ∋ A → Γ' ∋ act 𝒯 θ A

conv∋ : ∀ {Δ} {Γ : Cx Δ} {A B : Ty Δ} → A ≡ B → Γ ∋ A → Γ ∋ B
conv∋ {Γ = Γ} = substEq (Γ ∋_)

{- the context of the images of the types of Γ, and the canonical map of
   its variables -}
mapᶜ : ∀ (𝒯 : TyKit) {Δ Δ'} → TK.Sub (TyKit.kit 𝒯) Δ Δ' → Cx Δ → Cx Δ'
mapᶜ 𝒯 θ ∅ = ∅
mapᶜ 𝒯 θ (Γ , A) = mapᶜ 𝒯 θ Γ , act 𝒯 θ A

mapᵛ : ∀ (𝒯 : TyKit) {Δ Δ'} (θ : TK.Sub (TyKit.kit 𝒯) Δ Δ') {Γ : Cx Δ}
  → TyRen 𝒯 θ Γ (mapᶜ 𝒯 θ Γ)
mapᵛ 𝒯 θ Z = Z
mapᵛ 𝒯 θ (S x) = S (mapᵛ 𝒯 θ x)

{- weakening a context, and its variables, past a type variable -}
⇑ᶜ : ∀ {Δ} → Cx Δ → Cx (Δ ▷ ⋆)
⇑ᶜ = mapᶜ renKᵗ there

⇑ᵛ : ∀ {Δ} {Γ : Cx Δ} → TyRen renKᵗ there Γ (⇑ᶜ Γ)
⇑ᵛ = mapᵛ renKᵗ there

{- under a term binder -}
extρ : ∀ (𝒯 : TyKit) {Δ Δ'} (θ : TK.Sub (TyKit.kit 𝒯) Δ Δ')
  {Γ : Cx Δ} {Γ' : Cx Δ'} {B : Ty Δ}
  → TyRen 𝒯 θ Γ Γ'
  → TyRen 𝒯 θ (Γ , B) (Γ' , act 𝒯 θ B)
extρ 𝒯 θ ρ Z = Z
extρ 𝒯 θ ρ (S x) = S (ρ x)

{- under a type binder -}
⇑ρ : ∀ (𝒯 : TyKit) {Δ Δ'} (θ : TK.Sub (TyKit.kit 𝒯) Δ Δ')
  {Γ : Cx Δ} {Γ' : Cx Δ'}
  → TyRen 𝒯 θ Γ Γ'
  → TyRen 𝒯 (TK.exts (TyKit.kit 𝒯) θ) (⇑ᶜ Γ) (⇑ᶜ Γ')
⇑ρ 𝒯 θ {Γ , B} ρ Z =
  conv∋ (sym (TP.Laws.exts-ren (TyKit.laws 𝒯) θ B)) (⇑ᵛ (ρ Z))
⇑ρ 𝒯 θ {Γ , B} ρ (S x) = ⇑ρ 𝒯 θ (λ y → ρ (S y)) x

{- instantiating the type variable bound last by B -}
instᵛ : ∀ {Δ} {Γ : Cx Δ} (B : Ty Δ) → TyRen subKᵗ (B TK.• TK.ids) (⇑ᶜ Γ) Γ
instᵛ {Γ = Γ , D} B Z = conv∋ (sym (TL.⇑-[] D B)) Z
instᵛ {Γ = Γ , D} B (S x) = S (instᵛ B x)

{- Terms ---------------------------------------------------------------------}

module Terms
  (Tm : ∀ {Δ} → Cx Δ → Ty Δ → Set)
  (`_ : ∀ {Δ} {Γ : Cx Δ} {A} → Γ ∋ A → Tm Γ A)
  where

  convᵀ : ∀ {Δ} {Γ : Cx Δ} {A B : Ty Δ} → A ≡ B → Tm Γ A → Tm Γ B
  convᵀ {Γ = Γ} = substEq (Tm Γ)

  {- A term-level kit: what a term variable is mapped to (`K`), how a
     variable is one (`vr`), how one is a term (`tm`), how one is moved
     under a term binder (`wk`) and under a type binder (`wkα`). -}
  record Kit : Set₁ where
    field
      K : ∀ {Δ} → Cx Δ → Ty Δ → Set
      vr : ∀ {Δ} {Γ : Cx Δ} {A} → Γ ∋ A → K Γ A
      tm : ∀ {Δ} {Γ : Cx Δ} {A} → K Γ A → Tm Γ A
      wk : ∀ {Δ} {Γ : Cx Δ} {A B} → K Γ A → K (Γ , B) A
      wkα : ∀ {Δ} {Γ : Cx Δ} {A} → K Γ A → K (⇑ᶜ Γ) (⇑ᵗ A)

  Sub : Kit → ∀ {Δ} → Cx Δ → Cx Δ → Set
  Sub 𝒦 Γ Γ' = ∀ {A} → Γ ∋ A → Kit.K 𝒦 Γ' A

  {- under a term binder -}
  exts : ∀ (𝒦 : Kit) {Δ} {Γ Γ' : Cx Δ} {B}
    → Sub 𝒦 Γ Γ' → Sub 𝒦 (Γ , B) (Γ' , B)
  exts 𝒦 σ Z = Kit.vr 𝒦 Z
  exts 𝒦 σ (S x) = Kit.wk 𝒦 (σ x)

  {- under a type binder -}
  ⇑s : ∀ (𝒦 : Kit) {Δ} {Γ Γ' : Cx Δ}
    → Sub 𝒦 Γ Γ' → Sub 𝒦 (⇑ᶜ Γ) (⇑ᶜ Γ')
  ⇑s 𝒦 {Γ = Γ , B} σ Z = Kit.wkα 𝒦 (σ Z)
  ⇑s 𝒦 {Γ = Γ , B} σ (S x) = ⇑s 𝒦 (λ y → σ (S y)) x

  {- The kit of variables.  Its traversal is renaming. -}
  varK : Kit
  varK = record { K = _∋_ ; vr = λ x → x ; tm = `_ ; wk = S_ ; wkα = ⇑ᵛ }

  ids : ∀ {Δ} {Γ : Cx Δ} {A} → Γ ∋ A → Tm Γ A
  ids = `_

  infixr 6 _•_
  _•_ : ∀ {Δ} {Γ Γ' : Cx Δ} {B}
    → Tm Γ' B
    → (∀ {A} → Γ ∋ A → Tm Γ' A)
    → ∀ {A} → Γ , B ∋ A → Tm Γ' A
  (M • σ) Z = M
  (M • σ) (S x) = σ x

  {- Acting on the type variables of terms --------------------------------}

  module TypeSubstitution
    (travᵀ : ∀ (𝒯 : TyKit) {Δ Δ'} (θ : TK.Sub (TyKit.kit 𝒯) Δ Δ')
      {Γ : Cx Δ} {Γ' : Cx Δ'} {A}
      → TyRen 𝒯 θ Γ Γ' → Tm Γ A → Tm Γ' (act 𝒯 θ A))
    where

    {- renaming and substitution of types in terms, to the canonical
       contexts -}
    renᵀ : ∀ {Δ Δ'} (θ : TK.Sub TK.varK Δ Δ') {Γ : Cx Δ} {A}
      → Tm Γ A → Tm (mapᶜ renKᵗ θ Γ) (act renKᵗ θ A)
    renᵀ θ = travᵀ renKᵗ θ (mapᵛ renKᵗ θ)

    subᵀ : ∀ {Δ Δ'} (θ : TK.Sub TP.tmK Δ Δ') {Γ : Cx Δ} {A}
      → Tm Γ A → Tm (mapᶜ subKᵗ θ Γ) (act subKᵗ θ A)
    subᵀ θ = travᵀ subKᵗ θ (mapᵛ subKᵗ θ)

    {- weakening a term past a type variable -}
    ⇑ᵀ : ∀ {Δ} {Γ : Cx Δ} {A} → Tm Γ A → Tm (⇑ᶜ Γ) (⇑ᵗ A)
    ⇑ᵀ = renᵀ there

    {- instantiating the type variable bound last in a term -}
    infixl 8 _[_]ᵀ
    _[_]ᵀ : ∀ {Δ} {Γ : Cx Δ} {A}
      → Tm (⇑ᶜ Γ) A → (B : Ty Δ) → Tm Γ (A [ B ]ᵗ)
    N [ B ]ᵀ = travᵀ subKᵗ (B TK.• TK.ids) (instᵛ B) N

    {- Acting on the term variables of terms ------------------------------}

    module Substitution
      (trav : ∀ (𝒦 : Kit) {Δ} {Γ Γ' : Cx Δ} {A}
        → Sub 𝒦 Γ Γ' → Tm Γ A → Tm Γ' A)
      where

      ren : ∀ {Δ} {Γ Γ' : Cx Δ} {A}
        → (∀ {B} → Γ ∋ B → Γ' ∋ B) → Tm Γ A → Tm Γ' A
      ren r = trav varK r

      {- weakening past a term variable -}
      ⇑ : ∀ {Δ} {Γ : Cx Δ} {A B} → Tm Γ A → Tm (Γ , B) A
      ⇑ = ren S_

      {- The kit of terms.  Its traversal is substitution. -}
      tmK : Kit
      tmK = record { K = Tm ; vr = `_ ; tm = λ M → M ; wk = ⇑ ; wkα = ⇑ᵀ }

      sub : ∀ {Δ} {Γ Γ' : Cx Δ} {A}
        → (∀ {B} → Γ ∋ B → Tm Γ' B) → Tm Γ A → Tm Γ' A
      sub σ = trav tmK σ

      infixr 5 _⨟_
      _⨟_ : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Cx Δ}
        → Sub tmK Γ₁ Γ₂ → Sub tmK Γ₂ Γ₃ → Sub tmK Γ₁ Γ₃
      (σ ⨟ τ) x = sub τ (σ x)

      {- substituting for the term variable bound last -}
      infixl 8 _[_]
      _[_] : ∀ {Δ} {Γ : Cx Δ} {A B} → Tm (Γ , B) A → Tm Γ B → Tm Γ A
      N [ M ] = sub (M • ids) N
