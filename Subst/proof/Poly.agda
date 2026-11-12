{-

  File Charter:
    * Laws of renaming and substitution for a polymorphic language
      (Subst/Poly.agda).  All equations between substitutions are
      pointwise, so no function extensionality is needed.
    * Acting on the type variables of terms (`travᵀ`) changes the types of
      terms, by equations that hold only propositionally, so its laws are
      stated with heterogeneous equality `_≅_`.  The language proves, by
      induction on its terms:
        - `Fuseᵀ`: two traversals `travᵀ` fuse into one, given the
          hypotheses `FuseHypᵀ` (the maps of types fuse pointwise, the
          target contexts are equal, and the maps of term variables fuse
          pointwise);
        - `Idᵀ`: a traversal `travᵀ` that is the identity on type and term
          variables (`IdHypᵀ`) is the identity.
      The hypotheses are closed under binders (`fuseᵀ-ext`, `fuseᵀ-⇑`,
      `idᵀ-ext`, `idᵀ-⇑`).
    * Acting on the term variables of terms (`trav`) keeps the types, so
      its laws are homogeneous, after the one-level library
      (Subst/proof/Kit.agda).  The language proves, by induction on its
      terms:
        - `Commute`: a term-level traversal after a type-level one is a
          type-level traversal after a term-level one;
        - `Fuse`: two term-level traversals fuse into one;
        - `SubId`: the identity substitution.
      The module `Lemmas` derives the rest.

-}

open import Subst.Scope using (Scope; Ctx; ∅; _,_; _∋_; Z; S_)
import Subst.Kit
import Subst.proof.Kit
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans;
  cong; cong₂; module ≡-Reasoning)
  renaming (subst to substEq)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl;
  ≡-to-≅; ≅-to-≡)

module Subst.proof.Poly
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

open import Subst.Poly 𝒮 ⋆ Typ `ᵗ_ travᵗ travᵗ-var fuseᵗ sub-idᵗ public
module TPK = Subst.proof.Kit 𝒮 Typ `ᵗ_
open ≡-Reasoning

{- Variables, heterogeneously ------------------------------------------------}

Z-≅ : ∀ {Δ} {Γ Γ' : Cx Δ} {A A' : Ty Δ}
  → Γ ≡ Γ' → A ≡ A'
  → Z {Γ = Γ} {A = A} ≅ Z {Γ = Γ'} {A = A'}
Z-≅ refl refl = refl

S-≅ : ∀ {Δ} {Γ Γ' : Cx Δ} {A A' B B' : Ty Δ}
  {x : Γ ∋ A} {x' : Γ' ∋ A'}
  → Γ ≡ Γ' → A ≡ A' → B ≡ B' → x ≅ x'
  → S_ {B = B} x ≅ S_ {B = B'} x'
S-≅ refl refl refl refl = refl

⇑ᵛ-≅ : ∀ {Δ} {Γ Γ' : Cx Δ} {A A' : Ty Δ} {x : Γ ∋ A} {x' : Γ' ∋ A'}
  → Γ ≡ Γ' → A ≡ A' → x ≅ x'
  → ⇑ᵛ x ≅ ⇑ᵛ x'
⇑ᵛ-≅ refl refl refl = refl

conv∋-≅ : ∀ {Δ} {Γ : Cx Δ} {A B : Ty Δ} (p : A ≡ B) (x : Γ ∋ A)
  → conv∋ p x ≅ x
conv∋-≅ refl x = refl

{- `⇑ρ` on a cast variable, and on a weakened variable -}
⇑ρ-conv : ∀ (𝒯 : TyKit) {Δ Δ'} (θ : TK.Sub (TyKit.kit 𝒯) Δ Δ')
  {Γ : Cx Δ} {Γ' : Cx Δ'} (ρ : TyRen 𝒯 θ Γ Γ')
  {C C' : Ty (Δ ▷ ⋆)} (p : C ≡ C') (y : ⇑ᶜ Γ ∋ C)
  → ⇑ρ 𝒯 θ ρ (conv∋ p y) ≅ ⇑ρ 𝒯 θ ρ y
⇑ρ-conv 𝒯 θ ρ refl y = refl

⇑ρ-⇑ᵛ : ∀ (𝒯 : TyKit) {Δ Δ'} (θ : TK.Sub (TyKit.kit 𝒯) Δ Δ')
  {Γ : Cx Δ} {Γ' : Cx Δ'} (ρ : TyRen 𝒯 θ Γ Γ') {C : Ty Δ} (y : Γ ∋ C)
  → ⇑ρ 𝒯 θ ρ (⇑ᵛ y)
    ≡ conv∋ (sym (TP.Laws.exts-ren (TyKit.laws 𝒯) θ C)) (⇑ᵛ (ρ y))
⇑ρ-⇑ᵛ 𝒯 θ ρ Z = refl
⇑ρ-⇑ᵛ 𝒯 θ ρ (S y) = ⇑ρ-⇑ᵛ 𝒯 θ (λ z → ρ (S z)) y

⇑ρ-⇑ᵛ-≅ : ∀ (𝒯 : TyKit) {Δ Δ'} (θ : TK.Sub (TyKit.kit 𝒯) Δ Δ')
  {Γ : Cx Δ} {Γ' : Cx Δ'} (ρ : TyRen 𝒯 θ Γ Γ') {C : Ty Δ} (y : Γ ∋ C)
  → ⇑ρ 𝒯 θ ρ (⇑ᵛ y) ≅ ⇑ᵛ (ρ y)
⇑ρ-⇑ᵛ-≅ 𝒯 θ ρ {C} y =
  H.trans (≡-to-≅ (⇑ρ-⇑ᵛ 𝒯 θ ρ y))
    (conv∋-≅ (sym (TP.Laws.exts-ren (TyKit.laws 𝒯) θ C)) (⇑ᵛ (ρ y)))

{- a renaming of term variables, lifted under a type binder -}
⇑s-var : ∀ {Δ} {Γ Γ' : Cx Δ}
  → (∀ {A} → Γ ∋ A → Γ' ∋ A)
  → ∀ {A} → ⇑ᶜ Γ ∋ A → ⇑ᶜ Γ' ∋ A
⇑s-var {Γ = Γ , B} r Z = ⇑ᵛ (r Z)
⇑s-var {Γ = Γ , B} r (S x) = ⇑s-var (λ y → r (S y)) x

⇑s-var-S : ∀ {Δ} {Γ Γ' : Cx Δ} {B : Ty Δ} (r : ∀ {A} → Γ ∋ A → Γ' ∋ A)
  → ∀ {A} (x : ⇑ᶜ Γ ∋ A)
  → ⇑s-var (λ y → S_ {B = B} (r y)) x ≡ S (⇑s-var r x)
⇑s-var-S {Γ = Γ , C} r Z = refl
⇑s-var-S {Γ = Γ , C} r (S x) = ⇑s-var-S (λ y → r (S y)) x

⇑s-var-id : ∀ {Δ} {Γ : Cx Δ} {A} (x : ⇑ᶜ Γ ∋ A) → ⇑s-var (λ y → y) x ≡ x
⇑s-var-id {Γ = Γ , B} Z = refl
⇑s-var-id {Γ = Γ , B} (S x) =
  trans (⇑s-var-S (λ y → y) x) (cong S_ (⇑s-var-id x))

{- the canonical context of a map that is the identity on types -}
mapᶜ-id : ∀ (𝒯 : TyKit) {Δ} (θ : TK.Sub (TyKit.kit 𝒯) Δ Δ)
  → (∀ (A : Ty Δ) → act 𝒯 θ A ≡ A)
  → (Γ : Cx Δ) → mapᶜ 𝒯 θ Γ ≡ Γ
mapᶜ-id 𝒯 θ h ∅ = refl
mapᶜ-id 𝒯 θ h (Γ , A) = cong₂ _,_ (mapᶜ-id 𝒯 θ h Γ) (h A)

mapᵛ-id : ∀ (𝒯 : TyKit) {Δ} (θ : TK.Sub (TyKit.kit 𝒯) Δ Δ)
  (h : ∀ (A : Ty Δ) → act 𝒯 θ A ≡ A)
  → ∀ {Γ : Cx Δ} {A} (x : Γ ∋ A) → mapᵛ 𝒯 θ x ≅ x
mapᵛ-id 𝒯 θ h {Γ , B} Z = Z-≅ (mapᶜ-id 𝒯 θ h Γ) (h B)
mapᵛ-id 𝒯 θ h {Γ , B} {A} (S x) =
  S-≅ (mapᶜ-id 𝒯 θ h Γ) (h A) (h B) (mapᵛ-id 𝒯 θ h x)

{- Hypotheses for the laws of `travᵀ` -----------------------------------------}

{- for fusing a traversal by θ₁, ρ₁ and one by θ₂, ρ₂ into one by θ₃, ρ₃ -}
record FuseHypᵀ (𝒯₁ 𝒯₂ 𝒯₃ : TyKit) {Δ Δ' Δ''}
  (θ₁ : TK.Sub (TyKit.kit 𝒯₁) Δ Δ')
  (θ₂ : TK.Sub (TyKit.kit 𝒯₂) Δ' Δ'')
  (θ₃ : TK.Sub (TyKit.kit 𝒯₃) Δ Δ'')
  {Γ : Cx Δ} {Γ' : Cx Δ'} {Γ'' Γ''' : Cx Δ''}
  (ρ₁ : TyRen 𝒯₁ θ₁ Γ Γ') (ρ₂ : TyRen 𝒯₂ θ₂ Γ' Γ'') (ρ₃ : TyRen 𝒯₃ θ₃ Γ Γ''')
  : Set where
  field
    ty-var : ∀ {s} (α : Var Δ s)
      → travᵗ (TyKit.kit 𝒯₂) θ₂ (TK.Kit.tm (TyKit.kit 𝒯₁) (θ₁ α))
        ≡ TK.Kit.tm (TyKit.kit 𝒯₃) (θ₃ α)
    ctx : Γ'' ≡ Γ'''
    var : ∀ {A} (x : Γ ∋ A) → ρ₂ (ρ₁ x) ≅ ρ₃ x

{- for a traversal by θ, ρ that is the identity -}
record IdHypᵀ (𝒯 : TyKit) {Δ} (θ : TK.Sub (TyKit.kit 𝒯) Δ Δ)
  {Γ Γ' : Cx Δ} (ρ : TyRen 𝒯 θ Γ Γ') : Set where
  field
    ty-var : ∀ {s} (α : Var Δ s) → TK.Kit.tm (TyKit.kit 𝒯) (θ α) ≡ `ᵗ α
    ctx : Γ' ≡ Γ
    var : ∀ {A} (x : Γ ∋ A) → ρ x ≅ x

module _ {𝒯₁ 𝒯₂ 𝒯₃ : TyKit} {Δ Δ' Δ''}
  {θ₁ : TK.Sub (TyKit.kit 𝒯₁) Δ Δ'}
  {θ₂ : TK.Sub (TyKit.kit 𝒯₂) Δ' Δ''}
  {θ₃ : TK.Sub (TyKit.kit 𝒯₃) Δ Δ''}
  where

  {- the types fuse -}
  fuseᵀ-ty : ∀ {Γ : Cx Δ} {Γ' : Cx Δ'} {Γ'' Γ''' : Cx Δ''}
    {ρ₁ : TyRen 𝒯₁ θ₁ Γ Γ'} {ρ₂ : TyRen 𝒯₂ θ₂ Γ' Γ''}
    {ρ₃ : TyRen 𝒯₃ θ₃ Γ Γ'''}
    → FuseHypᵀ 𝒯₁ 𝒯₂ 𝒯₃ θ₁ θ₂ θ₃ ρ₁ ρ₂ ρ₃
    → ∀ {s} (A : Typ Δ s)
    → travᵗ (TyKit.kit 𝒯₂) θ₂ (travᵗ (TyKit.kit 𝒯₁) θ₁ A)
      ≡ travᵗ (TyKit.kit 𝒯₃) θ₃ A
  fuseᵀ-ty h =
    TL.trav-trav (TyKit.laws 𝒯₁) (TyKit.laws 𝒯₂) (TyKit.laws 𝒯₃)
      (FuseHypᵀ.ty-var h)

  {- under a term binder -}
  fuseᵀ-ext : ∀ {Γ : Cx Δ} {Γ' : Cx Δ'} {Γ'' Γ''' : Cx Δ''} {B : Ty Δ}
    {ρ₁ : TyRen 𝒯₁ θ₁ Γ Γ'} {ρ₂ : TyRen 𝒯₂ θ₂ Γ' Γ''}
    {ρ₃ : TyRen 𝒯₃ θ₃ Γ Γ'''}
    → FuseHypᵀ 𝒯₁ 𝒯₂ 𝒯₃ θ₁ θ₂ θ₃ ρ₁ ρ₂ ρ₃
    → FuseHypᵀ 𝒯₁ 𝒯₂ 𝒯₃ θ₁ θ₂ θ₃
        (extρ 𝒯₁ θ₁ {B = B} ρ₁) (extρ 𝒯₂ θ₂ ρ₂) (extρ 𝒯₃ θ₃ ρ₃)
  fuseᵀ-ext {B = B} h = record
    { ty-var = FuseHypᵀ.ty-var h
    ; ctx = cong₂ _,_ (FuseHypᵀ.ctx h) (fuseᵀ-ty h B)
    ; var = λ { Z → Z-≅ (FuseHypᵀ.ctx h) (fuseᵀ-ty h B)
              ; (S x) → S-≅ (FuseHypᵀ.ctx h) (fuseᵀ-ty h _) (fuseᵀ-ty h B)
                          (FuseHypᵀ.var h x) }
    }

  private
    ⇑ρ-fuse : ∀ {Γ : Cx Δ} {Γ' : Cx Δ'} {Γ'' Γ''' : Cx Δ''}
      (ρ₁ : TyRen 𝒯₁ θ₁ Γ Γ') (ρ₂ : TyRen 𝒯₂ θ₂ Γ' Γ'')
      (ρ₃ : TyRen 𝒯₃ θ₃ Γ Γ''')
      → Γ'' ≡ Γ'''
      → (∀ (A : Ty Δ) → act 𝒯₂ θ₂ (act 𝒯₁ θ₁ A) ≡ act 𝒯₃ θ₃ A)
      → (∀ {A} (x : Γ ∋ A) → ρ₂ (ρ₁ x) ≅ ρ₃ x)
      → ∀ {C} (x : ⇑ᶜ Γ ∋ C)
      → ⇑ρ 𝒯₂ θ₂ ρ₂ (⇑ρ 𝒯₁ θ₁ ρ₁ x) ≅ ⇑ρ 𝒯₃ θ₃ ρ₃ x
    ⇑ρ-fuse {Γ , B} ρ₁ ρ₂ ρ₃ ctx ty var Z =
      H.trans (⇑ρ-conv 𝒯₂ θ₂ ρ₂ _ (⇑ᵛ (ρ₁ Z)))
        (H.trans (⇑ρ-⇑ᵛ-≅ 𝒯₂ θ₂ ρ₂ (ρ₁ Z))
          (H.trans (⇑ᵛ-≅ ctx (ty B) (var Z))
            (H.sym (conv∋-≅ _ (⇑ᵛ (ρ₃ Z))))))
    ⇑ρ-fuse {Γ , B} ρ₁ ρ₂ ρ₃ ctx ty var (S x) =
      ⇑ρ-fuse (λ y → ρ₁ (S y)) ρ₂ (λ y → ρ₃ (S y)) ctx ty (λ y → var (S y)) x

  {- under a type binder -}
  fuseᵀ-⇑ : ∀ {Γ : Cx Δ} {Γ' : Cx Δ'} {Γ'' Γ''' : Cx Δ''}
    {ρ₁ : TyRen 𝒯₁ θ₁ Γ Γ'} {ρ₂ : TyRen 𝒯₂ θ₂ Γ' Γ''}
    {ρ₃ : TyRen 𝒯₃ θ₃ Γ Γ'''}
    → FuseHypᵀ 𝒯₁ 𝒯₂ 𝒯₃ θ₁ θ₂ θ₃ ρ₁ ρ₂ ρ₃
    → FuseHypᵀ 𝒯₁ 𝒯₂ 𝒯₃
        (TK.exts (TyKit.kit 𝒯₁) {B = ⋆} θ₁) (TK.exts (TyKit.kit 𝒯₂) θ₂)
        (TK.exts (TyKit.kit 𝒯₃) θ₃)
        (⇑ρ 𝒯₁ θ₁ ρ₁) (⇑ρ 𝒯₂ θ₂ ρ₂) (⇑ρ 𝒯₃ θ₃ ρ₃)
  fuseᵀ-⇑ {ρ₁ = ρ₁} {ρ₂} {ρ₃} h = record
    { ty-var = TP.trav-trav-exts (TyKit.laws 𝒯₁) (TyKit.laws 𝒯₂)
                 (TyKit.laws 𝒯₃) (FuseHypᵀ.ty-var h)
    ; ctx = cong ⇑ᶜ (FuseHypᵀ.ctx h)
    ; var = ⇑ρ-fuse ρ₁ ρ₂ ρ₃ (FuseHypᵀ.ctx h) (fuseᵀ-ty h) (FuseHypᵀ.var h)
    }

module _ {𝒯 : TyKit} {Δ} {θ : TK.Sub (TyKit.kit 𝒯) Δ Δ} where

  {- the types stay -}
  idᵀ-ty : ∀ {Γ Γ' : Cx Δ} {ρ : TyRen 𝒯 θ Γ Γ'}
    → IdHypᵀ 𝒯 θ ρ
    → ∀ {s} (A : Typ Δ s) → travᵗ (TyKit.kit 𝒯) θ A ≡ A
  idᵀ-ty h = TL.trav-id (TyKit.laws 𝒯) (IdHypᵀ.ty-var h)

  {- under a term binder -}
  idᵀ-ext : ∀ {Γ Γ' : Cx Δ} {B : Ty Δ} {ρ : TyRen 𝒯 θ Γ Γ'}
    → IdHypᵀ 𝒯 θ ρ
    → IdHypᵀ 𝒯 θ (extρ 𝒯 θ {B = B} ρ)
  idᵀ-ext {B = B} h = record
    { ty-var = IdHypᵀ.ty-var h
    ; ctx = cong₂ _,_ (IdHypᵀ.ctx h) (idᵀ-ty h B)
    ; var = λ { Z → Z-≅ (IdHypᵀ.ctx h) (idᵀ-ty h B)
              ; (S x) → S-≅ (IdHypᵀ.ctx h) (idᵀ-ty h _) (idᵀ-ty h B)
                          (IdHypᵀ.var h x) }
    }

  private
    {- `⇑ρ` of a map that agrees with a renaming of term variables -}
    ⇑ρ-ren : ∀ {Γ₀ Γ' Γ'' : Cx Δ}
      (ρ : TyRen 𝒯 θ Γ₀ Γ') (r : ∀ {A} → Γ₀ ∋ A → Γ'' ∋ A)
      → Γ' ≡ Γ''
      → (∀ (A : Ty Δ) → act 𝒯 θ A ≡ A)
      → (∀ {A} (y : Γ₀ ∋ A) → ρ y ≅ r y)
      → ∀ {C} (x : ⇑ᶜ Γ₀ ∋ C) → ⇑ρ 𝒯 θ ρ x ≅ ⇑s-var r x
    ⇑ρ-ren {Γ₀ , B} ρ r ctx ty h Z =
      H.trans (conv∋-≅ _ (⇑ᵛ (ρ Z))) (⇑ᵛ-≅ ctx (ty B) (h Z))
    ⇑ρ-ren {Γ₀ , B} ρ r ctx ty h (S x) =
      ⇑ρ-ren (λ y → ρ (S y)) (λ y → r (S y)) ctx ty (λ y → h (S y)) x

  {- under a type binder -}
  idᵀ-⇑ : ∀ {Γ Γ' : Cx Δ} {ρ : TyRen 𝒯 θ Γ Γ'}
    → IdHypᵀ 𝒯 θ ρ
    → IdHypᵀ 𝒯 (TK.exts (TyKit.kit 𝒯) {B = ⋆} θ) (⇑ρ 𝒯 θ ρ)
  idᵀ-⇑ {ρ = ρ} h = record
    { ty-var = TP.trav-id-exts (TyKit.laws 𝒯) (IdHypᵀ.ty-var h)
    ; ctx = cong ⇑ᶜ (IdHypᵀ.ctx h)
    ; var = λ x → H.trans
              (⇑ρ-ren ρ (λ y → y) (IdHypᵀ.ctx h) (idᵀ-ty h) (IdHypᵀ.var h) x)
              (≡-to-≅ (⇑s-var-id x))
    }

{- Terms ---------------------------------------------------------------------}

module TermLaws
  (Tm : ∀ {Δ} → Cx Δ → Ty Δ → Set)
  (`_ : ∀ {Δ} {Γ : Cx Δ} {A} → Γ ∋ A → Tm Γ A)
  where

  open Terms Tm `_ public

  convᵀ-≅ : ∀ {Δ} {Γ : Cx Δ} {A B : Ty Δ} (p : A ≡ B) (M : Tm Γ A)
    → convᵀ p M ≅ M
  convᵀ-≅ refl M = refl

  `-≅ : ∀ {Δ} {Γ Γ' : Cx Δ} {A A' : Ty Δ} {x : Γ ∋ A} {x' : Γ' ∋ A'}
    → Γ ≡ Γ' → A ≡ A' → x ≅ x'
    → ` x ≅ ` x'
  `-≅ refl refl refl = refl

  {- a cast of a thing of a term-level kit -}
  convK : ∀ (𝒦 : Kit) {Δ} {Γ : Cx Δ} {A B : Ty Δ}
    → A ≡ B → Kit.K 𝒦 Γ A → Kit.K 𝒦 Γ B
  convK 𝒦 {Γ = Γ} = substEq (Kit.K 𝒦 Γ)

  tm-convK : ∀ (𝒦 : Kit) {Δ} {Γ : Cx Δ} {A B : Ty Δ} (p : A ≡ B)
    (k : Kit.K 𝒦 Γ A)
    → Kit.tm 𝒦 (convK 𝒦 p k) ≡ convᵀ p (Kit.tm 𝒦 k)
  tm-convK 𝒦 refl k = refl

  {- `⇑s` on a cast variable, and on a weakened variable -}
  ⇑s-conv : ∀ (𝒦 : Kit) {Δ} {Γ Γ' : Cx Δ} (σ : Sub 𝒦 Γ Γ')
    {C C' : Ty (Δ ▷ ⋆)} (p : C ≡ C') (y : ⇑ᶜ Γ ∋ C)
    → ⇑s 𝒦 σ (conv∋ p y) ≡ convK 𝒦 p (⇑s 𝒦 σ y)
  ⇑s-conv 𝒦 σ refl y = refl

  ⇑s-⇑ᵛ : ∀ (𝒦 : Kit) {Δ} {Γ Γ' : Cx Δ} (σ : Sub 𝒦 Γ Γ') {C : Ty Δ}
    (y : Γ ∋ C)
    → ⇑s 𝒦 σ (⇑ᵛ y) ≡ Kit.wkα 𝒦 (σ y)
  ⇑s-⇑ᵛ 𝒦 σ Z = refl
  ⇑s-⇑ᵛ 𝒦 σ (S y) = ⇑s-⇑ᵛ 𝒦 (λ z → σ (S z)) y

  {- Acting on the type variables of terms --------------------------------}

  module TypeLaws
    (travᵀ : ∀ (𝒯 : TyKit) {Δ Δ'} (θ : TK.Sub (TyKit.kit 𝒯) Δ Δ')
      {Γ : Cx Δ} {Γ' : Cx Δ'} {A}
      → TyRen 𝒯 θ Γ Γ' → Tm Γ A → Tm Γ' (act 𝒯 θ A))
    (travᵀ-var : ∀ (𝒯 : TyKit) {Δ Δ'} (θ : TK.Sub (TyKit.kit 𝒯) Δ Δ')
      {Γ : Cx Δ} {Γ' : Cx Δ'} (ρ : TyRen 𝒯 θ Γ Γ') {A} (x : Γ ∋ A)
      → travᵀ 𝒯 θ ρ (` x) ≡ ` (ρ x))
    where

    open TypeSubstitution travᵀ public

    {- What a language proves by induction on its terms -------------------}

    Fuseᵀ : Set₁
    Fuseᵀ =
      ∀ {𝒯₁ 𝒯₂ 𝒯₃ : TyKit} {Δ Δ' Δ''}
      {θ₁ : TK.Sub (TyKit.kit 𝒯₁) Δ Δ'}
      {θ₂ : TK.Sub (TyKit.kit 𝒯₂) Δ' Δ''}
      {θ₃ : TK.Sub (TyKit.kit 𝒯₃) Δ Δ''}
      {Γ : Cx Δ} {Γ' : Cx Δ'} {Γ'' Γ''' : Cx Δ''}
      {ρ₁ : TyRen 𝒯₁ θ₁ Γ Γ'} {ρ₂ : TyRen 𝒯₂ θ₂ Γ' Γ''}
      {ρ₃ : TyRen 𝒯₃ θ₃ Γ Γ'''}
      → FuseHypᵀ 𝒯₁ 𝒯₂ 𝒯₃ θ₁ θ₂ θ₃ ρ₁ ρ₂ ρ₃
      → ∀ {A} (M : Tm Γ A)
      → travᵀ 𝒯₂ θ₂ ρ₂ (travᵀ 𝒯₁ θ₁ ρ₁ M) ≅ travᵀ 𝒯₃ θ₃ ρ₃ M

    Idᵀ : Set₁
    Idᵀ =
      ∀ {𝒯 : TyKit} {Δ} {θ : TK.Sub (TyKit.kit 𝒯) Δ Δ}
      {Γ Γ' : Cx Δ} {ρ : TyRen 𝒯 θ Γ Γ'}
      → IdHypᵀ 𝒯 θ ρ
      → ∀ {A} (M : Tm Γ A)
      → travᵀ 𝒯 θ ρ M ≅ M

    {- The consequences ---------------------------------------------------}

    module TypeLemmas (fuseᵀ : Fuseᵀ) (idᵀ : Idᵀ) where

      private
        instᵛ-⇑ᵛ : ∀ {Δ} {Γ : Cx Δ} (B : Ty Δ) {A} (x : Γ ∋ A)
          → instᵛ B (⇑ᵛ x) ≅ x
        instᵛ-⇑ᵛ {Γ = Γ , D} B Z = conv∋-≅ (sym (TL.⇑-[] D B)) Z
        instᵛ-⇑ᵛ {Γ = Γ , D} B {A} (S x) =
          S-≅ refl (TL.⇑-[] A B) refl (instᵛ-⇑ᵛ B x)

        sub-ids : ∀ {Δ} (A : Ty Δ) → act subKᵗ TK.ids A ≡ A
        sub-ids A = sub-idᵗ (λ _ → refl) A

      {- instantiating a weakened term -}
      ⇑ᵀ-[]ᵀ : ∀ {Δ} {Γ : Cx Δ} {A} (M : Tm Γ A) (B : Ty Δ)
        → ⇑ᵀ M [ B ]ᵀ ≅ M
      ⇑ᵀ-[]ᵀ {Γ = Γ} M B =
        H.trans
          (fuseᵀ {𝒯₁ = renKᵗ} {𝒯₂ = subKᵗ} {𝒯₃ = subKᵗ}
            {θ₁ = λ α → there α} {θ₂ = B TK.• TK.ids} {θ₃ = TK.ids}
            {ρ₁ = ⇑ᵛ} {ρ₂ = instᵛ B} {ρ₃ = mapᵛ subKᵗ TK.ids} (record
            { ty-var = λ α →
                trans (travᵗ-var TP.tmK (B TK.• TK.ids) (there α))
                  (TPK.cons-there {F = Typ _} B TK.ids α)
            ; ctx = sym (mapᶜ-id subKᵗ TK.ids sub-ids Γ)
            ; var = λ x →
                H.trans (instᵛ-⇑ᵛ B x)
                  (H.sym (mapᵛ-id subKᵗ TK.ids sub-ids x))
            }) M)
          (idᵀ {𝒯 = subKᵗ} {θ = TK.ids} {ρ = mapᵛ subKᵗ TK.ids} (record
            { ty-var = λ α → refl
            ; ctx = mapᶜ-id subKᵗ TK.ids sub-ids Γ
            ; var = mapᵛ-id subKᵗ TK.ids sub-ids
            }) M)

    {- Acting on the term variables of terms ------------------------------}

    module TermSubstLaws
      (trav : ∀ (𝒦 : Kit) {Δ} {Γ Γ' : Cx Δ} {A}
        → Sub 𝒦 Γ Γ' → Tm Γ A → Tm Γ' A)
      (trav-var : ∀ (𝒦 : Kit) {Δ} {Γ Γ' : Cx Δ} (σ : Sub 𝒦 Γ Γ') {A}
        (x : Γ ∋ A)
        → trav 𝒦 σ (` x) ≡ Kit.tm 𝒦 (σ x))
      where

      open Substitution trav public

      {- What a language proves by induction on its terms -----------------}

      Commute : Set₁
      Commute =
        ∀ (𝒦 : Kit) (𝒯 : TyKit)
        (R : ∀ {Δ Δ'} {θ : TK.Sub (TyKit.kit 𝒯) Δ Δ'}
             {Γ Γ₁ : Cx Δ} {Γ' Γ₁' : Cx Δ'}
           → Sub 𝒦 Γ Γ₁ → TyRen 𝒯 θ Γ Γ' → TyRen 𝒯 θ Γ₁ Γ₁'
           → Sub 𝒦 Γ' Γ₁' → Set)
        → (∀ {Δ Δ'} {θ : TK.Sub (TyKit.kit 𝒯) Δ Δ'}
             {Γ Γ₁ : Cx Δ} {Γ' Γ₁' : Cx Δ'} {B : Ty Δ}
             {σ : Sub 𝒦 Γ Γ₁} {ρ : TyRen 𝒯 θ Γ Γ'}
             {ρ₁ : TyRen 𝒯 θ Γ₁ Γ₁'} {σ' : Sub 𝒦 Γ' Γ₁'}
           → R σ ρ ρ₁ σ'
           → R (exts 𝒦 {B = B} σ) (extρ 𝒯 θ ρ) (extρ 𝒯 θ ρ₁) (exts 𝒦 σ'))
        → (∀ {Δ Δ'} {θ : TK.Sub (TyKit.kit 𝒯) Δ Δ'}
             {Γ Γ₁ : Cx Δ} {Γ' Γ₁' : Cx Δ'}
             {σ : Sub 𝒦 Γ Γ₁} {ρ : TyRen 𝒯 θ Γ Γ'}
             {ρ₁ : TyRen 𝒯 θ Γ₁ Γ₁'} {σ' : Sub 𝒦 Γ' Γ₁'}
           → R σ ρ ρ₁ σ'
           → R (⇑s 𝒦 σ) (⇑ρ 𝒯 θ ρ) (⇑ρ 𝒯 θ ρ₁) (⇑s 𝒦 σ'))
        → (∀ {Δ Δ'} {θ : TK.Sub (TyKit.kit 𝒯) Δ Δ'}
             {Γ Γ₁ : Cx Δ} {Γ' Γ₁' : Cx Δ'}
             {σ : Sub 𝒦 Γ Γ₁} {ρ : TyRen 𝒯 θ Γ Γ'}
             {ρ₁ : TyRen 𝒯 θ Γ₁ Γ₁'} {σ' : Sub 𝒦 Γ' Γ₁'}
           → R σ ρ ρ₁ σ'
           → ∀ {A} (x : Γ ∋ A)
           → trav 𝒦 σ' (` (ρ x)) ≡ travᵀ 𝒯 θ ρ₁ (Kit.tm 𝒦 (σ x)))
        → ∀ {Δ Δ'} {θ : TK.Sub (TyKit.kit 𝒯) Δ Δ'}
            {Γ Γ₁ : Cx Δ} {Γ' Γ₁' : Cx Δ'}
            {σ : Sub 𝒦 Γ Γ₁} {ρ : TyRen 𝒯 θ Γ Γ'}
            {ρ₁ : TyRen 𝒯 θ Γ₁ Γ₁'} {σ' : Sub 𝒦 Γ' Γ₁'}
          → R σ ρ ρ₁ σ'
          → ∀ {A} (M : Tm Γ A)
          → trav 𝒦 σ' (travᵀ 𝒯 θ ρ M) ≡ travᵀ 𝒯 θ ρ₁ (trav 𝒦 σ M)

      Fuse : Set₁
      Fuse =
        ∀ (𝒦₁ 𝒦₂ 𝒦₃ : Kit)
        (R : ∀ {Δ} {Γ Γ' Γ'' : Cx Δ}
           → Sub 𝒦₁ Γ Γ' → Sub 𝒦₂ Γ' Γ'' → Sub 𝒦₃ Γ Γ'' → Set)
        → (∀ {Δ} {Γ Γ' Γ'' : Cx Δ} {B : Ty Δ}
             {σ₁ : Sub 𝒦₁ Γ Γ'} {σ₂ : Sub 𝒦₂ Γ' Γ''} {σ₃ : Sub 𝒦₃ Γ Γ''}
           → R σ₁ σ₂ σ₃
           → R (exts 𝒦₁ {B = B} σ₁) (exts 𝒦₂ σ₂) (exts 𝒦₃ σ₃))
        → (∀ {Δ} {Γ Γ' Γ'' : Cx Δ}
             {σ₁ : Sub 𝒦₁ Γ Γ'} {σ₂ : Sub 𝒦₂ Γ' Γ''} {σ₃ : Sub 𝒦₃ Γ Γ''}
           → R σ₁ σ₂ σ₃
           → R (⇑s 𝒦₁ σ₁) (⇑s 𝒦₂ σ₂) (⇑s 𝒦₃ σ₃))
        → (∀ {Δ} {Γ Γ' Γ'' : Cx Δ}
             {σ₁ : Sub 𝒦₁ Γ Γ'} {σ₂ : Sub 𝒦₂ Γ' Γ''} {σ₃ : Sub 𝒦₃ Γ Γ''}
           → R σ₁ σ₂ σ₃
           → ∀ {A} (x : Γ ∋ A)
           → trav 𝒦₂ σ₂ (Kit.tm 𝒦₁ (σ₁ x)) ≡ Kit.tm 𝒦₃ (σ₃ x))
        → ∀ {Δ} {Γ Γ' Γ'' : Cx Δ}
            {σ₁ : Sub 𝒦₁ Γ Γ'} {σ₂ : Sub 𝒦₂ Γ' Γ''} {σ₃ : Sub 𝒦₃ Γ Γ''}
          → R σ₁ σ₂ σ₃
          → ∀ {A} (M : Tm Γ A)
          → trav 𝒦₂ σ₂ (trav 𝒦₁ σ₁ M) ≡ trav 𝒦₃ σ₃ M

      SubId : Set
      SubId =
        ∀ {Δ} {Γ : Cx Δ} {σ : Sub tmK Γ Γ}
        → (∀ {B} (x : Γ ∋ B) → σ x ≡ ` x)
        → ∀ {A} (M : Tm Γ A)
        → sub σ M ≡ M

      {- what the identity needs under a term binder and a type binder -}
      sub-id-exts : ∀ {Δ} {Γ : Cx Δ} {C : Ty Δ} {σ : Sub tmK Γ Γ}
        → (∀ {B} (x : Γ ∋ B) → σ x ≡ ` x)
        → ∀ {B} (x : Γ , C ∋ B)
        → exts tmK σ x ≡ ` x
      sub-id-exts h Z = refl
      sub-id-exts h (S x) = trans (cong ⇑ (h x)) (trav-var varK S_ x)

      private
        ⇑s-tm-ren : ∀ {Δ} {Γ₀ Γ : Cx Δ} (σ : Sub tmK Γ₀ Γ)
          (r : ∀ {A} → Γ₀ ∋ A → Γ ∋ A)
          → (∀ {A} (y : Γ₀ ∋ A) → σ y ≡ ` (r y))
          → ∀ {A} (x : ⇑ᶜ Γ₀ ∋ A) → ⇑s tmK σ x ≡ ` (⇑s-var r x)
        ⇑s-tm-ren {Γ₀ = Γ₀ , B} σ r h Z =
          trans (cong ⇑ᵀ (h Z)) (travᵀ-var renKᵗ there ⇑ᵛ (r Z))
        ⇑s-tm-ren {Γ₀ = Γ₀ , B} σ r h (S x) =
          ⇑s-tm-ren (λ y → σ (S y)) (λ y → r (S y)) (λ y → h (S y)) x

      sub-id-⇑s : ∀ {Δ} {Γ : Cx Δ} {σ : Sub tmK Γ Γ}
        → (∀ {B} (x : Γ ∋ B) → σ x ≡ ` x)
        → ∀ {B} (x : ⇑ᶜ Γ ∋ B)
        → ⇑s tmK σ x ≡ ` x
      sub-id-⇑s {σ = σ} h x =
        trans (⇑s-tm-ren σ (λ y → y) h x) (cong `_ (⇑s-var-id x))

      {- what both kits satisfy, directly -}
      record KitLaws (𝒦 : Kit) : Set where
        field
          tm-vr : ∀ {Δ} {Γ : Cx Δ} {A} (x : Γ ∋ A) → Kit.tm 𝒦 (Kit.vr 𝒦 x) ≡ ` x
          tm-wk : ∀ {Δ} {Γ : Cx Δ} {A B} (k : Kit.K 𝒦 Γ A)
            → Kit.tm 𝒦 (Kit.wk 𝒦 {B = B} k) ≡ ⇑ (Kit.tm 𝒦 k)
          tm-wkα : ∀ {Δ} {Γ : Cx Δ} {A} (k : Kit.K 𝒦 Γ A)
            → Kit.tm 𝒦 (Kit.wkα 𝒦 k) ≡ ⇑ᵀ (Kit.tm 𝒦 k)

      varKL : KitLaws varK
      varKL = record
        { tm-vr = λ _ → refl
        ; tm-wk = λ x → sym (trav-var varK S_ x)
        ; tm-wkα = λ x → sym (travᵀ-var renKᵗ there ⇑ᵛ x)
        }

      tmKL : KitLaws tmK
      tmKL = record { tm-vr = λ _ → refl ; tm-wk = λ _ → refl
                    ; tm-wkα = λ _ → refl }

      {- The consequences -------------------------------------------------}

      module Lemmas (fuseᵀ : Fuseᵀ) (commute : Commute) (fuse : Fuse)
        (sub-id : SubId) where

        {- a renaming of term variables after a traversal of types -}
        ren-travᵀ : ∀ (𝒯 : TyKit) {Δ Δ'} {θ : TK.Sub (TyKit.kit 𝒯) Δ Δ'}
          {Γ Γ₁ : Cx Δ} {Γ' Γ₁' : Cx Δ'}
          {r : ∀ {A} → Γ ∋ A → Γ₁ ∋ A} {ρ : TyRen 𝒯 θ Γ Γ'}
          {ρ₁ : TyRen 𝒯 θ Γ₁ Γ₁'} {r' : ∀ {A} → Γ' ∋ A → Γ₁' ∋ A}
          → (∀ {A} (x : Γ ∋ A) → r' (ρ x) ≡ ρ₁ (r x))
          → ∀ {A} (M : Tm Γ A)
          → ren r' (travᵀ 𝒯 θ ρ M) ≡ travᵀ 𝒯 θ ρ₁ (ren r M)
        ren-travᵀ 𝒯 =
          commute varK 𝒯 (λ r ρ ρ₁ r' → ∀ {A} (x : _ ∋ A) → r' (ρ x) ≡ ρ₁ (r x))
            (λ h → λ { Z → refl ; (S x) → cong S_ (h x) })
            (λ { {θ = θ} {σ = r} {ρ} {ρ₁} {r'} h → ⇑-closure θ r ρ ρ₁ r' h })
            (λ { {θ = θ} {σ = r} {ρ} {ρ₁} {r'} h x →
                 trans (trav-var varK r' (ρ x))
                   (trans (cong `_ (h x))
                      (sym (travᵀ-var 𝒯 θ ρ₁ (r x)))) })
          where
          ⇑-closure : ∀ {Δ Δ'} (θ : TK.Sub (TyKit.kit 𝒯) Δ Δ')
            {Γ Γ₁ : Cx Δ} {Γ' Γ₁' : Cx Δ'}
            (r : ∀ {A} → Γ ∋ A → Γ₁ ∋ A) (ρ : TyRen 𝒯 θ Γ Γ')
            (ρ₁ : TyRen 𝒯 θ Γ₁ Γ₁') (r' : ∀ {A} → Γ' ∋ A → Γ₁' ∋ A)
            → (∀ {A} (x : Γ ∋ A) → r' (ρ x) ≡ ρ₁ (r x))
            → ∀ {A} (x : ⇑ᶜ Γ ∋ A)
            → ⇑s varK r' (⇑ρ 𝒯 θ ρ x) ≡ ⇑ρ 𝒯 θ ρ₁ (⇑s varK r x)
          ⇑-closure θ {Γ = Γ , B} r ρ ρ₁ r' h Z =
            begin
              ⇑s varK r' (conv∋ p (⇑ᵛ (ρ Z)))
            ≡⟨ ⇑s-conv varK r' p (⇑ᵛ (ρ Z)) ⟩
              conv∋ p (⇑s varK r' (⇑ᵛ (ρ Z)))
            ≡⟨ cong (conv∋ p) (⇑s-⇑ᵛ varK r' (ρ Z)) ⟩
              conv∋ p (⇑ᵛ (r' (ρ Z)))
            ≡⟨ cong (λ y → conv∋ p (⇑ᵛ y)) (h Z) ⟩
              conv∋ p (⇑ᵛ (ρ₁ (r Z)))
            ≡⟨ sym (⇑ρ-⇑ᵛ 𝒯 θ ρ₁ (r Z)) ⟩
              ⇑ρ 𝒯 θ ρ₁ (⇑ᵛ (r Z))
            ∎
            where p = sym (TP.Laws.exts-ren (TyKit.laws 𝒯) θ B)
          ⇑-closure θ {Γ = Γ , B} r ρ ρ₁ r' h (S x) =
            ⇑-closure θ (λ y → r (S y)) (λ y → ρ (S y)) ρ₁ r'
              (λ y → h (S y)) x

        {- weakening a type-weakened term by a term variable -}
        private
          ⇑-⇑ᵀ : ∀ {Δ} {Γ : Cx Δ} {A B} (M : Tm Γ A)
            → ⇑ {B = ⇑ᵗ B} (⇑ᵀ M) ≡ ⇑ᵀ (⇑ {B = B} M)
          ⇑-⇑ᵀ M = ren-travᵀ renKᵗ (λ _ → refl) M

        {- a type-weakening, then a traversal of types -}
        private
          ⇑ᵀ-travᵀ : ∀ (𝒯 : TyKit) {Δ Δ'} (θ : TK.Sub (TyKit.kit 𝒯) Δ Δ')
            {Γ : Cx Δ} {Γ' : Cx Δ'} (ρ : TyRen 𝒯 θ Γ Γ') {B} (N : Tm Γ B)
            → travᵀ 𝒯 (TK.exts (TyKit.kit 𝒯) θ) (⇑ρ 𝒯 θ ρ) (⇑ᵀ N)
              ≡ convᵀ (sym (TP.Laws.exts-ren (TyKit.laws 𝒯) θ B))
                  (⇑ᵀ (travᵀ 𝒯 θ ρ N))
          ⇑ᵀ-travᵀ 𝒯 {Δ} {Δ'} θ {Γ} {Γ'} ρ {B} N =
            ≅-to-≡
              (H.trans
                (fuseᵀ {𝒯₁ = renKᵗ} {𝒯₂ = 𝒯} {𝒯₃ = 𝒯}
                  {θ₁ = λ α → there α} {θ₂ = TK.exts k θ} {θ₃ = θ₃}
                  {ρ₁ = ⇑ᵛ} {ρ₂ = ⇑ρ 𝒯 θ ρ} {ρ₃ = ρ₃} (record
                  { ty-var = λ α → travᵗ-var k (TK.exts k θ) (there α)
                  ; ctx = refl
                  ; var = λ x → H.sym (conv∋-≅ (q _) (⇑ρ 𝒯 θ ρ (⇑ᵛ x)))
                  }) N)
                (H.sym
                  (H.trans (convᵀ-≅ p (⇑ᵀ (travᵀ 𝒯 θ ρ N)))
                    (fuseᵀ {𝒯₁ = 𝒯} {𝒯₂ = renKᵗ} {𝒯₃ = 𝒯}
                      {θ₁ = θ} {θ₂ = λ α → there α} {θ₃ = θ₃}
                      {ρ₁ = ρ} {ρ₂ = ⇑ᵛ} {ρ₃ = ρ₃} (record
                      { ty-var = λ α →
                          trans (sym (TP.Laws.tm-wk (TyKit.laws 𝒯) (θ α)))
                            (sym (cong (TK.Kit.tm k)
                               (TPK.exts-there k θ α)))
                      ; ctx = refl
                      ; var = λ x → H.trans (H.sym (⇑ρ-⇑ᵛ-≅ 𝒯 θ ρ x))
                                    (H.sym (conv∋-≅ (q _) (⇑ρ 𝒯 θ ρ (⇑ᵛ x))))
                      }) N))))
            where
            k = TyKit.kit 𝒯
            p = sym (TP.Laws.exts-ren (TyKit.laws 𝒯) θ B)
            θ₃ : TK.Sub k Δ (Δ' ▷ ⋆)
            θ₃ α = TK.exts k θ (there α)
            q : ∀ (A : Ty Δ) → act 𝒯 (TK.exts k θ) (⇑ᵗ A) ≡ act 𝒯 θ₃ A
            q A = TL.ren-trav k (λ _ → refl) A
            ρ₃ : TyRen 𝒯 θ₃ Γ (⇑ᶜ Γ')
            ρ₃ x = conv∋ (q _) (⇑ρ 𝒯 θ ρ (⇑ᵛ x))

        {- a term-level traversal after a type-level one -}
        trav-travᵀ : ∀ {𝒦} → KitLaws 𝒦 → ∀ (𝒯 : TyKit) {Δ Δ'}
          {θ : TK.Sub (TyKit.kit 𝒯) Δ Δ'}
          {Γ Γ₁ : Cx Δ} {Γ' Γ₁' : Cx Δ'}
          {σ : Sub 𝒦 Γ Γ₁} {ρ : TyRen 𝒯 θ Γ Γ'}
          {ρ₁ : TyRen 𝒯 θ Γ₁ Γ₁'} {σ' : Sub 𝒦 Γ' Γ₁'}
          → (∀ {A} (x : Γ ∋ A)
               → Kit.tm 𝒦 (σ' (ρ x)) ≡ travᵀ 𝒯 θ ρ₁ (Kit.tm 𝒦 (σ x)))
          → ∀ {A} (M : Tm Γ A)
          → trav 𝒦 σ' (travᵀ 𝒯 θ ρ M) ≡ travᵀ 𝒯 θ ρ₁ (trav 𝒦 σ M)
        trav-travᵀ {𝒦} L 𝒯 =
          commute 𝒦 𝒯
            (λ {θ = θ} σ ρ ρ₁ σ' → ∀ {A} (x : _ ∋ A)
               → Kit.tm 𝒦 (σ' (ρ x)) ≡ travᵀ 𝒯 θ ρ₁ (Kit.tm 𝒦 (σ x)))
            (λ { {θ = θ} {σ = σ} {ρ} {ρ₁} {σ'} h → ext-closure θ σ ρ ρ₁ σ' h })
            (λ { {θ = θ} {σ = σ} {ρ} {ρ₁} {σ'} h → ⇑-closure θ σ ρ ρ₁ σ' h })
            (λ { {ρ = ρ} {σ' = σ'} h x → trans (trav-var 𝒦 σ' (ρ x)) (h x) })
          where
          ext-closure : ∀ {Δ Δ'} (θ : TK.Sub (TyKit.kit 𝒯) Δ Δ')
            {Γ Γ₁ : Cx Δ} {Γ' Γ₁' : Cx Δ'} {B : Ty Δ}
            (σ : Sub 𝒦 Γ Γ₁) (ρ : TyRen 𝒯 θ Γ Γ')
            (ρ₁ : TyRen 𝒯 θ Γ₁ Γ₁') (σ' : Sub 𝒦 Γ' Γ₁')
            → (∀ {A} (x : Γ ∋ A)
                 → Kit.tm 𝒦 (σ' (ρ x)) ≡ travᵀ 𝒯 θ ρ₁ (Kit.tm 𝒦 (σ x)))
            → ∀ {A} (x : Γ , B ∋ A)
            → Kit.tm 𝒦 (exts 𝒦 σ' (extρ 𝒯 θ ρ x))
              ≡ travᵀ 𝒯 θ (extρ 𝒯 θ ρ₁) (Kit.tm 𝒦 (exts 𝒦 σ x))
          ext-closure θ σ ρ ρ₁ σ' h Z =
            trans (KitLaws.tm-vr L Z)
              (sym (trans (cong (travᵀ 𝒯 θ (extρ 𝒯 θ ρ₁)) (KitLaws.tm-vr L Z))
                      (travᵀ-var 𝒯 θ (extρ 𝒯 θ ρ₁) Z)))
          ext-closure θ σ ρ ρ₁ σ' h (S x) =
            begin
              Kit.tm 𝒦 (Kit.wk 𝒦 (σ' (ρ x)))
            ≡⟨ KitLaws.tm-wk L (σ' (ρ x)) ⟩
              ⇑ (Kit.tm 𝒦 (σ' (ρ x)))
            ≡⟨ cong ⇑ (h x) ⟩
              ⇑ (travᵀ 𝒯 θ ρ₁ (Kit.tm 𝒦 (σ x)))
            ≡⟨ ren-travᵀ 𝒯 (λ _ → refl) (Kit.tm 𝒦 (σ x)) ⟩
              travᵀ 𝒯 θ (extρ 𝒯 θ ρ₁) (⇑ (Kit.tm 𝒦 (σ x)))
            ≡⟨ cong (travᵀ 𝒯 θ (extρ 𝒯 θ ρ₁)) (sym (KitLaws.tm-wk L (σ x))) ⟩
              travᵀ 𝒯 θ (extρ 𝒯 θ ρ₁) (Kit.tm 𝒦 (Kit.wk 𝒦 (σ x)))
            ∎
          ⇑-closure : ∀ {Δ Δ'} (θ : TK.Sub (TyKit.kit 𝒯) Δ Δ')
            {Γ Γ₁ : Cx Δ} {Γ' Γ₁' : Cx Δ'}
            (σ : Sub 𝒦 Γ Γ₁) (ρ : TyRen 𝒯 θ Γ Γ')
            (ρ₁ : TyRen 𝒯 θ Γ₁ Γ₁') (σ' : Sub 𝒦 Γ' Γ₁')
            → (∀ {A} (x : Γ ∋ A)
                 → Kit.tm 𝒦 (σ' (ρ x)) ≡ travᵀ 𝒯 θ ρ₁ (Kit.tm 𝒦 (σ x)))
            → ∀ {A} (x : ⇑ᶜ Γ ∋ A)
            → Kit.tm 𝒦 (⇑s 𝒦 σ' (⇑ρ 𝒯 θ ρ x))
              ≡ travᵀ 𝒯 (TK.exts (TyKit.kit 𝒯) θ) (⇑ρ 𝒯 θ ρ₁)
                  (Kit.tm 𝒦 (⇑s 𝒦 σ x))
          ⇑-closure θ {Γ = Γ , B} σ ρ ρ₁ σ' h Z =
            begin
              Kit.tm 𝒦 (⇑s 𝒦 σ' (conv∋ p (⇑ᵛ (ρ Z))))
            ≡⟨ cong (Kit.tm 𝒦) (⇑s-conv 𝒦 σ' p (⇑ᵛ (ρ Z))) ⟩
              Kit.tm 𝒦 (convK 𝒦 p (⇑s 𝒦 σ' (⇑ᵛ (ρ Z))))
            ≡⟨ tm-convK 𝒦 p (⇑s 𝒦 σ' (⇑ᵛ (ρ Z))) ⟩
              convᵀ p (Kit.tm 𝒦 (⇑s 𝒦 σ' (⇑ᵛ (ρ Z))))
            ≡⟨ cong (λ k → convᵀ p (Kit.tm 𝒦 k)) (⇑s-⇑ᵛ 𝒦 σ' (ρ Z)) ⟩
              convᵀ p (Kit.tm 𝒦 (Kit.wkα 𝒦 (σ' (ρ Z))))
            ≡⟨ cong (convᵀ p) (KitLaws.tm-wkα L (σ' (ρ Z))) ⟩
              convᵀ p (⇑ᵀ (Kit.tm 𝒦 (σ' (ρ Z))))
            ≡⟨ cong (λ N → convᵀ p (⇑ᵀ N)) (h Z) ⟩
              convᵀ p (⇑ᵀ (travᵀ 𝒯 θ ρ₁ (Kit.tm 𝒦 (σ Z))))
            ≡⟨ sym (⇑ᵀ-travᵀ 𝒯 θ ρ₁ (Kit.tm 𝒦 (σ Z))) ⟩
              travᵀ 𝒯 (TK.exts (TyKit.kit 𝒯) θ) (⇑ρ 𝒯 θ ρ₁)
                (⇑ᵀ (Kit.tm 𝒦 (σ Z)))
            ≡⟨ cong (travᵀ 𝒯 (TK.exts (TyKit.kit 𝒯) θ) (⇑ρ 𝒯 θ ρ₁))
                 (sym (KitLaws.tm-wkα L (σ Z))) ⟩
              travᵀ 𝒯 (TK.exts (TyKit.kit 𝒯) θ) (⇑ρ 𝒯 θ ρ₁)
                (Kit.tm 𝒦 (Kit.wkα 𝒦 (σ Z)))
            ∎
            where p = sym (TP.Laws.exts-ren (TyKit.laws 𝒯) θ B)
          ⇑-closure θ {Γ = Γ , B} σ ρ ρ₁ σ' h (S x) =
            ⇑-closure θ (λ y → σ (S y)) (λ y → ρ (S y)) ρ₁ σ'
              (λ y → h (S y)) x

        {- a term-level traversal after a type-weakening -}
        ⇑s-⇑ᵀ : ∀ {𝒦} → KitLaws 𝒦
          → ∀ {Δ} {Γ Γ' : Cx Δ} (τ : Sub 𝒦 Γ Γ') {A} (M : Tm Γ A)
          → trav 𝒦 (⇑s 𝒦 τ) (⇑ᵀ M) ≡ ⇑ᵀ (trav 𝒦 τ M)
        ⇑s-⇑ᵀ {𝒦} L τ M =
          trav-travᵀ L renKᵗ
            (λ x → trans (cong (Kit.tm 𝒦) (⇑s-⇑ᵛ 𝒦 τ x))
                     (KitLaws.tm-wkα L (τ x)))
            M

        {- a renaming, then a traversal -}
        ren-trav : ∀ 𝒦 {Δ} {Γ Γ' Γ'' : Cx Δ}
          {r : ∀ {B} → Γ ∋ B → Γ' ∋ B} {σ : Sub 𝒦 Γ' Γ''} {τ : Sub 𝒦 Γ Γ''}
          → (∀ {B} (x : Γ ∋ B) → σ (r x) ≡ τ x)
          → ∀ {A} (M : Tm Γ A)
          → trav 𝒦 σ (ren r M) ≡ trav 𝒦 τ M
        ren-trav 𝒦 =
          fuse varK 𝒦 𝒦 (λ r σ τ → ∀ {B} (x : _ ∋ B) → σ (r x) ≡ τ x)
            (λ h → λ { Z → refl ; (S x) → cong (Kit.wk 𝒦) (h x) })
            (λ { {σ₁ = r} {σ} {τ} h → ⇑-closure r σ τ h })
            (λ { {σ₁ = r} {σ} h x
                 → trans (trav-var 𝒦 σ (r x)) (cong (Kit.tm 𝒦) (h x)) })
          where
          ⇑-closure : ∀ {Δ} {Γ Γ' Γ'' : Cx Δ}
            (r : ∀ {B} → Γ ∋ B → Γ' ∋ B) (σ : Sub 𝒦 Γ' Γ'')
            (τ : Sub 𝒦 Γ Γ'')
            → (∀ {B} (x : Γ ∋ B) → σ (r x) ≡ τ x)
            → ∀ {B} (x : ⇑ᶜ Γ ∋ B) → ⇑s 𝒦 σ (⇑s varK r x) ≡ ⇑s 𝒦 τ x
          ⇑-closure {Γ = Γ , C} r σ τ h Z =
            trans (⇑s-⇑ᵛ 𝒦 σ (r Z)) (cong (Kit.wkα 𝒦) (h Z))
          ⇑-closure {Γ = Γ , C} r σ τ h (S x) =
            ⇑-closure (λ y → r (S y)) σ (λ y → τ (S y)) (λ y → h (S y)) x

        {- a substitution, then a renaming -}
        sub-ren : ∀ {Δ} {Γ Γ' Γ'' : Cx Δ}
          {σ : Sub tmK Γ Γ'} {r : ∀ {B} → Γ' ∋ B → Γ'' ∋ B}
          {τ : Sub tmK Γ Γ''}
          → (∀ {B} (x : Γ ∋ B) → ren r (σ x) ≡ τ x)
          → ∀ {A} (M : Tm Γ A)
          → ren r (sub σ M) ≡ sub τ M
        sub-ren =
          fuse tmK varK tmK (λ σ r τ → ∀ {B} (x : _ ∋ B) → ren r (σ x) ≡ τ x)
            (λ { {σ₁ = σ} {r} {τ} h → ext-closure σ r τ h })
            (λ { {σ₁ = σ} {r} {τ} h → ⇑-closure σ r τ h })
            (λ h x → h x)
          where
          ext-closure : ∀ {Δ} {Γ Γ' Γ'' : Cx Δ} {C : Ty Δ}
            (σ : Sub tmK Γ Γ') (r : ∀ {B} → Γ' ∋ B → Γ'' ∋ B)
            (τ : Sub tmK Γ Γ'')
            → (∀ {B} (x : Γ ∋ B) → ren r (σ x) ≡ τ x)
            → ∀ {B} (x : Γ , C ∋ B)
            → ren (exts varK r) (exts tmK σ x) ≡ exts tmK τ x
          ext-closure σ r τ h Z = trav-var varK (exts varK r) Z
          ext-closure σ r τ h (S x) =
            begin
              ren (exts varK r) (⇑ (σ x))
            ≡⟨ ren-trav varK (λ _ → refl) (σ x) ⟩
              ren (λ y → S (r y)) (σ x)
            ≡⟨ sym (ren-trav varK (λ _ → refl) (σ x)) ⟩
              ⇑ (ren r (σ x))
            ≡⟨ cong ⇑ (h x) ⟩
              ⇑ (τ x)
            ∎
          ⇑-closure : ∀ {Δ} {Γ Γ' Γ'' : Cx Δ}
            (σ : Sub tmK Γ Γ') (r : ∀ {B} → Γ' ∋ B → Γ'' ∋ B)
            (τ : Sub tmK Γ Γ'')
            → (∀ {B} (x : Γ ∋ B) → ren r (σ x) ≡ τ x)
            → ∀ {B} (x : ⇑ᶜ Γ ∋ B)
            → ren (⇑s varK r) (⇑s tmK σ x) ≡ ⇑s tmK τ x
          ⇑-closure {Γ = Γ , C} σ r τ h Z =
            trans (⇑s-⇑ᵀ varKL r (σ Z)) (cong ⇑ᵀ (h Z))
          ⇑-closure {Γ = Γ , C} σ r τ h (S x) =
            ⇑-closure (λ y → σ (S y)) r (λ y → τ (S y)) (λ y → h (S y)) x

        {- what both kits satisfy -}
        record Laws (𝒦 : Kit) : Set where
          field
            kit-laws : KitLaws 𝒦
            exts-ren : ∀ {Δ} {Γ Γ' : Cx Δ} {A B} (τ : Sub 𝒦 Γ Γ') (M : Tm Γ A)
              → trav 𝒦 (exts 𝒦 {B = B} τ) (⇑ M) ≡ ⇑ (trav 𝒦 τ M)

        varL : Laws varK
        varL = record
          { kit-laws = varKL
          ; exts-ren = λ τ M →
              trans (ren-trav varK (λ _ → refl) M)
                    (sym (ren-trav varK (λ _ → refl) M))
          }

        tmL : Laws tmK
        tmL = record
          { kit-laws = tmKL
          ; exts-ren = λ τ M →
              trans (ren-trav tmK (λ _ → refl) M)
                    (sym (sub-ren (λ _ → refl) M))
          }

        {- any two traversals of term variables, when their kits have
           laws -}
        trav-trav : ∀ {𝒦₁ 𝒦₂ 𝒦₃} → Laws 𝒦₁ → Laws 𝒦₂ → Laws 𝒦₃
          → ∀ {Δ} {Γ Γ' Γ'' : Cx Δ}
            {σ₁ : Sub 𝒦₁ Γ Γ'} {σ₂ : Sub 𝒦₂ Γ' Γ''} {σ₃ : Sub 𝒦₃ Γ Γ''}
          → (∀ {B} (x : Γ ∋ B)
               → trav 𝒦₂ σ₂ (Kit.tm 𝒦₁ (σ₁ x)) ≡ Kit.tm 𝒦₃ (σ₃ x))
          → ∀ {A} (M : Tm Γ A)
          → trav 𝒦₂ σ₂ (trav 𝒦₁ σ₁ M) ≡ trav 𝒦₃ σ₃ M
        trav-trav {𝒦₁} {𝒦₂} {𝒦₃} L₁ L₂ L₃ =
          fuse 𝒦₁ 𝒦₂ 𝒦₃
            (λ σ₁ σ₂ σ₃ → ∀ {B} (x : _ ∋ B)
               → trav 𝒦₂ σ₂ (Kit.tm 𝒦₁ (σ₁ x)) ≡ Kit.tm 𝒦₃ (σ₃ x))
            (λ { {σ₁ = σ₁} {σ₂} {σ₃} h → ext-closure σ₁ σ₂ σ₃ h })
            (λ { {σ₁ = σ₁} {σ₂} {σ₃} h → ⇑-closure σ₁ σ₂ σ₃ h })
            (λ h x → h x)
          where
          KL₁ = Laws.kit-laws L₁
          KL₂ = Laws.kit-laws L₂
          KL₃ = Laws.kit-laws L₃
          ext-closure : ∀ {Δ} {Γ Γ' Γ'' : Cx Δ} {C : Ty Δ}
            (σ₁ : Sub 𝒦₁ Γ Γ') (σ₂ : Sub 𝒦₂ Γ' Γ'') (σ₃ : Sub 𝒦₃ Γ Γ'')
            → (∀ {B} (x : Γ ∋ B)
                 → trav 𝒦₂ σ₂ (Kit.tm 𝒦₁ (σ₁ x)) ≡ Kit.tm 𝒦₃ (σ₃ x))
            → ∀ {B} (x : Γ , C ∋ B)
            → trav 𝒦₂ (exts 𝒦₂ σ₂) (Kit.tm 𝒦₁ (exts 𝒦₁ σ₁ x))
              ≡ Kit.tm 𝒦₃ (exts 𝒦₃ σ₃ x)
          ext-closure σ₁ σ₂ σ₃ h Z =
            begin
              trav 𝒦₂ (exts 𝒦₂ σ₂) (Kit.tm 𝒦₁ (Kit.vr 𝒦₁ Z))
            ≡⟨ cong (trav 𝒦₂ (exts 𝒦₂ σ₂)) (KitLaws.tm-vr KL₁ Z) ⟩
              trav 𝒦₂ (exts 𝒦₂ σ₂) (` Z)
            ≡⟨ trav-var 𝒦₂ (exts 𝒦₂ σ₂) Z ⟩
              Kit.tm 𝒦₂ (Kit.vr 𝒦₂ Z)
            ≡⟨ KitLaws.tm-vr KL₂ Z ⟩
              ` Z
            ≡⟨ sym (KitLaws.tm-vr KL₃ Z) ⟩
              Kit.tm 𝒦₃ (Kit.vr 𝒦₃ Z)
            ∎
          ext-closure σ₁ σ₂ σ₃ h (S x) =
            begin
              trav 𝒦₂ (exts 𝒦₂ σ₂) (Kit.tm 𝒦₁ (Kit.wk 𝒦₁ (σ₁ x)))
            ≡⟨ cong (trav 𝒦₂ (exts 𝒦₂ σ₂)) (KitLaws.tm-wk KL₁ (σ₁ x)) ⟩
              trav 𝒦₂ (exts 𝒦₂ σ₂) (⇑ (Kit.tm 𝒦₁ (σ₁ x)))
            ≡⟨ Laws.exts-ren L₂ σ₂ (Kit.tm 𝒦₁ (σ₁ x)) ⟩
              ⇑ (trav 𝒦₂ σ₂ (Kit.tm 𝒦₁ (σ₁ x)))
            ≡⟨ cong ⇑ (h x) ⟩
              ⇑ (Kit.tm 𝒦₃ (σ₃ x))
            ≡⟨ sym (KitLaws.tm-wk KL₃ (σ₃ x)) ⟩
              Kit.tm 𝒦₃ (Kit.wk 𝒦₃ (σ₃ x))
            ∎
          ⇑-closure : ∀ {Δ} {Γ Γ' Γ'' : Cx Δ}
            (σ₁ : Sub 𝒦₁ Γ Γ') (σ₂ : Sub 𝒦₂ Γ' Γ'') (σ₃ : Sub 𝒦₃ Γ Γ'')
            → (∀ {B} (x : Γ ∋ B)
                 → trav 𝒦₂ σ₂ (Kit.tm 𝒦₁ (σ₁ x)) ≡ Kit.tm 𝒦₃ (σ₃ x))
            → ∀ {B} (x : ⇑ᶜ Γ ∋ B)
            → trav 𝒦₂ (⇑s 𝒦₂ σ₂) (Kit.tm 𝒦₁ (⇑s 𝒦₁ σ₁ x))
              ≡ Kit.tm 𝒦₃ (⇑s 𝒦₃ σ₃ x)
          ⇑-closure {Γ = Γ , C} σ₁ σ₂ σ₃ h Z =
            begin
              trav 𝒦₂ (⇑s 𝒦₂ σ₂) (Kit.tm 𝒦₁ (Kit.wkα 𝒦₁ (σ₁ Z)))
            ≡⟨ cong (trav 𝒦₂ (⇑s 𝒦₂ σ₂)) (KitLaws.tm-wkα KL₁ (σ₁ Z)) ⟩
              trav 𝒦₂ (⇑s 𝒦₂ σ₂) (⇑ᵀ (Kit.tm 𝒦₁ (σ₁ Z)))
            ≡⟨ ⇑s-⇑ᵀ KL₂ σ₂ (Kit.tm 𝒦₁ (σ₁ Z)) ⟩
              ⇑ᵀ (trav 𝒦₂ σ₂ (Kit.tm 𝒦₁ (σ₁ Z)))
            ≡⟨ cong ⇑ᵀ (h Z) ⟩
              ⇑ᵀ (Kit.tm 𝒦₃ (σ₃ Z))
            ≡⟨ sym (KitLaws.tm-wkα KL₃ (σ₃ Z)) ⟩
              Kit.tm 𝒦₃ (Kit.wkα 𝒦₃ (σ₃ Z))
            ∎
          ⇑-closure {Γ = Γ , C} σ₁ σ₂ σ₃ h (S x) =
            ⇑-closure (λ y → σ₁ (S y)) σ₂ (λ y → σ₃ (S y)) (λ y → h (S y)) x

        {- the instances with one kit throughout -}
        ren-ren : ∀ {Δ} {Γ Γ' Γ'' : Cx Δ} {r₁ : ∀ {B} → Γ ∋ B → Γ' ∋ B}
          {r₂ : ∀ {B} → Γ' ∋ B → Γ'' ∋ B} {r₃ : ∀ {B} → Γ ∋ B → Γ'' ∋ B}
          → (∀ {B} (x : Γ ∋ B) → r₂ (r₁ x) ≡ r₃ x)
          → ∀ {A} (M : Tm Γ A)
          → ren r₂ (ren r₁ M) ≡ ren r₃ M
        ren-ren = ren-trav varK

        ren-sub : ∀ {Δ} {Γ Γ' Γ'' : Cx Δ} {r : ∀ {B} → Γ ∋ B → Γ' ∋ B}
          {σ : Sub tmK Γ' Γ''} {τ : Sub tmK Γ Γ''}
          → (∀ {B} (x : Γ ∋ B) → σ (r x) ≡ τ x)
          → ∀ {A} (M : Tm Γ A)
          → sub σ (ren r M) ≡ sub τ M
        ren-sub = ren-trav tmK

        sub-sub : ∀ {Δ} {Γ Γ' Γ'' : Cx Δ} {σ : Sub tmK Γ Γ'}
          {τ : Sub tmK Γ' Γ''} {ρ : Sub tmK Γ Γ''}
          → (∀ {B} (x : Γ ∋ B) → sub τ (σ x) ≡ ρ x)
          → ∀ {A} (M : Tm Γ A)
          → sub τ (sub σ M) ≡ sub ρ M
        sub-sub = trav-trav tmL tmL tmL

        {- a substitution of terms after a type-weakening -}
        sub-⇑ᵀ : ∀ {Δ} {Γ Γ' : Cx Δ} (σ : Sub tmK Γ Γ') {A} (M : Tm Γ A)
          → sub (⇑s tmK σ) (⇑ᵀ M) ≡ ⇑ᵀ (sub σ M)
        sub-⇑ᵀ = ⇑s-⇑ᵀ tmKL

        {- pointwise equal substitutions act equally -}
        trav-cong : ∀ 𝒦 {Δ} {Γ Γ' : Cx Δ} {σ τ : Sub 𝒦 Γ Γ'}
          → (∀ {B} (x : Γ ∋ B) → σ x ≡ τ x)
          → ∀ {A} (M : Tm Γ A)
          → trav 𝒦 σ M ≡ trav 𝒦 τ M
        trav-cong 𝒦 {σ = σ} h M =
          trans (sym (ren-trav 𝒦 {r = λ x → x} {σ = σ} {τ = σ} (λ _ → refl) M))
                (ren-trav 𝒦 {r = λ x → x} h M)

        ren-cong : ∀ {Δ} {Γ Γ' : Cx Δ} {r s : ∀ {B} → Γ ∋ B → Γ' ∋ B}
          → (∀ {B} (x : Γ ∋ B) → r x ≡ s x)
          → ∀ {A} (M : Tm Γ A)
          → ren r M ≡ ren s M
        ren-cong = trav-cong varK

        sub-cong : ∀ {Δ} {Γ Γ' : Cx Δ} {σ τ : Sub tmK Γ Γ'}
          → (∀ {B} (x : Γ ∋ B) → σ x ≡ τ x)
          → ∀ {A} (M : Tm Γ A)
          → sub σ M ≡ sub τ M
        sub-cong = trav-cong tmK

        {- renaming is substitution by variables -}
        ren-as-sub : ∀ {Δ} {Γ Γ' : Cx Δ} (r : ∀ {B} → Γ ∋ B → Γ' ∋ B)
          → ∀ {A} (M : Tm Γ A)
          → ren r M ≡ sub (λ x → ` (r x)) M
        ren-as-sub r M =
          trans (sym (sub-id (λ _ → refl) (ren r M)))
                (ren-trav tmK (λ _ → refl) M)

        ren-id : ∀ {Δ} {Γ : Cx Δ} {r : ∀ {B} → Γ ∋ B → Γ ∋ B}
          → (∀ {B} (x : Γ ∋ B) → r x ≡ x)
          → ∀ {A} (M : Tm Γ A)
          → ren r M ≡ M
        ren-id {r = r} h M =
          trans (ren-as-sub r M) (sub-id (λ x → cong `_ (h x)) M)

        {- Single substitution --------------------------------------------}

        sub-⇑-• : ∀ {Δ} {Γ Γ' : Cx Δ} {A B} (W : Tm Γ' B) (σ : Sub tmK Γ Γ')
          (M : Tm Γ A)
          → sub (W • σ) (⇑ M) ≡ sub σ M
        sub-⇑-• W σ M = ren-sub (λ _ → refl) M

        ⇑-[] : ∀ {Δ} {Γ : Cx Δ} {A B} (M : Tm Γ A) (W : Tm Γ B)
          → ⇑ M [ W ] ≡ M
        ⇑-[] M W = trans (sub-⇑-• W ids M) (sub-id (λ _ → refl) M)

        {- under a binder, then for the bound variable -}
        exts-[] : ∀ {Δ} {Γ Γ' : Cx Δ} {A B} (σ : Sub tmK Γ Γ')
          (N : Tm (Γ , B) A) (W : Tm Γ' B)
          → sub (exts tmK σ) N [ W ] ≡ sub (W • σ) N
        exts-[] σ N W = sub-sub pt N
          where
          pt : ∀ {C} (x : _ , _ ∋ C) → sub (W • ids) (exts tmK σ x) ≡ (W • σ) x
          pt Z = trav-var tmK (W • ids) Z
          pt (S x) = ⇑-[] (σ x) W

        {- a traversal of term variables commutes with a single
           substitution -}
        trav-[] : ∀ {𝒦} → Laws 𝒦
          → ∀ {Δ} {Γ Γ' : Cx Δ} {A B} (σ : Sub 𝒦 Γ Γ')
            (N : Tm (Γ , B) A) (M : Tm Γ B)
          → trav 𝒦 σ (N [ M ]) ≡ trav 𝒦 (exts 𝒦 σ) N [ trav 𝒦 σ M ]
        trav-[] {𝒦} L σ N M =
          begin
            trav 𝒦 σ (N [ M ])
          ≡⟨ trav-trav tmL L tmL (λ _ → refl) N ⟩
            sub (λ x → trav 𝒦 σ ((M • ids) x)) N
          ≡⟨ sub-cong pt N ⟩
            sub (λ x → sub (W • ids) (Kit.tm 𝒦 (exts 𝒦 σ x))) N
          ≡⟨ sym (trav-trav L tmL tmL (λ _ → refl) N) ⟩
            trav 𝒦 (exts 𝒦 σ) N [ W ]
          ∎
          where
          W = trav 𝒦 σ M
          KL = Laws.kit-laws L
          pt : ∀ {C} (x : _ , _ ∋ C)
            → trav 𝒦 σ ((M • ids) x)
              ≡ sub (W • ids) (Kit.tm 𝒦 (exts 𝒦 σ x))
          pt Z =
            sym (trans (cong (sub (W • ids)) (KitLaws.tm-vr KL Z))
                   (trav-var tmK (W • ids) Z))
          pt (S x) =
            begin
              trav 𝒦 σ (` x)
            ≡⟨ trav-var 𝒦 σ x ⟩
              Kit.tm 𝒦 (σ x)
            ≡⟨ sym (⇑-[] (Kit.tm 𝒦 (σ x)) W) ⟩
              sub (W • ids) (⇑ (Kit.tm 𝒦 (σ x)))
            ≡⟨ cong (sub (W • ids)) (sym (KitLaws.tm-wk KL (σ x))) ⟩
              sub (W • ids) (Kit.tm 𝒦 (Kit.wk 𝒦 (σ x)))
            ∎

        ren-[] : ∀ {Δ} {Γ Γ' : Cx Δ} {A B} (r : ∀ {C} → Γ ∋ C → Γ' ∋ C)
          (N : Tm (Γ , B) A) (M : Tm Γ B)
          → ren r (N [ M ]) ≡ ren (exts varK r) N [ ren r M ]
        ren-[] = trav-[] varL

        sub-[] : ∀ {Δ} {Γ Γ' : Cx Δ} {A B} (σ : Sub tmK Γ Γ')
          (N : Tm (Γ , B) A) (M : Tm Γ B)
          → sub σ (N [ M ]) ≡ sub (exts tmK σ) N [ sub σ M ]
        sub-[] = trav-[] tmL

        {- a traversal of type variables commutes with a single
           substitution of a term -}
        travᵀ-[] : ∀ (𝒯 : TyKit) {Δ Δ'} (θ : TK.Sub (TyKit.kit 𝒯) Δ Δ')
          {Γ : Cx Δ} {Γ' : Cx Δ'} (ρ : TyRen 𝒯 θ Γ Γ') {A B}
          (N : Tm (Γ , B) A) (M : Tm Γ B)
          → travᵀ 𝒯 θ ρ (N [ M ])
            ≡ travᵀ 𝒯 θ (extρ 𝒯 θ ρ) N [ travᵀ 𝒯 θ ρ M ]
        travᵀ-[] 𝒯 θ ρ N M =
          sym (trav-travᵀ tmKL 𝒯 {σ = M • ids} {ρ = extρ 𝒯 θ ρ} {ρ₁ = ρ}
                 {σ' = travᵀ 𝒯 θ ρ M • ids} pt N)
          where
          pt : ∀ {C} (x : _ , _ ∋ C)
            → (travᵀ 𝒯 θ ρ M • ids) (extρ 𝒯 θ ρ x)
              ≡ travᵀ 𝒯 θ ρ ((M • ids) x)
          pt Z = refl
          pt (S x) = sym (travᵀ-var 𝒯 θ ρ x)
