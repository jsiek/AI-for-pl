module Terms where

-- File Charter:
--   * Raw PolyNuBar term syntax and extrinsic typing rules.
--   * Defines type-variable renaming/substitution through terms and
--     term-variable renaming/substitution through terms.
--   * Uses the `Types` de Bruijn type infrastructure.

open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Types public

------------------------------------------------------------------------
-- Raw terms
------------------------------------------------------------------------

infix  9 `_
infix  9 $_
infix  5 ƛ[_]_
infixl 7 _·_
infixl 8 _•_
infix  6 ν[_]_∙_
infix  6 _⦂_⇒[_]_
infix  6 _⦂_⇒⟨_⟩_

data Term : Set where
  `_       : Var → Term
  $_       : Const → Term
  ƛ[_]_    : Ty → Term → Term
  _·_      : Term → Term → Term
  letin    : Term → Term → Term
  Λ[_]_::_ : Label → Term → Ty → Term
  _•_      : Term → Ty → Term
  ν[_]_∙_  : Ty → Label → Term → Term
  _⦂_⇒[_]_ : Term → Ty → Label → Ty → Term
  _⦂_⇒⟨_⟩_ : Term → Ty → Binder → Ty → Term
  is       : Label → Term → Ty → Term
  pair     : Term → Term → Term
  fst      : Term → Term
  snd      : Term → Term
  ifte     : Term → Term → Term → Term
  prim     : Prim → Term → Term
  blame    : Label → Term

------------------------------------------------------------------------
-- Type-variable renaming/substitution through terms
------------------------------------------------------------------------

renameᵀ : Renameᵗ → Term → Term
renameᵀ ρ (` x) = ` x
renameᵀ ρ ($ c) = $ c
renameᵀ ρ (ƛ[ A ] M) = ƛ[ renameᵗ ρ A ] renameᵀ ρ M
renameᵀ ρ (L · M) = renameᵀ ρ L · renameᵀ ρ M
renameᵀ ρ (letin L M) = letin (renameᵀ ρ L) (renameᵀ ρ M)
renameᵀ ρ (Λ[ p ] M :: A) = Λ[ p ] renameᵀ (extᵗ ρ) M :: renameᵗ (extᵗ ρ) A
renameᵀ ρ (M • A) = renameᵀ ρ M • renameᵗ ρ A
renameᵀ ρ (ν[ A ] p ∙ M) = ν[ renameᵗ ρ A ] p ∙ renameᵀ ρ M
renameᵀ ρ (M ⦂ A ⇒[ p ] B) =
  renameᵀ ρ M ⦂ renameᵗ ρ A ⇒[ p ] renameᵗ ρ B
renameᵀ ρ (M ⦂ A ⇒⟨ bind X ⟩ B) =
  renameᵀ (extᵗ ρ) M
    ⦂ renameᵗ (extᵗ ρ) A ⇒⟨ bind X ⟩ renameᵗ ρ B
renameᵀ ρ (M ⦂ A ⇒⟨ unbind X ⟩ B) =
  renameᵀ ρ M
    ⦂ renameᵗ ρ A ⇒⟨ unbind X ⟩ renameᵗ ρ B
renameᵀ ρ (is p M G) = is p (renameᵀ ρ M) (renameᵗ ρ G)
renameᵀ ρ (pair L M) = pair (renameᵀ ρ L) (renameᵀ ρ M)
renameᵀ ρ (fst M) = fst (renameᵀ ρ M)
renameᵀ ρ (snd M) = snd (renameᵀ ρ M)
renameᵀ ρ (ifte L M N) = ifte (renameᵀ ρ L) (renameᵀ ρ M) (renameᵀ ρ N)
renameᵀ ρ (prim op M) = prim op (renameᵀ ρ M)
renameᵀ ρ (blame p) = blame p

substᵀ : Substᵗ → Term → Term
substᵀ σ (` x) = ` x
substᵀ σ ($ c) = $ c
substᵀ σ (ƛ[ A ] M) = ƛ[ substᵗ σ A ] substᵀ σ M
substᵀ σ (L · M) = substᵀ σ L · substᵀ σ M
substᵀ σ (letin L M) = letin (substᵀ σ L) (substᵀ σ M)
substᵀ σ (Λ[ p ] M :: A) = Λ[ p ] substᵀ (extsᵗ σ) M :: substᵗ (extsᵗ σ) A
substᵀ σ (M • A) = substᵀ σ M • substᵗ σ A
substᵀ σ (ν[ A ] p ∙ M) = ν[ substᵗ σ A ] p ∙ substᵀ σ M
substᵀ σ (M ⦂ A ⇒[ p ] B) =
  substᵀ σ M ⦂ substᵗ σ A ⇒[ p ] substᵗ σ B
substᵀ σ (M ⦂ A ⇒⟨ bind X ⟩ B) =
  substᵀ (extsᵗ σ) M
    ⦂ substᵗ (extsᵗ σ) A ⇒⟨ bind X ⟩ substᵗ σ B
substᵀ σ (M ⦂ A ⇒⟨ unbind X ⟩ B) =
  substᵀ σ M
    ⦂ substᵗ σ A ⇒⟨ unbind X ⟩ substᵗ σ B
substᵀ σ (is p M G) = is p (substᵀ σ M) (substᵗ σ G)
substᵀ σ (pair L M) = pair (substᵀ σ L) (substᵀ σ M)
substᵀ σ (fst M) = fst (substᵀ σ M)
substᵀ σ (snd M) = snd (substᵀ σ M)
substᵀ σ (ifte L M N) = ifte (substᵀ σ L) (substᵀ σ M) (substᵀ σ N)
substᵀ σ (prim op M) = prim op (substᵀ σ M)
substᵀ σ (blame p) = blame p

infixl 8 _[_]ᵀ
_[_]ᵀ : Term → Ty → Term
M [ A ]ᵀ = substᵀ (singleTyEnv A) M

------------------------------------------------------------------------
-- Seal-variable renaming through terms
------------------------------------------------------------------------

Renameˢ : Set
Renameˢ = SealVar → SealVar

extˢ : Renameˢ → Renameˢ
extˢ ρ zero = zero
extˢ ρ (suc X) = suc (ρ X)

renameᴮ : Renameˢ → Binder → Binder
renameᴮ ρ (bind X) = bind (ρ X)
renameᴮ ρ (unbind X) = unbind (ρ X)

renameˢ : Renameˢ → Term → Term
renameˢ ρ (` x) = ` x
renameˢ ρ ($ c) = $ c
renameˢ ρ (ƛ[ A ] M) = ƛ[ A ] renameˢ ρ M
renameˢ ρ (L · M) = renameˢ ρ L · renameˢ ρ M
renameˢ ρ (letin L M) = letin (renameˢ ρ L) (renameˢ ρ M)
renameˢ ρ (Λ[ p ] M :: A) = Λ[ p ] renameˢ ρ M :: A
renameˢ ρ (M • A) = renameˢ ρ M • A
renameˢ ρ (ν[ A ] p ∙ M) = ν[ A ] p ∙ renameˢ (extˢ ρ) M
renameˢ ρ (M ⦂ A ⇒[ p ] B) = renameˢ ρ M ⦂ A ⇒[ p ] B
renameˢ ρ (M ⦂ A ⇒⟨ P ⟩ B) = renameˢ ρ M ⦂ A ⇒⟨ renameᴮ ρ P ⟩ B
renameˢ ρ (is p M G) = is p (renameˢ ρ M) G
renameˢ ρ (pair L M) = pair (renameˢ ρ L) (renameˢ ρ M)
renameˢ ρ (fst M) = fst (renameˢ ρ M)
renameˢ ρ (snd M) = snd (renameˢ ρ M)
renameˢ ρ (ifte L M N) = ifte (renameˢ ρ L) (renameˢ ρ M) (renameˢ ρ N)
renameˢ ρ (prim op M) = prim op (renameˢ ρ M)
renameˢ ρ (blame p) = blame p

------------------------------------------------------------------------
-- Term-variable renaming/substitution
------------------------------------------------------------------------

Rename : Set
Rename = Var → Var

Subst : Set
Subst = Var → Term

ren : Rename → Subst
ren ρ x = ` (ρ x)

ext : Rename → Rename
ext ρ zero = zero
ext ρ (suc x) = suc (ρ x)

rename : Rename → Term → Term
rename ρ (` x) = ` (ρ x)
rename ρ ($ c) = $ c
rename ρ (ƛ[ A ] M) = ƛ[ A ] rename (ext ρ) M
rename ρ (L · M) = rename ρ L · rename ρ M
rename ρ (letin L M) = letin (rename ρ L) (rename (ext ρ) M)
rename ρ (Λ[ p ] M :: A) = Λ[ p ] rename ρ M :: A
rename ρ (M • A) = rename ρ M • A
rename ρ (ν[ A ] p ∙ M) = ν[ A ] p ∙ rename ρ M
rename ρ (M ⦂ A ⇒[ p ] B) = rename ρ M ⦂ A ⇒[ p ] B
rename ρ (M ⦂ A ⇒⟨ P ⟩ B) = rename ρ M ⦂ A ⇒⟨ P ⟩ B
rename ρ (is p M G) = is p (rename ρ M) G
rename ρ (pair L M) = pair (rename ρ L) (rename ρ M)
rename ρ (fst M) = fst (rename ρ M)
rename ρ (snd M) = snd (rename ρ M)
rename ρ (ifte L M N) = ifte (rename ρ L) (rename ρ M) (rename ρ N)
rename ρ (prim op M) = prim op (rename ρ M)
rename ρ (blame p) = blame p

exts : Subst → Subst
exts σ zero = ` zero
exts σ (suc x) = rename suc (σ x)

⇑ : Subst → Subst
⇑ σ x = renameᵀ suc (σ x)

⇑ˢ : Subst → Subst
⇑ˢ σ x = renameˢ suc (σ x)

id : Subst
id = `_

infixr 6 _•ˢ_
_•ˢ_ : Term → Subst → Subst
(M •ˢ σ) zero = M
(M •ˢ σ) (suc x) = σ x

------------------------------------------------------------------------
-- Raw total type-scope pop helpers for substitution
------------------------------------------------------------------------

downVarAtᵀᵐ : ℕ → Var → Var
downVarAtᵀᵐ zero zero = zero
downVarAtᵀᵐ zero (suc X) = X
downVarAtᵀᵐ (suc k) zero = zero
downVarAtᵀᵐ (suc k) (suc X) = suc (downVarAtᵀᵐ k X)

downTyAtᵀᵐ : ℕ → Ty → Ty
downTyAtᵀᵐ k (` X) = ` downVarAtᵀᵐ k X
downTyAtᵀᵐ k (`ι ι) = `ι ι
downTyAtᵀᵐ k ★ = ★
downTyAtᵀᵐ k (A ⇒ B) = downTyAtᵀᵐ k A ⇒ downTyAtᵀᵐ k B
downTyAtᵀᵐ k (A `× B) = downTyAtᵀᵐ k A `× downTyAtᵀᵐ k B
downTyAtᵀᵐ k (`∀ A) = `∀ downTyAtᵀᵐ (suc k) A

downTermAtᵀᵐ : ℕ → Term → Term
downTermAtᵀᵐ k (` x) = ` x
downTermAtᵀᵐ k ($ c) = $ c
downTermAtᵀᵐ k (ƛ[ A ] M) = ƛ[ downTyAtᵀᵐ k A ] downTermAtᵀᵐ k M
downTermAtᵀᵐ k (L · M) = downTermAtᵀᵐ k L · downTermAtᵀᵐ k M
downTermAtᵀᵐ k (letin L M) =
  letin (downTermAtᵀᵐ k L) (downTermAtᵀᵐ k M)
downTermAtᵀᵐ k (Λ[ p ] M :: A) =
  Λ[ p ] downTermAtᵀᵐ (suc k) M :: downTyAtᵀᵐ (suc k) A
downTermAtᵀᵐ k (M • A) = downTermAtᵀᵐ k M • downTyAtᵀᵐ k A
downTermAtᵀᵐ k (ν[ A ] p ∙ M) =
  ν[ downTyAtᵀᵐ k A ] p ∙ downTermAtᵀᵐ k M
downTermAtᵀᵐ k (M ⦂ A ⇒[ p ] B) =
  downTermAtᵀᵐ k M ⦂ downTyAtᵀᵐ k A ⇒[ p ] downTyAtᵀᵐ k B
downTermAtᵀᵐ k (M ⦂ A ⇒⟨ bind X ⟩ B) =
  downTermAtᵀᵐ (suc k) M
    ⦂ downTyAtᵀᵐ (suc k) A ⇒⟨ bind X ⟩ downTyAtᵀᵐ k B
downTermAtᵀᵐ k (M ⦂ A ⇒⟨ unbind X ⟩ B) =
  downTermAtᵀᵐ k M
    ⦂ downTyAtᵀᵐ k A ⇒⟨ unbind X ⟩ downTyAtᵀᵐ k B
downTermAtᵀᵐ k (is p M G) = is p (downTermAtᵀᵐ k M) (downTyAtᵀᵐ k G)
downTermAtᵀᵐ k (pair L M) = pair (downTermAtᵀᵐ k L) (downTermAtᵀᵐ k M)
downTermAtᵀᵐ k (fst M) = fst (downTermAtᵀᵐ k M)
downTermAtᵀᵐ k (snd M) = snd (downTermAtᵀᵐ k M)
downTermAtᵀᵐ k (ifte L M N) =
  ifte (downTermAtᵀᵐ k L) (downTermAtᵀᵐ k M) (downTermAtᵀᵐ k N)
downTermAtᵀᵐ k (prim op M) = prim op (downTermAtᵀᵐ k M)
downTermAtᵀᵐ k (blame p) = blame p

Scope : Set
Scope = SealVar → ℕ

emptyScope : Scope
emptyScope X = zero

liftScope : Scope → Scope
liftScope γ X = suc (γ X)

pushScope : SealVar → Scope → Scope
pushScope X γ Y with X ≟ Y
pushScope X γ Y | yes refl = zero
pushScope X γ Y | no _ = suc (γ Y)

sealScope : Scope → Scope
sealScope γ zero = zero
sealScope γ (suc X) = γ X

popScopeAt : ℕ → Scope → Scope
popScopeAt k γ X = downVarAtᵀᵐ k (γ X)

downSubstAt : ℕ → Subst → Subst
downSubstAt k σ x = downTermAtᵀᵐ k (σ x)

pushVarAt : Var → Var → Var
pushVarAt k X with X ≟ k
pushVarAt k X | yes refl = zero
pushVarAt k X | no _ = suc X

pushTermAt : Var → Term → Term
pushTermAt k = renameᵀ (pushVarAt k)

pushSubst : SealVar → Scope → Subst → Subst
pushSubst X γ σ x = pushTermAt (γ X) (σ x)

substScoped : Scope → Subst → Term → Term
substScoped γ σ (` x) = σ x
substScoped γ σ ($ c) = $ c
substScoped γ σ (ƛ[ A ] M) = ƛ[ A ] substScoped γ (exts σ) M
substScoped γ σ (L · M) = substScoped γ σ L · substScoped γ σ M
substScoped γ σ (letin L M) =
  letin (substScoped γ σ L) (substScoped γ (exts σ) M)
substScoped γ σ (Λ[ p ] M :: A) =
  Λ[ p ] substScoped (liftScope γ) (⇑ σ) M :: A
substScoped γ σ (M • A) = substScoped γ σ M • A
substScoped γ σ (ν[ A ] p ∙ M) =
  ν[ A ] p ∙ substScoped (sealScope γ) (⇑ˢ σ) M
substScoped γ σ (M ⦂ A ⇒[ p ] B) = substScoped γ σ M ⦂ A ⇒[ p ] B
substScoped γ σ (M ⦂ A ⇒⟨ bind X ⟩ B) =
  substScoped (pushScope X γ) (pushSubst X γ σ) M ⦂ A ⇒⟨ bind X ⟩ B
substScoped γ σ (M ⦂ A ⇒⟨ unbind X ⟩ B) =
  substScoped (popScopeAt (γ X) γ) (downSubstAt (γ X) σ) M
    ⦂ A ⇒⟨ unbind X ⟩ B
substScoped γ σ (is p M G) = is p (substScoped γ σ M) G
substScoped γ σ (pair L M) = pair (substScoped γ σ L) (substScoped γ σ M)
substScoped γ σ (fst M) = fst (substScoped γ σ M)
substScoped γ σ (snd M) = snd (substScoped γ σ M)
substScoped γ σ (ifte L M N) =
  ifte (substScoped γ σ L) (substScoped γ σ M) (substScoped γ σ N)
substScoped γ σ (prim op M) = prim op (substScoped γ σ M)
substScoped γ σ (blame p) = blame p

subst : Subst → Term → Term
subst σ M = substScoped emptyScope σ M

singleEnv : Term → Subst
singleEnv M zero = M
singleEnv M (suc x) = ` x

infixl 8 _[_]
_[_] : Term → Term → Term
M [ V ] = subst (singleEnv V) M

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

infix 4 _⊢_⦂_
data _⊢_⦂_ : Ctx → Term → Ty → Set where
  ⊢` :
    ∀ {Γ x A} →
    Γ ∋ x ⦂ A →
    Γ ⊢ (` x) ⦂ A

  ⊢const :
    ∀ {Γ c} →
    Γ ⊢ ($ c) ⦂ typeOfConst c

  ⊢ƛ :
    ∀ {Γ A B M} →
    WfTy Γ A →
    (Γ ▷ᵛ A) ⊢ M ⦂ B →
    Γ ⊢ ƛ[ A ] M ⦂ (A ⇒ B)

  ⊢· :
    ∀ {Γ L M A B} →
    Γ ⊢ L ⦂ (A ⇒ B) →
    Γ ⊢ M ⦂ A →
    Γ ⊢ L · M ⦂ B

  ⊢let :
    ∀ {Γ L M A B} →
    Γ ⊢ L ⦂ A →
    (Γ ▷ᵛ A) ⊢ M ⦂ B →
    Γ ⊢ letin L M ⦂ B

  ⊢Λ :
    ∀ {Γ p M B} →
    WfTy (Γ ▷ᵗ) B →
    (Γ ▷ᵗ) ⊢ M ⦂ B →
    Γ ⊢ Λ[ p ] M :: B ⦂ `∀ B

  ⊢inst :
    ∀ {Γ M A B} →
    Γ ⊢ M ⦂ `∀ B →
    WfTy Γ A →
    Γ ⊢ M • A ⦂ B [ A ]ᵗ

  ⊢ν :
    ∀ {Γ A M B p} →
    WfTy Γ A →
    WfTy Γ B →
    (Γ ▷ˢ A) ⊢ M ⦂ B →
    Γ ⊢ ν[ A ] p ∙ M ⦂ B

  ⊢cast :
    ∀ {Γ M A A′ B p} →
    WfTy Γ A →
    WfTy Γ B →
    Γ ⊢ M ⦂ A′ →
    A′ ≡ A →
    A ∼ B →
    Γ ⊢ (M ⦂ A ⇒[ p ] B) ⦂ B

  ⊢bar :
    ∀ {Γ M A B X C} →
    WfTy (Γ ▷ᵇ X) A →
    WfTy Γ B →
    Γ ∋ˢ X := C →
    (Γ ▷ᵇ X) ⊢ M ⦂ A →
    B ≡ A [ C ]ᵗ →
    Γ ⊢ (M ⦂ A ⇒⟨ bind X ⟩ B) ⦂ B

  ⊢barᵛ :
    ∀ {Γ M A B X C D D′} →
    WfTy ((Γ ▷ᵇ X) ▷ᵛ D) A →
    WfTy (Γ ▷ᵛ D′) B →
    Γ ∋ˢ X := C →
    ((Γ ▷ᵇ X) ▷ᵛ D) ⊢ M ⦂ A →
    D′ ≡ D [ C ]ᵗ →
    B ≡ A [ C ]ᵗ →
    (Γ ▷ᵛ D′) ⊢ (M ⦂ A ⇒⟨ bind X ⟩ B) ⦂ B

  ⊢barᴾ :
    ∀ {Γᵒ Γᶜ M A B X C k} →
    PopCtx X C k Γᵒ Γᶜ →
    WfTy Γᵒ A →
    WfTy Γᶜ B →
    Γᵒ ⊢ M ⦂ A →
    B ≡ closeTyAt k C A →
    Γᶜ ⊢ (M ⦂ A ⇒⟨ bind X ⟩ B) ⦂ B

  ⊢bar̄ :
    ∀ {Γ M A B X C} →
    WfTy Γ A →
    WfTy (Γ ▷ᵇ X) B →
    Γ ∋ˢ X := C →
    Γ ⊢ M ⦂ A →
    A ≡ B [ C ]ᵗ →
    (Γ ▷ᵇ X) ⊢ (M ⦂ A ⇒⟨ unbind X ⟩ B) ⦂ B

  ⊢bar̄ᵛ :
    ∀ {Γ M A B X C D D′} →
    WfTy (Γ ▷ᵛ D′) A →
    WfTy ((Γ ▷ᵇ X) ▷ᵛ D) B →
    Γ ∋ˢ X := C →
    (Γ ▷ᵛ D′) ⊢ M ⦂ A →
    D′ ≡ D [ C ]ᵗ →
    A ≡ B [ C ]ᵗ →
    ((Γ ▷ᵇ X) ▷ᵛ D) ⊢ (M ⦂ A ⇒⟨ unbind X ⟩ B) ⦂ B

  ⊢bar̄ᴾ :
    ∀ {Γᵒ Γᶜ M A B X C k} →
    PopCtx X C k Γᵒ Γᶜ →
    WfTy Γᶜ A →
    WfTy Γᵒ B →
    Γᶜ ⊢ M ⦂ A →
    A ≡ closeTyAt k C B →
    Γᵒ ⊢ (M ⦂ A ⇒⟨ unbind X ⟩ B) ⦂ B

  ⊢is :
    ∀ {Γ p M G} →
    Ground G →
    Γ ⊢ M ⦂ ★ →
    Γ ⊢ is p M G ⦂ `ι 𝔹

  ⊢pair :
    ∀ {Γ L M A B} →
    Γ ⊢ L ⦂ A →
    Γ ⊢ M ⦂ B →
    Γ ⊢ pair L M ⦂ A `× B

  ⊢fst :
    ∀ {Γ M A B} →
    Γ ⊢ M ⦂ A `× B →
    Γ ⊢ fst M ⦂ A

  ⊢snd :
    ∀ {Γ M A B} →
    Γ ⊢ M ⦂ A `× B →
    Γ ⊢ snd M ⦂ B

  ⊢if :
    ∀ {Γ L M N A} →
    Γ ⊢ L ⦂ `ι 𝔹 →
    Γ ⊢ M ⦂ A →
    Γ ⊢ N ⦂ A →
    Γ ⊢ ifte L M N ⦂ A

  ⊢prim :
    ∀ {Γ op M A B} →
    typeOfPrim op ≡ (A ⇒ B) →
    Γ ⊢ M ⦂ A →
    Γ ⊢ prim op M ⦂ B

  ⊢blame :
    ∀ {Γ A p} →
    WfTy Γ A →
    Γ ⊢ blame p ⦂ A
