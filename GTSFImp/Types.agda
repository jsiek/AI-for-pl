module Types where

-- File Charter: Core syntax and operations for polymorphic types.

open import Data.Bool using (Bool; false; true; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _<_; zero; suc; z<s; s<s)
open import Data.Nat.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)
open import Relation.Nullary using (Dec; yes; no)

------------------------------------------------------------------------
-- Type variables, base types, types
------------------------------------------------------------------------

TyVar : Set
TyVar = ℕ

TyCtx : Set
TyCtx = ℕ

data Base : Set where
  `ℕ : Base
  `𝔹 : Base

infixr 7 _⇒_
infix 6 `∀

data Ty : Set where
  ＇_ : TyVar → Ty
  ‵_ : Base → Ty
  ★ : Ty
  _⇒_ : Ty → Ty → Ty
  `∀ : Ty → Ty

------------------------------------------------------------------------
-- Non-variable types
------------------------------------------------------------------------

data NonVar : Ty → Set where
  nonvar-base : ∀ {ι} → NonVar (‵ ι)
  nonvar-star : NonVar ★
  nonvar-fun : ∀ {A B} → NonVar (A ⇒ B)
  nonvar-all : ∀ {A} → NonVar (`∀ A)

nonVar-unique : ∀ {A} (p q : NonVar A)
  → p ≡ q
nonVar-unique nonvar-base nonvar-base = refl
nonVar-unique nonvar-star nonvar-star = refl
nonVar-unique nonvar-fun nonvar-fun = refl
nonVar-unique nonvar-all nonvar-all = refl

instance
  nonVar-base-instance : ∀ {ι} → NonVar (‵ ι)
  nonVar-base-instance = nonvar-base

  nonVar-star-instance : NonVar ★
  nonVar-star-instance = nonvar-star

  nonVar-fun-instance : ∀ {A B} → NonVar (A ⇒ B)
  nonVar-fun-instance = nonvar-fun

  nonVar-all-instance : ∀ {A} → NonVar (`∀ A)
  nonVar-all-instance = nonvar-all

------------------------------------------------------------------------
-- _∈ᵗ_, Tag, Non∀, Atom
------------------------------------------------------------------------

infix 5 _∈ᵗ_
data _∈ᵗ_ : TyVar → Ty → Set where
  var-∈ : ∀{X} → X ∈ᵗ ＇ X
  ∈-fun-left : ∀{X A B} → X ∈ᵗ A → X ∈ᵗ A ⇒ B
  ∈-fun-right : ∀{X A B} → X ∈ᵗ B → X ∈ᵗ A ⇒ B
  ∈-all : ∀{X A} → suc X ∈ᵗ A → X ∈ᵗ `∀ A

data Ground : Ty → Set where
  ＇_ : (X : TyVar) → Ground (＇ X)
  ‵_ : (ι : Base) → Ground (‵ ι)
  ★⇒★ : Ground (★ ⇒ ★)

data Non∀ : Ty → Set where
  non∀-＇ : ∀ {X} → Non∀ (＇ X)
  non∀-‵ : ∀ {ι} → Non∀ (‵ ι)
  non∀-★ : Non∀ ★
  non∀-⇒ : ∀ {A B} → Non∀ (A ⇒ B)
  
data Atom : Ty → Set where
  ＇_ : (X : TyVar) → Atom (＇ X)
  ‵_ : (ι : Base) → Atom (‵ ι)
  ★ : Atom ★

------------------------------------------------------------------------
-- Decidable equality of base, ground, and types
------------------------------------------------------------------------

infix 4 _≟Base_
_≟Base_ : (ι ι′ : Base) → Dec (ι ≡ ι′)
`ℕ ≟Base `ℕ = yes refl
`ℕ ≟Base `𝔹 = no (λ ())
`𝔹 ≟Base `ℕ = no (λ ())
`𝔹 ≟Base `𝔹 = yes refl

infix 4 _≟Ground_
_≟Ground_ :
  ∀ {G H : Ty} →
  Ground G →
  Ground H →
  Dec (G ≡ H)
(＇ α) ≟Ground (＇ β) with α ≟ β
... | yes eq = yes (cong ＇_ eq)
... | no neq = no (λ { refl → neq refl })
(＇ α) ≟Ground (‵ ι) = no (λ ())
(＇ α) ≟Ground ★⇒★ = no (λ ())
(‵ ι) ≟Ground (＇ α) = no (λ ())
(‵ ι) ≟Ground (‵ ι′) with ι ≟Base ι′
... | yes eq = yes (cong ‵_ eq)
... | no neq = no (λ { refl → neq refl })
(‵ ι) ≟Ground ★⇒★ = no (λ ())
★⇒★ ≟Ground (＇ α) = no (λ ())
★⇒★ ≟Ground (‵ ι) = no (λ ())
★⇒★ ≟Ground ★⇒★ = yes refl

infix 4 _≟Ty_
_≟Ty_ : (A B : Ty) → Dec (A ≡ B)
＇ X ≟Ty ＇ Y with X ≟ Y
＇ X ≟Ty ＇ Y | yes X≡Y = yes (cong ＇_ X≡Y)
＇ X ≟Ty ＇ Y | no X≢Y = no (λ { refl → X≢Y refl })
＇ X ≟Ty ‵ ι = no (λ ())
＇ X ≟Ty ★ = no (λ ())
＇ X ≟Ty (A ⇒ B) = no (λ ())
＇ X ≟Ty `∀ B = no (λ ())
‵ ι ≟Ty ＇ Y = no (λ ())
‵ ι ≟Ty ‵ ι′ with ι ≟Base ι′
‵ ι ≟Ty ‵ ι′ | yes ι≡ι′ = yes (cong ‵_ ι≡ι′)
‵ ι ≟Ty ‵ ι′ | no ι≢ι′ = no (λ { refl → ι≢ι′ refl })
‵ ι ≟Ty ★ = no (λ ())
‵ ι ≟Ty (A ⇒ B) = no (λ ())
‵ ι ≟Ty `∀ B = no (λ ())
★ ≟Ty ＇ Y = no (λ ())
★ ≟Ty ‵ ι = no (λ ())
★ ≟Ty ★ = yes refl
★ ≟Ty (A ⇒ B) = no (λ ())
★ ≟Ty `∀ B = no (λ ())
(A ⇒ B) ≟Ty ＇ Y = no (λ ())
(A ⇒ B) ≟Ty ‵ ι = no (λ ())
(A ⇒ B) ≟Ty ★ = no (λ ())
(A ⇒ B) ≟Ty (A′ ⇒ B′) with A ≟Ty A′ | B ≟Ty B′
(A ⇒ B) ≟Ty (A′ ⇒ B′) | yes A≡A′ | yes B≡B′ =
  yes (cong₂ _⇒_ A≡A′ B≡B′)
(A ⇒ B) ≟Ty (A′ ⇒ B′) | no A≢A′ | _ =
  no (λ { refl → A≢A′ refl })
(A ⇒ B) ≟Ty (A′ ⇒ B′) | yes A≡A′ | no B≢B′ =
  no (λ { refl → B≢B′ refl })
(A ⇒ B) ≟Ty `∀ C = no (λ ())
`∀ A ≟Ty ＇ Y = no (λ ())
`∀ A ≟Ty ‵ ι = no (λ ())
`∀ A ≟Ty ★ = no (λ ())
`∀ A ≟Ty (B ⇒ C) = no (λ ())
`∀ A ≟Ty `∀ B with A ≟Ty B
`∀ A ≟Ty `∀ B | yes A≡B = yes (cong `∀ A≡B)
`∀ A ≟Ty `∀ B | no A≢B = no (λ { refl → A≢B refl })

------------------------------------------------------------------------
-- Type-variable renaming and substitution (de Bruijn)
------------------------------------------------------------------------

Renameᵗ : Set
Renameᵗ = TyVar → TyVar

Substᵗ : Set
Substᵗ = TyVar → Ty

extᵗ : Renameᵗ → Renameᵗ
extᵗ ρ zero = zero
extᵗ ρ (suc X) = suc (ρ X)

renameᵗ : Renameᵗ → Ty → Ty
renameᵗ ρ (＇ X) = ＇ (ρ X)
renameᵗ ρ (‵ ι) = ‵ ι
renameᵗ ρ ★ = ★
renameᵗ ρ (A ⇒ B) = renameᵗ ρ A ⇒ renameᵗ ρ B
renameᵗ ρ (`∀ A) = `∀ (renameᵗ (extᵗ ρ) A)

singleRenameᵗ : TyVar → Renameᵗ
singleRenameᵗ Y zero = Y
singleRenameᵗ Y (suc X) = X

⇑ᵗ : Ty → Ty
⇑ᵗ = renameᵗ suc

infixl 8 _[_]ᴿ
_[_]ᴿ : Ty → TyVar → Ty
A [ X ]ᴿ = renameᵗ (singleRenameᵗ X) A

extsᵗ : Substᵗ → Substᵗ
extsᵗ σ zero = ＇ 0
extsᵗ σ (suc X) = renameᵗ suc (σ X)

substᵗ : Substᵗ → Ty → Ty
substᵗ σ (＇ X) = σ X
substᵗ σ (‵ ι) = ‵ ι
substᵗ σ ★ = ★
substᵗ σ (A ⇒ B) = substᵗ σ A ⇒ substᵗ σ B
substᵗ σ (`∀ A) = `∀ (substᵗ (extsᵗ σ) A)

renameNonVar : ∀ {A} (ρ : Renameᵗ)
  → NonVar A
  → NonVar (renameᵗ ρ A)
renameNonVar ρ nonvar-base = nonvar-base
renameNonVar ρ nonvar-star = nonvar-star
renameNonVar ρ nonvar-fun = nonvar-fun
renameNonVar ρ nonvar-all = nonvar-all

substNonVar : ∀ {A} (σ : Substᵗ)
  → NonVar A
  → NonVar (substᵗ σ A)
substNonVar σ nonvar-base = nonvar-base
substNonVar σ nonvar-star = nonvar-star
substNonVar σ nonvar-fun = nonvar-fun
substNonVar σ nonvar-all = nonvar-all

singleSubᵗ : Ty → Substᵗ
singleSubᵗ B zero = B
singleSubᵗ B (suc X) = ＇ X

substVarFrom : TyVar → Ty → Substᵗ
substVarFrom zero T = singleSubᵗ T
substVarFrom (suc k) T = extsᵗ (substVarFrom k T)

infixl 8 _[_]ᵗ
_[_]ᵗ : Ty → Ty → Ty
A [ B ]ᵗ = substᵗ (singleSubᵗ B) A

------------------------------------------------------------------------
-- Type Well-formedness
------------------------------------------------------------------------

data WfTy : TyCtx → Ty → Set where
  wfVar : ∀ {Δ X} → X < Δ → WfTy Δ (＇ X)
  wfBase : ∀ {Δ ι} → WfTy Δ (‵ ι)
  wf★ : ∀ {Δ} → WfTy Δ ★
  wf⇒ : ∀ {Δ A B} → WfTy Δ A → WfTy Δ B → WfTy Δ (A ⇒ B)
  wf∀ : ∀ {Δ A} → WfTy (suc Δ) A → WfTy Δ (`∀ A)

------------------------------------------------------------------------
-- List Membership
------------------------------------------------------------------------

infix 4 _∋_⦂_
data _∋_⦂_ : ∀{X : Set} → List X → ℕ → X → Set₁ where
  Z : ∀ {X}{Γ : List X}{A : X} →
      (A ∷ Γ) ∋ zero ⦂ A

  S : ∀{X}{Γ}{A B : X}{x} →
      Γ ∋ x ⦂ A →
      (B ∷ Γ) ∋ suc x ⦂ A
