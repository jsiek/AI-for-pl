module Types where

-- File Charter: Core syntax and operations for polymorphic types.

open import Data.Bool using (Bool; false; true; _∨_)
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
-- occurs, Ground, Non∀, Atom
------------------------------------------------------------------------

occurs : TyVar → Ty → Bool
occurs X (＇ Y) with X ≟ Y
occurs X (＇ Y) | yes eq = true
occurs X (＇ Y) | no neq = false
occurs X (‵ ι) = false
occurs X ★ = false
occurs X (A ⇒ B) = occurs X A ∨ occurs X B
occurs X (`∀ A) = occurs (suc X) A

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
(＇ X) ≟Ground (＇ Y) with X ≟ Y
... | yes eq = yes (cong ＇_ eq)
... | no neq = no (λ { refl → neq refl })
(＇ X) ≟Ground (‵ ι) = no (λ ())
(＇ X) ≟Ground ★⇒★ = no (λ ())
(‵ ι) ≟Ground (＇ X) = no (λ ())
(‵ ι) ≟Ground (‵ ι′) with ι ≟Base ι′
... | yes eq = yes (cong ‵_ eq)
... | no neq = no (λ { refl → neq refl })
(‵ ι) ≟Ground ★⇒★ = no (λ ())
★⇒★ ≟Ground (＇ X) = no (λ ())
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

