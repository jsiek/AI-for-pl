module Types where

-- File Charter: Core syntax and operations for polymorphic types.

open import Agda.Builtin.FromNat public
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Literals as NatLiterals
open import Data.Fin using (Fin; zero; suc)
import Data.Fin.Literals as FinLiterals
open import Data.Fin.Properties using (_≟_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)
open import Relation.Nullary using (Dec; yes; no)

------------------------------------------------------------------------
-- Type variables, base types, types
------------------------------------------------------------------------

TyCtx : Set
TyCtx = ℕ

TyVar : TyCtx → Set
TyVar Δ = Fin Δ

instance
  Nat-number : Number ℕ
  Nat-number = NatLiterals.number

  Fin-number : ∀ {n} → Number (Fin n)
  Fin-number {n} = FinLiterals.number n

  literal-constraint : ⊤
  literal-constraint = tt

data Base : Set where
  `ℕ : Base
  `𝔹 : Base

infixr 7 _⇒_
infixr 7 _⇒ʳ_
infixr 7 _⇒ˢ_
infix 6 `∀

data Ty : TyCtx → Set where
  ＇_ : ∀ {Δ} → TyVar Δ → Ty Δ
  ‵_ : ∀ {Δ} → Base → Ty Δ
  ★ : ∀ {Δ} → Ty Δ
  _⇒_ : ∀ {Δ} → Ty Δ → Ty Δ → Ty Δ
  `∀ : ∀ {Δ} → Ty (suc Δ) → Ty Δ

private
  variable
    Δ Δ′ : TyCtx
    A B C D : Ty Δ

------------------------------------------------------------------------
-- Non-variable types
------------------------------------------------------------------------

data NonVar {Δ : TyCtx} : Ty Δ → Set where
  nonvar-base : ∀ {ι} → NonVar {Δ} (‵ ι)
  nonvar-star : NonVar {Δ} ★
  nonvar-fun : ∀ {A B} → NonVar {Δ} (A ⇒ B)
  nonvar-all : ∀ {A} → NonVar {Δ} (`∀ A)

nonVar-unique : ∀ {Δ} {A : Ty Δ} (p q : NonVar A)
  → p ≡ q
nonVar-unique nonvar-base nonvar-base = refl
nonVar-unique nonvar-star nonvar-star = refl
nonVar-unique nonvar-fun nonvar-fun = refl
nonVar-unique nonvar-all nonvar-all = refl

instance
  nonVar-base-instance : ∀ {Δ ι} → NonVar {Δ} (‵ ι)
  nonVar-base-instance = nonvar-base

  nonVar-star-instance : ∀ {Δ} → NonVar {Δ} ★
  nonVar-star-instance = nonvar-star

  nonVar-fun-instance : ∀ {Δ} {A B : Ty Δ} → NonVar (A ⇒ B)
  nonVar-fun-instance = nonvar-fun

  nonVar-all-instance : ∀ {Δ} {A : Ty (suc Δ)} → NonVar (`∀ A)
  nonVar-all-instance = nonvar-all

------------------------------------------------------------------------
-- Non-dynamic types
------------------------------------------------------------------------

data NonStar {Δ : TyCtx} : Ty Δ → Set where
  nonstar-X : ∀ {X} → NonStar (＇ X)
  nonstar-ι : ∀ {ι} → NonStar (‵ ι)
  nonstar-⇒ : ∀ {A B} → NonStar (A ⇒ B)
  nonstar-∀ : ∀ {A} → NonStar (`∀ A)

nonStar≢★ : ∀ {Δ} {A : Ty Δ} → NonStar A → A ≢ ★
nonStar≢★ nonstar-X = λ ()
nonStar≢★ nonstar-ι = λ ()
nonStar≢★ nonstar-⇒ = λ ()
nonStar≢★ nonstar-∀ = λ ()

nonStar-unique : ∀ {Δ} {A : Ty Δ} (p q : NonStar A) → p ≡ q
nonStar-unique nonstar-X nonstar-X = refl
nonStar-unique nonstar-ι nonstar-ι = refl
nonStar-unique nonstar-⇒ nonstar-⇒ = refl
nonStar-unique nonstar-∀ nonstar-∀ = refl

instance
  nonstar-X-instance : ∀ {Δ} {X : TyVar Δ} → NonStar (＇ X)
  nonstar-X-instance = nonstar-X

  nonstar-ι-instance : ∀ {Δ ι} → NonStar (‵_ {Δ} ι)
  nonstar-ι-instance = nonstar-ι

  nonstar-⇒-instance : ∀ {Δ} {A B : Ty Δ} → NonStar (A ⇒ B)
  nonstar-⇒-instance = nonstar-⇒

  nonstar-∀-instance : ∀ {Δ} {A : Ty (suc Δ)} → NonStar (`∀ A)
  nonstar-∀-instance = nonstar-∀

------------------------------------------------------------------------
-- _∈ᵗ_, _∉ᵗ_, Tag, Non∀, Atom
------------------------------------------------------------------------

infix 5 _∈ᵗ_ _∉ᵗ_ _≢ᶠ_

data _≢ᶠ_ : ∀ {n} → Fin n → Fin n → Set where
  fin-zero≢suc : ∀ {n} {Y : Fin n} → _≢ᶠ_ {suc n} zero (suc Y)
  fin-suc≢zero : ∀ {n} {X : Fin n} → _≢ᶠ_ {suc n} (suc X) zero
  fin-suc≢suc : ∀ {n} {X Y : Fin n} → X ≢ᶠ Y → suc X ≢ᶠ suc Y

≢ᶠ→≢ : ∀ {n} {X Y : Fin n} → X ≢ᶠ Y → X ≢ Y
≢ᶠ→≢ fin-zero≢suc ()
≢ᶠ→≢ fin-suc≢zero ()
≢ᶠ→≢ (fin-suc≢suc X≢Y) refl = ≢ᶠ→≢ X≢Y refl

≢→≢ᶠ : ∀ {n} {X Y : Fin n} → X ≢ Y → X ≢ᶠ Y
≢→≢ᶠ {X = zero} {Y = zero} X≢X = ⊥-elim (X≢X refl)
≢→≢ᶠ {X = zero} {Y = suc Y} X≢Y = fin-zero≢suc
≢→≢ᶠ {X = suc X} {Y = zero} X≢Y = fin-suc≢zero
≢→≢ᶠ {X = suc X} {Y = suc Y} X≢Y =
  fin-suc≢suc (≢→≢ᶠ (λ X≡Y → X≢Y (cong suc X≡Y)))

≢ᶠ-unique : ∀ {n} {X Y : Fin n} (p q : X ≢ᶠ Y) → p ≡ q
≢ᶠ-unique fin-zero≢suc fin-zero≢suc = refl
≢ᶠ-unique fin-suc≢zero fin-suc≢zero = refl
≢ᶠ-unique (fin-suc≢suc p) (fin-suc≢suc q)
    rewrite ≢ᶠ-unique p q =
  refl

data _∉ᵗ_ {Δ : TyCtx} (X : TyVar Δ) : Ty Δ → Set where
  ∉-var : ∀ {Y} → X ≢ᶠ Y → X ∉ᵗ ＇ Y
  ∉-base : ∀ {ι} → X ∉ᵗ ‵ ι
  ∉-star : X ∉ᵗ ★
  ∉-fun : ∀ {A B} → X ∉ᵗ A → X ∉ᵗ B → X ∉ᵗ A ⇒ B
  ∉-all : ∀ {A} → suc X ∉ᵗ A → X ∉ᵗ `∀ A

data _∈ᵗ_ {Δ : TyCtx} : TyVar Δ → Ty Δ → Set where
  var-∈ : ∀ {X} → X ∈ᵗ ＇ X
  ∈-fun-left : ∀ {X A B} → X ∈ᵗ A → X ∈ᵗ A ⇒ B
  ∈-fun-right : ∀ {X A B} → X ∉ᵗ A → X ∈ᵗ B → X ∈ᵗ A ⇒ B
  ∈-all : ∀ {X A} → suc X ∈ᵗ A → X ∈ᵗ `∀ A

data Occurs? {Δ : TyCtx} (X : TyVar Δ) (A : Ty Δ) : Set where
  present : X ∈ᵗ A → Occurs? X A
  absent : X ∉ᵗ A → Occurs? X A

occurs? : ∀ {Δ} (X : TyVar Δ) (A : Ty Δ) → Occurs? X A
occurs? X (＇ Y) with X ≟ Y
occurs? X (＇ .X) | yes refl = present var-∈
occurs? X (＇ Y) | no X≢Y = absent (∉-var (≢→≢ᶠ X≢Y))
occurs? X (‵ ι) = absent ∉-base
occurs? X ★ = absent ∉-star
occurs? X (A ⇒ B) with occurs? X A
occurs? X (A ⇒ B) | present X∈A = present (∈-fun-left X∈A)
occurs? X (A ⇒ B) | absent X∉A with occurs? X B
occurs? X (A ⇒ B) | absent X∉A | present X∈B =
  present (∈-fun-right X∉A X∈B)
occurs? X (A ⇒ B) | absent X∉A | absent X∉B =
  absent (∉-fun X∉A X∉B)
occurs? X (`∀ A) with occurs? (suc X) A
occurs? X (`∀ A) | present X∈A = present (∈-all X∈A)
occurs? X (`∀ A) | absent X∉A = absent (∉-all X∉A)

data Ground {Δ : TyCtx} : Ty Δ → Set where
  ＇_ : (X : TyVar Δ) → Ground {Δ} (＇ X)
  ‵_ : (ι : Base) → Ground {Δ} (‵ ι)
  ★⇒★ : Ground {Δ} (★ ⇒ ★)
  ∀★ : Ground {Δ} (`∀ ★)

ground-unique : ∀ {Δ} {G : Ty Δ} (p q : Ground G) → p ≡ q
ground-unique (＇ X) (＇ .X) = refl
ground-unique (‵ ι) (‵ .ι) = refl
ground-unique ★⇒★ ★⇒★ = refl
ground-unique ∀★ ∀★ = refl

instance
  ground-var-instance : ∀ {Δ} {X : TyVar Δ} → Ground (＇ X)
  ground-var-instance = ＇ _

  ground-base-instance : ∀ {Δ ι} → Ground {Δ} (‵ ι)
  ground-base-instance = ‵ _

  ground-fun-instance : ∀ {Δ} → Ground {Δ} (★ ⇒ ★)
  ground-fun-instance = ★⇒★

  ground-all-instance : ∀ {Δ} → Ground {Δ} (`∀ ★)
  ground-all-instance = ∀★

data Non∀ {Δ : TyCtx} : Ty Δ → Set where
  non∀-＇ : ∀ {X} → Non∀ {Δ} (＇ X)
  non∀-‵ : ∀ {ι} → Non∀ {Δ} (‵ ι)
  non∀-★ : Non∀ {Δ} ★
  non∀-⇒ : ∀ {A B} → Non∀ {Δ} (A ⇒ B)

data Atom {Δ : TyCtx} : Ty Δ → Set where
  ＇_ : (X : TyVar Δ) → Atom {Δ} (＇ X)
  ‵_ : (ι : Base) → Atom {Δ} (‵ ι)
  ★ : Atom {Δ} ★

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
  ∀ {Δ} {G H : Ty Δ} →
  Ground G →
  Ground H →
  Dec (G ≡ H)
(＇ α) ≟Ground (＇ β) with α ≟ β
(＇ α) ≟Ground (＇ β) | yes eq = yes (cong ＇_ eq)
(＇ α) ≟Ground (＇ β) | no neq = no (λ { refl → neq refl })
(＇ α) ≟Ground (‵ ι) = no (λ ())
(＇ α) ≟Ground ★⇒★ = no (λ ())
(＇ α) ≟Ground ∀★ = no (λ ())
(‵ ι) ≟Ground (＇ α) = no (λ ())
(‵ ι) ≟Ground (‵ ι′) with ι ≟Base ι′
(‵ ι) ≟Ground (‵ ι′) | yes eq = yes (cong ‵_ eq)
(‵ ι) ≟Ground (‵ ι′) | no neq = no (λ { refl → neq refl })
(‵ ι) ≟Ground ★⇒★ = no (λ ())
(‵ ι) ≟Ground ∀★ = no (λ ())
★⇒★ ≟Ground (＇ α) = no (λ ())
★⇒★ ≟Ground (‵ ι) = no (λ ())
★⇒★ ≟Ground ★⇒★ = yes refl
★⇒★ ≟Ground ∀★ = no (λ ())
∀★ ≟Ground (＇ α) = no (λ ())
∀★ ≟Ground (‵ ι) = no (λ ())
∀★ ≟Ground ★⇒★ = no (λ ())
∀★ ≟Ground ∀★ = yes refl

infix 4 _≟Ty_
_≟Ty_ : ∀ {Δ} (A B : Ty Δ) → Dec (A ≡ B)
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

_⇒ʳ_ : TyCtx → TyCtx → Set
Δ ⇒ʳ Δ′ = TyVar Δ → TyVar Δ′

_⇒ˢ_ : TyCtx → TyCtx → Set
Δ ⇒ˢ Δ′ = TyVar Δ → Ty Δ′

extᵗ : Δ ⇒ʳ Δ′ → suc Δ ⇒ʳ suc Δ′
extᵗ ρ zero = zero
extᵗ ρ (suc X) = suc (ρ X)

renameᵗ : Δ ⇒ʳ Δ′ → Ty Δ → Ty Δ′
renameᵗ ρ (＇ X) = ＇ (ρ X)
renameᵗ ρ (‵ ι) = ‵ ι
renameᵗ ρ ★ = ★
renameᵗ ρ (A ⇒ B) = renameᵗ ρ A ⇒ renameᵗ ρ B
renameᵗ ρ (`∀ A) = `∀ (renameᵗ (extᵗ ρ) A)

singleRenameᵗ : TyVar Δ → suc Δ ⇒ʳ Δ
singleRenameᵗ Y zero = Y
singleRenameᵗ Y (suc X) = X

⇑ᵗ : Ty Δ → Ty (suc Δ)
⇑ᵗ = renameᵗ suc

infixl 8 _[_]ᴿ
_[_]ᴿ : Ty (suc Δ) → TyVar Δ → Ty Δ
A [ X ]ᴿ = renameᵗ (singleRenameᵗ X) A

extsᵗ : Δ ⇒ˢ Δ′ → suc Δ ⇒ˢ suc Δ′
extsᵗ σ zero = ＇ zero
extsᵗ σ (suc X) = renameᵗ suc (σ X)

substᵗ : Δ ⇒ˢ Δ′ → Ty Δ → Ty Δ′
substᵗ σ (＇ X) = σ X
substᵗ σ (‵ ι) = ‵ ι
substᵗ σ ★ = ★
substᵗ σ (A ⇒ B) = substᵗ σ A ⇒ substᵗ σ B
substᵗ σ (`∀ A) = `∀ (substᵗ (extsᵗ σ) A)

renameᵗ-cong : ∀ {Δ Δ′} {ρ ρ′ : Δ ⇒ʳ Δ′} (A : Ty Δ)
  → (∀ X → ρ X ≡ ρ′ X)
  → renameᵗ ρ A ≡ renameᵗ ρ′ A
renameᵗ-cong (＇ X) eq = cong ＇_ (eq X)
renameᵗ-cong (‵ ι) eq = refl
renameᵗ-cong ★ eq = refl
renameᵗ-cong (A ⇒ B) eq
  rewrite renameᵗ-cong A eq | renameᵗ-cong B eq = refl
renameᵗ-cong {ρ = ρ} {ρ′} (`∀ A) eq =
  cong `∀ (renameᵗ-cong A ext-eq)
  where
  ext-eq : ∀ X → extᵗ ρ X ≡ extᵗ ρ′ X
  ext-eq zero = refl
  ext-eq (suc X) = cong suc (eq X)

substᵗ-cong : ∀ {Δ Δ′} {σ σ′ : Δ ⇒ˢ Δ′} (A : Ty Δ)
  → (∀ X → σ X ≡ σ′ X)
  → substᵗ σ A ≡ substᵗ σ′ A
substᵗ-cong (＇ X) eq = eq X
substᵗ-cong (‵ ι) eq = refl
substᵗ-cong ★ eq = refl
substᵗ-cong (A ⇒ B) eq
  rewrite substᵗ-cong A eq | substᵗ-cong B eq = refl
substᵗ-cong {σ = σ} {σ′} (`∀ A) eq =
  cong `∀ (substᵗ-cong A exts-eq)
  where
  exts-eq : ∀ X → extsᵗ σ X ≡ extsᵗ σ′ X
  exts-eq zero = refl
  exts-eq (suc X) = cong (renameᵗ suc) (eq X)

substᵗ-id : ∀ {Δ} (A : Ty Δ)
  → substᵗ (λ X → ＇ X) A ≡ A
substᵗ-id (＇ X) = refl
substᵗ-id (‵ ι) = refl
substᵗ-id ★ = refl
substᵗ-id (A ⇒ B) rewrite substᵗ-id A | substᵗ-id B = refl
substᵗ-id (`∀ A) = cong `∀
  (trans (substᵗ-cong A ext-id) (substᵗ-id A))
  where
  ext-id : ∀ X → extsᵗ (λ Y → ＇ Y) X ≡ ＇ X
  ext-id zero = refl
  ext-id (suc X) = refl

renameᵗ-comp : ∀ {Δ₁ Δ₂ Δ₃}
  → (ρ₁ : Δ₁ ⇒ʳ Δ₂)
  → (ρ₂ : Δ₂ ⇒ʳ Δ₃)
  → (A : Ty Δ₁)
  → renameᵗ ρ₂ (renameᵗ ρ₁ A)
    ≡ renameᵗ (λ X → ρ₂ (ρ₁ X)) A
renameᵗ-comp ρ₁ ρ₂ (＇ X) = refl
renameᵗ-comp ρ₁ ρ₂ (‵ ι) = refl
renameᵗ-comp ρ₁ ρ₂ ★ = refl
renameᵗ-comp ρ₁ ρ₂ (A ⇒ B)
  rewrite renameᵗ-comp ρ₁ ρ₂ A | renameᵗ-comp ρ₁ ρ₂ B = refl
renameᵗ-comp ρ₁ ρ₂ (`∀ A) = cong `∀
  (trans (renameᵗ-comp (extᵗ ρ₁) (extᵗ ρ₂) A)
         (renameᵗ-cong A ext-comp))
  where
  ext-comp : ∀ X
    → extᵗ ρ₂ (extᵗ ρ₁ X)
      ≡ extᵗ (λ Y → ρ₂ (ρ₁ Y)) X
  ext-comp zero = refl
  ext-comp (suc X) = refl

renameᵗ-shift : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) (A : Ty Δ)
  → renameᵗ (extᵗ ρ) (⇑ᵗ A) ≡ ⇑ᵗ (renameᵗ ρ A)
renameᵗ-shift ρ A =
  trans (renameᵗ-comp suc (extᵗ ρ) A)
    (trans (renameᵗ-cong A (λ X → refl))
           (sym (renameᵗ-comp ρ suc A)))

renameᵗ-subst : ∀ {Δ₁ Δ₂ Δ₃}
  → (ρ : Δ₂ ⇒ʳ Δ₃)
  → (σ : Δ₁ ⇒ˢ Δ₂)
  → (A : Ty Δ₁)
  → renameᵗ ρ (substᵗ σ A)
    ≡ substᵗ (λ X → renameᵗ ρ (σ X)) A
renameᵗ-subst ρ σ (＇ X) = refl
renameᵗ-subst ρ σ (‵ ι) = refl
renameᵗ-subst ρ σ ★ = refl
renameᵗ-subst ρ σ (A ⇒ B)
  rewrite renameᵗ-subst ρ σ A | renameᵗ-subst ρ σ B = refl
renameᵗ-subst ρ σ (`∀ A) = cong `∀
  (trans (renameᵗ-subst (extᵗ ρ) (extsᵗ σ) A)
         (substᵗ-cong A exts-comp))
  where
  exts-comp : ∀ X
    → renameᵗ (extᵗ ρ) (extsᵗ σ X)
      ≡ extsᵗ (λ Y → renameᵗ ρ (σ Y)) X
  exts-comp zero = refl
  exts-comp (suc X) = renameᵗ-shift ρ (σ X)

substᵗ-rename : ∀ {Δ₁ Δ₂ Δ₃}
  → (σ : Δ₂ ⇒ˢ Δ₃)
  → (ρ : Δ₁ ⇒ʳ Δ₂)
  → (A : Ty Δ₁)
  → substᵗ σ (renameᵗ ρ A) ≡ substᵗ (λ X → σ (ρ X)) A
substᵗ-rename σ ρ (＇ X) = refl
substᵗ-rename σ ρ (‵ ι) = refl
substᵗ-rename σ ρ ★ = refl
substᵗ-rename σ ρ (A ⇒ B)
  rewrite substᵗ-rename σ ρ A | substᵗ-rename σ ρ B = refl
substᵗ-rename σ ρ (`∀ A) = cong `∀
  (trans (substᵗ-rename (extsᵗ σ) (extᵗ ρ) A)
         (substᵗ-cong A exts-comp))
  where
  exts-comp : ∀ X
    → extsᵗ σ (extᵗ ρ X) ≡ extsᵗ (λ Y → σ (ρ Y)) X
  exts-comp zero = refl
  exts-comp (suc X) = refl

substᵗ-shift : ∀ {Δ Δ′} (σ : Δ ⇒ˢ Δ′) (A : Ty Δ)
  → substᵗ (extsᵗ σ) (⇑ᵗ A) ≡ ⇑ᵗ (substᵗ σ A)
substᵗ-shift σ A =
  trans (substᵗ-rename (extsᵗ σ) suc A)
        (sym (renameᵗ-subst suc σ A))

renameNonVar : ∀ {A : Ty Δ} (ρ : Δ ⇒ʳ Δ′)
  → NonVar A
  → NonVar (renameᵗ ρ A)
renameNonVar ρ nonvar-base = nonvar-base
renameNonVar ρ nonvar-star = nonvar-star
renameNonVar ρ nonvar-fun = nonvar-fun
renameNonVar ρ nonvar-all = nonvar-all

substNonVar : ∀ {A : Ty Δ} (σ : Δ ⇒ˢ Δ′)
  → NonVar A
  → NonVar (substᵗ σ A)
substNonVar σ nonvar-base = nonvar-base
substNonVar σ nonvar-star = nonvar-star
substNonVar σ nonvar-fun = nonvar-fun
substNonVar σ nonvar-all = nonvar-all

singleSubᵗ : Ty Δ → suc Δ ⇒ˢ Δ
singleSubᵗ B zero = B
singleSubᵗ B (suc X) = ＇ X

infixl 8 _[_]ᵗ
_[_]ᵗ : Ty (suc Δ) → Ty Δ → Ty Δ
A [ B ]ᵗ = substᵗ (singleSubᵗ B) A

shift-openᵗ : ∀ {Δ} (A B : Ty Δ) → (⇑ᵗ A) [ B ]ᵗ ≡ A
shift-openᵗ A B =
  trans (substᵗ-rename (singleSubᵗ B) suc A)
    (trans (substᵗ-cong A (λ X → refl)) (substᵗ-id A))
