module Types where

-- File Charter:
--   * Core syntax and primitive operations for GTSF types.
--   * Introduces the redesigned de Bruijn treatment of regular type
--     variables and runtime seals as separate namespaces inside one telescope.
--   * Defines type well-formedness, telescope well-formedness, lookup,
--     renaming, and substitution.  Proof-only metatheory belongs in
--     `proof/TypeProperties.agda`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; false; true; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_; suc-injective)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
open import Relation.Nullary using (Dec; yes; no)

------------------------------------------------------------------------
-- Variables, base types, and types
------------------------------------------------------------------------

Var : Set
Var = ℕ

TyVar : Set
TyVar = ℕ

SealVar : Set
SealVar = ℕ

data Base : Set where
  `ℕ : Base
  `𝔹 : Base

infixr 7 _⇒_
infix 6 `∀
infix 9 `X_
infix 9 `α_

data Ty : Set where
  `X_ : TyVar → Ty
  `α_ : SealVar → Ty
  ‵_ : Base → Ty
  ★ : Ty
  _⇒_ : Ty → Ty → Ty
  `∀ : Ty → Ty

occursᵗ : TyVar → Ty → Bool
occursᵗ X (`X Y) with X ≟ Y
... | yes eq = true
... | no neq = false
occursᵗ X (`α α) = false
occursᵗ X (‵ ι) = false
occursᵗ X ★ = false
occursᵗ X (A ⇒ B) = occursᵗ X A ∨ occursᵗ X B
occursᵗ X (`∀ A) = occursᵗ (suc X) A

occursˢ : SealVar → Ty → Bool
occursˢ α (`X X) = false
occursˢ α (`α β) with α ≟ β
... | yes eq = true
... | no neq = false
occursˢ α (‵ ι) = false
occursˢ α ★ = false
occursˢ α (A ⇒ B) = occursˢ α A ∨ occursˢ α B
occursˢ α (`∀ A) = occursˢ α A

X₀ : Ty
X₀ = `X zero

α₀ : Ty
α₀ = `α zero

------------------------------------------------------------------------
-- Type shapes
------------------------------------------------------------------------

data Ground : Ty → Set where
  `α_ : (α : SealVar) → Ground (`α α)
  ‵_ : (ι : Base) → Ground (‵ ι)
  ★⇒★ : Ground (★ ⇒ ★)

data Star : Ty → Set where
  ★ : Star ★

data Gnd : Ty → Set where
  `α_ : (α : SealVar) → Gnd (`α α)
  ‵_ : (ι : Base) → Gnd (‵ ι)
  _⇒_ : ∀ {A B} → Star A → Star B → Gnd (A ⇒ B)

data Non∀ : Ty → Set where
  non∀-X : ∀ {X} → Non∀ (`X X)
  non∀-α : ∀ {α} → Non∀ (`α α)
  non∀-‵ : ∀ {ι} → Non∀ (‵ ι)
  non∀-★ : Non∀ ★
  non∀-⇒ : ∀ {A B} → Non∀ (A ⇒ B)

data Atom : Ty → Set where
  `X_ : (X : TyVar) → Atom (`X X)
  `α_ : (α : SealVar) → Atom (`α α)
  ‵_ : (ι : Base) → Atom (‵ ι)
  ★ : Atom ★

------------------------------------------------------------------------
-- Decidable equality
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
(`α α) ≟Ground (`α β) with α ≟ β
... | yes eq = yes (cong `α_ eq)
... | no neq = no (λ { refl → neq refl })
(`α α) ≟Ground (‵ ι) = no (λ ())
(`α α) ≟Ground ★⇒★ = no (λ ())
(‵ ι) ≟Ground (`α α) = no (λ ())
(‵ ι) ≟Ground (‵ ι′) with ι ≟Base ι′
... | yes eq = yes (cong ‵_ eq)
... | no neq = no (λ { refl → neq refl })
(‵ ι) ≟Ground ★⇒★ = no (λ ())
★⇒★ ≟Ground (`α α) = no (λ ())
★⇒★ ≟Ground (‵ ι) = no (λ ())
★⇒★ ≟Ground ★⇒★ = yes refl

infix 4 _≟Ty_
_≟Ty_ : (A B : Ty) → Dec (A ≡ B)
`X X ≟Ty `X Y with X ≟ Y
`X X ≟Ty `X .X | yes refl = yes refl
`X X ≟Ty `X Y | no X≢Y = no (λ { refl → X≢Y refl })
`X X ≟Ty `α β = no (λ ())
`X X ≟Ty ‵ ι = no (λ ())
`X X ≟Ty ★ = no (λ ())
`X X ≟Ty (A ⇒ B) = no (λ ())
`X X ≟Ty `∀ B = no (λ ())
`α α ≟Ty `X X = no (λ ())
`α α ≟Ty `α β with α ≟ β
`α α ≟Ty `α .α | yes refl = yes refl
`α α ≟Ty `α β | no α≢β = no (λ { refl → α≢β refl })
`α α ≟Ty ‵ ι = no (λ ())
`α α ≟Ty ★ = no (λ ())
`α α ≟Ty (A ⇒ B) = no (λ ())
`α α ≟Ty `∀ B = no (λ ())
‵ ι ≟Ty `X X = no (λ ())
‵ ι ≟Ty `α α = no (λ ())
‵ ι ≟Ty ‵ ι′ with ι ≟Base ι′
‵ ι ≟Ty ‵ .ι | yes refl = yes refl
‵ ι ≟Ty ‵ ι′ | no ι≢ι′ = no (λ { refl → ι≢ι′ refl })
‵ ι ≟Ty ★ = no (λ ())
‵ ι ≟Ty (A ⇒ B) = no (λ ())
‵ ι ≟Ty `∀ B = no (λ ())
★ ≟Ty `X X = no (λ ())
★ ≟Ty `α α = no (λ ())
★ ≟Ty ‵ ι = no (λ ())
★ ≟Ty ★ = yes refl
★ ≟Ty (A ⇒ B) = no (λ ())
★ ≟Ty `∀ B = no (λ ())
(A ⇒ B) ≟Ty `X X = no (λ ())
(A ⇒ B) ≟Ty `α α = no (λ ())
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
`∀ A ≟Ty `X X = no (λ ())
`∀ A ≟Ty `α α = no (λ ())
`∀ A ≟Ty ‵ ι = no (λ ())
`∀ A ≟Ty ★ = no (λ ())
`∀ A ≟Ty (B ⇒ C) = no (λ ())
`∀ A ≟Ty `∀ B with A ≟Ty B
`∀ A ≟Ty `∀ .A | yes refl = yes refl
`∀ A ≟Ty `∀ B | no A≢B = no (λ { refl → A≢B refl })

------------------------------------------------------------------------
-- Telescopes
------------------------------------------------------------------------

data Entry : Set where
  tyᵉ : Entry
  sealᵉ : Ty → Entry
  termᵉ : Ty → Entry

Telescope : Set
Telescope = List Entry

------------------------------------------------------------------------
-- Raw renaming and substitution
------------------------------------------------------------------------

Renameᵗ : Set
Renameᵗ = TyVar → TyVar

Renameˢ : Set
Renameˢ = SealVar → SealVar

Substᵗ : Set
Substᵗ = TyVar → Ty

Substˢ : Set
Substˢ = SealVar → Ty

idᵗ : Renameᵗ
idᵗ X = X

idˢ : Renameˢ
idˢ α = α

extᵗ : Renameᵗ → Renameᵗ
extᵗ ρ zero = zero
extᵗ ρ (suc X) = suc (ρ X)

extˢ : Renameˢ → Renameˢ
extˢ ρ zero = zero
extˢ ρ (suc α) = suc (ρ α)

rename : Renameᵗ → Renameˢ → Ty → Ty
rename ρ σ (`X X) = `X (ρ X)
rename ρ σ (`α α) = `α (σ α)
rename ρ σ (‵ ι) = ‵ ι
rename ρ σ ★ = ★
rename ρ σ (A ⇒ B) = rename ρ σ A ⇒ rename ρ σ B
rename ρ σ (`∀ A) = `∀ (rename (extᵗ ρ) σ A)

renameᵗ : Renameᵗ → Ty → Ty
renameᵗ ρ = rename ρ idˢ

renameˢ : Renameˢ → Ty → Ty
renameˢ σ = rename idᵗ σ

⇑ᵗ : Ty → Ty
⇑ᵗ = renameᵗ suc

⇑ˢ : Ty → Ty
⇑ˢ = renameˢ suc

singleRenameᵗ : TyVar → Renameᵗ
singleRenameᵗ Y zero = Y
singleRenameᵗ Y (suc X) = X

singleRenameˢ : SealVar → Renameˢ
singleRenameˢ β zero = β
singleRenameˢ β (suc α) = α

infixl 8 _[_]ᴿ
_[_]ᴿ : Ty → TyVar → Ty
A [ X ]ᴿ = renameᵗ (singleRenameᵗ X) A

infixl 8 _[_]ˢᴿ
_[_]ˢᴿ : Ty → SealVar → Ty
A [ α ]ˢᴿ = renameˢ (singleRenameˢ α) A

extSubstᵗ : Substᵗ → Substᵗ
extSubstᵗ σ zero = X₀
extSubstᵗ σ (suc X) = ⇑ᵗ (σ X)

extSubstˢ : Substˢ → Substˢ
extSubstˢ σ zero = α₀
extSubstˢ σ (suc α) = ⇑ˢ (σ α)

liftSubstˢOverTy : Substˢ → Substˢ
liftSubstˢOverTy σ α = ⇑ᵗ (σ α)

subst : Substᵗ → Substˢ → Ty → Ty
subst σ τ (`X X) = σ X
subst σ τ (`α α) = τ α
subst σ τ (‵ ι) = ‵ ι
subst σ τ ★ = ★
subst σ τ (A ⇒ B) = subst σ τ A ⇒ subst σ τ B
subst σ τ (`∀ A) = `∀ (subst (extSubstᵗ σ) (liftSubstˢOverTy τ) A)

substᵗ : Substᵗ → Ty → Ty
substᵗ σ = subst σ `α_

substˢ : Substˢ → Ty → Ty
substˢ τ = subst `X_ τ

singleTyEnv : Ty → Substᵗ
singleTyEnv B zero = B
singleTyEnv B (suc X) = `X X

singleSealEnv : Ty → Substˢ
singleSealEnv B zero = B
singleSealEnv B (suc α) = `α α

infixl 8 _[_]ᵗ
_[_]ᵗ : Ty → Ty → Ty
A [ B ]ᵗ = substᵗ (singleTyEnv B) A

infixl 8 _[_]ˢ
_[_]ˢ : Ty → Ty → Ty
A [ B ]ˢ = substˢ (singleSealEnv B) A

------------------------------------------------------------------------
-- Lookup in telescopes
------------------------------------------------------------------------

infix 4 _∋ᵗ_
data _∋ᵗ_ : Telescope → TyVar → Set where
  Zᵗ : ∀ {Γ} →
      (tyᵉ ∷ Γ) ∋ᵗ zero

  Sᵗ-ty : ∀ {Γ X} →
      Γ ∋ᵗ X →
      (tyᵉ ∷ Γ) ∋ᵗ suc X

  Sᵗ-seal : ∀ {Γ X A} →
      Γ ∋ᵗ X →
      (sealᵉ A ∷ Γ) ∋ᵗ X

  Sᵗ-term : ∀ {Γ X A} →
      Γ ∋ᵗ X →
      (termᵉ A ∷ Γ) ∋ᵗ X

infix 4 _∋ˢ_
data _∋ˢ_ : Telescope → SealVar → Set where
  Zˢ : ∀ {Γ A} →
      (sealᵉ A ∷ Γ) ∋ˢ zero

  Sˢ-ty : ∀ {Γ α} →
      Γ ∋ˢ α →
      (tyᵉ ∷ Γ) ∋ˢ α

  Sˢ-seal : ∀ {Γ α A} →
      Γ ∋ˢ α →
      (sealᵉ A ∷ Γ) ∋ˢ suc α

  Sˢ-term : ∀ {Γ α A} →
      Γ ∋ˢ α →
      (termᵉ A ∷ Γ) ∋ˢ α

infix 4 _∋α_⦂_
data _∋α_⦂_ : Telescope → SealVar → Ty → Set where
  Zα : ∀ {Γ A} →
      (sealᵉ A ∷ Γ) ∋α zero ⦂ ⇑ˢ A

  Sα-ty : ∀ {Γ α A} →
      Γ ∋α α ⦂ A →
      (tyᵉ ∷ Γ) ∋α α ⦂ ⇑ᵗ A

  Sα-seal : ∀ {Γ α A B} →
      Γ ∋α α ⦂ A →
      (sealᵉ B ∷ Γ) ∋α suc α ⦂ ⇑ˢ A

  Sα-term : ∀ {Γ α A B} →
      Γ ∋α α ⦂ A →
      (termᵉ B ∷ Γ) ∋α α ⦂ A

infix 4 _∋ˣ_⦂_
data _∋ˣ_⦂_ : Telescope → Var → Ty → Set where
  Zˣ : ∀ {Γ A} →
      (termᵉ A ∷ Γ) ∋ˣ zero ⦂ A

  Sˣ-ty : ∀ {Γ x A} →
      Γ ∋ˣ x ⦂ A →
      (tyᵉ ∷ Γ) ∋ˣ x ⦂ ⇑ᵗ A

  Sˣ-seal : ∀ {Γ x A B} →
      Γ ∋ˣ x ⦂ A →
      (sealᵉ B ∷ Γ) ∋ˣ x ⦂ ⇑ˢ A

  Sˣ-term : ∀ {Γ x A B} →
      Γ ∋ˣ x ⦂ A →
      (termᵉ B ∷ Γ) ∋ˣ suc x ⦂ A

------------------------------------------------------------------------
-- Type and telescope well-formedness
------------------------------------------------------------------------

data WfTy : Telescope → Ty → Set where
  wfX : ∀ {Γ X} →
    Γ ∋ᵗ X →
    WfTy Γ (`X X)

  wfα : ∀ {Γ α} →
    Γ ∋ˢ α →
    WfTy Γ (`α α)

  wfBase : ∀ {Γ ι} →
    WfTy Γ (‵ ι)

  wf★ : ∀ {Γ} →
    WfTy Γ ★

  wf⇒ : ∀ {Γ A B} →
    WfTy Γ A →
    WfTy Γ B →
    WfTy Γ (A ⇒ B)

  wf∀ : ∀ {Γ A} →
    WfTy (tyᵉ ∷ Γ) A →
    WfTy Γ (`∀ A)

data WfTelescope : Telescope → Set where
  wf∅ : WfTelescope []

  wfTy : ∀ {Γ} →
    WfTelescope Γ →
    WfTelescope (tyᵉ ∷ Γ)

  wfSeal : ∀ {Γ A} →
    WfTelescope Γ →
    WfTy Γ A →
    WfTelescope (sealᵉ A ∷ Γ)

  wfTerm : ∀ {Γ A} →
    WfTelescope Γ →
    WfTy Γ A →
    WfTelescope (termᵉ A ∷ Γ)

------------------------------------------------------------------------
-- Well-typed renamings and substitutions between telescopes
------------------------------------------------------------------------

record TyRenaming (Γ Γ′ : Telescope) : Set where
  constructor ty-ren
  field
    renᵗ : Renameᵗ
    renᵗ-wf : ∀ {X} → Γ ∋ᵗ X → Γ′ ∋ᵗ renᵗ X

open TyRenaming public

-- A seal renaming must know the accompanying type-variable renaming because a
-- seal's assigned type can mention ordinary type variables.  For example,
-- suppose the source telescope contains one type variable and a seal assigned to
-- that type:
--
--   sealᵉ (`X zero) ∷ tyᵉ ∷ []
--
-- If the target telescope has an extra type variable in front of the old one,
-- the type-variable renaming maps the old `X zero` to `X (suc zero)`.  So the
-- corresponding target seal entry must assign the renamed seal to the renamed
-- type:
--
--   sealᵉ (`X (suc zero)) ∷ tyᵉ ∷ tyᵉ ∷ []
--
-- The `renα-wf` field records exactly this: a source lookup `α := A` is carried
-- to a target lookup `ρˢ α := rename ρᵗ ρˢ A`.  Without applying `ρᵗ` to `A`,
-- the target assignment would still point at the source telescope's type
-- variable index.
record SealRenaming {Γ Γ′ : Telescope} (ρ : TyRenaming Γ Γ′) : Set where
  constructor seal-ren
  field
    renˢ : Renameˢ
    renˢ-wf : ∀ {α} → Γ ∋ˢ α → Γ′ ∋ˢ renˢ α
    renα-wf :
      ∀ {α A} →
      Γ ∋α α ⦂ A →
      Γ′ ∋α renˢ α ⦂ rename (renᵗ ρ) renˢ A

open SealRenaming public

renameʳ :
  ∀ {Γ Γ′} →
  (ρ : TyRenaming Γ Γ′) →
  SealRenaming ρ →
  Ty →
  Ty
renameʳ ρ σ = rename (renᵗ ρ) (renˢ σ)

record TySubstitution (Γ Γ′ : Telescope) : Set where
  constructor ty-sub
  field
    subᵗ : Substᵗ
    subᵗ-wf : ∀ {X} → Γ ∋ᵗ X → WfTy Γ′ (subᵗ X)

open TySubstitution public

record SealSubstitution (Γ Γ′ : Telescope) : Set where
  constructor seal-sub
  field
    subˢ : Substˢ
    subˢ-wf : ∀ {α} → Γ ∋ˢ α → WfTy Γ′ (subˢ α)

open SealSubstitution public

substˢᵘᵇ :
  ∀ {Γ Γ′} →
  TySubstitution Γ Γ′ →
  SealSubstitution Γ Γ′ →
  Ty →
  Ty
substˢᵘᵇ σ τ = subst (subᵗ σ) (subˢ τ)
