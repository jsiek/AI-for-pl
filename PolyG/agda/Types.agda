module Types where

-- File Charter:
--   * Types, ground types and type precision derivations of PolyCν, the
--     cast calculus of Max New's thesis (Ch. 10), restricted to the ∀ν
--     fragment (no pairs, no ∃ν).
--   * Type variables are de Bruijn indices; runtime seals are natural
--     numbers (positions in the store).  A name is either.
--   * Substitution replaces type variables by names only: instantiation
--     substitutes a seal, and every other substitution is a renaming.
--   * Type contexts record abstract and known (X ≅ A) type variables.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no)

------------------------------------------------------------------------
-- Names and types
------------------------------------------------------------------------

Var : Set
Var = ℕ

Seal : Set
Seal = ℕ

data Name : Set where
  tvar  : Var → Name
  tseal : Seal → Name

infixr 7 _⇒_
infix 9 ‵_

data Ty : Set where
  ‵_  : Name → Ty
  𝔹   : Ty
  ★   : Ty
  _⇒_ : Ty → Ty → Ty
  ∀ν  : Ty → Ty

data Ground : Set where
  G‵ : Name → Ground
  G𝔹 : Ground
  G⇒ : Ground
  G∀ : Ground

groundTy : Ground → Ty
groundTy (G‵ α) = ‵ α
groundTy G𝔹 = 𝔹
groundTy G⇒ = ★ ⇒ ★
groundTy G∀ = ∀ν ★

------------------------------------------------------------------------
-- Type precision derivations (thesis Fig. 10.8): p : A ⊑ B, where A is
-- the more precise type
------------------------------------------------------------------------

infixr 7 _⇒⊑_

data Prec : Set where
  ★⊑   : Prec                  -- ? : ? ⊑ ?
  tag  : Ground → Prec → Prec  -- tag_G(p) : A ⊑ ?   when p : A ⊑ G
  ‵⊑   : Name → Prec           -- α : α ⊑ α
  𝔹⊑   : Prec
  _⇒⊑_ : Prec → Prec → Prec
  ∀⊑   : Prec → Prec

------------------------------------------------------------------------
-- Decidable equality of names and grounds
------------------------------------------------------------------------

_≟ₙ_ : (α β : Name) → Dec (α ≡ β)
tvar i ≟ₙ tvar j with i ≟ℕ j
... | yes refl = yes refl
... | no i≢j = no (λ { refl → i≢j refl })
tvar i ≟ₙ tseal s = no (λ ())
tseal s ≟ₙ tvar j = no (λ ())
tseal s ≟ₙ tseal t with s ≟ℕ t
... | yes refl = yes refl
... | no s≢t = no (λ { refl → s≢t refl })

_≟G_ : (G H : Ground) → Dec (G ≡ H)
G‵ α ≟G G‵ β with α ≟ₙ β
... | yes refl = yes refl
... | no α≢β = no (λ { refl → α≢β refl })
G‵ α ≟G G𝔹 = no (λ ())
G‵ α ≟G G⇒ = no (λ ())
G‵ α ≟G G∀ = no (λ ())
G𝔹 ≟G G‵ β = no (λ ())
G𝔹 ≟G G𝔹 = yes refl
G𝔹 ≟G G⇒ = no (λ ())
G𝔹 ≟G G∀ = no (λ ())
G⇒ ≟G G‵ β = no (λ ())
G⇒ ≟G G𝔹 = no (λ ())
G⇒ ≟G G⇒ = yes refl
G⇒ ≟G G∀ = no (λ ())
G∀ ≟G G‵ β = no (λ ())
G∀ ≟G G𝔹 = no (λ ())
G∀ ≟G G⇒ = no (λ ())
G∀ ≟G G∀ = yes refl

------------------------------------------------------------------------
-- Substitution of names for type variables
------------------------------------------------------------------------

NSubst : Set
NSubst = Var → Name

⇑ₙ : Name → Name
⇑ₙ (tvar i) = tvar (suc i)
⇑ₙ (tseal s) = tseal s

extₙ : NSubst → NSubst
extₙ σ zero = tvar zero
extₙ σ (suc i) = ⇑ₙ (σ i)

substₙ : NSubst → Name → Name
substₙ σ (tvar i) = σ i
substₙ σ (tseal s) = tseal s

substᵗ : NSubst → Ty → Ty
substᵗ σ (‵ α) = ‵ substₙ σ α
substᵗ σ 𝔹 = 𝔹
substᵗ σ ★ = ★
substᵗ σ (A ⇒ B) = substᵗ σ A ⇒ substᵗ σ B
substᵗ σ (∀ν A) = ∀ν (substᵗ (extₙ σ) A)

substG : NSubst → Ground → Ground
substG σ (G‵ α) = G‵ (substₙ σ α)
substG σ G𝔹 = G𝔹
substG σ G⇒ = G⇒
substG σ G∀ = G∀

substᵖ : NSubst → Prec → Prec
substᵖ σ ★⊑ = ★⊑
substᵖ σ (tag G p) = tag (substG σ G) (substᵖ σ p)
substᵖ σ (‵⊑ α) = ‵⊑ (substₙ σ α)
substᵖ σ 𝔹⊑ = 𝔹⊑
substᵖ σ (p ⇒⊑ q) = substᵖ σ p ⇒⊑ substᵖ σ q
substᵖ σ (∀⊑ p) = ∀⊑ (substᵖ (extₙ σ) p)

-- shifting (weakening by one type variable)
↑ₙ : NSubst
↑ₙ i = tvar (suc i)

⇑ᵗ : Ty → Ty
⇑ᵗ = substᵗ ↑ₙ

-- instantiating type variable 0 with a name
singleₙ : Name → NSubst
singleₙ α zero = α
singleₙ α (suc i) = tvar i

infix 8 _[_]ᵗ _[_]ᵖ

_[_]ᵗ : Ty → Name → Ty
A [ α ]ᵗ = substᵗ (singleₙ α) A

_[_]ᵖ : Prec → Name → Prec
p [ α ]ᵖ = substᵖ (singleₙ α) p

------------------------------------------------------------------------
-- Well-formedness (n type variables in scope; seals are always
-- well-formed)
------------------------------------------------------------------------

WfName : ℕ → Name → Set
WfName n (tvar i) = i < n
WfName n (tseal s) = ⊤

data WfTy (n : ℕ) : Ty → Set where
  wf‵ : ∀ {α} → WfName n α → WfTy n (‵ α)
  wf𝔹 : WfTy n 𝔹
  wf★ : WfTy n ★
  wf⇒ : ∀ {A B} → WfTy n A → WfTy n B → WfTy n (A ⇒ B)
  wf∀ : ∀ {A} → WfTy (suc n) A → WfTy n (∀ν A)

data WfGround (n : ℕ) : Ground → Set where
  wfG‵ : ∀ {α} → WfName n α → WfGround n (G‵ α)
  wfG𝔹 : WfGround n G𝔹
  wfG⇒ : WfGround n G⇒
  wfG∀ : WfGround n G∀

------------------------------------------------------------------------
-- Precision typing (thesis Fig. 10.8): n ⊢ p ⦂ A ⊑ B
------------------------------------------------------------------------

infix 4 _⊢_⦂_⊑_

data _⊢_⦂_⊑_ (n : ℕ) : Prec → Ty → Ty → Set where
  ⊑★ : n ⊢ ★⊑ ⦂ ★ ⊑ ★

  ⊑tag : ∀ {G p A} →
    WfGround n G →
    n ⊢ p ⦂ A ⊑ groundTy G →
    n ⊢ tag G p ⦂ A ⊑ ★

  ⊑‵ : ∀ {α} →
    WfName n α →
    n ⊢ ‵⊑ α ⦂ ‵ α ⊑ ‵ α

  ⊑𝔹 : n ⊢ 𝔹⊑ ⦂ 𝔹 ⊑ 𝔹

  ⊑⇒ : ∀ {p q A A′ B B′} →
    n ⊢ p ⦂ A ⊑ A′ →
    n ⊢ q ⦂ B ⊑ B′ →
    n ⊢ p ⇒⊑ q ⦂ A ⇒ B ⊑ A′ ⇒ B′

  ⊑∀ : ∀ {p A B} →
    suc n ⊢ p ⦂ A ⊑ B →
    n ⊢ ∀⊑ p ⦂ ∀ν A ⊑ ∀ν B

------------------------------------------------------------------------
-- Reflexive and ground derivations
------------------------------------------------------------------------

-- the reflexive derivation A : A ⊑ A
idᵖ : Ty → Prec
idᵖ (‵ α) = ‵⊑ α
idᵖ 𝔹 = 𝔹⊑
idᵖ ★ = ★⊑
idᵖ (A ⇒ B) = idᵖ A ⇒⊑ idᵖ B
idᵖ (∀ν A) = ∀⊑ (idᵖ A)

-- the derivation A? : A ⊑ ?
dynᵖ : Ty → Prec
dynᵖ (‵ α) = tag (G‵ α) (‵⊑ α)
dynᵖ 𝔹 = tag G𝔹 𝔹⊑
dynᵖ ★ = ★⊑
dynᵖ (A ⇒ B) = tag G⇒ (dynᵖ A ⇒⊑ dynᵖ B)
dynᵖ (∀ν A) = tag G∀ (∀⊑ (dynᵖ A))

------------------------------------------------------------------------
-- Type contexts: abstract and known type variables
------------------------------------------------------------------------

data TyInfo : Set where
  abs   : TyInfo
  known : Ty → TyInfo   -- X ≅ A, with A well-formed in the outer context

TyEnv : Set
TyEnv = List TyInfo

tsize : TyEnv → ℕ
tsize [] = zero
tsize (_ ∷ Δ) = suc (tsize Δ)

infix 4 _∋_≅_

-- Δ ∋ X ≅ A: type variable X is known to be isomorphic to A, where A is
-- read in Δ
data _∋_≅_ : TyEnv → Var → Ty → Set where
  Z≅ : ∀ {Δ A} → (known A ∷ Δ) ∋ zero ≅ ⇑ᵗ A
  S≅ : ∀ {Δ I i A} → Δ ∋ i ≅ A → (I ∷ Δ) ∋ suc i ≅ ⇑ᵗ A

data WfTyEnv : TyEnv → Set where
  wf[] : WfTyEnv []
  wf-abs : ∀ {Δ} → WfTyEnv Δ → WfTyEnv (abs ∷ Δ)
  wf-known : ∀ {Δ A} → WfTy (tsize Δ) A → WfTyEnv Δ → WfTyEnv (known A ∷ Δ)

------------------------------------------------------------------------
-- Stores: the seals created so far, each with its type and the label of
-- the instantiation that created it (labels do not affect evaluation)
------------------------------------------------------------------------

Store : Set
Store = List (Ty × Prec)

infix 4 _∋ˢ_⦂_

data _∋ˢ_⦂_ : Store → Seal → Ty → Set where
  Zˢ : ∀ {Σ A ℓ} → ((A , ℓ) ∷ Σ) ∋ˢ zero ⦂ A
  Sˢ : ∀ {Σ A s e} → Σ ∋ˢ s ⦂ A → (e ∷ Σ) ∋ˢ suc s ⦂ A
