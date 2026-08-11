module Consistency where

-- File Charter:
--   * Defines environment-indexed type consistency.
--   * Gives every universal type the ground representation `∀ X. ★`.
--   * Provides renaming and substitution for consistency evidence.
--   * Closes instantiation-bound consistency evidence at ★.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; +-mono-≤)
open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)
open import Relation.Nullary using (no; yes)

open import Types
open import FunExt using (funext)

private
  variable
    Δ Δ′ : TyCtx

data Var∼ : Set where
  X∼X : Var∼
  X∼★ : Var∼
  ★∼X : Var∼
  ★∼X∼★ : Var∼

flipVar∼ : Var∼ → Var∼
flipVar∼ X∼X = X∼X
flipVar∼ X∼★ = ★∼X
flipVar∼ ★∼X = X∼★
flipVar∼ ★∼X∼★ = ★∼X∼★

flipVar∼-involutive : ∀ v → flipVar∼ (flipVar∼ v) ≡ v
flipVar∼-involutive X∼X = refl
flipVar∼-involutive X∼★ = refl
flipVar∼-involutive ★∼X = refl
flipVar∼-involutive ★∼X∼★ = refl

flipVar∼-to-X∼★ : ∀ {v}
  → flipVar∼ v ≡ X∼★
  → v ≡ ★∼X
flipVar∼-to-X∼★ {X∼X} ()
flipVar∼-to-X∼★ {X∼★} ()
flipVar∼-to-X∼★ {★∼X} refl = refl
flipVar∼-to-X∼★ {★∼X∼★} ()

flipVar∼-to-★∼X : ∀ {v}
  → flipVar∼ v ≡ ★∼X
  → v ≡ X∼★
flipVar∼-to-★∼X {X∼X} ()
flipVar∼-to-★∼X {X∼★} refl = refl
flipVar∼-to-★∼X {★∼X} ()
flipVar∼-to-★∼X {★∼X∼★} ()

flipVar∼-to-★∼X∼★ : ∀ {v}
  → flipVar∼ v ≡ ★∼X∼★
  → v ≡ ★∼X∼★
flipVar∼-to-★∼X∼★ {X∼X} ()
flipVar∼-to-★∼X∼★ {X∼★} ()
flipVar∼-to-★∼X∼★ {★∼X} ()
flipVar∼-to-★∼X∼★ {★∼X∼★} refl = refl

Env∼ : TyCtx → Set
Env∼ Δ = TyVar Δ → Var∼

idᶜ : ∀ {Δ} → Env∼ Δ
idᶜ X = ★∼X∼★

extᵐ : Env∼ Δ → Env∼ (suc Δ)
extᵐ μ zero = X∼X
extᵐ μ (suc X) = μ X

instᵐ : Env∼ Δ → Env∼ (suc Δ)
instᵐ μ zero = X∼★
instᵐ μ (suc X) = μ X

genᵐ : Env∼ Δ → Env∼ (suc Δ)
genᵐ μ zero = ★∼X
genᵐ μ (suc X) = μ X

flipᵐ : Env∼ Δ → Env∼ Δ
flipᵐ μ X = flipVar∼ (μ X)

flipᵐ-involutive : ∀ {Δ} {μ : Env∼ Δ} → flipᵐ (flipᵐ μ) ≡ μ
flipᵐ-involutive = funext λ X → flipVar∼-involutive _

----------------------------------------------------------------------
-- Consistency
----------------------------------------------------------------------

infix 4 _⊢_∼★ _⊢★∼_

data _⊢_∼★ {Δ : TyCtx} (μ : Env∼ Δ) : Ty Δ → Set where
  ⇒∼★ : μ ⊢ (★ ⇒ ★) ∼★
  ι∼★ : ∀ {ι} → μ ⊢ ‵ ι ∼★
  X∼★ᵍ : ∀ {X}
    → μ X ≡ X∼★
      ---------------
    → μ ⊢ ＇ X ∼★
  X∼★ᶜ : ∀ {X}
    → μ X ≡ ★∼X∼★
      ---------------
    → μ ⊢ ＇ X ∼★
  ∀∼★ : μ ⊢ (`∀ ★) ∼★

data _⊢★∼_ {Δ : TyCtx} (μ : Env∼ Δ) : Ty Δ → Set where
  ★∼⇒ : μ ⊢★∼ (★ ⇒ ★)
  ★∼ι : ∀ {ι} → μ ⊢★∼ ‵ ι
  ★∼Xᵍ : ∀ {X}
    → μ X ≡ ★∼X
      ---------------
    → μ ⊢★∼ ＇ X
  ★∼Xᶜ : ∀ {X}
    → μ X ≡ ★∼X∼★
      ---------------
    → μ ⊢★∼ ＇ X
  ★∼∀ : μ ⊢★∼ (`∀ ★)

data VarTo★ : Var∼ → Set where
  to★-dynamic : VarTo★ X∼★
  to★-cross : VarTo★ ★∼X∼★

data ★ToVar : Var∼ → Set where
  from★-dynamic : ★ToVar ★∼X
  from★-cross : ★ToVar ★∼X∼★

var-to★-gate : ∀ {Δ} {μ : Env∼ Δ} {X} {v}
  → μ X ≡ v
  → VarTo★ v
  → μ ⊢ ＇ X ∼★
var-to★-gate eq to★-dynamic = X∼★ᵍ eq
var-to★-gate eq to★-cross = X∼★ᶜ eq

★-to-var-gate : ∀ {Δ} {μ : Env∼ Δ} {X} {v}
  → μ X ≡ v
  → ★ToVar v
  → μ ⊢★∼ ＇ X
★-to-var-gate eq from★-dynamic = ★∼Xᵍ eq
★-to-var-gate eq from★-cross = ★∼Xᶜ eq

instance
  refl-instance : ∀ {A : Set} {x : A} → x ≡ x
  refl-instance = refl

  ∼★-⇒-instance : ∀ {Δ} {μ : Env∼ Δ} → μ ⊢ (★ ⇒ ★) ∼★
  ∼★-⇒-instance = ⇒∼★

  ∼★-ι-instance : ∀ {Δ} {μ : Env∼ Δ} {ι} → μ ⊢ ‵ ι ∼★
  ∼★-ι-instance = ι∼★

  to★-dynamic-instance : VarTo★ X∼★
  to★-dynamic-instance = to★-dynamic

  to★-cross-instance : VarTo★ ★∼X∼★
  to★-cross-instance = to★-cross

  ∼★-X-instance : ∀ {Δ} {μ : Env∼ Δ} {X}
    → ⦃ mode : VarTo★ (μ X) ⦄
    → μ ⊢ ＇ X ∼★
  ∼★-X-instance ⦃ mode ⦄ = var-to★-gate refl mode

  ∼★-∀-instance : ∀ {Δ} {μ : Env∼ Δ} → μ ⊢ (`∀ ★) ∼★
  ∼★-∀-instance = ∀∼★

  ★∼-⇒-instance : ∀ {Δ} {μ : Env∼ Δ} → μ ⊢★∼ (★ ⇒ ★)
  ★∼-⇒-instance = ★∼⇒

  ★∼-ι-instance : ∀ {Δ} {μ : Env∼ Δ} {ι} → μ ⊢★∼ ‵ ι
  ★∼-ι-instance = ★∼ι

  from★-dynamic-instance : ★ToVar ★∼X
  from★-dynamic-instance = from★-dynamic

  from★-cross-instance : ★ToVar ★∼X∼★
  from★-cross-instance = from★-cross

  ★∼-X-instance : ∀ {Δ} {μ : Env∼ Δ} {X}
    → ⦃ mode : ★ToVar (μ X) ⦄
    → μ ⊢★∼ ＇ X
  ★∼-X-instance ⦃ mode ⦄ = ★-to-var-gate refl mode

  ★∼-∀-instance : ∀ {Δ} {μ : Env∼ Δ} → μ ⊢★∼ (`∀ ★)
  ★∼-∀-instance = ★∼∀

infix 4 _⊢_∼_
infixr 7 _↦_
infix 8 _! ？_

data _⊢_∼_ {Δ : TyCtx} (μ : Env∼ Δ) :
    Ty Δ → Ty Δ → Set where

  id : ∀ {A}
    → Atom A
      ---------
    → μ ⊢ A ∼ A

  _↦_ : ∀ {A A′ B B′}
    → flipᵐ μ ⊢ A′ ∼ A
    → μ ⊢ B ∼ B′
      ---------------------------
    → μ ⊢ (A ⇒ B) ∼ (A′ ⇒ B′)

  ∀ᶜ_ : ∀ {A B}
    → extᵐ μ ⊢ A ∼ B
      -----------------------
    → μ ⊢ (`∀ A) ∼ (`∀ B)

  _! : ∀ {A G}
    → ⦃ Gᵍ : Ground G ⦄
    → ⦃ G∼★ : μ ⊢ G ∼★ ⦄
    → μ ⊢ A ∼ G
    → ⦃ Ans : NonStar A ⦄
      -----------
    → μ ⊢ A ∼ ★

  ？_ : ∀ {G B}
    → ⦃ Gᵍ : Ground G ⦄
    → ⦃ ★∼G : μ ⊢★∼ G ⦄
    → μ ⊢ G ∼ B
    → ⦃ Bns : NonStar B ⦄
      -----------
    → μ ⊢ ★ ∼ B

  inst_ : ∀ {A B}
    → ⦃ Anv : NonVar A ⦄
    → ⦃ z∈A : zero ∈ᵗ A ⦄
    → instᵐ μ ⊢ A ∼ ⇑ᵗ B
    → B ≢ ★
      ---------------------------
    → μ ⊢ (`∀ A) ∼ B

  gen_ : ∀ {A B}
    → ⦃ Bnv : NonVar B ⦄
    → ⦃ z∈B : zero ∈ᵗ B ⦄
    → genᵐ μ ⊢ ⇑ᵗ A ∼ B
    → A ≢ ★
      ---------------------------
    → μ ⊢ A ∼ (`∀ B)

  bot-elim :
      --------------------------------
    μ ⊢ (`∀ (＇ zero)) ∼ (`∀ ★)

  bot-intro :
      --------------------------------
    μ ⊢ (`∀ ★) ∼ (`∀ (＇ zero))

infix 4 _∼_

_∼_ : ∀ {Δ} → Ty Δ → Ty Δ → Set
A ∼ B = idᶜ ⊢ A ∼ B

idᵍ : ∀ {Δ} {G : Ty Δ} {μ : Env∼ Δ}
  → Ground G
  → μ ⊢ G ∼ G
idᵍ ★⇒★ = id ★ ↦ id ★
idᵍ (‵ ι) = id (‵ ι)
idᵍ (＇ X) = id (＇ X)
idᵍ ∀★ = ∀ᶜ (id ★)

ground≢★ : ∀ {Δ} {G : Ty Δ}
  → Ground G
  → G ≢ ★
ground≢★ ★⇒★ = λ ()
ground≢★ (‵ ι) = λ ()
ground≢★ (＇ X) = λ ()
ground≢★ ∀★ = λ ()

ground-nonstar : ∀ {Δ} {G : Ty Δ}
  → Ground G
  → NonStar G
ground-nonstar ★⇒★ = nonstar-⇒
ground-nonstar (‵ ι) = nonstar-ι
ground-nonstar (＇ X) = nonstar-X
ground-nonstar ∀★ = nonstar-∀

renameNonStar : ∀ {Δ Δ′} {A : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → NonStar A
  → NonStar (renameᵗ ρ A)
renameNonStar ρ nonstar-X = nonstar-X
renameNonStar ρ nonstar-ι = nonstar-ι
renameNonStar ρ nonstar-⇒ = nonstar-⇒
renameNonStar ρ nonstar-∀ = nonstar-∀

flip-∼★ : ∀ {Δ} {G : Ty Δ} {μ : Env∼ Δ}
  → μ ⊢ G ∼★
  → flipᵐ μ ⊢★∼ G
flip-∼★ ⇒∼★ = ★∼⇒
flip-∼★ ι∼★ = ★∼ι
flip-∼★ (X∼★ᵍ eq) = ★∼Xᵍ (cong flipVar∼ eq)
flip-∼★ (X∼★ᶜ eq) = ★∼Xᶜ (cong flipVar∼ eq)
flip-∼★ ∀∼★ = ★∼∀

flip-★∼ : ∀ {Δ} {G : Ty Δ} {μ : Env∼ Δ}
  → μ ⊢★∼ G
  → flipᵐ μ ⊢ G ∼★
flip-★∼ ★∼⇒ = ⇒∼★
flip-★∼ ★∼ι = ι∼★
flip-★∼ (★∼Xᵍ eq) = X∼★ᵍ (cong flipVar∼ eq)
flip-★∼ (★∼Xᶜ eq) = X∼★ᶜ (cong flipVar∼ eq)
flip-★∼ ★∼∀ = ∀∼★

private
  flip-extᵐ : ∀ {Δ} {μ : Env∼ Δ}
    → flipᵐ (extᵐ μ) ≡ extᵐ (flipᵐ μ)
  flip-extᵐ = funext λ { zero → refl; (suc X) → refl }

  flip-instᵐ : ∀ {Δ} {μ : Env∼ Δ}
    → flipᵐ (instᵐ μ) ≡ genᵐ (flipᵐ μ)
  flip-instᵐ = funext λ { zero → refl; (suc X) → refl }

  flip-genᵐ : ∀ {Δ} {μ : Env∼ Δ}
    → flipᵐ (genᵐ μ) ≡ instᵐ (flipᵐ μ)
  flip-genᵐ = funext λ { zero → refl; (suc X) → refl }

  flip-idᵐ : ∀ {Δ} → flipᵐ (idᶜ {Δ}) ≡ idᶜ
  flip-idᵐ = refl

  transport-env∼ : ∀ {Δ} {μ ν : Env∼ Δ} {A B : Ty Δ}
    → μ ≡ ν
    → μ ⊢ A ∼ B
    → ν ⊢ A ∼ B
  transport-env∼ refl c = c

sym∼ : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
  → μ ⊢ A ∼ B
  → flipᵐ μ ⊢ B ∼ A
sym∼ (id a) = id a
sym∼ (c ↦ d) = sym∼ c ↦ sym∼ d
sym∼ (∀ᶜ c) = ∀ᶜ (transport-env∼ flip-extᵐ (sym∼ c))
sym∼ (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄) =
  ？_ ⦃ Gᵍ ⦄ ⦃ flip-∼★ G∼★ ⦄ (sym∼ c) ⦃ Ans ⦄
sym∼ (？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) =
  _! ⦃ Gᵍ ⦄ ⦃ flip-★∼ ★∼G ⦄ (sym∼ c) ⦃ Bns ⦄
sym∼ (inst_ ⦃ A-nonvar ⦄ ⦃ zero∈A ⦄ c B≢★) =
  gen_ ⦃ A-nonvar ⦄ ⦃ zero∈A ⦄
    (transport-env∼ flip-instᵐ (sym∼ c)) B≢★
sym∼ (gen_ ⦃ B-nonvar ⦄ ⦃ zero∈B ⦄ c A≢★) =
  inst_ ⦃ B-nonvar ⦄ ⦃ zero∈B ⦄
    (transport-env∼ flip-genᵐ (sym∼ c)) A≢★
sym∼ bot-elim = bot-intro
sym∼ bot-intro = bot-elim

symᶜ : ∀ {Δ} {A B : Ty Δ} → A ∼ B → B ∼ A
symᶜ c = transport-env∼ flip-idᵐ (sym∼ c)

private

  rename-∈ᵗ : ∀ {Δ Δ′} {X : TyVar Δ} {A : Ty Δ}
    → (ρ : Δ ⇒ʳ Δ′)
    → X ∈ᵗ A
    → ρ X ∈ᵗ renameᵗ ρ A
  rename-∈ᵗ ρ var-∈ = var-∈
  rename-∈ᵗ ρ (∈-fun-left X∈A) = ∈-fun-left (rename-∈ᵗ ρ X∈A)
  rename-∈ᵗ {X = X} {A = A ⇒ B} ρ (∈-fun-right X∉A X∈B)
      with occurs? (ρ X) (renameᵗ ρ A)
  rename-∈ᵗ {X = X} {A = A ⇒ B} ρ (∈-fun-right X∉A X∈B)
      | present ρX∈A = ∈-fun-left ρX∈A
  rename-∈ᵗ {X = X} {A = A ⇒ B} ρ (∈-fun-right X∉A X∈B)
      | absent ρX∉A =
    ∈-fun-right ρX∉A (rename-∈ᵗ ρ X∈B)
  rename-∈ᵗ ρ (∈-all X∈A) = ∈-all (rename-∈ᵗ (extᵗ ρ) X∈A)

  rename-≢★ : ∀ {Δ Δ′} {A : Ty Δ}
    → (ρ : Δ ⇒ʳ Δ′)
    → A ≢ ★
    → renameᵗ ρ A ≢ ★
  rename-≢★ {A = ＇ X} ρ A≢★ ()
  rename-≢★ {A = ‵ ι} ρ A≢★ ()
  rename-≢★ {A = ★} ρ A≢★ refl = A≢★ refl
  rename-≢★ {A = A ⇒ B} ρ A≢★ ()
  rename-≢★ {A = `∀ A} ρ A≢★ ()

  extᵐ-rename : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
    → (ρ : Δ ⇒ʳ Δ′)
    → (∀ X → μ′ (ρ X) ≡ μ X)
    → ∀ X → extᵐ μ′ (extᵗ ρ X) ≡ extᵐ μ X
  extᵐ-rename ρ eq zero = refl
  extᵐ-rename ρ eq (suc X) = eq X

  instᵐ-rename : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
    → (ρ : Δ ⇒ʳ Δ′)
    → (∀ X → μ′ (ρ X) ≡ μ X)
    → ∀ X → instᵐ μ′ (extᵗ ρ X) ≡ instᵐ μ X
  instᵐ-rename ρ eq zero = refl
  instᵐ-rename ρ eq (suc X) = eq X

  genᵐ-rename : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
    → (ρ : Δ ⇒ʳ Δ′)
    → (∀ X → μ′ (ρ X) ≡ μ X)
    → ∀ X → genᵐ μ′ (extᵗ ρ X) ≡ genᵐ μ X
  genᵐ-rename ρ eq zero = refl
  genᵐ-rename ρ eq (suc X) = eq X

  subst-left-∼ : ∀ {Δ} {μ : Env∼ Δ} {A A′ B : Ty Δ}
    → A ≡ A′
    → μ ⊢ A ∼ B
    → μ ⊢ A′ ∼ B
  subst-left-∼ refl c = c

  subst-right-∼ : ∀ {Δ} {μ : Env∼ Δ} {A B B′ : Ty Δ}
    → B ≡ B′
    → μ ⊢ A ∼ B
    → μ ⊢ A ∼ B′
  subst-right-∼ refl c = c

  renameGround : ∀ {Δ Δ′} {G : Ty Δ}
    → (ρ : Δ ⇒ʳ Δ′)
    → Ground G
    → Ground (renameᵗ ρ G)
  renameGround ρ ★⇒★ = ★⇒★
  renameGround ρ (‵ ι) = ‵ ι
  renameGround ρ (＇ X) = ＇ (ρ X)
  renameGround ρ ∀★ = ∀★

  rename∼★ : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
      {G : Ty Δ}
    → (ρ : Δ ⇒ʳ Δ′)
    → (∀ X → μ′ (ρ X) ≡ μ X)
    → μ ⊢ G ∼★
    → μ′ ⊢ renameᵗ ρ G ∼★
  rename∼★ ρ eq ⇒∼★ = ⇒∼★
  rename∼★ ρ eq ι∼★ = ι∼★
  rename∼★ ρ eq (X∼★ᵍ {X = X} eq-X) =
    X∼★ᵍ (trans (eq X) eq-X)
  rename∼★ ρ eq (X∼★ᶜ {X = X} eq-X) =
    X∼★ᶜ (trans (eq X) eq-X)
  rename∼★ ρ eq ∀∼★ = ∀∼★

  rename★∼ : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
      {G : Ty Δ}
    → (ρ : Δ ⇒ʳ Δ′)
    → (∀ X → μ′ (ρ X) ≡ μ X)
    → μ ⊢★∼ G
    → μ′ ⊢★∼ renameᵗ ρ G
  rename★∼ ρ eq ★∼⇒ = ★∼⇒
  rename★∼ ρ eq ★∼ι = ★∼ι
  rename★∼ ρ eq (★∼Xᵍ {X = X} eq-X) =
    ★∼Xᵍ (trans (eq X) eq-X)
  rename★∼ ρ eq (★∼Xᶜ {X = X} eq-X) =
    ★∼Xᶜ (trans (eq X) eq-X)
  rename★∼ ρ eq ★∼∀ = ★∼∀

  flip-rename-env : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
    → (ρ : Δ ⇒ʳ Δ′)
    → (∀ X → μ′ (ρ X) ≡ μ X)
    → ∀ X → flipᵐ μ′ (ρ X) ≡ flipᵐ μ X
  flip-rename-env ρ eq X = cong flipVar∼ (eq X)

  rename∼ : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
      {A B : Ty Δ}
    → (ρ : Δ ⇒ʳ Δ′)
    → (∀ X → μ′ (ρ X) ≡ μ X)
    → μ ⊢ A ∼ B
    → μ′ ⊢ renameᵗ ρ A ∼ renameᵗ ρ B
  rename∼ ρ eq (id ★) = id ★
  rename∼ ρ eq (id (‵ ι)) = id (‵ ι)
  rename∼ ρ eq (id (＇ X)) = id (＇ (ρ X))
  rename∼ {μ = μ} {μ′ = μ′} ρ eq (A∼A′ ↦ B∼B′) =
    rename∼ {μ = flipᵐ μ} {μ′ = flipᵐ μ′} ρ
      (flip-rename-env {μ = μ} {μ′ = μ′} ρ eq) A∼A′ ↦
    rename∼ {μ = μ} {μ′ = μ′} ρ eq B∼B′
  rename∼ ρ eq (∀ᶜ A∼B) =
    ∀ᶜ (rename∼ (extᵗ ρ) (extᵐ-rename ρ eq) A∼B)
  rename∼ {μ = μ} {μ′ = μ′} ρ eq
      (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄) =
    _! ⦃ renameGround ρ Gᵍ ⦄ ⦃ rename∼★ ρ eq G∼★ ⦄
      (rename∼ ρ eq c) ⦃ renameNonStar ρ Ans ⦄
  rename∼ {μ = μ} {μ′ = μ′} ρ eq
      (？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) =
    ？_ ⦃ renameGround ρ Gᵍ ⦄ ⦃ rename★∼ ρ eq ★∼G ⦄
      (rename∼ ρ eq c) ⦃ renameNonStar ρ Bns ⦄
  rename∼ ρ eq
      (inst_ {B = B} ⦃ A-nonvar ⦄ ⦃ zero∈A ⦄ A∼B B≢★) =
    inst_ ⦃ renameNonVar (extᵗ ρ) A-nonvar ⦄
      ⦃ rename-∈ᵗ (extᵗ ρ) zero∈A ⦄
      (subst-right-∼ (renameᵗ-shift ρ B)
        (rename∼ (extᵗ ρ) (instᵐ-rename ρ eq) A∼B))
      (rename-≢★ ρ B≢★)
  rename∼ ρ eq
      (gen_ {A = A} ⦃ B-nonvar ⦄ ⦃ zero∈B ⦄ A∼B A≢★) =
    gen_ ⦃ renameNonVar (extᵗ ρ) B-nonvar ⦄
      ⦃ rename-∈ᵗ (extᵗ ρ) zero∈B ⦄
      (subst-left-∼ (renameᵗ-shift ρ A)
        (rename∼ (extᵗ ρ) (genᵐ-rename ρ eq) A∼B))
      (rename-≢★ ρ A≢★)
  rename∼ ρ eq bot-elim = bot-elim
  rename∼ ρ eq bot-intro = bot-intro

renameᶜ : ∀ {Δ Δ′} {A B : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → A ∼ B
  → renameᵗ ρ A ∼ renameᵗ ρ B
renameᶜ ρ c = rename∼ ρ (λ X → refl) c

renameEnvᶜ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
    {A B : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → (∀ X → ν (ρ X) ≡ μ X)
  → μ ⊢ A ∼ B
  → ν ⊢ renameᵗ ρ A ∼ renameᵗ ρ B
renameEnvᶜ = rename∼

------------------------------------------------------------------------
-- Order-preserving renaming of environment-indexed consistency
------------------------------------------------------------------------

infix 4 _↪ᵗ_

data _↪ᵗ_ : TyCtx → TyCtx → Set where
  empty : ∀ {Δ} → zero ↪ᵗ Δ
  keep : ∀ {Δ Δ′} → Δ ↪ᵗ Δ′ → suc Δ ↪ᵗ suc Δ′
  skip : ∀ {Δ Δ′} → Δ ↪ᵗ Δ′ → Δ ↪ᵗ suc Δ′

toRenameᵗ : ∀ {Δ Δ′} → Δ ↪ᵗ Δ′ → Δ ⇒ʳ Δ′
toRenameᵗ empty ()
toRenameᵗ (keep ρ) zero = zero
toRenameᵗ (keep ρ) (suc X) = suc (toRenameᵗ ρ X)
toRenameᵗ (skip ρ) X = suc (toRenameᵗ ρ X)

id↪ᵗ : ∀ {Δ} → Δ ↪ᵗ Δ
id↪ᵗ {zero} = empty
id↪ᵗ {suc Δ} = keep id↪ᵗ

wk↪ᵗ : ∀ {Δ} → Δ ↪ᵗ suc Δ
wk↪ᵗ = skip id↪ᵗ

renameEnv∼ : ∀ {Δ Δ′} → Δ ↪ᵗ Δ′ → Env∼ Δ → Env∼ Δ′
renameEnv∼ empty μ = idᶜ
renameEnv∼ (keep ρ) μ zero = μ zero
renameEnv∼ (keep ρ) μ (suc X) =
  renameEnv∼ ρ (λ Y → μ (suc Y)) X
renameEnv∼ (skip ρ) μ zero = X∼X
renameEnv∼ (skip ρ) μ (suc X) = renameEnv∼ ρ μ X

renameEnv∼-preserves : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′) (μ : Env∼ Δ)
  → ∀ X → renameEnv∼ ρ μ (toRenameᵗ ρ X) ≡ μ X
renameEnv∼-preserves (keep ρ) μ zero = refl
renameEnv∼-preserves (keep ρ) μ (suc X) =
  renameEnv∼-preserves ρ (λ Y → μ (suc Y)) X
renameEnv∼-preserves (skip ρ) μ X = renameEnv∼-preserves ρ μ X

renameGroundᵐ : ∀ {Δ Δ′} {G : Ty Δ}
  → (ρ : Δ ↪ᵗ Δ′)
  → Ground G
  → Ground (renameᵗ (toRenameᵗ ρ) G)
renameGroundᵐ ρ = renameGround (toRenameᵗ ρ)

rename∼★ᵐ : ∀ {Δ Δ′} {μ : Env∼ Δ} {G : Ty Δ}
  → (ρ : Δ ↪ᵗ Δ′)
  → μ ⊢ G ∼★
  → renameEnv∼ ρ μ ⊢ renameᵗ (toRenameᵗ ρ) G ∼★
rename∼★ᵐ {μ = μ} ρ = rename∼★ (toRenameᵗ ρ)
  (renameEnv∼-preserves ρ μ)

rename★∼ᵐ : ∀ {Δ Δ′} {μ : Env∼ Δ} {G : Ty Δ}
  → (ρ : Δ ↪ᵗ Δ′)
  → μ ⊢★∼ G
  → renameEnv∼ ρ μ ⊢★∼ renameᵗ (toRenameᵗ ρ) G
rename★∼ᵐ {μ = μ} ρ = rename★∼ (toRenameᵗ ρ)
  (renameEnv∼-preserves ρ μ)

renameᵐᶜ : ∀ {Δ Δ′} {μ : Env∼ Δ} {A B : Ty Δ}
  → (ρ : Δ ↪ᵗ Δ′)
  → μ ⊢ A ∼ B
  → renameEnv∼ ρ μ ⊢ renameᵗ (toRenameᵗ ρ) A ∼
      renameᵗ (toRenameᵗ ρ) B
renameᵐᶜ {μ = μ} ρ c = rename∼ (toRenameᵗ ρ)
  (renameEnv∼-preserves ρ μ) c

renameᵐᶜ-idᵍ : ∀ {Δ Δ′} {μ : Env∼ Δ} {G : Ty Δ}
  → (ρ : Δ ↪ᵗ Δ′)
  → (Gᵍ : Ground G)
  → renameᵐᶜ {μ = μ} ρ (idᵍ Gᵍ) ≡ idᵍ (renameGroundᵐ ρ Gᵍ)
renameᵐᶜ-idᵍ ρ ★⇒★ = refl
renameᵐᶜ-idᵍ ρ (‵ ι) = refl
renameᵐᶜ-idᵍ ρ (＇ X) = refl
renameᵐᶜ-idᵍ ρ ∀★ = refl

renameᵐᶜ-idᵍ! : ∀ {Δ Δ′} {μ : Env∼ Δ} {G : Ty Δ}
    {G∼★ : μ ⊢ G ∼★} {Gns : NonStar G}
  → (ρ : Δ ↪ᵗ Δ′)
  → (Gᵍ : Ground G)
  → renameᵐᶜ ρ (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ) ⦃ Gns ⦄)
      ≡ _! ⦃ renameGroundᵐ ρ Gᵍ ⦄ ⦃ rename∼★ᵐ ρ G∼★ ⦄
          (idᵍ (renameGroundᵐ ρ Gᵍ))
          ⦃ renameNonStar (toRenameᵗ ρ) Gns ⦄
renameᵐᶜ-idᵍ! {G∼★ = ⇒∼★} ρ ★⇒★ = refl
renameᵐᶜ-idᵍ! {G∼★ = ι∼★} ρ (‵ ι) = refl
renameᵐᶜ-idᵍ! {G∼★ = X∼★ᵍ eq} ρ (＇ X) = refl
renameᵐᶜ-idᵍ! {G∼★ = X∼★ᶜ eq} ρ (＇ X) = refl
renameᵐᶜ-idᵍ! {G∼★ = ∀∼★} ρ ∀★ = refl

↑ᶜ_ : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
  → μ ⊢ A ∼ B
  → renameEnv∼ wk↪ᵗ μ
      ⊢ renameᵗ (toRenameᵗ wk↪ᵗ) A
      ∼ renameᵗ (toRenameᵗ wk↪ᵗ) B
↑ᶜ c = renameᵐᶜ wk↪ᵗ c

refl∼ : ∀ {Δ} {μ : Env∼ Δ} (A : Ty Δ) → μ ⊢ A ∼ A
refl∼ (＇ X) = id (＇ X)
refl∼ (‵ ι) = id (‵ ι)
refl∼ ★ = id ★
refl∼ (A ⇒ B) = refl∼ A ↦ refl∼ B
refl∼ (`∀ A) = ∀ᶜ (refl∼ A)

------------------------------------------------------------------------
-- Mode-restricted consistency with ★
------------------------------------------------------------------------

mutual
  data To★OK {Δ : TyCtx} (μ : Env∼ Δ) : Ty Δ → Set where
    to★-X∼★ : ∀ {X}
      → μ X ≡ X∼★
      → To★OK μ (＇ X)
    to★-★∼X∼★ : ∀ {X}
      → μ X ≡ ★∼X∼★
      → To★OK μ (＇ X)
    to★-ι : ∀ {ι} → To★OK μ (‵ ι)
    to★-★ : To★OK μ ★
    to★-⇒ : ∀ {A B}
      → From★OK (flipᵐ μ) A
      → To★OK μ B
      → To★OK μ (A ⇒ B)
    to★-∀ : ∀ {A}
      → To★OK (extᵐ μ) A
      → To★OK μ (`∀ A)

  data From★OK {Δ : TyCtx} (μ : Env∼ Δ) : Ty Δ → Set where
    from★-★∼X : ∀ {X}
      → μ X ≡ ★∼X
      → From★OK μ (＇ X)
    from★-★∼X∼★ : ∀ {X}
      → μ X ≡ ★∼X∼★
      → From★OK μ (＇ X)
    from★-ι : ∀ {ι} → From★OK μ (‵ ι)
    from★-★ : From★OK μ ★
    from★-⇒ : ∀ {A B}
      → To★OK (flipᵐ μ) A
      → From★OK μ B
      → From★OK μ (A ⇒ B)
    from★-∀ : ∀ {A}
      → From★OK (extᵐ μ) A
      → From★OK μ (`∀ A)

mutual
  total-to-★ : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
    → To★OK μ A
    → μ ⊢ A ∼ ★
  total-to-★ (to★-X∼★ eq) =
    _! ⦃ G∼★ = X∼★ᵍ eq ⦄ (id (＇ _)) ⦃ nonstar-X ⦄
  total-to-★ (to★-★∼X∼★ eq) =
    _! ⦃ G∼★ = X∼★ᶜ eq ⦄ (id (＇ _)) ⦃ nonstar-X ⦄
  total-to-★ to★-ι =
    _! ⦃ Gᵍ = ‵ _ ⦄ (id (‵ _)) ⦃ nonstar-ι ⦄
  total-to-★ to★-★ = id ★
  total-to-★ (to★-⇒ A-ok B-ok) =
    _! ⦃ Gᵍ = ★⇒★ ⦄ (total-from-★ A-ok ↦ total-to-★ B-ok)
      ⦃ nonstar-⇒ ⦄
  total-to-★ (to★-∀ A-ok) =
    _! ⦃ Gᵍ = ∀★ ⦄ (∀ᶜ (total-to-★ A-ok)) ⦃ nonstar-∀ ⦄

  total-from-★ : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
    → From★OK μ A
    → μ ⊢ ★ ∼ A
  total-from-★ (from★-★∼X eq) =
    ？_ ⦃ ★∼G = ★∼Xᵍ eq ⦄ (id (＇ _)) ⦃ nonstar-X ⦄
  total-from-★ (from★-★∼X∼★ eq) =
    ？_ ⦃ ★∼G = ★∼Xᶜ eq ⦄ (id (＇ _)) ⦃ nonstar-X ⦄
  total-from-★ from★-ι =
    ？_ ⦃ Gᵍ = ‵ _ ⦄ (id (‵ _)) ⦃ nonstar-ι ⦄
  total-from-★ from★-★ = id ★
  total-from-★ (from★-⇒ A-ok B-ok) =
    ？_ ⦃ Gᵍ = ★⇒★ ⦄ (total-to-★ A-ok ↦ total-from-★ B-ok)
      ⦃ nonstar-⇒ ⦄
  total-from-★ (from★-∀ A-ok) =
    ？_ ⦃ Gᵍ = ∀★ ⦄
      (∀ᶜ (total-from-★ A-ok)) ⦃ nonstar-∀ ⦄

record SubstEnv∼ {Δ Δ′ : TyCtx}
    (μ : Env∼ Δ) (ν : Env∼ Δ′) (σ : Δ ⇒ˢ Δ′) : Set where
  constructor subst-env∼
  field
    self : ∀ X → ν ⊢ σ X ∼ σ X
    to-★ : ∀ X → μ X ≡ X∼★ → ν ⊢ σ X ∼ ★
    from-★ : ∀ X → μ X ≡ ★∼X → ν ⊢ ★ ∼ σ X
    cross-to-★ : ∀ X → μ X ≡ ★∼X∼★ → ν ⊢ σ X ∼ ★
    cross-from-★ : ∀ X → μ X ≡ ★∼X∼★ → ν ⊢ ★ ∼ σ X

open SubstEnv∼

private

  ext-SubstEnv∼ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′}
    → SubstEnv∼ μ ν σ
    → SubstEnv∼ (extᵐ μ) (extᵐ ν) (extsᵗ σ)
  ext-SubstEnv∼
      (subst-env∼ self to-★ from-★ cross-to-★ cross-from-★) =
    subst-env∼ self′ to-★′ from-★′ cross-to-★′ cross-from-★′
    where
    self′ : ∀ X → extᵐ _ ⊢ extsᵗ _ X ∼ extsᵗ _ X
    self′ zero = id (＇ zero)
    self′ (suc X) = rename∼ suc (λ Y → refl) (self X)

    to-★′ : ∀ X
      → extᵐ _ X ≡ X∼★
      → extᵐ _ ⊢ extsᵗ _ X ∼ ★
    to-★′ zero ()
    to-★′ (suc X) eq = rename∼ suc (λ Y → refl) (to-★ X eq)

    from-★′ : ∀ X
      → extᵐ _ X ≡ ★∼X
      → extᵐ _ ⊢ ★ ∼ extsᵗ _ X
    from-★′ zero ()
    from-★′ (suc X) eq =
      rename∼ suc (λ Y → refl) (from-★ X eq)

    cross-to-★′ : ∀ X
      → extᵐ _ X ≡ ★∼X∼★
      → extᵐ _ ⊢ extsᵗ _ X ∼ ★
    cross-to-★′ zero ()
    cross-to-★′ (suc X) eq =
      rename∼ suc (λ Y → refl) (cross-to-★ X eq)

    cross-from-★′ : ∀ X
      → extᵐ _ X ≡ ★∼X∼★
      → extᵐ _ ⊢ ★ ∼ extsᵗ _ X
    cross-from-★′ zero ()
    cross-from-★′ (suc X) eq =
      rename∼ suc (λ Y → refl) (cross-from-★ X eq)

  inst-SubstEnv∼ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′}
    → SubstEnv∼ μ ν σ
    → SubstEnv∼ (instᵐ μ) (instᵐ ν) (extsᵗ σ)
  inst-SubstEnv∼ {ν = ν}
      (subst-env∼ self to-★ from-★ cross-to-★ cross-from-★) =
    subst-env∼ self′ to-★′ from-★′ cross-to-★′ cross-from-★′
    where
    self′ : ∀ X → instᵐ _ ⊢ extsᵗ _ X ∼ extsᵗ _ X
    self′ zero = id (＇ zero)
    self′ (suc X) = rename∼ suc (λ Y → refl) (self X)

    to-★′ : ∀ X
      → instᵐ _ X ≡ X∼★
      → instᵐ _ ⊢ extsᵗ _ X ∼ ★
    to-★′ zero eq =
      _! ⦃ G∼★ = X∼★ᵍ refl ⦄ (id (＇ zero))
    to-★′ (suc X) eq = rename∼ suc (λ Y → refl) (to-★ X eq)

    from-★′ : ∀ X
      → instᵐ _ X ≡ ★∼X
      → instᵐ _ ⊢ ★ ∼ extsᵗ _ X
    from-★′ zero ()
    from-★′ (suc X) eq =
      rename∼ suc (λ Y → refl) (from-★ X eq)

    cross-to-★′ : ∀ X
      → instᵐ _ X ≡ ★∼X∼★
      → instᵐ _ ⊢ extsᵗ _ X ∼ ★
    cross-to-★′ zero ()
    cross-to-★′ (suc X) eq =
      rename∼ suc (λ Y → refl) (cross-to-★ X eq)

    cross-from-★′ : ∀ X
      → instᵐ _ X ≡ ★∼X∼★
      → instᵐ _ ⊢ ★ ∼ extsᵗ _ X
    cross-from-★′ zero ()
    cross-from-★′ (suc X) eq =
      rename∼ suc (λ Y → refl) (cross-from-★ X eq)

  gen-SubstEnv∼ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′}
    → SubstEnv∼ μ ν σ
    → SubstEnv∼ (genᵐ μ) (genᵐ ν) (extsᵗ σ)
  gen-SubstEnv∼ {ν = ν}
      (subst-env∼ self to-★ from-★ cross-to-★ cross-from-★) =
    subst-env∼ self′ to-★′ from-★′ cross-to-★′ cross-from-★′
    where
    self′ : ∀ X → genᵐ _ ⊢ extsᵗ _ X ∼ extsᵗ _ X
    self′ zero = id (＇ zero)
    self′ (suc X) = rename∼ suc (λ Y → refl) (self X)

    to-★′ : ∀ X
      → genᵐ _ X ≡ X∼★
      → genᵐ _ ⊢ extsᵗ _ X ∼ ★
    to-★′ zero ()
    to-★′ (suc X) eq = rename∼ suc (λ Y → refl) (to-★ X eq)

    from-★′ : ∀ X
      → genᵐ _ X ≡ ★∼X
      → genᵐ _ ⊢ ★ ∼ extsᵗ _ X
    from-★′ zero eq =
      ？_ ⦃ ★∼G = ★∼Xᵍ refl ⦄ (id (＇ zero))
    from-★′ (suc X) eq =
      rename∼ suc (λ Y → refl) (from-★ X eq)

    cross-to-★′ : ∀ X
      → genᵐ _ X ≡ ★∼X∼★
      → genᵐ _ ⊢ extsᵗ _ X ∼ ★
    cross-to-★′ zero ()
    cross-to-★′ (suc X) eq =
      rename∼ suc (λ Y → refl) (cross-to-★ X eq)

    cross-from-★′ : ∀ X
      → genᵐ _ X ≡ ★∼X∼★
      → genᵐ _ ⊢ ★ ∼ extsᵗ _ X
    cross-from-★′ zero ()
    cross-from-★′ (suc X) eq =
      rename∼ suc (λ Y → refl) (cross-from-★ X eq)

  flip-SubstEnv∼ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′}
    → SubstEnv∼ μ ν σ
    → SubstEnv∼ (flipᵐ μ) (flipᵐ ν) σ
  flip-SubstEnv∼ {μ = μ} {ν = ν} {σ = σ}
      (subst-env∼ self to-★ from-★ cross-to-★ cross-from-★) =
    subst-env∼ self′ to-★′ from-★′ cross-to-★′ cross-from-★′
    where
    self′ : ∀ X → flipᵐ ν ⊢ σ X ∼ σ X
    self′ X = sym∼ (self X)

    to-★′ : ∀ X
      → flipᵐ μ X ≡ X∼★
      → flipᵐ ν ⊢ σ X ∼ ★
    to-★′ X eq = sym∼ (from-★ X (flipVar∼-to-X∼★ eq))

    from-★′ : ∀ X
      → flipᵐ μ X ≡ ★∼X
      → flipᵐ ν ⊢ ★ ∼ σ X
    from-★′ X eq = sym∼ (to-★ X (flipVar∼-to-★∼X eq))

    cross-to-★′ : ∀ X
      → flipᵐ μ X ≡ ★∼X∼★
      → flipᵐ ν ⊢ σ X ∼ ★
    cross-to-★′ X eq =
      sym∼ (cross-from-★ X (flipVar∼-to-★∼X∼★ eq))

    cross-from-★′ : ∀ X
      → flipᵐ μ X ≡ ★∼X∼★
      → flipᵐ ν ⊢ ★ ∼ σ X
    cross-from-★′ X eq =
      sym∼ (cross-to-★ X (flipVar∼-to-★∼X∼★ eq))

  subst-∈ᵗ : ∀ {Δ Δ′} {σ : Δ ⇒ˢ Δ′} {X : TyVar Δ}
      {Y : TyVar Δ′} {A : Ty Δ}
    → X ∈ᵗ A
    → Y ∈ᵗ σ X
    → Y ∈ᵗ substᵗ σ A
  subst-∈ᵗ var-∈ Y∈σX = Y∈σX
  subst-∈ᵗ (∈-fun-left X∈A) Y∈σX =
    ∈-fun-left (subst-∈ᵗ X∈A Y∈σX)
  subst-∈ᵗ {σ = σ} {Y = Y} {A = A ⇒ B}
      (∈-fun-right X∉A X∈B) Y∈σX
      with occurs? Y (substᵗ σ A)
  subst-∈ᵗ {σ = σ} {Y = Y} {A = A ⇒ B}
      (∈-fun-right X∉A X∈B) Y∈σX
      | present Y∈A = ∈-fun-left Y∈A
  subst-∈ᵗ {σ = σ} {Y = Y} {A = A ⇒ B}
      (∈-fun-right X∉A X∈B) Y∈σX
      | absent Y∉A =
    ∈-fun-right Y∉A (subst-∈ᵗ X∈B Y∈σX)
  subst-∈ᵗ {σ = σ} (∈-all X∈A) Y∈σX =
    ∈-all (subst-∈ᵗ {σ = extsᵗ σ} X∈A (rename-∈ᵗ suc Y∈σX))

  tag-source-nonvar-⇒ : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
    → μ ⊢ A ∼ (★ ⇒ ★)
    → NonStar A
    → NonVar A
  tag-source-nonvar-⇒ (c ↦ d) Ans = nonvar-fun
  tag-source-nonvar-⇒
      (？_ ⦃ g ⦄ c ⦃ Gns ⦄) Ans =
    ⊥-elim (nonStar≢★ Ans refl)
  tag-source-nonvar-⇒ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) Ans =
    nonvar-all

  tag-source-nonvar-ι : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ} {ι}
    → μ ⊢ A ∼ (‵ ι)
    → NonStar A
    → NonVar A
  tag-source-nonvar-ι (id (‵ ι)) Ans = nonvar-base
  tag-source-nonvar-ι
      (？_ ⦃ g ⦄ c ⦃ Gns ⦄) Ans =
    ⊥-elim (nonStar≢★ Ans refl)
  tag-source-nonvar-ι (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) Ans =
    nonvar-all

  tag-source-nonvar-∀ : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
    → μ ⊢ A ∼ (`∀ ★)
    → NonStar A
    → NonVar A
  tag-source-nonvar-∀ (∀ᶜ c) Ans = nonvar-all
  tag-source-nonvar-∀ (？_ ⦃ g ⦄ c ⦃ Gns ⦄) Ans =
    ⊥-elim (nonStar≢★ Ans refl)
  tag-source-nonvar-∀ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) Ans =
    nonvar-all
  tag-source-nonvar-∀ bot-elim Ans = nonvar-all

  untag-target-nonvar-⇒ : ∀ {Δ} {μ : Env∼ Δ} {B : Ty Δ}
    → μ ⊢ (★ ⇒ ★) ∼ B
    → NonStar B
    → NonVar B
  untag-target-nonvar-⇒ (c ↦ d) Bns = nonvar-fun
  untag-target-nonvar-⇒
      (_! ⦃ g ⦄ c ⦃ Gns ⦄) Bns =
    ⊥-elim (nonStar≢★ Bns refl)
  untag-target-nonvar-⇒ (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) Bns =
    nonvar-all

  untag-target-nonvar-ι : ∀ {Δ} {μ : Env∼ Δ} {B : Ty Δ} {ι}
    → μ ⊢ (‵ ι) ∼ B
    → NonStar B
    → NonVar B
  untag-target-nonvar-ι (id (‵ ι)) Bns = nonvar-base
  untag-target-nonvar-ι
      (_! ⦃ g ⦄ c ⦃ Gns ⦄) Bns =
    ⊥-elim (nonStar≢★ Bns refl)
  untag-target-nonvar-ι (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) Bns =
    nonvar-all

  untag-target-nonvar-∀ : ∀ {Δ} {μ : Env∼ Δ} {B : Ty Δ}
    → μ ⊢ (`∀ ★) ∼ B
    → NonStar B
    → NonVar B
  untag-target-nonvar-∀ (∀ᶜ c) Bns = nonvar-all
  untag-target-nonvar-∀ (_! ⦃ g ⦄ c ⦃ Gns ⦄) Bns =
    ⊥-elim (nonStar≢★ Bns refl)
  untag-target-nonvar-∀ (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) Bns =
    nonvar-all
  untag-target-nonvar-∀ bot-intro Bns = nonvar-all

  nonvar-occurs-nonstar : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
    → NonVar A
    → X ∈ᵗ A
    → NonStar A
  nonvar-occurs-nonstar nonvar-base ()
  nonvar-occurs-nonstar nonvar-star ()
  nonvar-occurs-nonstar nonvar-fun X∈A = nonstar-⇒
  nonvar-occurs-nonstar nonvar-all X∈A = nonstar-∀

  nonstar-nonvar-to-var-impossible : ∀ {Δ} {μ : Env∼ Δ}
      {A : Ty Δ} {X}
    → μ ⊢ A ∼ ＇ X
    → NonVar A
    → NonStar A
    → ⊥
  nonstar-nonvar-to-var-impossible (id (＇ X)) () Ans
  nonstar-nonvar-to-var-impossible (？_ c ⦃ Bns ⦄) nonvar-star ()
  nonstar-nonvar-to-var-impossible
      (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) nonvar-all Ans =
    nonstar-nonvar-to-var-impossible c Anv
      (nonvar-occurs-nonstar Anv z∈A)

  var-to-nonstar-nonvar-impossible : ∀ {Δ} {μ : Env∼ Δ}
      {B : Ty Δ} {X}
    → μ ⊢ ＇ X ∼ B
    → NonVar B
    → NonStar B
    → ⊥
  var-to-nonstar-nonvar-impossible (id (＇ X)) () Bns
  var-to-nonstar-nonvar-impossible (_! c ⦃ Ans ⦄) nonvar-star ()
  var-to-nonstar-nonvar-impossible
      (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) nonvar-all Bns =
    var-to-nonstar-nonvar-impossible c Bnv
      (nonvar-occurs-nonstar Bnv z∈B)

  subst-to-star-var : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′} {A : Ty Δ} {X}
    → SubstEnv∼ μ ν σ
    → μ ⊢ A ∼ ＇ X
    → μ X ≡ X∼★
    → NonStar A
    → ν ⊢ substᵗ σ A ∼ ★
  subst-to-star-var s (id (＇ X)) eq Ans = to-★ s X eq
  subst-to-star-var s (？_ c ⦃ Bns ⦄) eq ()
  subst-to-star-var s c@(inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ d B≢★) eq Ans =
    ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all Ans)

  subst-cross-to-star-var : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′} {A : Ty Δ} {X}
    → SubstEnv∼ μ ν σ
    → μ ⊢ A ∼ ＇ X
    → μ X ≡ ★∼X∼★
    → NonStar A
    → ν ⊢ substᵗ σ A ∼ ★
  subst-cross-to-star-var s (id (＇ X)) eq Ans = cross-to-★ s X eq
  subst-cross-to-star-var s (？_ c ⦃ Bns ⦄) eq ()
  subst-cross-to-star-var
      s c@(inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ d B≢★) eq Ans =
    ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all Ans)

  subst-from-star-var : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′} {B : Ty Δ} {X}
    → SubstEnv∼ μ ν σ
    → μ ⊢ ＇ X ∼ B
    → μ X ≡ ★∼X
    → NonStar B
    → ν ⊢ ★ ∼ substᵗ σ B
  subst-from-star-var s (id (＇ X)) eq Bns = from-★ s X eq
  subst-from-star-var s (_! c ⦃ Ans ⦄) eq ()
  subst-from-star-var s c@(gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ d A≢★) eq Bns =
    ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all Bns)

  subst-cross-from-star-var : ∀ {Δ Δ′} {μ : Env∼ Δ}
      {ν : Env∼ Δ′} {σ : Δ ⇒ˢ Δ′} {B : Ty Δ} {X}
    → SubstEnv∼ μ ν σ
    → μ ⊢ ＇ X ∼ B
    → μ X ≡ ★∼X∼★
    → NonStar B
    → ν ⊢ ★ ∼ substᵗ σ B
  subst-cross-from-star-var s (id (＇ X)) eq Bns =
    cross-from-★ s X eq
  subst-cross-from-star-var s (_! c ⦃ Ans ⦄) eq ()
  subst-cross-from-star-var
      s c@(gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ d A≢★) eq Bns =
    ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all Bns)

  subst-nonvar-nonstar : ∀ {Δ Δ′} {A : Ty Δ}
    → (σ : Δ ⇒ˢ Δ′)
    → NonVar A
    → NonStar A
    → NonStar (substᵗ σ A)
  subst-nonvar-nonstar σ nonvar-base Ans = nonstar-ι
  subst-nonvar-nonstar σ nonvar-star ()
  subst-nonvar-nonstar σ nonvar-fun Ans = nonstar-⇒
  subst-nonvar-nonstar σ nonvar-all Ans = nonstar-∀

  inst-to-var-occurs-impossible : ∀ {Δ} {μ : Env∼ Δ}
      {A : Ty (suc Δ)} {X}
    → instᵐ μ ⊢ A ∼ ＇ X
    → instᵐ μ X ≡ X∼★
    → NonVar A
    → X ∈ᵗ A
    → ⊥
  inst-to-var-occurs-impossible (id (＇ X)) eq () X∈A
  inst-to-var-occurs-impossible
      (？_ ⦃ g ⦄ c ⦃ Bns ⦄) eq nonvar-star ()
  inst-to-var-occurs-impossible
      (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) eq nonvar-all (∈-all X∈A) =
    inst-to-var-occurs-impossible c eq Anv X∈A

  gen-from-var-occurs-impossible : ∀ {Δ} {μ : Env∼ Δ}
      {B : Ty (suc Δ)} {X}
    → genᵐ μ ⊢ ＇ X ∼ B
    → genᵐ μ X ≡ ★∼X
    → NonVar B
    → X ∈ᵗ B
    → ⊥
  gen-from-var-occurs-impossible (id (＇ X)) eq () X∈B
  gen-from-var-occurs-impossible (_! ⦃ g ⦄ c ⦃ Ans ⦄) eq nonvar-star ()
  gen-from-var-occurs-impossible
      (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) eq nonvar-all (∈-all X∈B) =
    gen-from-var-occurs-impossible c eq Bnv X∈B

  factor-inst-star : ∀ {Δ} {μ : Env∼ Δ} {A : Ty (suc Δ)}
    → (c : instᵐ μ ⊢ A ∼ ★)
    → NonVar A
    → zero ∈ᵗ A
    → μ ⊢ (`∀ A) ∼ ★
  factor-inst-star (id ★) Anv ()
  factor-inst-star (_! ⦃ Gᵍ = ★⇒★ ⦄ c ⦃ Ans ⦄) Anv z∈A =
    _! ⦃ Gᵍ = ★⇒★ ⦄ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c (λ ()))
      ⦃ nonstar-∀ ⦄
  factor-inst-star (_! ⦃ Gᵍ = ‵ ι ⦄ c ⦃ Ans ⦄) Anv z∈A =
    _! ⦃ Gᵍ = ‵ ι ⦄ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c (λ ()))
      ⦃ nonstar-∀ ⦄
  factor-inst-star
      (_! ⦃ Gᵍ = ＇ zero ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ c ⦃ Ans ⦄)
      Anv z∈A =
    ⊥-elim (inst-to-var-occurs-impossible c eq Anv z∈A)
  factor-inst-star
      (_! ⦃ Gᵍ = ＇ zero ⦄ ⦃ G∼★ = X∼★ᶜ () ⦄ c ⦃ Ans ⦄)
      Anv z∈A
  factor-inst-star
      (_! ⦃ Gᵍ = ＇ suc X ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ c ⦃ Ans ⦄)
      Anv z∈A =
    _! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄
      (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c (λ ())) ⦃ nonstar-∀ ⦄
  factor-inst-star
      (_! ⦃ Gᵍ = ＇ suc X ⦄
          ⦃ G∼★ = X∼★ᶜ eq ⦄ c ⦃ Ans ⦄)
      Anv z∈A =
    _! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ eq ⦄
      (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c (λ ())) ⦃ nonstar-∀ ⦄
  factor-inst-star (_! ⦃ Gᵍ = ∀★ ⦄ c ⦃ Ans ⦄) Anv z∈A =
    _! ⦃ Gᵍ = ∀★ ⦄ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c (λ ()))
      ⦃ nonstar-∀ ⦄
  factor-inst-star (？_ ⦃ g ⦄ c ⦃ Bns ⦄) Anv ()
  factor-inst-star
      (inst_ ⦃ Anv′ ⦄ ⦃ z∈A′ ⦄ c ★≢★) Anv z∈A =
    ⊥-elim (★≢★ refl)

  factor-gen-star : ∀ {Δ} {μ : Env∼ Δ} {B : Ty (suc Δ)}
    → (c : genᵐ μ ⊢ ★ ∼ B)
    → NonVar B
    → zero ∈ᵗ B
    → μ ⊢ ★ ∼ (`∀ B)
  factor-gen-star (id ★) Bnv ()
  factor-gen-star (_! ⦃ g ⦄ c ⦃ () ⦄) Bnv z∈B
  factor-gen-star (？_ ⦃ Gᵍ = ★⇒★ ⦄ c ⦃ Bns ⦄) Bnv z∈B =
    ？_ ⦃ Gᵍ = ★⇒★ ⦄ (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c (λ ()))
      ⦃ nonstar-∀ ⦄
  factor-gen-star (？_ ⦃ Gᵍ = ‵ ι ⦄ c ⦃ Bns ⦄) Bnv z∈B =
    ？_ ⦃ Gᵍ = ‵ ι ⦄ (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c (λ ()))
      ⦃ nonstar-∀ ⦄
  factor-gen-star
      (？_ ⦃ Gᵍ = ＇ zero ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄ c ⦃ Bns ⦄)
      Bnv z∈B =
    ⊥-elim (gen-from-var-occurs-impossible c eq Bnv z∈B)
  factor-gen-star
      (？_ ⦃ Gᵍ = ＇ zero ⦄
          ⦃ ★∼G = ★∼Xᶜ () ⦄ c ⦃ Bns ⦄)
      Bnv z∈B
  factor-gen-star
      (？_ ⦃ Gᵍ = ＇ suc X ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄ c ⦃ Bns ⦄)
      Bnv z∈B =
    ？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄
      (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c (λ ())) ⦃ nonstar-∀ ⦄
  factor-gen-star
      (？_ ⦃ Gᵍ = ＇ suc X ⦄
          ⦃ ★∼G = ★∼Xᶜ eq ⦄ c ⦃ Bns ⦄)
      Bnv z∈B =
    ？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ eq ⦄
      (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c (λ ())) ⦃ nonstar-∀ ⦄
  factor-gen-star (？_ ⦃ Gᵍ = ∀★ ⦄ c ⦃ Bns ⦄) Bnv z∈B =
    ？_ ⦃ Gᵍ = ∀★ ⦄ (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c (λ ()))
      ⦃ nonstar-∀ ⦄
  factor-gen-star (gen_ ⦃ Bnv′ ⦄ ⦃ z∈B′ ⦄ c ★≢★) Bnv z∈B =
    ⊥-elim (★≢★ refl)

subst∼ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
    {σ : Δ ⇒ˢ Δ′} {A B : Ty Δ}
  → SubstEnv∼ μ ν σ
  → μ ⊢ A ∼ B
  → ν ⊢ substᵗ σ A ∼ substᵗ σ B
subst∼ s (id ★) = id ★
subst∼ s (id (‵ ι)) = id (‵ ι)
subst∼ s (id (＇ X)) = self s X
subst∼ s (c ↦ d) = subst∼ (flip-SubstEnv∼ s) c ↦ subst∼ s d
subst∼ s (∀ᶜ c) = ∀ᶜ (subst∼ (ext-SubstEnv∼ s) c)
subst∼ {σ = σ} s (_! ⦃ Gᵍ = ★⇒★ ⦄ c ⦃ Ans ⦄) =
  _! ⦃ Gᵍ = ★⇒★ ⦄ (subst∼ s c)
    ⦃ subst-nonvar-nonstar σ (tag-source-nonvar-⇒ c Ans) Ans ⦄
subst∼ {σ = σ} s (_! ⦃ Gᵍ = ‵ ι ⦄ c ⦃ Ans ⦄) =
  _! ⦃ Gᵍ = ‵ ι ⦄ (subst∼ s c)
    ⦃ subst-nonvar-nonstar σ (tag-source-nonvar-ι c Ans) Ans ⦄
subst∼ s (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ c ⦃ Ans ⦄) =
  subst-to-star-var s c eq Ans
subst∼ s
    (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ eq ⦄ c ⦃ Ans ⦄) =
  subst-cross-to-star-var s c eq Ans
subst∼ {σ = σ} s (_! ⦃ Gᵍ = ∀★ ⦄ c ⦃ Ans ⦄) =
  _! ⦃ Gᵍ = ∀★ ⦄ (subst∼ s c)
    ⦃ subst-nonvar-nonstar σ (tag-source-nonvar-∀ c Ans) Ans ⦄
subst∼ {σ = σ} s (？_ ⦃ Gᵍ = ★⇒★ ⦄ c ⦃ Bns ⦄) =
  ？_ ⦃ Gᵍ = ★⇒★ ⦄ (subst∼ s c)
    ⦃ subst-nonvar-nonstar σ (untag-target-nonvar-⇒ c Bns) Bns ⦄
subst∼ {σ = σ} s (？_ ⦃ Gᵍ = ‵ ι ⦄ c ⦃ Bns ⦄) =
  ？_ ⦃ Gᵍ = ‵ ι ⦄ (subst∼ s c)
    ⦃ subst-nonvar-nonstar σ (untag-target-nonvar-ι c Bns) Bns ⦄
subst∼ s (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄ c ⦃ Bns ⦄) =
  subst-from-star-var s c eq Bns
subst∼ s
    (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ eq ⦄ c ⦃ Bns ⦄) =
  subst-cross-from-star-var s c eq Bns
subst∼ {σ = σ} s (？_ ⦃ Gᵍ = ∀★ ⦄ c ⦃ Bns ⦄) =
  ？_ ⦃ Gᵍ = ∀★ ⦄ (subst∼ s c)
    ⦃ subst-nonvar-nonstar σ (untag-target-nonvar-∀ c Bns) Bns ⦄
subst∼ {σ = σ} s
    (inst_ {B = B} ⦃ A-nonvar ⦄ ⦃ zero∈A ⦄ c B≢★)
    with substᵗ σ B ≟Ty ★
subst∼ {σ = σ} s
    (inst_ {B = B} ⦃ A-nonvar ⦄ ⦃ zero∈A ⦄ c B≢★)
    | no Bσ≢★ =
  inst_ ⦃ substNonVar (extsᵗ σ) A-nonvar ⦄
    ⦃ subst-∈ᵗ zero∈A var-∈ ⦄
    (subst-right-∼ (substᵗ-shift σ B)
      (subst∼ (inst-SubstEnv∼ s) c)) Bσ≢★
subst∼ {σ = σ} s
    (inst_ {B = B} ⦃ A-nonvar ⦄ ⦃ zero∈A ⦄ c B≢★)
    | yes Bσ≡★ =
    subst-right-∼ (sym Bσ≡★)
      (factor-inst-star
        (subst-right-∼
          (trans (substᵗ-shift σ B) (cong (renameᵗ suc) Bσ≡★))
          (subst∼ (inst-SubstEnv∼ s) c))
        (substNonVar (extsᵗ σ) A-nonvar)
        (subst-∈ᵗ zero∈A var-∈))
subst∼ {σ = σ} s
    (gen_ {A = A} ⦃ B-nonvar ⦄ ⦃ zero∈B ⦄ c A≢★)
    with substᵗ σ A ≟Ty ★
subst∼ {σ = σ} s
    (gen_ {A = A} ⦃ B-nonvar ⦄ ⦃ zero∈B ⦄ c A≢★)
    | no Aσ≢★ =
  gen_ ⦃ substNonVar (extsᵗ σ) B-nonvar ⦄
    ⦃ subst-∈ᵗ zero∈B var-∈ ⦄
    (subst-left-∼ (substᵗ-shift σ A)
      (subst∼ (gen-SubstEnv∼ s) c)) Aσ≢★
subst∼ {σ = σ} s
    (gen_ {A = A} ⦃ B-nonvar ⦄ ⦃ zero∈B ⦄ c A≢★)
    | yes Aσ≡★ =
    subst-left-∼ (sym Aσ≡★)
      (factor-gen-star
        (subst-left-∼
          (trans (substᵗ-shift σ A) (cong (renameᵗ suc) Aσ≡★))
          (subst∼ (gen-SubstEnv∼ s) c))
        (substNonVar (extsᵗ σ) B-nonvar)
        (subst-∈ᵗ zero∈B var-∈))
subst∼ s bot-elim = bot-elim
subst∼ s bot-intro = bot-intro

factor-inst-starᶜ : ∀ {Δ} {μ : Env∼ Δ} {A : Ty (suc Δ)}
  → instᵐ μ ⊢ A ∼ ★
  → NonVar A
  → zero ∈ᵗ A
  → μ ⊢ (`∀ A) ∼ ★
factor-inst-starᶜ = factor-inst-star

factor-gen-starᶜ : ∀ {Δ} {μ : Env∼ Δ} {B : Ty (suc Δ)}
  → genᵐ μ ⊢ ★ ∼ B
  → NonVar B
  → zero ∈ᵗ B
  → μ ⊢ ★ ∼ (`∀ B)
factor-gen-starᶜ = factor-gen-star

private

  close-inst-self : ∀ {Δ} {μ : Env∼ Δ} (X : TyVar (suc Δ))
    → μ ⊢ singleSubᵗ ★ X ∼ singleSubᵗ ★ X
  close-inst-self X = refl∼ (singleSubᵗ ★ X)

  close-inst-to-★ : ∀ {Δ} {μ : Env∼ Δ} (X : TyVar (suc Δ))
    → instᵐ μ X ≡ X∼★
    → μ ⊢ singleSubᵗ ★ X ∼ ★
  close-inst-to-★ zero eq = id ★
  close-inst-to-★ {μ = μ} (suc X) eq =
    _! ⦃ G∼★ = X∼★ᵍ eq ⦄ (id (＇ X))
      ⦃ nonstar-X ⦄

  close-inst-from-★ : ∀ {Δ} {μ : Env∼ Δ} (X : TyVar (suc Δ))
    → instᵐ μ X ≡ ★∼X
    → μ ⊢ ★ ∼ singleSubᵗ ★ X
  close-inst-from-★ zero ()
  close-inst-from-★ {μ = μ} (suc X) eq =
    ？_ ⦃ ★∼G = ★∼Xᵍ eq ⦄ (id (＇ X))
      ⦃ nonstar-X ⦄

  close-inst-cross-to-★ : ∀ {Δ} {μ : Env∼ Δ}
      (X : TyVar (suc Δ))
    → instᵐ μ X ≡ ★∼X∼★
    → μ ⊢ singleSubᵗ ★ X ∼ ★
  close-inst-cross-to-★ zero ()
  close-inst-cross-to-★ {μ = μ} (suc X) eq =
    _! ⦃ G∼★ = X∼★ᶜ eq ⦄ (id (＇ X)) ⦃ nonstar-X ⦄

  close-inst-cross-from-★ : ∀ {Δ} {μ : Env∼ Δ}
      (X : TyVar (suc Δ))
    → instᵐ μ X ≡ ★∼X∼★
    → μ ⊢ ★ ∼ singleSubᵗ ★ X
  close-inst-cross-from-★ zero ()
  close-inst-cross-from-★ {μ = μ} (suc X) eq =
    ？_ ⦃ ★∼G = ★∼Xᶜ eq ⦄ (id (＇ X)) ⦃ nonstar-X ⦄

close-instᶜ : ∀ {Δ} {μ : Env∼ Δ} {A : Ty (suc Δ)} {B : Ty Δ}
  → instᵐ μ ⊢ A ∼ ⇑ᵗ B
  → μ ⊢ A [ ★ ]ᵗ ∼ B
syntax close-instᶜ c = c [ ★/0 ]ᶜ

close-instᶜ {B = B} c =
  subst-right-∼ (shift-openᵗ B ★)
    (subst∼
      (subst-env∼ close-inst-self close-inst-to-★ close-inst-from-★
        close-inst-cross-to-★ close-inst-cross-from-★)
      c)

private

  close-gen-self : ∀ {Δ} {μ : Env∼ Δ} (X : TyVar (suc Δ))
    → μ ⊢ singleSubᵗ ★ X ∼ singleSubᵗ ★ X
  close-gen-self X = refl∼ (singleSubᵗ ★ X)

  close-gen-to-★ : ∀ {Δ} {μ : Env∼ Δ} (X : TyVar (suc Δ))
    → genᵐ μ X ≡ X∼★
    → μ ⊢ singleSubᵗ ★ X ∼ ★
  close-gen-to-★ zero ()
  close-gen-to-★ {μ = μ} (suc X) eq =
    _! ⦃ G∼★ = X∼★ᵍ eq ⦄ (id (＇ X))
      ⦃ nonstar-X ⦄

  close-gen-from-★ : ∀ {Δ} {μ : Env∼ Δ} (X : TyVar (suc Δ))
    → genᵐ μ X ≡ ★∼X
    → μ ⊢ ★ ∼ singleSubᵗ ★ X
  close-gen-from-★ zero eq = id ★
  close-gen-from-★ {μ = μ} (suc X) eq =
    ？_ ⦃ ★∼G = ★∼Xᵍ eq ⦄ (id (＇ X))
      ⦃ nonstar-X ⦄

  close-gen-cross-to-★ : ∀ {Δ} {μ : Env∼ Δ}
      (X : TyVar (suc Δ))
    → genᵐ μ X ≡ ★∼X∼★
    → μ ⊢ singleSubᵗ ★ X ∼ ★
  close-gen-cross-to-★ zero ()
  close-gen-cross-to-★ {μ = μ} (suc X) eq =
    _! ⦃ G∼★ = X∼★ᶜ eq ⦄ (id (＇ X)) ⦃ nonstar-X ⦄

  close-gen-cross-from-★ : ∀ {Δ} {μ : Env∼ Δ}
      (X : TyVar (suc Δ))
    → genᵐ μ X ≡ ★∼X∼★
    → μ ⊢ ★ ∼ singleSubᵗ ★ X
  close-gen-cross-from-★ zero ()
  close-gen-cross-from-★ {μ = μ} (suc X) eq =
    ？_ ⦃ ★∼G = ★∼Xᶜ eq ⦄ (id (＇ X)) ⦃ nonstar-X ⦄

close-genᶜ : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ} {B : Ty (suc Δ)}
  → genᵐ μ ⊢ ⇑ᵗ A ∼ B
  → μ ⊢ A ∼ B [ ★ ]ᵗ
close-genᶜ {A = A} c =
  subst-left-∼ (shift-openᵗ A ★)
    (subst∼
      (subst-env∼ close-gen-self close-gen-to-★ close-gen-from-★
        close-gen-cross-to-★ close-gen-cross-from-★)
      c)

private

  open-self : ∀ {Δ} {μ : Env∼ Δ} (C : Ty Δ)
      (X : TyVar (suc Δ))
    → μ ⊢ singleSubᵗ C X ∼ singleSubᵗ C X
  open-self C X = refl∼ (singleSubᵗ C X)

  open-to-★ : ∀ {Δ} {μ : Env∼ Δ} (C : Ty Δ)
      (X : TyVar (suc Δ))
    → extᵐ μ X ≡ X∼★
    → μ ⊢ singleSubᵗ C X ∼ ★
  open-to-★ C zero ()
  open-to-★ {μ = μ} C (suc X) eq =
    _! ⦃ G∼★ = X∼★ᵍ eq ⦄ (id (＇ X))
      ⦃ nonstar-X ⦄

  open-from-★ : ∀ {Δ} {μ : Env∼ Δ} (C : Ty Δ)
      (X : TyVar (suc Δ))
    → extᵐ μ X ≡ ★∼X
    → μ ⊢ ★ ∼ singleSubᵗ C X
  open-from-★ C zero ()
  open-from-★ {μ = μ} C (suc X) eq =
    ？_ ⦃ ★∼G = ★∼Xᵍ eq ⦄ (id (＇ X))
      ⦃ nonstar-X ⦄

  open-cross-to-★ : ∀ {Δ} {μ : Env∼ Δ} (C : Ty Δ)
      (X : TyVar (suc Δ))
    → extᵐ μ X ≡ ★∼X∼★
    → μ ⊢ singleSubᵗ C X ∼ ★
  open-cross-to-★ C zero ()
  open-cross-to-★ {μ = μ} C (suc X) eq =
    _! ⦃ G∼★ = X∼★ᶜ eq ⦄ (id (＇ X)) ⦃ nonstar-X ⦄

  open-cross-from-★ : ∀ {Δ} {μ : Env∼ Δ} (C : Ty Δ)
      (X : TyVar (suc Δ))
    → extᵐ μ X ≡ ★∼X∼★
    → μ ⊢ ★ ∼ singleSubᵗ C X
  open-cross-from-★ C zero ()
  open-cross-from-★ {μ = μ} C (suc X) eq =
    ？_ ⦃ ★∼G = ★∼Xᶜ eq ⦄ (id (＇ X)) ⦃ nonstar-X ⦄

infixl 8 _[_]ᶜ
_[_]ᶜ : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty (suc Δ)}
  → extᵐ μ ⊢ A ∼ B
  → (C : Ty Δ)
  → μ ⊢ A [ C ]ᵗ ∼ B [ C ]ᵗ
_[_]ᶜ {μ = μ} c C =
  subst∼
    (subst-env∼ (open-self C) (open-to-★ {μ = μ} C)
      (open-from-★ C) (open-cross-to-★ C) (open-cross-from-★ C))
    c

------------------------------------------------------------------------
-- Structural size of consistency proofs — measure for the DGG value
-- catch-up driver (M6)
------------------------------------------------------------------------

castSize : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
  → μ ⊢ A ∼ B
  → ℕ
castSize (id a) = suc zero
castSize (c ↦ d) = suc (castSize c + castSize d)
castSize (∀ᶜ c) = suc (castSize c)
castSize (_! c) = suc (castSize c)
castSize (？ c) = suc (castSize c)
castSize (inst_ c B≢★) = suc (castSize c)
castSize (gen_ c A≢★) = suc (castSize c)
castSize bot-elim = suc zero
castSize bot-intro = suc zero

castSize-subst-left-∼ : ∀ {Δ} {μ : Env∼ Δ}
    {A A′ B : Ty Δ}
  → (eq : A ≡ A′)
  → (c : μ ⊢ A ∼ B)
  → castSize (subst-left-∼ eq c) ≡ castSize c
castSize-subst-left-∼ refl c = refl

castSize-subst-right-∼ : ∀ {Δ} {μ : Env∼ Δ}
    {A B B′ : Ty Δ}
  → (eq : B ≡ B′)
  → (c : μ ⊢ A ∼ B)
  → castSize (subst-right-∼ eq c) ≡ castSize c
castSize-subst-right-∼ refl c = refl

castSize-rename∼ : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
    {A B : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → (eq : ∀ X → μ′ (ρ X) ≡ μ X)
  → (c : μ ⊢ A ∼ B)
  → castSize (rename∼ {μ = μ} {μ′ = μ′} ρ eq c) ≡ castSize c
castSize-rename∼ ρ eq (id ★) = refl
castSize-rename∼ ρ eq (id (‵ ι)) = refl
castSize-rename∼ ρ eq (id (＇ X)) = refl
castSize-rename∼ {μ = μ} {μ′ = μ′} ρ eq (c ↦ d) =
  cong₂ (λ m n → suc (m + n))
    (castSize-rename∼ {μ = flipᵐ μ} {μ′ = flipᵐ μ′} ρ
      (flip-rename-env {μ = μ} {μ′ = μ′} ρ eq) c)
    (castSize-rename∼ {μ = μ} {μ′ = μ′} ρ eq d)
castSize-rename∼ {μ = μ} {μ′ = μ′} ρ eq (∀ᶜ c) =
  cong suc
    (castSize-rename∼ {μ = extᵐ μ} {μ′ = extᵐ μ′}
      (extᵗ ρ) (extᵐ-rename ρ eq) c)
castSize-rename∼ {μ = μ} {μ′ = μ′} ρ eq (_! c) =
  cong suc (castSize-rename∼ {μ = μ} {μ′ = μ′} ρ eq c)
castSize-rename∼ {μ = μ} {μ′ = μ′} ρ eq (？ c) =
  cong suc (castSize-rename∼ {μ = μ} {μ′ = μ′} ρ eq c)
castSize-rename∼ {μ = μ} {μ′ = μ′} ρ eq
    (inst_ {B = B} c B≢★) =
  cong suc
    (trans
      (castSize-subst-right-∼ (renameᵗ-shift ρ B)
        (rename∼ {μ = instᵐ μ} {μ′ = instᵐ μ′}
          (extᵗ ρ) (instᵐ-rename ρ eq) c))
      (castSize-rename∼ {μ = instᵐ μ} {μ′ = instᵐ μ′}
        (extᵗ ρ) (instᵐ-rename ρ eq) c))
castSize-rename∼ {μ = μ} {μ′ = μ′} ρ eq
    (gen_ {A = A} c A≢★) =
  cong suc
    (trans
      (castSize-subst-left-∼ (renameᵗ-shift ρ A)
        (rename∼ {μ = genᵐ μ} {μ′ = genᵐ μ′}
          (extᵗ ρ) (genᵐ-rename ρ eq) c))
      (castSize-rename∼ {μ = genᵐ μ} {μ′ = genᵐ μ′}
        (extᵗ ρ) (genᵐ-rename ρ eq) c))
castSize-rename∼ ρ eq bot-elim = refl
castSize-rename∼ ρ eq bot-intro = refl

castSize-renameEnvᶜ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
    {A B : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → (eq : ∀ X → ν (ρ X) ≡ μ X)
  → (c : μ ⊢ A ∼ B)
  → castSize (renameEnvᶜ {μ = μ} {ν = ν} ρ eq c) ≡ castSize c
castSize-renameEnvᶜ {μ = μ} {ν = ν} ρ eq c =
  castSize-rename∼ {μ = μ} {μ′ = ν} ρ eq c

castSize-renameᵐᶜ : ∀ {Δ Δ′} {μ : Env∼ Δ}
    {A B : Ty Δ}
  → (ρ : Δ ↪ᵗ Δ′)
  → (c : μ ⊢ A ∼ B)
  → castSize (renameᵐᶜ ρ c) ≡ castSize c
castSize-renameᵐᶜ {μ = μ} ρ c =
  castSize-rename∼ {μ = μ} {μ′ = renameEnv∼ ρ μ}
    (toRenameᵗ ρ) (renameEnv∼-preserves ρ μ) c

castSize-↑ᶜ : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
  → (c : μ ⊢ A ∼ B)
  → castSize (↑ᶜ c) ≡ castSize c
castSize-↑ᶜ = castSize-renameᵐᶜ wk↪ᵗ

castSize-subst-left-∼-≤ : ∀ {Δ} {μ : Env∼ Δ}
    {A A′ B : Ty Δ}
  → (eq : A ≡ A′)
  → (c : μ ⊢ A ∼ B)
  → castSize (subst-left-∼ eq c) ≤ castSize c
castSize-subst-left-∼-≤ refl c = ≤-refl

castSize-subst-right-∼-≤ : ∀ {Δ} {μ : Env∼ Δ}
    {A B B′ : Ty Δ}
  → (eq : B ≡ B′)
  → (c : μ ⊢ A ∼ B)
  → castSize (subst-right-∼ eq c) ≤ castSize c
castSize-subst-right-∼-≤ refl c = ≤-refl

castSize-transport-env∼ : ∀ {Δ} {μ ν : Env∼ Δ} {A B : Ty Δ}
  → (eq : μ ≡ ν)
  → (c : μ ⊢ A ∼ B)
  → castSize (transport-env∼ eq c) ≡ castSize c
castSize-transport-env∼ refl c = refl

castSize-sym∼ : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
  → (c : μ ⊢ A ∼ B)
  → castSize (sym∼ c) ≡ castSize c
castSize-sym∼ (id ★) = refl
castSize-sym∼ (id (‵ ι)) = refl
castSize-sym∼ (id (＇ X)) = refl
castSize-sym∼ (c ↦ d) =
  cong₂ (λ m n → suc (m + n)) (castSize-sym∼ c)
    (castSize-sym∼ d)
castSize-sym∼ (∀ᶜ c) =
  cong suc
    (trans (castSize-transport-env∼ flip-extᵐ (sym∼ c))
      (castSize-sym∼ c))
castSize-sym∼ (_! c) = cong suc (castSize-sym∼ c)
castSize-sym∼ (？ c) = cong suc (castSize-sym∼ c)
castSize-sym∼ (inst_ c B≢★) =
  cong suc
    (trans (castSize-transport-env∼ flip-instᵐ (sym∼ c))
      (castSize-sym∼ c))
castSize-sym∼ (gen_ c A≢★) =
  cong suc
    (trans (castSize-transport-env∼ flip-genᵐ (sym∼ c))
      (castSize-sym∼ c))
castSize-sym∼ bot-elim = refl
castSize-sym∼ bot-intro = refl

private

  record SubstEnvSize≤ {Δ Δ′ : TyCtx} {μ : Env∼ Δ}
      {ν : Env∼ Δ′} {σ : Δ ⇒ˢ Δ′}
      (s : SubstEnv∼ μ ν σ) : Set where
    constructor subst-env-size≤
    field
      self≤ : ∀ X → castSize (self s X) ≤ suc zero
      to-★≤ : ∀ X eq → castSize (to-★ s X eq) ≤ suc (suc zero)
      from-★≤ : ∀ X eq → castSize (from-★ s X eq) ≤ suc (suc zero)
      cross-to-★≤ :
        ∀ X eq → castSize (cross-to-★ s X eq) ≤ suc (suc zero)
      cross-from-★≤ :
        ∀ X eq → castSize (cross-from-★ s X eq) ≤ suc (suc zero)

  open SubstEnvSize≤

  ext-SubstEnvSize≤ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′}
    → (s : SubstEnv∼ μ ν σ)
    → SubstEnvSize≤ s
    → SubstEnvSize≤ (ext-SubstEnv∼ s)
  ext-SubstEnvSize≤ {μ = μ} {ν = ν} s bounds =
    subst-env-size≤ self≤′ to-★≤′ from-★≤′ cross-to-★≤′
      cross-from-★≤′
    where
    self≤′ : ∀ X
      → castSize (self (ext-SubstEnv∼ s) X) ≤ suc zero
    self≤′ zero = ≤-refl
    self≤′ (suc X)
      rewrite castSize-rename∼ {μ = ν} {μ′ = extᵐ ν}
        suc (λ Y → refl) (self s X) =
        self≤ bounds X

    to-★≤′ : ∀ X eq
      → castSize (to-★ (ext-SubstEnv∼ s) X eq) ≤ suc (suc zero)
    to-★≤′ zero ()
    to-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = extᵐ ν}
        suc (λ Y → refl) (to-★ s X eq) =
        to-★≤ bounds X eq

    from-★≤′ : ∀ X eq
      → castSize (from-★ (ext-SubstEnv∼ s) X eq) ≤ suc (suc zero)
    from-★≤′ zero ()
    from-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = extᵐ ν}
        suc (λ Y → refl) (from-★ s X eq) =
        from-★≤ bounds X eq

    cross-to-★≤′ : ∀ X eq
      → castSize (cross-to-★ (ext-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    cross-to-★≤′ zero ()
    cross-to-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = extᵐ ν}
        suc (λ Y → refl) (cross-to-★ s X eq) =
        cross-to-★≤ bounds X eq

    cross-from-★≤′ : ∀ X eq
      → castSize (cross-from-★ (ext-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    cross-from-★≤′ zero ()
    cross-from-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = extᵐ ν}
        suc (λ Y → refl)
        (cross-from-★ s X eq) =
          cross-from-★≤ bounds X eq

  inst-SubstEnvSize≤ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′}
    → (s : SubstEnv∼ μ ν σ)
    → SubstEnvSize≤ s
    → SubstEnvSize≤ (inst-SubstEnv∼ s)
  inst-SubstEnvSize≤ {μ = μ} {ν = ν} s bounds =
    subst-env-size≤ self≤′ to-★≤′ from-★≤′ cross-to-★≤′
      cross-from-★≤′
    where
    self≤′ : ∀ X
      → castSize (self (inst-SubstEnv∼ s) X) ≤ suc zero
    self≤′ zero = ≤-refl
    self≤′ (suc X)
      rewrite castSize-rename∼ {μ = ν} {μ′ = instᵐ ν}
        suc (λ Y → refl) (self s X) =
        self≤ bounds X

    to-★≤′ : ∀ X eq
      → castSize (to-★ (inst-SubstEnv∼ s) X eq) ≤ suc (suc zero)
    to-★≤′ zero eq = ≤-refl
    to-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = instᵐ ν}
        suc (λ Y → refl) (to-★ s X eq) =
        to-★≤ bounds X eq

    from-★≤′ : ∀ X eq
      → castSize (from-★ (inst-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    from-★≤′ zero ()
    from-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = instᵐ ν}
        suc (λ Y → refl) (from-★ s X eq) =
        from-★≤ bounds X eq

    cross-to-★≤′ : ∀ X eq
      → castSize (cross-to-★ (inst-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    cross-to-★≤′ zero ()
    cross-to-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = instᵐ ν}
        suc (λ Y → refl) (cross-to-★ s X eq) =
        cross-to-★≤ bounds X eq

    cross-from-★≤′ : ∀ X eq
      → castSize (cross-from-★ (inst-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    cross-from-★≤′ zero ()
    cross-from-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = instᵐ ν}
        suc (λ Y → refl)
        (cross-from-★ s X eq) =
          cross-from-★≤ bounds X eq

  gen-SubstEnvSize≤ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′}
    → (s : SubstEnv∼ μ ν σ)
    → SubstEnvSize≤ s
    → SubstEnvSize≤ (gen-SubstEnv∼ s)
  gen-SubstEnvSize≤ {μ = μ} {ν = ν} s bounds =
    subst-env-size≤ self≤′ to-★≤′ from-★≤′ cross-to-★≤′
      cross-from-★≤′
    where
    self≤′ : ∀ X
      → castSize (self (gen-SubstEnv∼ s) X) ≤ suc zero
    self≤′ zero = ≤-refl
    self≤′ (suc X)
      rewrite castSize-rename∼ {μ = ν} {μ′ = genᵐ ν}
        suc (λ Y → refl) (self s X) =
        self≤ bounds X

    to-★≤′ : ∀ X eq
      → castSize (to-★ (gen-SubstEnv∼ s) X eq) ≤ suc (suc zero)
    to-★≤′ zero ()
    to-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = genᵐ ν}
        suc (λ Y → refl) (to-★ s X eq) =
        to-★≤ bounds X eq

    from-★≤′ : ∀ X eq
      → castSize (from-★ (gen-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    from-★≤′ zero eq = ≤-refl
    from-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = genᵐ ν}
        suc (λ Y → refl) (from-★ s X eq) =
        from-★≤ bounds X eq

    cross-to-★≤′ : ∀ X eq
      → castSize (cross-to-★ (gen-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    cross-to-★≤′ zero ()
    cross-to-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = genᵐ ν}
        suc (λ Y → refl) (cross-to-★ s X eq) =
        cross-to-★≤ bounds X eq

    cross-from-★≤′ : ∀ X eq
      → castSize (cross-from-★ (gen-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    cross-from-★≤′ zero ()
    cross-from-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = genᵐ ν}
        suc (λ Y → refl)
        (cross-from-★ s X eq) =
          cross-from-★≤ bounds X eq

  flip-SubstEnvSize≤ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′}
    → (s : SubstEnv∼ μ ν σ)
    → SubstEnvSize≤ s
    → SubstEnvSize≤ (flip-SubstEnv∼ s)
  flip-SubstEnvSize≤ {μ = μ} {ν = ν} s bounds =
    subst-env-size≤ self≤′ to-★≤′ from-★≤′ cross-to-★≤′
      cross-from-★≤′
    where
    self≤′ : ∀ X
      → castSize (self (flip-SubstEnv∼ s) X) ≤ suc zero
    self≤′ X rewrite castSize-sym∼ (self s X) = self≤ bounds X

    to-★≤′ : ∀ X eq
      → castSize (to-★ (flip-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    to-★≤′ X eq
      rewrite castSize-sym∼ (from-★ s X (flipVar∼-to-X∼★ eq)) =
        from-★≤ bounds X (flipVar∼-to-X∼★ eq)

    from-★≤′ : ∀ X eq
      → castSize (from-★ (flip-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    from-★≤′ X eq
      rewrite castSize-sym∼ (to-★ s X (flipVar∼-to-★∼X eq)) =
        to-★≤ bounds X (flipVar∼-to-★∼X eq)

    cross-to-★≤′ : ∀ X eq
      → castSize (cross-to-★ (flip-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    cross-to-★≤′ X eq
      rewrite castSize-sym∼
        (cross-from-★ s X (flipVar∼-to-★∼X∼★ eq)) =
          cross-from-★≤ bounds X (flipVar∼-to-★∼X∼★ eq)

    cross-from-★≤′ : ∀ X eq
      → castSize (cross-from-★ (flip-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    cross-from-★≤′ X eq
      rewrite castSize-sym∼
        (cross-to-★ s X (flipVar∼-to-★∼X∼★ eq)) =
          cross-to-★≤ bounds X (flipVar∼-to-★∼X∼★ eq)

  castSize-factor-inst-star-≤ :
      ∀ {Δ} {μ : Env∼ Δ} {A : Ty (suc Δ)}
    → (c : instᵐ μ ⊢ A ∼ ★)
    → (Anv : NonVar A)
    → (z∈A : zero ∈ᵗ A)
    → castSize (factor-inst-star c Anv z∈A) ≤ suc (castSize c)
  castSize-factor-inst-star-≤ (id ★) Anv ()
  castSize-factor-inst-star-≤
      (_! ⦃ Gᵍ = ★⇒★ ⦄ c ⦃ Ans ⦄) Anv z∈A = ≤-refl
  castSize-factor-inst-star-≤
      (_! ⦃ Gᵍ = ‵ ι ⦄ c ⦃ Ans ⦄) Anv z∈A = ≤-refl
  castSize-factor-inst-star-≤
      (_! ⦃ Gᵍ = ＇ zero ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ c ⦃ Ans ⦄)
      Anv z∈A =
    ⊥-elim (inst-to-var-occurs-impossible c eq Anv z∈A)
  castSize-factor-inst-star-≤
      (_! ⦃ Gᵍ = ＇ zero ⦄ ⦃ G∼★ = X∼★ᶜ () ⦄ c ⦃ Ans ⦄)
      Anv z∈A
  castSize-factor-inst-star-≤
      (_! ⦃ Gᵍ = ＇ suc X ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄
          c ⦃ Ans ⦄)
      Anv z∈A = ≤-refl
  castSize-factor-inst-star-≤
      (_! ⦃ Gᵍ = ＇ suc X ⦄
          ⦃ G∼★ = X∼★ᶜ eq ⦄ c ⦃ Ans ⦄)
      Anv z∈A = ≤-refl
  castSize-factor-inst-star-≤
      (_! ⦃ Gᵍ = ∀★ ⦄ c ⦃ Ans ⦄) Anv z∈A = ≤-refl
  castSize-factor-inst-star-≤ (？_ ⦃ g ⦄ c ⦃ Bns ⦄) Anv ()
  castSize-factor-inst-star-≤
      (inst_ ⦃ Anv′ ⦄ ⦃ z∈A′ ⦄ c ★≢★) Anv z∈A =
    ⊥-elim (★≢★ refl)

  castSize-factor-gen-star-≤ :
      ∀ {Δ} {μ : Env∼ Δ} {B : Ty (suc Δ)}
    → (c : genᵐ μ ⊢ ★ ∼ B)
    → (Bnv : NonVar B)
    → (z∈B : zero ∈ᵗ B)
    → castSize (factor-gen-star c Bnv z∈B) ≤ suc (castSize c)
  castSize-factor-gen-star-≤ (id ★) Bnv ()
  castSize-factor-gen-star-≤ (_! ⦃ g ⦄ c ⦃ () ⦄) Bnv z∈B
  castSize-factor-gen-star-≤
      (？_ ⦃ Gᵍ = ★⇒★ ⦄ c ⦃ Bns ⦄) Bnv z∈B = ≤-refl
  castSize-factor-gen-star-≤
      (？_ ⦃ Gᵍ = ‵ ι ⦄ c ⦃ Bns ⦄) Bnv z∈B = ≤-refl
  castSize-factor-gen-star-≤
      (？_ ⦃ Gᵍ = ＇ zero ⦄
          ⦃ ★∼G = ★∼Xᵍ eq ⦄ c ⦃ Bns ⦄)
      Bnv z∈B =
    ⊥-elim (gen-from-var-occurs-impossible c eq Bnv z∈B)
  castSize-factor-gen-star-≤
      (？_ ⦃ Gᵍ = ＇ zero ⦄
          ⦃ ★∼G = ★∼Xᶜ () ⦄ c ⦃ Bns ⦄)
      Bnv z∈B
  castSize-factor-gen-star-≤
      (？_ ⦃ Gᵍ = ＇ suc X ⦄
          ⦃ ★∼G = ★∼Xᵍ eq ⦄ c ⦃ Bns ⦄)
      Bnv z∈B = ≤-refl
  castSize-factor-gen-star-≤
      (？_ ⦃ Gᵍ = ＇ suc X ⦄
          ⦃ ★∼G = ★∼Xᶜ eq ⦄ c ⦃ Bns ⦄)
      Bnv z∈B = ≤-refl
  castSize-factor-gen-star-≤
      (？_ ⦃ Gᵍ = ∀★ ⦄ c ⦃ Bns ⦄) Bnv z∈B = ≤-refl
  castSize-factor-gen-star-≤
      (gen_ ⦃ Bnv′ ⦄ ⦃ z∈B′ ⦄ c ★≢★) Bnv z∈B =
    ⊥-elim (★≢★ refl)

  castSize-subst-to-star-var-≤ :
      ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
        {σ : Δ ⇒ˢ Δ′} {A : Ty Δ} {X}
    → (s : SubstEnv∼ μ ν σ)
    → SubstEnvSize≤ s
    → (c : μ ⊢ A ∼ ＇ X)
    → (eq : μ X ≡ X∼★)
    → (Ans : NonStar A)
    → castSize (subst-to-star-var s c eq Ans) ≤ suc (castSize c)
  castSize-subst-to-star-var-≤ s bounds (id (＇ X)) eq Ans =
    to-★≤ bounds X eq
  castSize-subst-to-star-var-≤ s bounds (？_ c ⦃ Bns ⦄) eq ()
  castSize-subst-to-star-var-≤ s bounds
      c@(inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ d B≢★) eq Ans =
    ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all Ans)

  castSize-subst-cross-to-star-var-≤ :
      ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
        {σ : Δ ⇒ˢ Δ′} {A : Ty Δ} {X}
    → (s : SubstEnv∼ μ ν σ)
    → SubstEnvSize≤ s
    → (c : μ ⊢ A ∼ ＇ X)
    → (eq : μ X ≡ ★∼X∼★)
    → (Ans : NonStar A)
    → castSize (subst-cross-to-star-var s c eq Ans)
      ≤ suc (castSize c)
  castSize-subst-cross-to-star-var-≤ s bounds (id (＇ X)) eq Ans =
    cross-to-★≤ bounds X eq
  castSize-subst-cross-to-star-var-≤ s bounds
      (？_ c ⦃ Bns ⦄) eq ()
  castSize-subst-cross-to-star-var-≤ s bounds
      c@(inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ d B≢★) eq Ans =
    ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all Ans)

  castSize-subst-from-star-var-≤ :
      ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
        {σ : Δ ⇒ˢ Δ′} {B : Ty Δ} {X}
    → (s : SubstEnv∼ μ ν σ)
    → SubstEnvSize≤ s
    → (c : μ ⊢ ＇ X ∼ B)
    → (eq : μ X ≡ ★∼X)
    → (Bns : NonStar B)
    → castSize (subst-from-star-var s c eq Bns) ≤ suc (castSize c)
  castSize-subst-from-star-var-≤ s bounds (id (＇ X)) eq Bns =
    from-★≤ bounds X eq
  castSize-subst-from-star-var-≤ s bounds (_! c ⦃ Ans ⦄) eq ()
  castSize-subst-from-star-var-≤ s bounds
      c@(gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ d A≢★) eq Bns =
    ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all Bns)

  castSize-subst-cross-from-star-var-≤ :
      ∀ {Δ Δ′} {μ : Env∼ Δ}
        {ν : Env∼ Δ′} {σ : Δ ⇒ˢ Δ′} {B : Ty Δ} {X}
    → (s : SubstEnv∼ μ ν σ)
    → SubstEnvSize≤ s
    → (c : μ ⊢ ＇ X ∼ B)
    → (eq : μ X ≡ ★∼X∼★)
    → (Bns : NonStar B)
    → castSize (subst-cross-from-star-var s c eq Bns)
      ≤ suc (castSize c)
  castSize-subst-cross-from-star-var-≤ s bounds (id (＇ X)) eq Bns =
    cross-from-★≤ bounds X eq
  castSize-subst-cross-from-star-var-≤ s bounds
      (_! c ⦃ Ans ⦄) eq ()
  castSize-subst-cross-from-star-var-≤ s bounds
      c@(gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ d A≢★) eq Bns =
    ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all Bns)

  castSize-subst∼-≤ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′} {A B : Ty Δ}
    → (s : SubstEnv∼ μ ν σ)
    → SubstEnvSize≤ s
    → (c : μ ⊢ A ∼ B)
    → castSize (subst∼ s c) ≤ castSize c
  castSize-subst∼-≤ s bounds (id ★) = ≤-refl
  castSize-subst∼-≤ s bounds (id (‵ ι)) = ≤-refl
  castSize-subst∼-≤ s bounds (id (＇ X)) = self≤ bounds X
  castSize-subst∼-≤ s bounds (c ↦ d) =
    s≤s (+-mono-≤
      (castSize-subst∼-≤ (flip-SubstEnv∼ s)
        (flip-SubstEnvSize≤ s bounds) c)
      (castSize-subst∼-≤ s bounds d))
  castSize-subst∼-≤ s bounds (∀ᶜ c) =
    s≤s (castSize-subst∼-≤ (ext-SubstEnv∼ s)
      (ext-SubstEnvSize≤ s bounds) c)
  castSize-subst∼-≤ {σ = σ} s bounds
      (_! ⦃ Gᵍ = ★⇒★ ⦄ c ⦃ Ans ⦄) =
    s≤s (castSize-subst∼-≤ s bounds c)
  castSize-subst∼-≤ {σ = σ} s bounds
      (_! ⦃ Gᵍ = ‵ ι ⦄ c ⦃ Ans ⦄) =
    s≤s (castSize-subst∼-≤ s bounds c)
  castSize-subst∼-≤ s bounds
      (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ c ⦃ Ans ⦄) =
    castSize-subst-to-star-var-≤ s bounds c eq Ans
  castSize-subst∼-≤ s bounds
      (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ eq ⦄ c ⦃ Ans ⦄) =
    castSize-subst-cross-to-star-var-≤ s bounds c eq Ans
  castSize-subst∼-≤ {σ = σ} s bounds
      (_! ⦃ Gᵍ = ∀★ ⦄ c ⦃ Ans ⦄) =
    s≤s (castSize-subst∼-≤ s bounds c)
  castSize-subst∼-≤ {σ = σ} s bounds
      (？_ ⦃ Gᵍ = ★⇒★ ⦄ c ⦃ Bns ⦄) =
    s≤s (castSize-subst∼-≤ s bounds c)
  castSize-subst∼-≤ {σ = σ} s bounds
      (？_ ⦃ Gᵍ = ‵ ι ⦄ c ⦃ Bns ⦄) =
    s≤s (castSize-subst∼-≤ s bounds c)
  castSize-subst∼-≤ s bounds
      (？_ ⦃ Gᵍ = ＇ X ⦄
          ⦃ ★∼G = ★∼Xᵍ eq ⦄ c ⦃ Bns ⦄) =
    castSize-subst-from-star-var-≤ s bounds c eq Bns
  castSize-subst∼-≤ s bounds
      (？_ ⦃ Gᵍ = ＇ X ⦄
          ⦃ ★∼G = ★∼Xᶜ eq ⦄ c ⦃ Bns ⦄) =
    castSize-subst-cross-from-star-var-≤ s bounds c eq Bns
  castSize-subst∼-≤ {σ = σ} s bounds
      (？_ ⦃ Gᵍ = ∀★ ⦄ c ⦃ Bns ⦄) =
    s≤s (castSize-subst∼-≤ s bounds c)
  castSize-subst∼-≤ {σ = σ} s bounds
      (inst_ {B = B} ⦃ A-nonvar ⦄ ⦃ zero∈A ⦄ c B≢★)
      with substᵗ σ B ≟Ty ★
  castSize-subst∼-≤ {σ = σ} s bounds
      (inst_ {B = B} ⦃ A-nonvar ⦄ ⦃ zero∈A ⦄ c B≢★)
      | no Bσ≢★ =
    s≤s (≤-trans
      (castSize-subst-right-∼-≤ (substᵗ-shift σ B)
        (subst∼ (inst-SubstEnv∼ s) c))
      (castSize-subst∼-≤ (inst-SubstEnv∼ s)
        (inst-SubstEnvSize≤ s bounds) c))
  castSize-subst∼-≤ {σ = σ} s bounds
      (inst_ {B = B} ⦃ A-nonvar ⦄ ⦃ zero∈A ⦄ c B≢★)
      | yes Bσ≡★ =
    ≤-trans
      (castSize-subst-right-∼-≤ (sym Bσ≡★)
        (factor-inst-star
          (subst-right-∼
            (trans (substᵗ-shift σ B) (cong (renameᵗ suc) Bσ≡★))
            (subst∼ (inst-SubstEnv∼ s) c))
          (substNonVar (extsᵗ σ) A-nonvar)
          (subst-∈ᵗ zero∈A var-∈)))
      (≤-trans
      (castSize-factor-inst-star-≤
        (subst-right-∼
          (trans (substᵗ-shift σ B) (cong (renameᵗ suc) Bσ≡★))
          (subst∼ (inst-SubstEnv∼ s) c))
        (substNonVar (extsᵗ σ) A-nonvar)
        (subst-∈ᵗ zero∈A var-∈))
      (s≤s (≤-trans
        (castSize-subst-right-∼-≤
          (trans (substᵗ-shift σ B) (cong (renameᵗ suc) Bσ≡★))
          (subst∼ (inst-SubstEnv∼ s) c))
        (castSize-subst∼-≤ (inst-SubstEnv∼ s)
          (inst-SubstEnvSize≤ s bounds) c))))
  castSize-subst∼-≤ {σ = σ} s bounds
      (gen_ {A = A} ⦃ B-nonvar ⦄ ⦃ zero∈B ⦄ c A≢★)
      with substᵗ σ A ≟Ty ★
  castSize-subst∼-≤ {σ = σ} s bounds
      (gen_ {A = A} ⦃ B-nonvar ⦄ ⦃ zero∈B ⦄ c A≢★)
      | no Aσ≢★ =
    s≤s (≤-trans
      (castSize-subst-left-∼-≤ (substᵗ-shift σ A)
        (subst∼ (gen-SubstEnv∼ s) c))
      (castSize-subst∼-≤ (gen-SubstEnv∼ s)
        (gen-SubstEnvSize≤ s bounds) c))
  castSize-subst∼-≤ {σ = σ} s bounds
      (gen_ {A = A} ⦃ B-nonvar ⦄ ⦃ zero∈B ⦄ c A≢★)
      | yes Aσ≡★ =
    ≤-trans
      (castSize-subst-left-∼-≤ (sym Aσ≡★)
        (factor-gen-star
          (subst-left-∼
            (trans (substᵗ-shift σ A) (cong (renameᵗ suc) Aσ≡★))
            (subst∼ (gen-SubstEnv∼ s) c))
          (substNonVar (extsᵗ σ) B-nonvar)
          (subst-∈ᵗ zero∈B var-∈)))
      (≤-trans
      (castSize-factor-gen-star-≤
        (subst-left-∼
          (trans (substᵗ-shift σ A) (cong (renameᵗ suc) Aσ≡★))
          (subst∼ (gen-SubstEnv∼ s) c))
        (substNonVar (extsᵗ σ) B-nonvar)
        (subst-∈ᵗ zero∈B var-∈))
      (s≤s (≤-trans
        (castSize-subst-left-∼-≤
          (trans (substᵗ-shift σ A) (cong (renameᵗ suc) Aσ≡★))
          (subst∼ (gen-SubstEnv∼ s) c))
        (castSize-subst∼-≤ (gen-SubstEnv∼ s)
          (gen-SubstEnvSize≤ s bounds) c))))
  castSize-subst∼-≤ s bounds bot-elim = ≤-refl
  castSize-subst∼-≤ s bounds bot-intro = ≤-refl

  close-inst-SubstEnvSize≤ : ∀ {Δ} {μ : Env∼ Δ}
    → SubstEnvSize≤
        (subst-env∼ (close-inst-self {μ = μ}) close-inst-to-★
          close-inst-from-★ close-inst-cross-to-★
          close-inst-cross-from-★)
  close-inst-SubstEnvSize≤ =
    subst-env-size≤ self≤′ to-★≤′ from-★≤′ cross-to-★≤′
      cross-from-★≤′
    where
    self≤′ : ∀ {Δ} {μ : Env∼ Δ} X
      → castSize (close-inst-self {μ = μ} X) ≤ suc zero
    self≤′ zero = ≤-refl
    self≤′ (suc X) = ≤-refl

    to-★≤′ : ∀ {Δ} {μ : Env∼ Δ} X eq
      → castSize (close-inst-to-★ {μ = μ} X eq) ≤ suc (suc zero)
    to-★≤′ zero eq = s≤s z≤n
    to-★≤′ (suc X) eq = ≤-refl

    from-★≤′ : ∀ {Δ} {μ : Env∼ Δ} X eq
      → castSize (close-inst-from-★ {μ = μ} X eq)
        ≤ suc (suc zero)
    from-★≤′ zero ()
    from-★≤′ (suc X) eq = ≤-refl

    cross-to-★≤′ : ∀ {Δ} {μ : Env∼ Δ} X eq
      → castSize (close-inst-cross-to-★ {μ = μ} X eq)
        ≤ suc (suc zero)
    cross-to-★≤′ zero ()
    cross-to-★≤′ (suc X) eq = ≤-refl

    cross-from-★≤′ : ∀ {Δ} {μ : Env∼ Δ} X eq
      → castSize (close-inst-cross-from-★ {μ = μ} X eq)
        ≤ suc (suc zero)
    cross-from-★≤′ zero ()
    cross-from-★≤′ (suc X) eq = ≤-refl

castSize-close-inst-≤ : ∀ {Δ} {μ : Env∼ Δ}
    {A : Ty (suc Δ)} {B : Ty Δ}
  → (c : instᵐ μ ⊢ A ∼ ⇑ᵗ B)
  → castSize (↑ᶜ (close-instᶜ c)) ≤ castSize c
castSize-close-inst-≤ {B = B} c
  rewrite castSize-↑ᶜ (close-instᶜ c) =
    ≤-trans
      (castSize-subst-right-∼-≤ (shift-openᵗ B ★)
        (subst∼
          (subst-env∼ close-inst-self close-inst-to-★
            close-inst-from-★ close-inst-cross-to-★
            close-inst-cross-from-★)
          c))
      (castSize-subst∼-≤
        (subst-env∼ close-inst-self close-inst-to-★ close-inst-from-★
          close-inst-cross-to-★ close-inst-cross-from-★)
        close-inst-SubstEnvSize≤ c)
