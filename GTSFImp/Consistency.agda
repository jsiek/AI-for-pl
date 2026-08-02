module Consistency where

-- File Charter:
--   * Defines environment-indexed type consistency.
--   * Gives every universal type the ground representation `∀ X. ★`.
--   * Provides renaming and substitution for consistency evidence.
--   * Closes instantiation-bound consistency evidence at ★.

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Level using (0ℓ)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (zero; suc)
open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans)
open import Relation.Nullary using (no; yes)

open import Types

private
  variable
    Δ Δ′ : TyCtx

data Var∼ : Set where
  X∼X : Var∼
  X∼★ : Var∼
  ★∼X : Var∼

flipVar∼ : Var∼ → Var∼
flipVar∼ X∼X = X∼X
flipVar∼ X∼★ = ★∼X
flipVar∼ ★∼X = X∼★

Env∼ : TyCtx → Set
Env∼ Δ = TyVar Δ → Var∼

idᶜ : ∀ {Δ} → Env∼ Δ
idᶜ X = X∼X

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

----------------------------------------------------------------------
-- Consistency
----------------------------------------------------------------------

data Groundʳ {Δ : TyCtx} (μ : Env∼ Δ) (r : Var∼) : Ty Δ → Set where
  g-⇒ : Groundʳ μ r (★ ⇒ ★)
  g-ι : ∀ {ι} → Groundʳ μ r (‵ ι)
  g-X : ∀ {X} → μ X ≡ r → Groundʳ μ r (＇ X)
  g-∀ : Groundʳ μ r (`∀ ★)

data GroundMatch {Δ : TyCtx} {μ : Env∼ Δ} {r : Var∼} :
    ∀ {G} → Groundʳ μ r G → Ty Δ → Set where
  match-⇒ : ∀ {A} → GroundMatch g-⇒ A
  match-ι : ∀ {A ι} → GroundMatch (g-ι {ι = ι}) A
  match-X : ∀ {X} {eq : μ X ≡ r} → GroundMatch (g-X eq) (＇ X)
  match-∀ : ∀ {A} → GroundMatch g-∀ (`∀ A)

groundMatch-unique : ∀ {Δ} {μ : Env∼ Δ} {r G A}
    {g : Groundʳ μ r G}
  → (p q : GroundMatch g A)
  → p ≡ q
groundMatch-unique match-⇒ match-⇒ = refl
groundMatch-unique match-ι match-ι = refl
groundMatch-unique match-X match-X = refl
groundMatch-unique match-∀ match-∀ = refl

instance
  refl-instance : ∀ {A : Set} {x : A} → x ≡ x
  refl-instance = refl

  ground-⇒-instance : ∀ {Δ μ r}
    → Groundʳ {Δ} μ r (★ ⇒ ★)
  ground-⇒-instance = g-⇒

  ground-ι-instance : ∀ {Δ μ r ι}
    → Groundʳ {Δ} μ r (‵ ι)
  ground-ι-instance = g-ι

  ground-X-instance : ∀ {Δ μ r X} ⦃ eq : μ X ≡ r ⦄
    → Groundʳ {Δ} μ r (＇ X)
  ground-X-instance ⦃ eq ⦄ = g-X eq

  ground-∀-instance : ∀ {Δ μ r}
    → Groundʳ {Δ} μ r (`∀ ★)
  ground-∀-instance = g-∀

  match-⇒-instance : ∀ {Δ μ r A}
    → GroundMatch (g-⇒ {Δ = Δ} {μ = μ} {r = r}) A
  match-⇒-instance = match-⇒

  match-ι-instance : ∀ {Δ μ r A ι}
    → GroundMatch (g-ι {Δ = Δ} {μ = μ} {r = r} {ι = ι}) A
  match-ι-instance = match-ι

  match-X-instance : ∀ {Δ μ r X} {eq : μ X ≡ r}
    → GroundMatch (g-X {Δ = Δ} {μ = μ} {r = r} {X = X} eq) (＇ X)
  match-X-instance = match-X

  match-∀-instance : ∀ {Δ μ r A}
    → GroundMatch (g-∀ {Δ = Δ} {μ = μ} {r = r}) (`∀ A)
  match-∀-instance = match-∀

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
    → μ ⊢ A ∼ A′
    → μ ⊢ B ∼ B′
      ---------------------------
    → μ ⊢ (A ⇒ B) ∼ (A′ ⇒ B′)

  ∀ᶜ_ : ∀ {A B}
    → extᵐ μ ⊢ A ∼ B
      -----------------------
    → μ ⊢ (`∀ A) ∼ (`∀ B)

  _! : ∀ {A G}
    → ⦃ g : Groundʳ μ X∼★ G ⦄
    → μ ⊢ A ∼ G
    → ⦃ Ans : NonStar A ⦄
    → ⦃ match : GroundMatch g A ⦄
      -----------
    → μ ⊢ A ∼ ★

  ？_ : ∀ {G B}
    → ⦃ g : Groundʳ μ ★∼X G ⦄
    → μ ⊢ G ∼ B
    → ⦃ Bns : NonStar B ⦄
    → ⦃ match : GroundMatch g B ⦄
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

idᵍ : ∀ {Δ} {G : Ty Δ} {μ : Env∼ Δ} {r : Var∼}
  → Groundʳ μ r G
  → μ ⊢ G ∼ G
idᵍ g-⇒ = id ★ ↦ id ★
idᵍ g-ι = id (‵ _)
idᵍ (g-X {X = X} eq) = id (＇ X)
idᵍ g-∀ = ∀ᶜ (id ★)

ground≢★ : ∀ {Δ} {G : Ty Δ} {μ : Env∼ Δ} {r : Var∼}
  → Groundʳ μ r G
  → G ≢ ★
ground≢★ g-⇒ = λ ()
ground≢★ g-ι = λ ()
ground≢★ (g-X eq) = λ ()
ground≢★ g-∀ = λ ()

ground-nonstar : ∀ {Δ} {G : Ty Δ} {μ : Env∼ Δ} {r : Var∼}
  → Groundʳ μ r G
  → NonStar G
ground-nonstar g-⇒ = nonstar-⇒
ground-nonstar g-ι = nonstar-ι
ground-nonstar (g-X eq) = nonstar-X
ground-nonstar g-∀ = nonstar-∀

renameNonStar : ∀ {Δ Δ′} {A : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → NonStar A
  → NonStar (renameᵗ ρ A)
renameNonStar ρ nonstar-X = nonstar-X
renameNonStar ρ nonstar-ι = nonstar-ι
renameNonStar ρ nonstar-⇒ = nonstar-⇒
renameNonStar ρ nonstar-∀ = nonstar-∀

ground-match : ∀ {Δ} {G : Ty Δ} {μ : Env∼ Δ} {r : Var∼}
  → (g : Groundʳ μ r G)
  → GroundMatch g G
ground-match g-⇒ = match-⇒
ground-match g-ι = match-ι
ground-match (g-X eq) = match-X
ground-match g-∀ = match-∀

flip-Groundʳ : ∀ {Δ} {G : Ty Δ} {μ : Env∼ Δ} {r : Var∼}
  → Groundʳ μ r G
  → Groundʳ (flipᵐ μ) (flipVar∼ r) G
flip-Groundʳ g-⇒ = g-⇒
flip-Groundʳ g-ι = g-ι
flip-Groundʳ (g-X eq) = g-X (cong flipVar∼ eq)
flip-Groundʳ g-∀ = g-∀

flip-GroundMatch : ∀ {Δ} {G A : Ty Δ} {μ : Env∼ Δ} {r : Var∼}
    {g : Groundʳ μ r G}
  → GroundMatch g A
  → GroundMatch (flip-Groundʳ g) A
flip-GroundMatch match-⇒ = match-⇒
flip-GroundMatch match-ι = match-ι
flip-GroundMatch match-X = match-X
flip-GroundMatch match-∀ = match-∀

private
  postulate
    funext : Extensionality 0ℓ 0ℓ

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
  flip-idᵐ = funext (λ X → refl)

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
sym∼ (_! ⦃ G ⦄ c ⦃ Ans ⦄ ⦃ match ⦄) =
  ？_ ⦃ flip-Groundʳ G ⦄ (sym∼ c) ⦃ Ans ⦄
    ⦃ flip-GroundMatch match ⦄
sym∼ (？_ ⦃ G ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) =
  _! ⦃ flip-Groundʳ G ⦄ (sym∼ c) ⦃ Bns ⦄
    ⦃ flip-GroundMatch match ⦄
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

  rename-Groundʳ : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
      {r : Var∼} {G : Ty Δ}
    → (ρ : Δ ⇒ʳ Δ′)
    → (∀ X → μ′ (ρ X) ≡ μ X)
    → Groundʳ μ r G
    → Groundʳ μ′ r (renameᵗ ρ G)
  rename-Groundʳ ρ eq g-⇒ = g-⇒
  rename-Groundʳ ρ eq g-ι = g-ι
  rename-Groundʳ ρ eq (g-X {X = X} eq-X) =
    g-X (trans (eq X) eq-X)
  rename-Groundʳ ρ eq g-∀ = g-∀

  rename-GroundMatch : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
      {r : Var∼} {G A : Ty Δ} {g : Groundʳ μ r G}
    → (ρ : Δ ⇒ʳ Δ′)
    → (eq : ∀ X → μ′ (ρ X) ≡ μ X)
    → GroundMatch g A
    → GroundMatch
        (rename-Groundʳ {μ = μ} {μ′ = μ′} ρ eq g) (renameᵗ ρ A)
  rename-GroundMatch ρ eq match-⇒ = match-⇒
  rename-GroundMatch ρ eq match-ι = match-ι
  rename-GroundMatch {μ = μ} {μ′ = μ′} ρ eq match-X = match-X
  rename-GroundMatch ρ eq match-∀ = match-∀

  rename∼ : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
      {A B : Ty Δ}
    → (ρ : Δ ⇒ʳ Δ′)
    → (∀ X → μ′ (ρ X) ≡ μ X)
    → μ ⊢ A ∼ B
    → μ′ ⊢ renameᵗ ρ A ∼ renameᵗ ρ B
  rename∼ ρ eq (id ★) = id ★
  rename∼ ρ eq (id (‵ ι)) = id (‵ ι)
  rename∼ ρ eq (id (＇ X)) = id (＇ (ρ X))
  rename∼ ρ eq (A∼A′ ↦ B∼B′) =
    rename∼ ρ eq A∼A′ ↦ rename∼ ρ eq B∼B′
  rename∼ ρ eq (∀ᶜ A∼B) =
    ∀ᶜ (rename∼ (extᵗ ρ) (extᵐ-rename ρ eq) A∼B)
  rename∼ {μ = μ} {μ′ = μ′} ρ eq
      (_! ⦃ g ⦄ c ⦃ Ans ⦄ ⦃ match ⦄) =
    _! ⦃ rename-Groundʳ ρ eq g ⦄ (rename∼ ρ eq c)
      ⦃ renameNonStar ρ Ans ⦄
      ⦃ rename-GroundMatch {μ = μ} {μ′ = μ′} ρ eq match ⦄
  rename∼ {μ = μ} {μ′ = μ′} ρ eq
      (？_ ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) =
    ？_ ⦃ rename-Groundʳ ρ eq g ⦄ (rename∼ ρ eq c)
      ⦃ renameNonStar ρ Bns ⦄
      ⦃ rename-GroundMatch {μ = μ} {μ′ = μ′} ρ eq match ⦄
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

renameᵐᶜ : ∀ {Δ Δ′} {μ : Env∼ Δ} {A B : Ty Δ}
  → (ρ : Δ ↪ᵗ Δ′)
  → μ ⊢ A ∼ B
  → renameEnv∼ ρ μ ⊢ renameᵗ (toRenameᵗ ρ) A ∼
      renameᵗ (toRenameᵗ ρ) B
renameᵐᶜ {μ = μ} ρ c = rename∼ (toRenameᵗ ρ)
  (renameEnv∼-preserves ρ μ) c

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

record SubstEnv∼ {Δ Δ′ : TyCtx}
    (μ : Env∼ Δ) (ν : Env∼ Δ′) (σ : Δ ⇒ˢ Δ′) : Set where
  constructor subst-env∼
  field
    self : ∀ X → ν ⊢ σ X ∼ σ X
    to-★ : ∀ X → μ X ≡ X∼★ → ν ⊢ σ X ∼ ★
    from-★ : ∀ X → μ X ≡ ★∼X → ν ⊢ ★ ∼ σ X

open SubstEnv∼

private

  ext-SubstEnv∼ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′}
    → SubstEnv∼ μ ν σ
    → SubstEnv∼ (extᵐ μ) (extᵐ ν) (extsᵗ σ)
  ext-SubstEnv∼ (subst-env∼ self to-★ from-★) =
    subst-env∼ self′ to-★′ from-★′
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

  inst-SubstEnv∼ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′}
    → SubstEnv∼ μ ν σ
    → SubstEnv∼ (instᵐ μ) (instᵐ ν) (extsᵗ σ)
  inst-SubstEnv∼ {ν = ν} (subst-env∼ self to-★ from-★) =
    subst-env∼ self′ to-★′ from-★′
    where
    self′ : ∀ X → instᵐ _ ⊢ extsᵗ _ X ∼ extsᵗ _ X
    self′ zero = id (＇ zero)
    self′ (suc X) = rename∼ suc (λ Y → refl) (self X)

    to-★′ : ∀ X
      → instᵐ _ X ≡ X∼★
      → instᵐ _ ⊢ extsᵗ _ X ∼ ★
    to-★′ zero eq =
      _! ⦃ g-X {μ = instᵐ ν} refl ⦄ (id (＇ zero))
    to-★′ (suc X) eq = rename∼ suc (λ Y → refl) (to-★ X eq)

    from-★′ : ∀ X
      → instᵐ _ X ≡ ★∼X
      → instᵐ _ ⊢ ★ ∼ extsᵗ _ X
    from-★′ zero ()
    from-★′ (suc X) eq =
      rename∼ suc (λ Y → refl) (from-★ X eq)

  gen-SubstEnv∼ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′}
    → SubstEnv∼ μ ν σ
    → SubstEnv∼ (genᵐ μ) (genᵐ ν) (extsᵗ σ)
  gen-SubstEnv∼ {ν = ν} (subst-env∼ self to-★ from-★) =
    subst-env∼ self′ to-★′ from-★′
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
      ？_ ⦃ g-X {μ = genᵐ ν} refl ⦄ (id (＇ zero))
    from-★′ (suc X) eq =
      rename∼ suc (λ Y → refl) (from-★ X eq)

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
      (？_ ⦃ g ⦄ c ⦃ Gns ⦄ ⦃ match ⦄) Ans =
    ⊥-elim (nonStar≢★ Ans refl)
  tag-source-nonvar-⇒ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) Ans =
    nonvar-all

  tag-source-nonvar-ι : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ} {ι}
    → μ ⊢ A ∼ (‵ ι)
    → NonStar A
    → NonVar A
  tag-source-nonvar-ι (id (‵ ι)) Ans = nonvar-base
  tag-source-nonvar-ι
      (？_ ⦃ g ⦄ c ⦃ Gns ⦄ ⦃ match ⦄) Ans =
    ⊥-elim (nonStar≢★ Ans refl)
  tag-source-nonvar-ι (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) Ans =
    nonvar-all

  untag-target-nonvar-⇒ : ∀ {Δ} {μ : Env∼ Δ} {B : Ty Δ}
    → μ ⊢ (★ ⇒ ★) ∼ B
    → NonStar B
    → NonVar B
  untag-target-nonvar-⇒ (c ↦ d) Bns = nonvar-fun
  untag-target-nonvar-⇒
      (_! ⦃ g ⦄ c ⦃ Gns ⦄ ⦃ match ⦄) Bns =
    ⊥-elim (nonStar≢★ Bns refl)
  untag-target-nonvar-⇒ (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) Bns =
    nonvar-all

  untag-target-nonvar-ι : ∀ {Δ} {μ : Env∼ Δ} {B : Ty Δ} {ι}
    → μ ⊢ (‵ ι) ∼ B
    → NonStar B
    → NonVar B
  untag-target-nonvar-ι (id (‵ ι)) Bns = nonvar-base
  untag-target-nonvar-ι
      (_! ⦃ g ⦄ c ⦃ Gns ⦄ ⦃ match ⦄) Bns =
    ⊥-elim (nonStar≢★ Bns refl)
  untag-target-nonvar-ι (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) Bns =
    nonvar-all

  subst-nonvar-nonstar : ∀ {Δ Δ′} {A : Ty Δ}
    → (σ : Δ ⇒ˢ Δ′)
    → NonVar A
    → NonStar A
    → NonStar (substᵗ σ A)
  subst-nonvar-nonstar σ nonvar-base Ans = nonstar-ι
  subst-nonvar-nonstar σ nonvar-star ()
  subst-nonvar-nonstar σ nonvar-fun Ans = nonstar-⇒
  subst-nonvar-nonstar σ nonvar-all Ans = nonstar-∀

  factor-inst-star : ∀ {Δ} {μ : Env∼ Δ} {A : Ty (suc Δ)}
    → (c : instᵐ μ ⊢ A ∼ ★)
    → NonVar A
    → zero ∈ᵗ A
    → μ ⊢ (`∀ A) ∼ ★
  factor-inst-star (id ★) Anv ()
  factor-inst-star
      (_! ⦃ g-⇒ ⦄ c ⦃ Ans ⦄ ⦃ match-⇒ ⦄) Anv z∈A =
    _! ⦃ g-⇒ ⦄ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c (λ ()))
      ⦃ nonstar-∀ ⦄ ⦃ match-⇒ ⦄
  factor-inst-star
      (_! ⦃ g-ι ⦄ c ⦃ Ans ⦄ ⦃ match-ι ⦄) Anv z∈A =
    _! ⦃ g-ι ⦄ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c (λ ()))
      ⦃ nonstar-∀ ⦄ ⦃ match-ι ⦄
  factor-inst-star
      (_! ⦃ g-X eq ⦄ c ⦃ Ans ⦄ ⦃ match-X ⦄) () z∈A
  factor-inst-star
      (_! ⦃ g-∀ ⦄ c ⦃ Ans ⦄ ⦃ match-∀ ⦄) Anv z∈A =
    _! ⦃ g-∀ ⦄ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c (λ ()))
      ⦃ nonstar-∀ ⦄ ⦃ match-∀ ⦄
  factor-inst-star (？_ ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) Anv ()
  factor-inst-star
      (inst_ ⦃ Anv′ ⦄ ⦃ z∈A′ ⦄ c ★≢★) Anv z∈A =
    ⊥-elim (★≢★ refl)

  factor-gen-star : ∀ {Δ} {μ : Env∼ Δ} {B : Ty (suc Δ)}
    → (c : genᵐ μ ⊢ ★ ∼ B)
    → NonVar B
    → zero ∈ᵗ B
    → μ ⊢ ★ ∼ (`∀ B)
  factor-gen-star (id ★) Bnv ()
  factor-gen-star (_! ⦃ g ⦄ c ⦃ () ⦄ ⦃ match ⦄) Bnv z∈B
  factor-gen-star
      (？_ ⦃ g-⇒ ⦄ c ⦃ Bns ⦄ ⦃ match-⇒ ⦄) Bnv z∈B =
    ？_ ⦃ g-⇒ ⦄ (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c (λ ()))
      ⦃ nonstar-∀ ⦄ ⦃ match-⇒ ⦄
  factor-gen-star
      (？_ ⦃ g-ι ⦄ c ⦃ Bns ⦄ ⦃ match-ι ⦄) Bnv z∈B =
    ？_ ⦃ g-ι ⦄ (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c (λ ()))
      ⦃ nonstar-∀ ⦄ ⦃ match-ι ⦄
  factor-gen-star
      (？_ ⦃ g-X eq ⦄ c ⦃ Bns ⦄ ⦃ match-X ⦄) () z∈B
  factor-gen-star
      (？_ ⦃ g-∀ ⦄ c ⦃ Bns ⦄ ⦃ match-∀ ⦄) Bnv z∈B =
    ？_ ⦃ g-∀ ⦄ (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c (λ ()))
      ⦃ nonstar-∀ ⦄ ⦃ match-∀ ⦄
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
subst∼ s (c ↦ d) = subst∼ s c ↦ subst∼ s d
subst∼ s (∀ᶜ c) = ∀ᶜ (subst∼ (ext-SubstEnv∼ s) c)
subst∼ {σ = σ} s
    (_! ⦃ g-⇒ ⦄ c ⦃ Ans ⦄ ⦃ match-⇒ ⦄) =
  _! ⦃ g-⇒ ⦄ (subst∼ s c)
    ⦃ subst-nonvar-nonstar σ (tag-source-nonvar-⇒ c Ans) Ans ⦄
    ⦃ match-⇒ ⦄
subst∼ {σ = σ} s
    (_! ⦃ g-ι ⦄ c ⦃ Ans ⦄ ⦃ match-ι ⦄) =
  _! ⦃ g-ι ⦄ (subst∼ s c)
    ⦃ subst-nonvar-nonstar σ (tag-source-nonvar-ι c Ans) Ans ⦄
    ⦃ match-ι ⦄
subst∼ s (_! ⦃ g-X {X = X} eq ⦄ c ⦃ Ans ⦄ ⦃ match-X ⦄) =
  to-★ s X eq
subst∼ s (_! ⦃ g-∀ ⦄ c ⦃ Ans ⦄ ⦃ match-∀ ⦄) =
  _! ⦃ g-∀ ⦄ (subst∼ s c) ⦃ nonstar-∀ ⦄ ⦃ match-∀ ⦄
subst∼ {σ = σ} s
    (？_ ⦃ g-⇒ ⦄ c ⦃ Bns ⦄ ⦃ match-⇒ ⦄) =
  ？_ ⦃ g-⇒ ⦄ (subst∼ s c)
    ⦃ subst-nonvar-nonstar σ (untag-target-nonvar-⇒ c Bns) Bns ⦄
    ⦃ match-⇒ ⦄
subst∼ {σ = σ} s
    (？_ ⦃ g-ι ⦄ c ⦃ Bns ⦄ ⦃ match-ι ⦄) =
  ？_ ⦃ g-ι ⦄ (subst∼ s c)
    ⦃ subst-nonvar-nonstar σ (untag-target-nonvar-ι c Bns) Bns ⦄
    ⦃ match-ι ⦄
subst∼ s (？_ ⦃ g-X {X = X} eq ⦄ c ⦃ Bns ⦄ ⦃ match-X ⦄) =
  from-★ s X eq
subst∼ s (？_ ⦃ g-∀ ⦄ c ⦃ Bns ⦄ ⦃ match-∀ ⦄) =
  ？_ ⦃ g-∀ ⦄ (subst∼ s c) ⦃ nonstar-∀ ⦄ ⦃ match-∀ ⦄
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
    | yes Bσ≡★ rewrite Bσ≡★ =
  factor-inst-star
    (subst-right-∼
      (trans (substᵗ-shift σ B) (cong (renameᵗ suc) Bσ≡★))
      (subst∼ (inst-SubstEnv∼ s) c))
    (substNonVar (extsᵗ σ) A-nonvar)
    (subst-∈ᵗ zero∈A var-∈)
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
    | yes Aσ≡★ rewrite Aσ≡★ =
  factor-gen-star
    (subst-left-∼
      (trans (substᵗ-shift σ A) (cong (renameᵗ suc) Aσ≡★))
      (subst∼ (gen-SubstEnv∼ s) c))
    (substNonVar (extsᵗ σ) B-nonvar)
    (subst-∈ᵗ zero∈B var-∈)
subst∼ s bot-elim = bot-elim
subst∼ s bot-intro = bot-intro

private

  close-inst-self : ∀ {Δ} {μ : Env∼ Δ} (X : TyVar (suc Δ))
    → μ ⊢ singleSubᵗ ★ X ∼ singleSubᵗ ★ X
  close-inst-self X = refl∼ (singleSubᵗ ★ X)

  close-inst-to-★ : ∀ {Δ} {μ : Env∼ Δ} (X : TyVar (suc Δ))
    → instᵐ μ X ≡ X∼★
    → μ ⊢ singleSubᵗ ★ X ∼ ★
  close-inst-to-★ zero eq = id ★
  close-inst-to-★ {μ = μ} (suc X) eq =
    _! ⦃ g-X eq ⦄ (id (＇ X))
      ⦃ nonstar-X ⦄ ⦃ match-X ⦄

  close-inst-from-★ : ∀ {Δ} {μ : Env∼ Δ} (X : TyVar (suc Δ))
    → instᵐ μ X ≡ ★∼X
    → μ ⊢ ★ ∼ singleSubᵗ ★ X
  close-inst-from-★ zero ()
  close-inst-from-★ {μ = μ} (suc X) eq =
    ？_ ⦃ g-X eq ⦄ (id (＇ X))
      ⦃ nonstar-X ⦄ ⦃ match-X ⦄

close-instᶜ : ∀ {Δ} {μ : Env∼ Δ} {A : Ty (suc Δ)} {B : Ty Δ}
  → instᵐ μ ⊢ A ∼ ⇑ᵗ B
  → μ ⊢ A [ ★ ]ᵗ ∼ B
syntax close-instᶜ c = c [ ★/0 ]ᶜ

close-instᶜ {B = B} c =
  subst-right-∼ (shift-openᵗ B ★)
    (subst∼
      (subst-env∼ close-inst-self close-inst-to-★ close-inst-from-★)
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
    _! ⦃ g-X eq ⦄ (id (＇ X))
      ⦃ nonstar-X ⦄ ⦃ match-X ⦄

  close-gen-from-★ : ∀ {Δ} {μ : Env∼ Δ} (X : TyVar (suc Δ))
    → genᵐ μ X ≡ ★∼X
    → μ ⊢ ★ ∼ singleSubᵗ ★ X
  close-gen-from-★ zero eq = id ★
  close-gen-from-★ {μ = μ} (suc X) eq =
    ？_ ⦃ g-X eq ⦄ (id (＇ X))
      ⦃ nonstar-X ⦄ ⦃ match-X ⦄

close-genᶜ : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ} {B : Ty (suc Δ)}
  → genᵐ μ ⊢ ⇑ᵗ A ∼ B
  → μ ⊢ A ∼ B [ ★ ]ᵗ
close-genᶜ {A = A} c =
  subst-left-∼ (shift-openᵗ A ★)
    (subst∼
      (subst-env∼ close-gen-self close-gen-to-★ close-gen-from-★)
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
    _! ⦃ g-X eq ⦄ (id (＇ X))
      ⦃ nonstar-X ⦄ ⦃ match-X ⦄

  open-from-★ : ∀ {Δ} {μ : Env∼ Δ} (C : Ty Δ)
      (X : TyVar (suc Δ))
    → extᵐ μ X ≡ ★∼X
    → μ ⊢ ★ ∼ singleSubᵗ C X
  open-from-★ C zero ()
  open-from-★ {μ = μ} C (suc X) eq =
    ？_ ⦃ g-X eq ⦄ (id (＇ X))
      ⦃ nonstar-X ⦄ ⦃ match-X ⦄

infixl 8 _[_]ᶜ
_[_]ᶜ : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty (suc Δ)}
  → extᵐ μ ⊢ A ∼ B
  → (C : Ty Δ)
  → μ ⊢ A [ C ]ᵗ ∼ B [ C ]ᵗ
_[_]ᶜ {μ = μ} c C =
  subst∼
    (subst-env∼ (open-self C) (open-to-★ {μ = μ} C)
      (open-from-★ C))
    c
