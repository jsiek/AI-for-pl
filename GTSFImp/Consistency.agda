module Consistency where

-- File Charter:
--   * Defines type consistency.

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Level using (0ℓ)
open import Data.Nat using (zero; suc)
open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)

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

data Groundʳ {Δ : TyCtx} : Ty Δ → Set where
  g-⇒ : Groundʳ (★ ⇒ ★)
  g-ι : ∀ {ι} → Groundʳ (‵ ι)

infix 4 _⊢_∼_

data _⊢_∼_ {Δ : TyCtx} (μ : Env∼ Δ) :
    Ty Δ → Ty Δ → Set where

  id∼ : ∀ {A}
    → Atom A
      ---------
    → μ ⊢ A ∼ A

  ⇒∼⇒ : ∀ {A A′ B B′}
    → μ ⊢ A ∼ A′
    → μ ⊢ B ∼ B′
      ---------------------------
    → μ ⊢ (A ⇒ B) ∼ (A′ ⇒ B′)

  ∀∼∀ : ∀ {A B}
    → extᵐ μ ⊢ A ∼ B
      -----------------------
    → μ ⊢ (`∀ A) ∼ (`∀ B)

  tag : ∀ {A G}
    → Groundʳ G
    → μ ⊢ A ∼ G
      -----------
    → μ ⊢ A ∼ ★

  untag : ∀ {G B}
    → Groundʳ G
    → μ ⊢ G ∼ B
      -----------
    → μ ⊢ ★ ∼ B

  X∼★ : ∀ {X}
    → μ X ≡ X∼★
      ----------------
    → μ ⊢ ＇ X ∼ ★

  ★∼X : ∀ {X}
    → μ X ≡ ★∼X
      ----------------
    → μ ⊢ ★ ∼ ＇ X

  ∀∼ : ∀ {A B}
    → instᵐ μ ⊢ A ∼ ⇑ᵗ B
    → NonVar A
    → zero ∈ᵗ A
      ---------------------------
    → μ ⊢ (`∀ A) ∼ B

  ∼∀ : ∀ {A B}
    → genᵐ μ ⊢ ⇑ᵗ A ∼ B
    → NonVar B
    → zero ∈ᵗ B
      ---------------------------
    → μ ⊢ A ∼ (`∀ B)

infix 4 _∼_

_∼_ : ∀ {Δ} → Ty Δ → Ty Δ → Set
A ∼ B = idᶜ ⊢ A ∼ B

idᵍ : ∀ {Δ} {G : Ty Δ} {μ : Env∼ Δ}
  → Groundʳ G
  → μ ⊢ G ∼ G
idᵍ g-⇒ = ⇒∼⇒ (id∼ ★) (id∼ ★)
idᵍ g-ι = id∼ (‵ _)

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
sym∼ (id∼ a) = id∼ a
sym∼ (⇒∼⇒ c d) = ⇒∼⇒ (sym∼ c) (sym∼ d)
sym∼ (∀∼∀ c) = ∀∼∀ (transport-env∼ flip-extᵐ (sym∼ c))
sym∼ (tag G c) = untag G (sym∼ c)
sym∼ (untag G c) = tag G (sym∼ c)
sym∼ (X∼★ eq) = ★∼X (cong flipVar∼ eq)
sym∼ (★∼X eq) = X∼★ (cong flipVar∼ eq)
sym∼ (∀∼ c A-nonvar zero∈A) =
  ∼∀ (transport-env∼ flip-instᵐ (sym∼ c)) A-nonvar zero∈A
sym∼ (∼∀ c B-nonvar zero∈B) =
  ∀∼ (transport-env∼ flip-genᵐ (sym∼ c)) B-nonvar zero∈B

symᶜ : ∀ {Δ} {A B : Ty Δ} → A ∼ B → B ∼ A
symᶜ c = transport-env∼ flip-idᵐ (sym∼ c)

private

  rename-∈ᵗ : ∀ {Δ Δ′} {X : TyVar Δ} {A : Ty Δ}
    → (ρ : Δ ⇒ʳ Δ′)
    → X ∈ᵗ A
    → ρ X ∈ᵗ renameᵗ ρ A
  rename-∈ᵗ ρ var-∈ = var-∈
  rename-∈ᵗ ρ (∈-fun-left X∈A) = ∈-fun-left (rename-∈ᵗ ρ X∈A)
  rename-∈ᵗ ρ (∈-fun-right X∈B) =
    ∈-fun-right (rename-∈ᵗ ρ X∈B)
  rename-∈ᵗ ρ (∈-all X∈A) = ∈-all (rename-∈ᵗ (extᵗ ρ) X∈A)

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

  rename∼ : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
      {A B : Ty Δ}
    → (ρ : Δ ⇒ʳ Δ′)
    → (∀ X → μ′ (ρ X) ≡ μ X)
    → μ ⊢ A ∼ B
    → μ′ ⊢ renameᵗ ρ A ∼ renameᵗ ρ B
  rename∼ ρ eq (id∼ ★) = id∼ ★
  rename∼ ρ eq (id∼ (‵ ι)) = id∼ (‵ ι)
  rename∼ ρ eq (id∼ (＇ X)) = id∼ (＇ (ρ X))
  rename∼ ρ eq (⇒∼⇒ A∼A′ B∼B′) =
    ⇒∼⇒ (rename∼ ρ eq A∼A′) (rename∼ ρ eq B∼B′)
  rename∼ ρ eq (∀∼∀ A∼B) =
    ∀∼∀ (rename∼ (extᵗ ρ) (extᵐ-rename ρ eq) A∼B)
  rename∼ ρ eq (tag g-⇒ c) = tag g-⇒ (rename∼ ρ eq c)
  rename∼ ρ eq (tag g-ι c) = tag g-ι (rename∼ ρ eq c)
  rename∼ ρ eq (untag g-⇒ c) = untag g-⇒ (rename∼ ρ eq c)
  rename∼ ρ eq (untag g-ι c) = untag g-ι (rename∼ ρ eq c)
  rename∼ ρ eq (X∼★ eq-X) = X∼★ (trans (eq _) eq-X)
  rename∼ ρ eq (★∼X eq-X) = ★∼X (trans (eq _) eq-X)
  rename∼ ρ eq (∀∼ {B = B} A∼B A-nonvar zero∈A) =
    ∀∼
      (subst-right-∼ (renameᵗ-shift ρ B)
        (rename∼ (extᵗ ρ) (instᵐ-rename ρ eq) A∼B))
      (renameNonVar (extᵗ ρ) A-nonvar)
      (rename-∈ᵗ (extᵗ ρ) zero∈A)
  rename∼ ρ eq (∼∀ {A = A} A∼B B-nonvar zero∈B) =
    ∼∀
      (subst-left-∼ (renameᵗ-shift ρ A)
        (rename∼ (extᵗ ρ) (genᵐ-rename ρ eq) A∼B))
      (renameNonVar (extᵗ ρ) B-nonvar)
      (rename-∈ᵗ (extᵗ ρ) zero∈B)

renameᶜ : ∀ {Δ Δ′} {A B : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → A ∼ B
  → renameᵗ ρ A ∼ renameᵗ ρ B
renameᶜ ρ c = rename∼ ρ (λ X → refl) c

refl∼ : ∀ {Δ} {μ : Env∼ Δ} (A : Ty Δ) → μ ⊢ A ∼ A
refl∼ (＇ X) = id∼ (＇ X)
refl∼ (‵ ι) = id∼ (‵ ι)
refl∼ ★ = id∼ ★
refl∼ (A ⇒ B) = ⇒∼⇒ (refl∼ A) (refl∼ B)
refl∼ (`∀ A) = ∀∼∀ (refl∼ A)

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
    self′ zero = id∼ (＇ zero)
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
  inst-SubstEnv∼ (subst-env∼ self to-★ from-★) =
    subst-env∼ self′ to-★′ from-★′
    where
    self′ : ∀ X → instᵐ _ ⊢ extsᵗ _ X ∼ extsᵗ _ X
    self′ zero = id∼ (＇ zero)
    self′ (suc X) = rename∼ suc (λ Y → refl) (self X)

    to-★′ : ∀ X
      → instᵐ _ X ≡ X∼★
      → instᵐ _ ⊢ extsᵗ _ X ∼ ★
    to-★′ zero eq = X∼★ refl
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
  gen-SubstEnv∼ (subst-env∼ self to-★ from-★) =
    subst-env∼ self′ to-★′ from-★′
    where
    self′ : ∀ X → genᵐ _ ⊢ extsᵗ _ X ∼ extsᵗ _ X
    self′ zero = id∼ (＇ zero)
    self′ (suc X) = rename∼ suc (λ Y → refl) (self X)

    to-★′ : ∀ X
      → genᵐ _ X ≡ X∼★
      → genᵐ _ ⊢ extsᵗ _ X ∼ ★
    to-★′ zero ()
    to-★′ (suc X) eq = rename∼ suc (λ Y → refl) (to-★ X eq)

    from-★′ : ∀ X
      → genᵐ _ X ≡ ★∼X
      → genᵐ _ ⊢ ★ ∼ extsᵗ _ X
    from-★′ zero eq = ★∼X refl
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
  subst-∈ᵗ (∈-fun-right X∈B) Y∈σX =
    ∈-fun-right (subst-∈ᵗ X∈B Y∈σX)
  subst-∈ᵗ {σ = σ} (∈-all X∈A) Y∈σX =
    ∈-all (subst-∈ᵗ {σ = extsᵗ σ} X∈A (rename-∈ᵗ suc Y∈σX))

subst∼ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
    {σ : Δ ⇒ˢ Δ′} {A B : Ty Δ}
  → SubstEnv∼ μ ν σ
  → μ ⊢ A ∼ B
  → ν ⊢ substᵗ σ A ∼ substᵗ σ B
subst∼ s (id∼ ★) = id∼ ★
subst∼ s (id∼ (‵ ι)) = id∼ (‵ ι)
subst∼ s (id∼ (＇ X)) = self s X
subst∼ s (⇒∼⇒ c d) = ⇒∼⇒ (subst∼ s c) (subst∼ s d)
subst∼ s (∀∼∀ c) = ∀∼∀ (subst∼ (ext-SubstEnv∼ s) c)
subst∼ s (tag g-⇒ c) = tag g-⇒ (subst∼ s c)
subst∼ s (tag g-ι c) = tag g-ι (subst∼ s c)
subst∼ s (untag g-⇒ c) = untag g-⇒ (subst∼ s c)
subst∼ s (untag g-ι c) = untag g-ι (subst∼ s c)
subst∼ s (X∼★ {X = X} eq) = to-★ s X eq
subst∼ s (★∼X {X = X} eq) = from-★ s X eq
subst∼ {σ = σ} s (∀∼ {B = B} c A-nonvar zero∈A) =
  ∀∼
    (subst-right-∼ (substᵗ-shift σ B)
      (subst∼ (inst-SubstEnv∼ s) c))
    (substNonVar (extsᵗ σ) A-nonvar)
    (subst-∈ᵗ zero∈A var-∈)
subst∼ {σ = σ} s (∼∀ {A = A} c B-nonvar zero∈B) =
  ∼∀
    (subst-left-∼ (substᵗ-shift σ A)
      (subst∼ (gen-SubstEnv∼ s) c))
    (substNonVar (extsᵗ σ) B-nonvar)
    (subst-∈ᵗ zero∈B var-∈)

private

  open-self : ∀ {Δ} (C : Ty Δ) (X : TyVar (suc Δ))
    → idᶜ ⊢ singleSubᵗ C X ∼ singleSubᵗ C X
  open-self C X = refl∼ (singleSubᵗ C X)

  open-to-★ : ∀ {Δ} (C : Ty Δ) (X : TyVar (suc Δ))
    → extᵐ idᶜ X ≡ X∼★
    → idᶜ ⊢ singleSubᵗ C X ∼ ★
  open-to-★ C zero ()
  open-to-★ C (suc X) ()

  open-from-★ : ∀ {Δ} (C : Ty Δ) (X : TyVar (suc Δ))
    → extᵐ idᶜ X ≡ ★∼X
    → idᶜ ⊢ ★ ∼ singleSubᵗ C X
  open-from-★ C zero ()
  open-from-★ C (suc X) ()

infixl 8 _[_]ᶜ
_[_]ᶜ : ∀ {Δ} {A B : Ty (suc Δ)}
  → extᵐ idᶜ ⊢ A ∼ B
  → (C : Ty Δ)
  → A [ C ]ᵗ ∼ B [ C ]ᵗ
c [ C ]ᶜ =
  subst∼
    (subst-env∼ (open-self C) (open-to-★ C) (open-from-★ C))
    c
