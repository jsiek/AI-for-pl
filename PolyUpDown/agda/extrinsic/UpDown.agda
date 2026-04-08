module UpDown where

-- File Charter:
--   * Raw widening/narrowing syntax and a separate well-typed judgment in extrinsic style.
--   * Theorems whose main subject is `_⊑_`, `_⊒_`, and their well-typed interpretation.
--   * No generic `Ty` substitution algebra (put that in `TypeProperties`) and no
--   * store-structural transport lemmas (put those in `Store`).
-- Note to self:
--   * Keep `_⊑_`/`_⊒_` free of store/permission indices; encode invariants only in
--     the well-typed layer.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)

open import Types
open import TypeProperties
open import Store

Label : Set
Label = ℕ

------------------------------------------------------------------------
-- Permissions as explicit seal membership in bool lists
------------------------------------------------------------------------

infix 4 _∈_ _∉_

data _∈_ : Seal → List Bool → Set where
  here  : ∀ {P} → zero ∈ (true ∷ P)
  there : ∀ {α b P} → α ∈ P → suc α ∈ (b ∷ P)

_∉_ : Seal → List Bool → Set
α ∉ P = α ∈ P → ⊥

⊢_ok_ : ∀ {G : Ty} → Ground G → List Bool → Set
⊢ (｀ α) ok Ξ = α ∈ Ξ
⊢ (‵ ι) ok Ξ = ⊤
⊢ ★⇒★ ok Ξ = ⊤

------------------------------------------------------------------------
-- Raw widening/narrowing (no indices)
------------------------------------------------------------------------

infixr 7 _↦_
infixl 6 _；_
infix 3 _⊑_ _⊒_

mutual
  data _⊑_ : Ty → Ty → Set where
    tag : ∀ {G}
      → Ground G
      → G ⊑ ★

    unseal : ∀ {α A}
      → ｀ α ⊑ A

    _↦_ : ∀ {A A′ B B′}
      → A′ ⊒ A
      → B ⊑ B′
      → (A ⇒ B) ⊑ (A′ ⇒ B′)

    ∀ᵖ : ∀ {A B}
      → A ⊑ B
      → `∀ A ⊑ `∀ B

    ν_ : ∀ {A B}
      → ((⇑ˢ A) [ ｀ zero ]ᵗ ⊑ ⇑ˢ B)
      → (`∀ A) ⊑ B

    id : ∀ {A}
      → A ⊑ A

    _；_ : ∀ {A B C}
      → A ⊑ B
      → B ⊑ C
      → A ⊑ C

  data _⊒_ : Ty → Ty → Set where
    untag : ∀ {G}
      → Ground G
      → Label
      → ★ ⊒ G

    seal : ∀ {α A}
      → A ⊒ ｀ α

    _↦_ : ∀ {A A′ B B′}
      → A′ ⊑ A
      → B ⊒ B′
      → (A ⇒ B) ⊒ (A′ ⇒ B′)

    ∀ᵖ : ∀ {A B}
      → A ⊒ B
      → `∀ A ⊒ `∀ B

    ν_ : ∀ {A B}
      → (⇑ˢ B ⊒ (⇑ˢ A) [ ｀ zero ]ᵗ)
      → B ⊒ `∀ A

    id : ∀ {A}
      → A ⊒ A

    _；_ : ∀ {A B C}
      → A ⊒ B
      → B ⊒ C
      → A ⊒ C

------------------------------------------------------------------------
-- Well-typed widening/narrowing (recaptures intrinsic invariants)
------------------------------------------------------------------------

infix 3 _∣_∣_⊢↑_ _∣_∣_⊢↓_

mutual
  data _∣_∣_⊢↑_ (Σ : Store) (Φ Ξ : List Bool) : ∀ {A B} → A ⊑ B → Set where
    wt-tag : ∀ {G}
      → (g : Ground G)
      → ⊢ g ok Ξ
      → Σ ∣ Φ ∣ Ξ ⊢↑ tag g

    wt-unseal : ∀ {α A}
      → Σ ∋ˢ α ⦂ A
      → α ∈ Φ
      → Σ ∣ Φ ∣ Ξ ⊢↑ unseal {α} {A}

    wt-↦ : ∀ {A A′ B B′}
      {p : A′ ⊒ A}
      {q : B ⊑ B′}
      → Σ ∣ Φ ∣ Ξ ⊢↓ p
      → Σ ∣ Φ ∣ Ξ ⊢↑ q
      → Σ ∣ Φ ∣ Ξ ⊢↑ (p ↦ q)

    wt-∀ : ∀ {A B}
      {p : A ⊑ B}
      → ⟰ᵗ Σ ∣ Φ ∣ Ξ ⊢↑ p
      → Σ ∣ Φ ∣ Ξ ⊢↑ (∀ᵖ p)

    wt-ν : ∀ {A B}
      {p : (⇑ˢ A) [ ｀ zero ]ᵗ ⊑ ⇑ˢ B}
      → ((zero , ★) ∷ ⟰ˢ Σ) ∣ (true ∷ Φ) ∣ (false ∷ Ξ) ⊢↑ p
      → Σ ∣ Φ ∣ Ξ ⊢↑ (ν_ {A = A} {B = B} p)

    wt-id : ∀ {A}
      → Σ ∣ Φ ∣ Ξ ⊢↑ (id {A})

    wt-； : ∀ {A B C}
      {p : A ⊑ B}
      {q : B ⊑ C}
      → Σ ∣ Φ ∣ Ξ ⊢↑ p
      → Σ ∣ Φ ∣ Ξ ⊢↑ q
      → Σ ∣ Φ ∣ Ξ ⊢↑ (p ； q)

  data _∣_∣_⊢↓_ (Σ : Store) (Φ Ξ : List Bool) : ∀ {A B} → A ⊒ B → Set where
    wt-untag : ∀ {G}
      → (g : Ground G)
      → ⊢ g ok Ξ
      → (ℓ : Label)
      → Σ ∣ Φ ∣ Ξ ⊢↓ (untag g ℓ)

    wt-seal : ∀ {α A}
      → Σ ∋ˢ α ⦂ A
      → α ∈ Φ
      → Σ ∣ Φ ∣ Ξ ⊢↓ (seal {α} {A})

    wt-↦ : ∀ {A A′ B B′}
      {p : A′ ⊑ A}
      {q : B ⊒ B′}
      → Σ ∣ Φ ∣ Ξ ⊢↑ p
      → Σ ∣ Φ ∣ Ξ ⊢↓ q
      → Σ ∣ Φ ∣ Ξ ⊢↓ (p ↦ q)

    wt-∀ : ∀ {A B}
      {p : A ⊒ B}
      → ⟰ᵗ Σ ∣ Φ ∣ Ξ ⊢↓ p
      → Σ ∣ Φ ∣ Ξ ⊢↓ (∀ᵖ p)

    wt-ν : ∀ {A B}
      {p : ⇑ˢ B ⊒ (⇑ˢ A) [ ｀ zero ]ᵗ}
      → ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (false ∷ Φ) ∣ (true ∷ Ξ) ⊢↓ p
      → Σ ∣ Φ ∣ Ξ ⊢↓ (ν_ {A = A} {B = B} p)

    wt-id : ∀ {A}
      → Σ ∣ Φ ∣ Ξ ⊢↓ (id {A})

    wt-； : ∀ {A B C}
      {p : A ⊒ B}
      {q : B ⊒ C}
      → Σ ∣ Φ ∣ Ξ ⊢↓ p
      → Σ ∣ Φ ∣ Ξ ⊢↓ q
      → Σ ∣ Φ ∣ Ξ ⊢↓ (p ； q)

------------------------------------------------------------------------
-- Transport helpers
------------------------------------------------------------------------

RenOk : Renameˢ → List Bool → List Bool → Set
RenOk ρ P P′ = ∀ {α} → α ∈ P → ρ α ∈ P′

RenOk-id : ∀ {P : List Bool} → RenOk (λ α → α) P P
RenOk-id p = p

RenOk-ext-true :
  ∀ {ρ : Renameˢ} {P P′ : List Bool} →
  RenOk ρ P P′ →
  RenOk (extˢ ρ) (true ∷ P) (true ∷ P′)
RenOk-ext-true ok {zero} here = here
RenOk-ext-true ok {suc α} (there p) = there (ok p)

RenOk-ext-false :
  ∀ {ρ : Renameˢ} {P P′ : List Bool} →
  RenOk ρ P P′ →
  RenOk (extˢ ρ) (false ∷ P) (false ∷ P′)
RenOk-ext-false ok {zero} ()
RenOk-ext-false ok {suc α} (there p) = there (ok p)

RenOk-singleSealEnv-true :
  ∀ {P : List Bool} {α : Seal} →
  α ∈ P →
  RenOk (singleSealEnv α) (true ∷ P) P
RenOk-singleSealEnv-true α∈P here = α∈P
RenOk-singleSealEnv-true α∈P (there p) = p

RenOk-singleSealEnv-false :
  ∀ {P : List Bool} {α : Seal} →
  RenOk (singleSealEnv α) (false ∷ P) P
RenOk-singleSealEnv-false {P = P} {α = α} {zero} ()
RenOk-singleSealEnv-false {P = P} {α = α} {suc β} (there p) = p

renameᵗ-ground-ok :
  ∀ {G : Ty}
  (ρ : Renameᵗ) (g : Ground G) {Ξ : List Bool} →
  ⊢ g ok Ξ →
  ⊢ renameᵗ-ground ρ g ok Ξ
renameᵗ-ground-ok ρ (｀ α) gok = gok
renameᵗ-ground-ok ρ (‵ ι) gok = gok
renameᵗ-ground-ok ρ ★⇒★ gok = gok

substᵗ-ground-ok :
  ∀ {G : Ty}
  (σ : Substᵗ) (g : Ground G) {Ξ : List Bool} →
  ⊢ g ok Ξ →
  ⊢ substᵗ-ground σ g ok Ξ
substᵗ-ground-ok σ (｀ α) gok = gok
substᵗ-ground-ok σ (‵ ι) gok = gok
substᵗ-ground-ok σ ★⇒★ gok = gok

renameˢ-ground-ok :
  ∀ {G : Ty}
  (ρ : Renameˢ) {Ξ Ξ′ : List Bool} →
  RenOk ρ Ξ Ξ′ →
  (g : Ground G) →
  ⊢ g ok Ξ →
  ⊢ renameˢ-ground ρ g ok Ξ′
renameˢ-ground-ok ρ ok (｀ α) gok = ok gok
renameˢ-ground-ok ρ ok (‵ ι) gok = gok
renameˢ-ground-ok ρ ok ★⇒★ gok = gok

------------------------------------------------------------------------
-- Raw coercion transport
------------------------------------------------------------------------

cast⊑ :
  ∀ {A A′ B B′ : Ty} →
  A ≡ A′ →
  B ≡ B′ →
  A ⊑ B →
  A′ ⊑ B′
cast⊑ refl refl p = p

cast⊒ :
  ∀ {A A′ B B′ : Ty} →
  A ≡ A′ →
  B ≡ B′ →
  A ⊒ B →
  A′ ⊒ B′
cast⊒ refl refl p = p

mutual
  rename⊑ᵗ : ∀ {A B} → (ρ : Renameᵗ) → A ⊑ B → renameᵗ ρ A ⊑ renameᵗ ρ B
  rename⊑ᵗ ρ (tag g) = tag (renameᵗ-ground ρ g)
  rename⊑ᵗ ρ (unseal {α} {A}) = unseal {α} {renameᵗ ρ A}
  rename⊑ᵗ ρ (p ↦ q) = rename⊒ᵗ ρ p ↦ rename⊑ᵗ ρ q
  rename⊑ᵗ ρ (∀ᵖ p) = ∀ᵖ (rename⊑ᵗ (extᵗ ρ) p)
  rename⊑ᵗ ρ (ν_ {A = A} {B = B} p) =
    ν
      (cast⊑
        (renameᵗ-ν-src ρ A)
        (renameᵗ-⇑ˢ ρ B)
        (rename⊑ᵗ ρ p))
  rename⊑ᵗ ρ id = id
  rename⊑ᵗ ρ (p ； q) = rename⊑ᵗ ρ p ； rename⊑ᵗ ρ q

  rename⊒ᵗ : ∀ {A B} → (ρ : Renameᵗ) → A ⊒ B → renameᵗ ρ A ⊒ renameᵗ ρ B
  rename⊒ᵗ ρ (untag g ℓ) = untag (renameᵗ-ground ρ g) ℓ
  rename⊒ᵗ ρ (seal {α} {A}) = seal {α} {renameᵗ ρ A}
  rename⊒ᵗ ρ (p ↦ q) = rename⊑ᵗ ρ p ↦ rename⊒ᵗ ρ q
  rename⊒ᵗ ρ (∀ᵖ p) = ∀ᵖ (rename⊒ᵗ (extᵗ ρ) p)
  rename⊒ᵗ ρ (ν_ {A = A} {B = B} p) =
    ν
      (cast⊒
        (renameᵗ-⇑ˢ ρ B)
        (renameᵗ-ν-src ρ A)
        (rename⊒ᵗ ρ p))
  rename⊒ᵗ ρ id = id
  rename⊒ᵗ ρ (p ； q) = rename⊒ᵗ ρ p ； rename⊒ᵗ ρ q

mutual
  rename⊑ˢ : ∀ {A B} → (ρ : Renameˢ) → A ⊑ B → renameˢ ρ A ⊑ renameˢ ρ B
  rename⊑ˢ ρ (tag g) = tag (renameˢ-ground ρ g)
  rename⊑ˢ ρ (unseal {α} {A}) = unseal {ρ α} {renameˢ ρ A}
  rename⊑ˢ ρ (p ↦ q) = rename⊒ˢ ρ p ↦ rename⊑ˢ ρ q
  rename⊑ˢ ρ (∀ᵖ p) = ∀ᵖ (rename⊑ˢ ρ p)
  rename⊑ˢ ρ (ν_ {A = A} {B = B} p) =
    ν
      (cast⊑
        (renameˢ-ν-src ρ A)
        (renameˢ-ext-⇑ˢ ρ B)
        (rename⊑ˢ (extˢ ρ) p))
  rename⊑ˢ ρ id = id
  rename⊑ˢ ρ (p ； q) = rename⊑ˢ ρ p ； rename⊑ˢ ρ q

  rename⊒ˢ : ∀ {A B} → (ρ : Renameˢ) → A ⊒ B → renameˢ ρ A ⊒ renameˢ ρ B
  rename⊒ˢ ρ (untag g ℓ) = untag (renameˢ-ground ρ g) ℓ
  rename⊒ˢ ρ (seal {α} {A}) = seal {ρ α} {renameˢ ρ A}
  rename⊒ˢ ρ (p ↦ q) = rename⊑ˢ ρ p ↦ rename⊒ˢ ρ q
  rename⊒ˢ ρ (∀ᵖ p) = ∀ᵖ (rename⊒ˢ ρ p)
  rename⊒ˢ ρ (ν_ {A = A} {B = B} p) =
    ν
      (cast⊒
        (renameˢ-ext-⇑ˢ ρ B)
        (renameˢ-ν-src ρ A)
        (rename⊒ˢ (extˢ ρ) p))
  rename⊒ˢ ρ id = id
  rename⊒ˢ ρ (p ； q) = rename⊒ˢ ρ p ； rename⊒ˢ ρ q

mutual
  subst⊑ᵗ : ∀ {A B} → (σ : Substᵗ) → A ⊑ B → substᵗ σ A ⊑ substᵗ σ B
  subst⊑ᵗ σ (tag g) = tag (substᵗ-ground σ g)
  subst⊑ᵗ σ (unseal {α} {A}) = unseal {α} {substᵗ σ A}
  subst⊑ᵗ σ (p ↦ q) = subst⊒ᵗ σ p ↦ subst⊑ᵗ σ q
  subst⊑ᵗ σ (∀ᵖ p) = ∀ᵖ (subst⊑ᵗ (extsᵗ σ) p)
  subst⊑ᵗ σ (ν_ {A = A} {B = B} p) =
    ν
      (cast⊑
        (substᵗ-ν-src σ A)
        (substᵗ-⇑ˢ σ B)
        (subst⊑ᵗ (liftSubstˢ σ) p))
  subst⊑ᵗ σ id = id
  subst⊑ᵗ σ (p ； q) = subst⊑ᵗ σ p ； subst⊑ᵗ σ q

  subst⊒ᵗ : ∀ {A B} → (σ : Substᵗ) → A ⊒ B → substᵗ σ A ⊒ substᵗ σ B
  subst⊒ᵗ σ (untag g ℓ) = untag (substᵗ-ground σ g) ℓ
  subst⊒ᵗ σ (seal {α} {A}) = seal {α} {substᵗ σ A}
  subst⊒ᵗ σ (p ↦ q) = subst⊑ᵗ σ p ↦ subst⊒ᵗ σ q
  subst⊒ᵗ σ (∀ᵖ p) = ∀ᵖ (subst⊒ᵗ (extsᵗ σ) p)
  subst⊒ᵗ σ (ν_ {A = A} {B = B} p) =
    ν
      (cast⊒
        (substᵗ-⇑ˢ σ B)
        (substᵗ-ν-src σ A)
        (subst⊒ᵗ (liftSubstˢ σ) p))
  subst⊒ᵗ σ id = id
  subst⊒ᵗ σ (p ； q) = subst⊒ᵗ σ p ； subst⊒ᵗ σ q

------------------------------------------------------------------------
-- Typed-judgment transport helpers
------------------------------------------------------------------------

castWt⊑ :
  ∀ {Σ Σ′ : Store}{Φ Φ′ Ξ Ξ′ : List Bool}{A B : Ty}{p : A ⊑ B} →
  Σ ≡ Σ′ →
  Φ ≡ Φ′ →
  Ξ ≡ Ξ′ →
  Σ ∣ Φ ∣ Ξ ⊢↑ p →
  Σ′ ∣ Φ′ ∣ Ξ′ ⊢↑ p
castWt⊑ refl refl refl h = h

castWt⊒ :
  ∀ {Σ Σ′ : Store}{Φ Φ′ Ξ Ξ′ : List Bool}{A B : Ty}{p : A ⊒ B} →
  Σ ≡ Σ′ →
  Φ ≡ Φ′ →
  Ξ ≡ Ξ′ →
  Σ ∣ Φ ∣ Ξ ⊢↓ p →
  Σ′ ∣ Φ′ ∣ Ξ′ ⊢↓ p
castWt⊒ refl refl refl h = h

castWt⊑-raw :
  ∀ {Σ : Store}{Φ Ξ : List Bool}{A A′ B B′ : Ty}{p : A ⊑ B} →
  (A≡A′ : A ≡ A′) →
  (B≡B′ : B ≡ B′) →
  Σ ∣ Φ ∣ Ξ ⊢↑ p →
  Σ ∣ Φ ∣ Ξ ⊢↑ cast⊑ A≡A′ B≡B′ p
castWt⊑-raw refl refl h = h

castWt⊒-raw :
  ∀ {Σ : Store}{Φ Ξ : List Bool}{A A′ B B′ : Ty}{p : A ⊒ B} →
  (A≡A′ : A ≡ A′) →
  (B≡B′ : B ≡ B′) →
  Σ ∣ Φ ∣ Ξ ⊢↓ p →
  Σ ∣ Φ ∣ Ξ ⊢↓ cast⊒ A≡A′ B≡B′ p
castWt⊒-raw refl refl h = h

------------------------------------------------------------------------
-- Type-variable renaming for well-typed widening and narrowing
------------------------------------------------------------------------

mutual
  ⊑-renameᵗ :
    ∀ {Σ : Store}{Φ Ξ : List Bool}{A B}
    {p : A ⊑ B} →
    (ρ : Renameᵗ) →
    Σ ∣ Φ ∣ Ξ ⊢↑ p →
    renameStoreᵗ ρ Σ ∣ Φ ∣ Ξ ⊢↑ rename⊑ᵗ ρ p
  ⊑-renameᵗ ρ (wt-tag g gokΞ) =
    wt-tag (renameᵗ-ground ρ g) (renameᵗ-ground-ok ρ g gokΞ)
  ⊑-renameᵗ ρ (wt-unseal h α∈Φ) = wt-unseal (renameLookupᵗ ρ h) α∈Φ
  ⊑-renameᵗ ρ (wt-↦ p q) = wt-↦ (⊒-renameᵗ ρ p) (⊑-renameᵗ ρ q)
  ⊑-renameᵗ {Σ = Σ} ρ (wt-∀ p) =
    wt-∀
      (castWt⊑
        (renameStoreᵗ-ext-⟰ᵗ ρ Σ)
        refl
        refl
        (⊑-renameᵗ (extᵗ ρ) p))
  ⊑-renameᵗ {Σ = Σ} ρ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊑
        (renameStoreᵗ-ν ρ Σ)
        refl
        refl
        (castWt⊑-raw
          (renameᵗ-ν-src ρ A)
          (renameᵗ-⇑ˢ ρ B)
          (⊑-renameᵗ ρ p)))
  ⊑-renameᵗ ρ wt-id = wt-id
  ⊑-renameᵗ ρ (wt-； p q) = wt-； (⊑-renameᵗ ρ p) (⊑-renameᵗ ρ q)

  ⊒-renameᵗ :
    ∀ {Σ : Store}{Φ Ξ : List Bool}{A B}
    {p : A ⊒ B} →
    (ρ : Renameᵗ) →
    Σ ∣ Φ ∣ Ξ ⊢↓ p →
    renameStoreᵗ ρ Σ ∣ Φ ∣ Ξ ⊢↓ rename⊒ᵗ ρ p
  ⊒-renameᵗ ρ (wt-untag g gokΞ ℓ) =
    wt-untag (renameᵗ-ground ρ g) (renameᵗ-ground-ok ρ g gokΞ) ℓ
  ⊒-renameᵗ ρ (wt-seal h α∈Φ) = wt-seal (renameLookupᵗ ρ h) α∈Φ
  ⊒-renameᵗ ρ (wt-↦ p q) = wt-↦ (⊑-renameᵗ ρ p) (⊒-renameᵗ ρ q)
  ⊒-renameᵗ {Σ = Σ} ρ (wt-∀ p) =
    wt-∀
      (castWt⊒
        (renameStoreᵗ-ext-⟰ᵗ ρ Σ)
        refl
        refl
        (⊒-renameᵗ (extᵗ ρ) p))
  ⊒-renameᵗ {Σ = Σ} ρ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊒
        (renameStoreᵗ-ν ρ Σ)
        refl
        refl
        (castWt⊒-raw
          (renameᵗ-⇑ˢ ρ B)
          (renameᵗ-ν-src ρ A)
          (⊒-renameᵗ ρ p)))
  ⊒-renameᵗ ρ wt-id = wt-id
  ⊒-renameᵗ ρ (wt-； p q) = wt-； (⊒-renameᵗ ρ p) (⊒-renameᵗ ρ q)

------------------------------------------------------------------------
-- Seal renaming for well-typed widening and narrowing
------------------------------------------------------------------------

mutual
  ⊑-renameˢ :
    ∀ {Σ : Store}
      {Φ Ξ : List Bool}{Φ′ Ξ′ : List Bool}{A B}
      {p : A ⊑ B} →
    (ρ : Renameˢ) →
    RenOk ρ Φ Φ′ →
    RenOk ρ Ξ Ξ′ →
    Σ ∣ Φ ∣ Ξ ⊢↑ p →
    renameStoreˢ ρ Σ ∣ Φ′ ∣ Ξ′ ⊢↑ rename⊑ˢ ρ p
  ⊑-renameˢ ρ okΦ okΞ (wt-tag g gokΞ) =
    wt-tag (renameˢ-ground ρ g) (renameˢ-ground-ok ρ okΞ g gokΞ)
  ⊑-renameˢ ρ okΦ okΞ (wt-unseal h α∈Φ) =
    wt-unseal (renameLookupˢ ρ h) (okΦ α∈Φ)
  ⊑-renameˢ ρ okΦ okΞ (wt-↦ p q) =
    wt-↦ (⊒-renameˢ ρ okΦ okΞ p) (⊑-renameˢ ρ okΦ okΞ q)
  ⊑-renameˢ {Σ = Σ} ρ okΦ okΞ (wt-∀ p) =
    wt-∀
      (castWt⊑
        (renameStoreˢ-ext-⟰ᵗ ρ Σ)
        refl
        refl
        (⊑-renameˢ ρ okΦ okΞ p))
  ⊑-renameˢ {Σ = Σ} ρ okΦ okΞ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊑
        (renameStoreˢ-ν ρ Σ)
        refl
        refl
        (castWt⊑-raw
          (renameˢ-ν-src ρ A)
          (renameˢ-ext-⇑ˢ ρ B)
          (⊑-renameˢ
            (extˢ ρ)
            (RenOk-ext-true okΦ)
            (RenOk-ext-false okΞ)
            p)))
  ⊑-renameˢ ρ okΦ okΞ wt-id = wt-id
  ⊑-renameˢ ρ okΦ okΞ (wt-； p q) =
    wt-； (⊑-renameˢ ρ okΦ okΞ p) (⊑-renameˢ ρ okΦ okΞ q)

  ⊒-renameˢ :
    ∀ {Σ : Store}
      {Φ Ξ : List Bool}{Φ′ Ξ′ : List Bool}{A B}
      {p : A ⊒ B} →
    (ρ : Renameˢ) →
    RenOk ρ Φ Φ′ →
    RenOk ρ Ξ Ξ′ →
    Σ ∣ Φ ∣ Ξ ⊢↓ p →
    renameStoreˢ ρ Σ ∣ Φ′ ∣ Ξ′ ⊢↓ rename⊒ˢ ρ p
  ⊒-renameˢ ρ okΦ okΞ (wt-untag g gokΞ ℓ) =
    wt-untag (renameˢ-ground ρ g) (renameˢ-ground-ok ρ okΞ g gokΞ) ℓ
  ⊒-renameˢ ρ okΦ okΞ (wt-seal h α∈Φ) =
    wt-seal (renameLookupˢ ρ h) (okΦ α∈Φ)
  ⊒-renameˢ ρ okΦ okΞ (wt-↦ p q) =
    wt-↦ (⊑-renameˢ ρ okΦ okΞ p) (⊒-renameˢ ρ okΦ okΞ q)
  ⊒-renameˢ {Σ = Σ} ρ okΦ okΞ (wt-∀ p) =
    wt-∀
      (castWt⊒
        (renameStoreˢ-ext-⟰ᵗ ρ Σ)
        refl
        refl
        (⊒-renameˢ ρ okΦ okΞ p))
  ⊒-renameˢ {Σ = Σ} ρ okΦ okΞ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊒
        (renameStoreˢ-ν ρ Σ)
        refl
        refl
        (castWt⊒-raw
          (renameˢ-ext-⇑ˢ ρ B)
          (renameˢ-ν-src ρ A)
          (⊒-renameˢ
            (extˢ ρ)
            (RenOk-ext-false okΦ)
            (RenOk-ext-true okΞ)
            p)))
  ⊒-renameˢ ρ okΦ okΞ wt-id = wt-id
  ⊒-renameˢ ρ okΦ okΞ (wt-； p q) =
    wt-； (⊒-renameˢ ρ okΦ okΞ p) (⊒-renameˢ ρ okΦ okΞ q)

------------------------------------------------------------------------
-- Type-variable substitution for well-typed widening and narrowing
------------------------------------------------------------------------

mutual
  ⊑-substᵗ :
    ∀ {Σ : Store}{Φ Ξ : List Bool}{A B}
      {p : A ⊑ B} →
    (σ : Substᵗ) →
    Σ ∣ Φ ∣ Ξ ⊢↑ p →
    substStoreᵗ σ Σ ∣ Φ ∣ Ξ ⊢↑ subst⊑ᵗ σ p
  ⊑-substᵗ σ (wt-tag g gokΞ) =
    wt-tag (substᵗ-ground σ g) (substᵗ-ground-ok σ g gokΞ)
  ⊑-substᵗ σ (wt-unseal h α∈Φ) = wt-unseal (substLookupᵗ σ h) α∈Φ
  ⊑-substᵗ σ (wt-↦ p q) = wt-↦ (⊒-substᵗ σ p) (⊑-substᵗ σ q)
  ⊑-substᵗ {Σ = Σ} σ (wt-∀ p) =
    wt-∀
      (castWt⊑
        (substStoreᵗ-ext-⟰ᵗ σ Σ)
        refl
        refl
        (⊑-substᵗ (extsᵗ σ) p))
  ⊑-substᵗ {Σ = Σ} σ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊑
        (substStoreᵗ-ν σ Σ)
        refl
        refl
        (castWt⊑-raw
          (substᵗ-ν-src σ A)
          (substᵗ-⇑ˢ σ B)
          (⊑-substᵗ (liftSubstˢ σ) p)))
  ⊑-substᵗ σ wt-id = wt-id
  ⊑-substᵗ σ (wt-； p q) = wt-； (⊑-substᵗ σ p) (⊑-substᵗ σ q)

  ⊒-substᵗ :
    ∀ {Σ : Store}{Φ Ξ : List Bool}{A B}
      {p : A ⊒ B} →
    (σ : Substᵗ) →
    Σ ∣ Φ ∣ Ξ ⊢↓ p →
    substStoreᵗ σ Σ ∣ Φ ∣ Ξ ⊢↓ subst⊒ᵗ σ p
  ⊒-substᵗ σ (wt-untag g gokΞ ℓ) =
    wt-untag (substᵗ-ground σ g) (substᵗ-ground-ok σ g gokΞ) ℓ
  ⊒-substᵗ σ (wt-seal h α∈Φ) = wt-seal (substLookupᵗ σ h) α∈Φ
  ⊒-substᵗ σ (wt-↦ p q) = wt-↦ (⊑-substᵗ σ p) (⊒-substᵗ σ q)
  ⊒-substᵗ {Σ = Σ} σ (wt-∀ p) =
    wt-∀
      (castWt⊒
        (substStoreᵗ-ext-⟰ᵗ σ Σ)
        refl
        refl
        (⊒-substᵗ (extsᵗ σ) p))
  ⊒-substᵗ {Σ = Σ} σ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊒
        (substStoreᵗ-ν σ Σ)
        refl
        refl
        (castWt⊒-raw
          (substᵗ-⇑ˢ σ B)
          (substᵗ-ν-src σ A)
          (⊒-substᵗ (liftSubstˢ σ) p)))
  ⊒-substᵗ σ wt-id = wt-id
  ⊒-substᵗ σ (wt-； p q) = wt-； (⊒-substᵗ σ p) (⊒-substᵗ σ q)

infixl 8 _[_]⊑ᵗ
_[_]⊑ᵗ :
  ∀ {Σ : Store}{Φ Ξ : List Bool}{A B : Ty}
    {p : A ⊑ B}
  → Σ ∣ Φ ∣ Ξ ⊢↑ p
  → (T : Ty)
  → substStoreᵗ (singleTyEnv T) Σ ∣ Φ ∣ Ξ ⊢↑
      subst⊑ᵗ (singleTyEnv T) p
h [ T ]⊑ᵗ = ⊑-substᵗ (singleTyEnv T) h

infixl 8 _[_]⊒ᵗ
_[_]⊒ᵗ :
  ∀ {Σ : Store}{Φ Ξ : List Bool}{A B : Ty}
    {p : A ⊒ B}
  → Σ ∣ Φ ∣ Ξ ⊢↓ p
  → (T : Ty)
  → substStoreᵗ (singleTyEnv T) Σ ∣ Φ ∣ Ξ ⊢↓
      subst⊒ᵗ (singleTyEnv T) p
h [ T ]⊒ᵗ = ⊒-substᵗ (singleTyEnv T) h

⊑-[]ᵗ-seal :
  ∀ {Σ : Store}{Φ Ξ : List Bool}{A B : Ty}{α : Seal}
    {p : A ⊑ B}
  → α ∈ Φ
  → Σ ∣ Φ ∣ Ξ ⊢↑ p
  → substStoreᵗ (singleTyEnv (｀ α)) Σ ∣ Φ ∣ Ξ ⊢↑
      subst⊑ᵗ (singleTyEnv (｀ α)) p
⊑-[]ᵗ-seal {α = α} α∈Φ h = h [ ｀ α ]⊑ᵗ

⊒-[]ᵗ-seal :
  ∀ {Σ : Store}{Φ Ξ : List Bool}{A B : Ty}{α : Seal}
    {p : A ⊒ B}
  → α ∈ Φ
  → Σ ∣ Φ ∣ Ξ ⊢↓ p
  → substStoreᵗ (singleTyEnv (｀ α)) Σ ∣ Φ ∣ Ξ ⊢↓
      subst⊒ᵗ (singleTyEnv (｀ α)) p
⊒-[]ᵗ-seal {α = α} α∈Φ h = h [ ｀ α ]⊒ᵗ
