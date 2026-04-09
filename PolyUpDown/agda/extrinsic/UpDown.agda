module UpDown where

-- File Charter:
--   * Raw widening/narrowing syntax and a separate well-typed judgment in extrinsic style.
--   * Theorems whose main subject is `Up`, `Down`, and their well-typed interpretation.
--   * No generic `Ty` substitution algebra (put that in `TypeProperties`) and no
--   * store-structural transport lemmas (put those in `Store`).
-- Note to self:
--   * Keep `Up`/`Down` free of store/permission indices; encode invariants only in
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

mutual
  data Up : Set where
    tag : Ty → Up

    unseal : Seal → Up

    _↦_ : Down → Up → Up

    ∀ᵖ : Up → Up

    ν_ : Up → Up

    id : Up

    _；_ : Up → Up → Up

  data Down : Set where
    untag : Ty → Label → Down

    seal : Seal → Down

    _↦_ : Up → Down → Down

    ∀ᵖ : Down → Down

    ν_ : Down → Down

    id : Down

    _；_ : Down → Down → Down

------------------------------------------------------------------------
-- Well-typed widening/narrowing (recaptures intrinsic invariants)
------------------------------------------------------------------------

infix 3 _∣_∣_⊢_⦂_⊑_ _∣_∣_⊢_⦂_⊒_

mutual
  data _∣_∣_⊢_⦂_⊑_ (Σ : Store) (Φ Ξ : List Bool) : Up → Ty → Ty → Set where
    wt-tag : ∀ {G}
      → (g : Ground G)
      → ⊢ g ok Ξ
      → Σ ∣ Φ ∣ Ξ ⊢ tag G ⦂ G ⊑ ★

    wt-unseal : ∀ {α A}
      → Σ ∋ˢ α ⦂ A
      → α ∈ Φ
      → Σ ∣ Φ ∣ Ξ ⊢ unseal α ⦂ ｀ α ⊑ A

    wt-↦ : ∀ {A A′ B B′}{p : Down}{q : Up}
      → Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A′ ⊒ A
      → Σ ∣ Φ ∣ Ξ ⊢ q ⦂ B ⊑ B′
      → Σ ∣ Φ ∣ Ξ ⊢ (p ↦ q) ⦂ (A ⇒ B) ⊑ (A′ ⇒ B′)

    wt-∀ : ∀ {A B}{p : Up}
      → ⟰ᵗ Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊑ B
      → Σ ∣ Φ ∣ Ξ ⊢ (∀ᵖ p) ⦂ `∀ A ⊑ `∀ B

    wt-ν : ∀ {A B}{p : Up}
      → ((zero , ★) ∷ ⟰ˢ Σ) ∣ (true ∷ Φ) ∣ (false ∷ Ξ) ⊢ p ⦂ (⇑ˢ A) [ ｀ zero ]ᵗ ⊑ ⇑ˢ B
      → Σ ∣ Φ ∣ Ξ ⊢ (ν p) ⦂ (`∀ A) ⊑ B

    wt-id : ∀ {A}
      → Σ ∣ Φ ∣ Ξ ⊢ id ⦂ A ⊑ A

    wt-； : ∀ {A B C}{p q : Up}
      → Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊑ B
      → Σ ∣ Φ ∣ Ξ ⊢ q ⦂ B ⊑ C
      → Σ ∣ Φ ∣ Ξ ⊢ (p ； q) ⦂ A ⊑ C

  data _∣_∣_⊢_⦂_⊒_ (Σ : Store) (Φ Ξ : List Bool) : Down → Ty → Ty → Set where
    wt-untag : ∀ {G}
      → (g : Ground G)
      → ⊢ g ok Ξ
      → (ℓ : Label)
      → Σ ∣ Φ ∣ Ξ ⊢ (untag G ℓ) ⦂ ★ ⊒ G

    wt-seal : ∀ {α A}
      → Σ ∋ˢ α ⦂ A
      → α ∈ Φ
      → Σ ∣ Φ ∣ Ξ ⊢ seal α ⦂ A ⊒ ｀ α

    wt-↦ : ∀ {A A′ B B′}{p : Up}{q : Down}
      → Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A′ ⊑ A
      → Σ ∣ Φ ∣ Ξ ⊢ q ⦂ B ⊒ B′
      → Σ ∣ Φ ∣ Ξ ⊢ (p ↦ q) ⦂ (A ⇒ B) ⊒ (A′ ⇒ B′)

    wt-∀ : ∀ {A B}{p : Down}
      → ⟰ᵗ Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊒ B
      → Σ ∣ Φ ∣ Ξ ⊢ (∀ᵖ p) ⦂ `∀ A ⊒ `∀ B

    wt-ν : ∀ {A B}{p : Down}
      → ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (false ∷ Φ) ∣ (true ∷ Ξ) ⊢ p ⦂ ⇑ˢ B ⊒ (⇑ˢ A) [ ｀ zero ]ᵗ
      → Σ ∣ Φ ∣ Ξ ⊢ (ν p) ⦂ B ⊒ `∀ A

    wt-id : ∀ {A}
      → Σ ∣ Φ ∣ Ξ ⊢ id ⦂ A ⊒ A

    wt-； : ∀ {A B C}{p q : Down}
      → Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊒ B
      → Σ ∣ Φ ∣ Ξ ⊢ q ⦂ B ⊒ C
      → Σ ∣ Φ ∣ Ξ ⊢ (p ； q) ⦂ A ⊒ C

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

mutual
  rename⊑ᵗ : (ρ : Renameᵗ) → Up → Up
  rename⊑ᵗ ρ (tag G) = tag (renameᵗ ρ G)
  rename⊑ᵗ ρ (unseal α) = unseal α
  rename⊑ᵗ ρ (p ↦ q) = rename⊒ᵗ ρ p ↦ rename⊑ᵗ ρ q
  rename⊑ᵗ ρ (∀ᵖ p) = ∀ᵖ (rename⊑ᵗ (extᵗ ρ) p)
  rename⊑ᵗ ρ (ν p) = ν (rename⊑ᵗ ρ p)
  rename⊑ᵗ ρ id = id
  rename⊑ᵗ ρ (p ； q) = rename⊑ᵗ ρ p ； rename⊑ᵗ ρ q

  rename⊒ᵗ : (ρ : Renameᵗ) → Down → Down
  rename⊒ᵗ ρ (untag G ℓ) = untag (renameᵗ ρ G) ℓ
  rename⊒ᵗ ρ (seal α) = seal α
  rename⊒ᵗ ρ (p ↦ q) = rename⊑ᵗ ρ p ↦ rename⊒ᵗ ρ q
  rename⊒ᵗ ρ (∀ᵖ p) = ∀ᵖ (rename⊒ᵗ (extᵗ ρ) p)
  rename⊒ᵗ ρ (ν p) = ν (rename⊒ᵗ ρ p)
  rename⊒ᵗ ρ id = id
  rename⊒ᵗ ρ (p ； q) = rename⊒ᵗ ρ p ； rename⊒ᵗ ρ q

mutual
  rename⊑ˢ : (ρ : Renameˢ) → Up → Up
  rename⊑ˢ ρ (tag G) = tag (renameˢ ρ G)
  rename⊑ˢ ρ (unseal α) = unseal (ρ α)
  rename⊑ˢ ρ (p ↦ q) = rename⊒ˢ ρ p ↦ rename⊑ˢ ρ q
  rename⊑ˢ ρ (∀ᵖ p) = ∀ᵖ (rename⊑ˢ ρ p)
  rename⊑ˢ ρ (ν p) = ν (rename⊑ˢ (extˢ ρ) p)
  rename⊑ˢ ρ id = id
  rename⊑ˢ ρ (p ； q) = rename⊑ˢ ρ p ； rename⊑ˢ ρ q

  rename⊒ˢ : (ρ : Renameˢ) → Down → Down
  rename⊒ˢ ρ (untag G ℓ) = untag (renameˢ ρ G) ℓ
  rename⊒ˢ ρ (seal α) = seal (ρ α)
  rename⊒ˢ ρ (p ↦ q) = rename⊑ˢ ρ p ↦ rename⊒ˢ ρ q
  rename⊒ˢ ρ (∀ᵖ p) = ∀ᵖ (rename⊒ˢ ρ p)
  rename⊒ˢ ρ (ν p) = ν (rename⊒ˢ (extˢ ρ) p)
  rename⊒ˢ ρ id = id
  rename⊒ˢ ρ (p ； q) = rename⊒ˢ ρ p ； rename⊒ˢ ρ q

mutual
  subst⊑ᵗ : (σ : Substᵗ) → Up → Up
  subst⊑ᵗ σ (tag G) = tag (substᵗ σ G)
  subst⊑ᵗ σ (unseal α) = unseal α
  subst⊑ᵗ σ (p ↦ q) = subst⊒ᵗ σ p ↦ subst⊑ᵗ σ q
  subst⊑ᵗ σ (∀ᵖ p) = ∀ᵖ (subst⊑ᵗ (extsᵗ σ) p)
  subst⊑ᵗ σ (ν p) = ν (subst⊑ᵗ (liftSubstˢ σ) p)
  subst⊑ᵗ σ id = id
  subst⊑ᵗ σ (p ； q) = subst⊑ᵗ σ p ； subst⊑ᵗ σ q

  subst⊒ᵗ : (σ : Substᵗ) → Down → Down
  subst⊒ᵗ σ (untag G ℓ) = untag (substᵗ σ G) ℓ
  subst⊒ᵗ σ (seal α) = seal α
  subst⊒ᵗ σ (p ↦ q) = subst⊑ᵗ σ p ↦ subst⊒ᵗ σ q
  subst⊒ᵗ σ (∀ᵖ p) = ∀ᵖ (subst⊒ᵗ (extsᵗ σ) p)
  subst⊒ᵗ σ (ν p) = ν (subst⊒ᵗ (liftSubstˢ σ) p)
  subst⊒ᵗ σ id = id
  subst⊒ᵗ σ (p ； q) = subst⊒ᵗ σ p ； subst⊒ᵗ σ q

infixl 8 _[_]↓ˢ
_[_]↓ˢ : Down → Seal → Down
p [ α ]↓ˢ = rename⊒ˢ (singleSealEnv α) p

------------------------------------------------------------------------
-- Typed-judgment transport helpers
------------------------------------------------------------------------

castWt⊑ :
  ∀ {Σ Σ′ : Store}{Φ Φ′ Ξ Ξ′ : List Bool}{A B : Ty}{p : Up} →
  Σ ≡ Σ′ →
  Φ ≡ Φ′ →
  Ξ ≡ Ξ′ →
  Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊑ B →
  Σ′ ∣ Φ′ ∣ Ξ′ ⊢ p ⦂ A ⊑ B
castWt⊑ refl refl refl h = h

castWt⊒ :
  ∀ {Σ Σ′ : Store}{Φ Φ′ Ξ Ξ′ : List Bool}{A B : Ty}{p : Down} →
  Σ ≡ Σ′ →
  Φ ≡ Φ′ →
  Ξ ≡ Ξ′ →
  Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊒ B →
  Σ′ ∣ Φ′ ∣ Ξ′ ⊢ p ⦂ A ⊒ B
castWt⊒ refl refl refl h = h

castWt⊑-raw :
  ∀ {Σ : Store}{Φ Ξ : List Bool}{A A′ B B′ : Ty}{p : Up} →
  (A≡A′ : A ≡ A′) →
  (B≡B′ : B ≡ B′) →
  Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊑ B →
  Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A′ ⊑ B′
castWt⊑-raw refl refl h = h

castWt⊒-raw :
  ∀ {Σ : Store}{Φ Ξ : List Bool}{A A′ B B′ : Ty}{p : Down} →
  (A≡A′ : A ≡ A′) →
  (B≡B′ : B ≡ B′) →
  Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊒ B →
  Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A′ ⊒ B′
castWt⊒-raw refl refl h = h

------------------------------------------------------------------------
-- Type-variable renaming for well-typed widening and narrowing
------------------------------------------------------------------------

mutual
  ⊑-renameᵗ-wt :
    ∀ {Σ : Store}{Φ Ξ : List Bool}{A B : Ty}
    {p : Up} →
    (ρ : Renameᵗ) →
    Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊑ B →
    renameStoreᵗ ρ Σ ∣ Φ ∣ Ξ ⊢ rename⊑ᵗ ρ p ⦂ renameᵗ ρ A ⊑ renameᵗ ρ B
  ⊑-renameᵗ-wt ρ (wt-tag g gokΞ) =
    wt-tag (renameᵗ-ground ρ g) (renameᵗ-ground-ok ρ g gokΞ)
  ⊑-renameᵗ-wt ρ (wt-unseal h α∈Φ) = wt-unseal (renameLookupᵗ ρ h) α∈Φ
  ⊑-renameᵗ-wt ρ (wt-↦ p q) = wt-↦ (⊒-renameᵗ-wt ρ p) (⊑-renameᵗ-wt ρ q)
  ⊑-renameᵗ-wt {Σ = Σ} ρ (wt-∀ p) =
    wt-∀
      (castWt⊑
        (renameStoreᵗ-ext-⟰ᵗ ρ Σ)
        refl
        refl
        (⊑-renameᵗ-wt (extᵗ ρ) p))
  ⊑-renameᵗ-wt {Σ = Σ} ρ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊑
        (renameStoreᵗ-ν ρ Σ)
        refl
        refl
        (castWt⊑-raw
          (renameᵗ-ν-src ρ A)
          (renameᵗ-⇑ˢ ρ B)
          (⊑-renameᵗ-wt ρ p)))
  ⊑-renameᵗ-wt ρ wt-id = wt-id
  ⊑-renameᵗ-wt ρ (wt-； p q) = wt-； (⊑-renameᵗ-wt ρ p) (⊑-renameᵗ-wt ρ q)

  ⊒-renameᵗ-wt :
    ∀ {Σ : Store}{Φ Ξ : List Bool}{A B : Ty}
    {p : Down} →
    (ρ : Renameᵗ) →
    Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊒ B →
    renameStoreᵗ ρ Σ ∣ Φ ∣ Ξ ⊢ rename⊒ᵗ ρ p ⦂ renameᵗ ρ A ⊒ renameᵗ ρ B
  ⊒-renameᵗ-wt ρ (wt-untag g gokΞ ℓ) =
    wt-untag (renameᵗ-ground ρ g) (renameᵗ-ground-ok ρ g gokΞ) ℓ
  ⊒-renameᵗ-wt ρ (wt-seal h α∈Φ) = wt-seal (renameLookupᵗ ρ h) α∈Φ
  ⊒-renameᵗ-wt ρ (wt-↦ p q) = wt-↦ (⊑-renameᵗ-wt ρ p) (⊒-renameᵗ-wt ρ q)
  ⊒-renameᵗ-wt {Σ = Σ} ρ (wt-∀ p) =
    wt-∀
      (castWt⊒
        (renameStoreᵗ-ext-⟰ᵗ ρ Σ)
        refl
        refl
        (⊒-renameᵗ-wt (extᵗ ρ) p))
  ⊒-renameᵗ-wt {Σ = Σ} ρ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊒
        (renameStoreᵗ-ν ρ Σ)
        refl
        refl
        (castWt⊒-raw
          (renameᵗ-⇑ˢ ρ B)
          (renameᵗ-ν-src ρ A)
          (⊒-renameᵗ-wt ρ p)))
  ⊒-renameᵗ-wt ρ wt-id = wt-id
  ⊒-renameᵗ-wt ρ (wt-； p q) = wt-； (⊒-renameᵗ-wt ρ p) (⊒-renameᵗ-wt ρ q)

------------------------------------------------------------------------
-- Seal renaming for well-typed widening and narrowing
------------------------------------------------------------------------

mutual
  ⊑-renameˢ-wt :
    ∀ {Σ : Store}
      {Φ Ξ : List Bool}{Φ′ Ξ′ : List Bool}{A B : Ty}
      {p : Up} →
    (ρ : Renameˢ) →
    RenOk ρ Φ Φ′ →
    RenOk ρ Ξ Ξ′ →
    Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊑ B →
    renameStoreˢ ρ Σ ∣ Φ′ ∣ Ξ′ ⊢ rename⊑ˢ ρ p ⦂ renameˢ ρ A ⊑ renameˢ ρ B
  ⊑-renameˢ-wt ρ okΦ okΞ (wt-tag g gokΞ) =
    wt-tag (renameˢ-ground ρ g) (renameˢ-ground-ok ρ okΞ g gokΞ)
  ⊑-renameˢ-wt ρ okΦ okΞ (wt-unseal h α∈Φ) =
    wt-unseal (renameLookupˢ ρ h) (okΦ α∈Φ)
  ⊑-renameˢ-wt ρ okΦ okΞ (wt-↦ p q) =
    wt-↦ (⊒-renameˢ-wt ρ okΦ okΞ p) (⊑-renameˢ-wt ρ okΦ okΞ q)
  ⊑-renameˢ-wt {Σ = Σ} ρ okΦ okΞ (wt-∀ p) =
    wt-∀
      (castWt⊑
        (renameStoreˢ-ext-⟰ᵗ ρ Σ)
        refl
        refl
        (⊑-renameˢ-wt ρ okΦ okΞ p))
  ⊑-renameˢ-wt {Σ = Σ} ρ okΦ okΞ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊑
        (renameStoreˢ-ν ρ Σ)
        refl
        refl
        (castWt⊑-raw
          (renameˢ-ν-src ρ A)
          (renameˢ-ext-⇑ˢ ρ B)
          (⊑-renameˢ-wt
            (extˢ ρ)
            (RenOk-ext-true okΦ)
            (RenOk-ext-false okΞ)
            p)))
  ⊑-renameˢ-wt ρ okΦ okΞ wt-id = wt-id
  ⊑-renameˢ-wt ρ okΦ okΞ (wt-； p q) =
    wt-； (⊑-renameˢ-wt ρ okΦ okΞ p) (⊑-renameˢ-wt ρ okΦ okΞ q)

  ⊒-renameˢ-wt :
    ∀ {Σ : Store}
      {Φ Ξ : List Bool}{Φ′ Ξ′ : List Bool}{A B : Ty}
      {p : Down} →
    (ρ : Renameˢ) →
    RenOk ρ Φ Φ′ →
    RenOk ρ Ξ Ξ′ →
    Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊒ B →
    renameStoreˢ ρ Σ ∣ Φ′ ∣ Ξ′ ⊢ rename⊒ˢ ρ p ⦂ renameˢ ρ A ⊒ renameˢ ρ B
  ⊒-renameˢ-wt ρ okΦ okΞ (wt-untag g gokΞ ℓ) =
    wt-untag (renameˢ-ground ρ g) (renameˢ-ground-ok ρ okΞ g gokΞ) ℓ
  ⊒-renameˢ-wt ρ okΦ okΞ (wt-seal h α∈Φ) =
    wt-seal (renameLookupˢ ρ h) (okΦ α∈Φ)
  ⊒-renameˢ-wt ρ okΦ okΞ (wt-↦ p q) =
    wt-↦ (⊑-renameˢ-wt ρ okΦ okΞ p) (⊒-renameˢ-wt ρ okΦ okΞ q)
  ⊒-renameˢ-wt {Σ = Σ} ρ okΦ okΞ (wt-∀ p) =
    wt-∀
      (castWt⊒
        (renameStoreˢ-ext-⟰ᵗ ρ Σ)
        refl
        refl
        (⊒-renameˢ-wt ρ okΦ okΞ p))
  ⊒-renameˢ-wt {Σ = Σ} ρ okΦ okΞ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊒
        (renameStoreˢ-ν ρ Σ)
        refl
        refl
        (castWt⊒-raw
          (renameˢ-ext-⇑ˢ ρ B)
          (renameˢ-ν-src ρ A)
          (⊒-renameˢ-wt
            (extˢ ρ)
            (RenOk-ext-false okΦ)
            (RenOk-ext-true okΞ)
            p)))
  ⊒-renameˢ-wt ρ okΦ okΞ wt-id = wt-id
  ⊒-renameˢ-wt ρ okΦ okΞ (wt-； p q) =
    wt-； (⊒-renameˢ-wt ρ okΦ okΞ p) (⊒-renameˢ-wt ρ okΦ okΞ q)

------------------------------------------------------------------------
-- Type-variable substitution for well-typed widening and narrowing
------------------------------------------------------------------------

mutual
  ⊑-substᵗ-wt :
    ∀ {Σ : Store}{Φ Ξ : List Bool}{A B : Ty}
      {p : Up} →
    (σ : Substᵗ) →
    Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊑ B →
    substStoreᵗ σ Σ ∣ Φ ∣ Ξ ⊢ subst⊑ᵗ σ p ⦂ substᵗ σ A ⊑ substᵗ σ B
  ⊑-substᵗ-wt σ (wt-tag g gokΞ) =
    wt-tag (substᵗ-ground σ g) (substᵗ-ground-ok σ g gokΞ)
  ⊑-substᵗ-wt σ (wt-unseal h α∈Φ) = wt-unseal (substLookupᵗ σ h) α∈Φ
  ⊑-substᵗ-wt σ (wt-↦ p q) = wt-↦ (⊒-substᵗ-wt σ p) (⊑-substᵗ-wt σ q)
  ⊑-substᵗ-wt {Σ = Σ} σ (wt-∀ p) =
    wt-∀
      (castWt⊑
        (substStoreᵗ-ext-⟰ᵗ σ Σ)
        refl
        refl
        (⊑-substᵗ-wt (extsᵗ σ) p))
  ⊑-substᵗ-wt {Σ = Σ} σ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊑
        (substStoreᵗ-ν σ Σ)
        refl
        refl
        (castWt⊑-raw
          (substᵗ-ν-src σ A)
          (substᵗ-⇑ˢ σ B)
          (⊑-substᵗ-wt (liftSubstˢ σ) p)))
  ⊑-substᵗ-wt σ wt-id = wt-id
  ⊑-substᵗ-wt σ (wt-； p q) = wt-； (⊑-substᵗ-wt σ p) (⊑-substᵗ-wt σ q)

  ⊒-substᵗ-wt :
    ∀ {Σ : Store}{Φ Ξ : List Bool}{A B : Ty}
      {p : Down} →
    (σ : Substᵗ) →
    Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊒ B →
    substStoreᵗ σ Σ ∣ Φ ∣ Ξ ⊢ subst⊒ᵗ σ p ⦂ substᵗ σ A ⊒ substᵗ σ B
  ⊒-substᵗ-wt σ (wt-untag g gokΞ ℓ) =
    wt-untag (substᵗ-ground σ g) (substᵗ-ground-ok σ g gokΞ) ℓ
  ⊒-substᵗ-wt σ (wt-seal h α∈Φ) = wt-seal (substLookupᵗ σ h) α∈Φ
  ⊒-substᵗ-wt σ (wt-↦ p q) = wt-↦ (⊑-substᵗ-wt σ p) (⊒-substᵗ-wt σ q)
  ⊒-substᵗ-wt {Σ = Σ} σ (wt-∀ p) =
    wt-∀
      (castWt⊒
        (substStoreᵗ-ext-⟰ᵗ σ Σ)
        refl
        refl
        (⊒-substᵗ-wt (extsᵗ σ) p))
  ⊒-substᵗ-wt {Σ = Σ} σ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊒
        (substStoreᵗ-ν σ Σ)
        refl
        refl
        (castWt⊒-raw
          (substᵗ-⇑ˢ σ B)
          (substᵗ-ν-src σ A)
          (⊒-substᵗ-wt (liftSubstˢ σ) p)))
  ⊒-substᵗ-wt σ wt-id = wt-id
  ⊒-substᵗ-wt σ (wt-； p q) = wt-； (⊒-substᵗ-wt σ p) (⊒-substᵗ-wt σ q)

infixl 8 _[_]↑
_[_]↑ :
  Up → Ty → Up
p [ T ]↑ = subst⊑ᵗ (singleTyEnv T) p

[]⊑ᵗ-wt :
  ∀ {Σ : Store}{Φ Ξ : List Bool}{A B : Ty}
    {p : Up}
  → Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊑ B
  → (T : Ty)
  → substStoreᵗ (singleTyEnv T) Σ ∣ Φ ∣ Ξ ⊢ p [ T ]↑ ⦂ (A [ T ]ᵗ) ⊑ (B [ T ]ᵗ)
[]⊑ᵗ-wt h T = ⊑-substᵗ-wt (singleTyEnv T) h

infixl 8 _[_]↓
_[_]↓ :
  Down → Ty → Down
p [ T ]↓ = subst⊒ᵗ (singleTyEnv T) p

[]⊒ᵗ-wt :
  ∀ {Σ : Store}{Φ Ξ : List Bool}{A B : Ty}
    {p : Down}
  → Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊒ B
  → (T : Ty)
  → substStoreᵗ (singleTyEnv T) Σ ∣ Φ ∣ Ξ ⊢ p [ T ]↓ ⦂ A [ T ]ᵗ ⊒ B [ T ]ᵗ
[]⊒ᵗ-wt h T = ⊒-substᵗ-wt (singleTyEnv T) h

⊑-[]ᵗ-seal :
  ∀ {Σ : Store}{Φ Ξ : List Bool}{A B : Ty}{α : Seal}
    {p : Up}
  → α ∈ Φ
  → Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊑ B
  → substStoreᵗ (singleTyEnv (｀ α)) Σ ∣ Φ ∣ Ξ ⊢ p [ ｀ α ]↑ ⦂ A [ ｀ α ]ᵗ ⊑ B [ ｀ α ]ᵗ
⊑-[]ᵗ-seal {α = α} α∈Φ h = []⊑ᵗ-wt h (｀ α)

⊒-[]ᵗ-seal :
  ∀ {Σ : Store}{Φ Ξ : List Bool}{A B : Ty}{α : Seal}
    {p : Down}
  → α ∈ Φ
  → Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊒ B
  → substStoreᵗ (singleTyEnv (｀ α)) Σ ∣ Φ ∣ Ξ ⊢ p [ ｀ α ]↓ ⦂ A [ ｀ α ]ᵗ ⊒ B [ ｀ α ]ᵗ
⊒-[]ᵗ-seal {α = α} α∈Φ h = []⊒ᵗ-wt h (｀ α)
