module UpDown where

-- File Charter:
--   * Intrinsically typed widening/narrowing witnesses and their judgment-specific metatheory.
--   * Theorems whose main subject is `_∣_∣_⊢_⊑_`, `_∣_∣_⊢_⊒_`, permission transport,
--   * or cast transport for widening/narrowing.
--   * No generic `Ty` substitution algebra (put that in `TypeProperties`) and no
--   * store-structural transport lemmas (put those in `Store`).
-- Note to self:
--   * If a new lemma primarily talks about `Ty` equalities or `Store` shape/lookup,
--   * move it to the owning module; keep `UpDown` focused on the relations themselves.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_,_)
open import Data.Fin.Subset using (Subset; _∈_; _∉_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; here; there)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans)
  renaming (subst to substEq)

open import Types
open import TypeProperties
open import Store

Label : Set
Label = ℕ

------------------------------------------------------------------------
-- Widening (Up)
------------------------------------------------------------------------

infixr 7 _↦_
infixl 6 _；_
infix 3 _∣_∣_⊢_⊑_
infix 3 _∣_∣_⊢_⊒_

⌊_⌋ : ∀{Ψ} → Seal Ψ → Fin Ψ
⌊_⌋ Zˢ = Fin.zero
⌊_⌋ (Sˢ α) = suc ⌊ α ⌋

⊢_ok_ : ∀{Δ}{Ψ}{G : Ty Δ Ψ} → Ground G → Vec Bool Ψ → Set
⊢ (｀ α) ok Ξ = ⌊ α ⌋ ∈ Ξ
⊢ (‵ ι) ok Ξ = ⊤
⊢ ★⇒★ ok Ξ = ⊤

-- Phil: make Label a parameter of narrowing and widening
-- so you can show an isomorphism between them.

-- Phil: get rid of Ξ, use negation with Φ for tag
-- Phil: replace Φ with a "set of Seal"
-- Phil: Define a version of widening that doesn't quantify over the Set's
--   and instead is existential.
mutual
  data _∣_∣_⊢_⊑_ {Δ}{Ψ} (Σ : Store Δ Ψ) (Φ Ξ : Vec Bool Ψ) : Ty Δ Ψ → Ty Δ Ψ → Set where
    tag : ∀{G}
      → (g : Ground G)
      → ⊢ g ok Ξ
      → Σ ∣ Φ ∣ Ξ ⊢ G ⊑ ★

    unseal : ∀{α}{A}
      → Σ ∋ˢ α ⦂ A
      → ⌊ α ⌋ ∈ Φ
      → Σ ∣ Φ ∣ Ξ ⊢ ｀ α ⊑ A

    _↦_ : ∀{A A′ B B′}
      → Σ ∣ Φ ∣ Ξ ⊢ A′ ⊒ A
      → Σ ∣ Φ ∣ Ξ ⊢ B ⊑ B′
      → Σ ∣ Φ ∣ Ξ ⊢ (A ⇒ B) ⊑ (A′ ⇒ B′)

    ∀ᵖ : ∀{A B : Ty (suc Δ) Ψ}
      → ⟰ᵗ Σ ∣ Φ ∣ Ξ ⊢ A ⊑ B
      → Σ ∣ Φ ∣ Ξ ⊢ `∀ A ⊑ `∀ B

    ν_ : ∀{A : Ty (suc Δ) Ψ}{B : Ty Δ Ψ}
      → (Zˢ , ★) ∷ ⟰ˢ Σ ∣ true ∷ Φ ∣ false ∷ Ξ ⊢ (⇑ˢ A) [ ｀ Zˢ ]ᵗ ⊑ ⇑ˢ B
      → Σ ∣ Φ ∣ Ξ ⊢ (`∀ A) ⊑ B

    id : ∀{A}
      → Σ ∣ Φ ∣ Ξ ⊢ A ⊑ A

    _；_ : ∀{A B C}
      → Σ ∣ Φ ∣ Ξ ⊢ A ⊑ B
      → Σ ∣ Φ ∣ Ξ ⊢ B ⊑ C
      → Σ ∣ Φ ∣ Ξ ⊢ A ⊑ C

  ------------------------------------------------------------------------
  -- Narrowing (Down)
  ------------------------------------------------------------------------

  data _∣_∣_⊢_⊒_ {Δ}{Ψ} (Σ : Store Δ Ψ) (Φ Ξ : Vec Bool Ψ) : Ty Δ Ψ → Ty Δ Ψ → Set where
    untag : ∀{G}
      → (g : Ground G)
      → ⊢ g ok Ξ
      → Label
      → Σ ∣ Φ ∣ Ξ ⊢ ★ ⊒ G

    seal : ∀{α}{A}
      → Σ ∋ˢ α ⦂ A
      → ⌊ α ⌋ ∈ Φ
      → Σ ∣ Φ ∣ Ξ ⊢ A ⊒ ｀ α

    _↦_ : ∀{A A′ B B′}
      → Σ ∣ Φ ∣ Ξ ⊢ A′ ⊑ A
      → Σ ∣ Φ ∣ Ξ ⊢ B ⊒ B′
      → Σ ∣ Φ ∣ Ξ ⊢ (A ⇒ B) ⊒ (A′ ⇒ B′)

    ∀ᵖ : ∀{A B : Ty (suc Δ) Ψ}
      → ⟰ᵗ Σ ∣ Φ ∣ Ξ ⊢ A ⊒ B
      → Σ ∣ Φ ∣ Ξ ⊢ (`∀ A) ⊒ (`∀ B)

    -- add side condition requiring 0 ∈ A
    ν_ : ∀{A : Ty (suc Δ) Ψ}{B : Ty Δ Ψ}
      → (Zˢ , ⇑ˢ ★) ∷ ⟰ˢ Σ ∣ false ∷ Φ ∣ true ∷ Ξ ⊢ ⇑ˢ B ⊒ (⇑ˢ A) [ ｀ Zˢ ]ᵗ
      → Σ ∣ Φ ∣ Ξ ⊢ B  ⊒  `∀ A

    id : ∀{A}
      → Σ ∣ Φ ∣ Ξ ⊢ A ⊒ A

    _；_ : ∀{A B C}
      → Σ ∣ Φ ∣ Ξ ⊢ A ⊒ B
      → Σ ∣ Φ ∣ Ξ ⊢ B ⊒ C
      → Σ ∣ Φ ∣ Ξ ⊢ A ⊒ C

------------------------------------------------------------------------
-- Transport helpers
------------------------------------------------------------------------

RenOk : ∀{Ψ}{Ψ′} → Renameˢ Ψ Ψ′ → Vec Bool Ψ → Vec Bool Ψ′ → Set
RenOk ρ P P′ = ∀ {α} → ⌊ α ⌋ ∈ P → ⌊ ρ α ⌋ ∈ P′

RenOk-id : ∀{Ψ} {P : Vec Bool Ψ} → RenOk (λ α → α) P P
RenOk-id p = p

RenOk-ext-true :
  ∀{Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}{P : Vec Bool Ψ}{P′ : Vec Bool Ψ′} →
  RenOk ρ P P′ →
  RenOk (extˢ ρ) (true ∷ P) (true ∷ P′)
RenOk-ext-true ok {Zˢ} here = here
RenOk-ext-true ok {Sˢ α} (there p) = there (ok p)

RenOk-ext-false :
  ∀{Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}{P : Vec Bool Ψ}{P′ : Vec Bool Ψ′} →
  RenOk ρ P P′ →
  RenOk (extˢ ρ) (false ∷ P) (false ∷ P′)
RenOk-ext-false ok {Zˢ} ()
RenOk-ext-false ok {Sˢ α} (there p) = there (ok p)

RenOk-singleSealEnv-true :
  ∀{Ψ}{P : Vec Bool Ψ} {α : Seal Ψ} →
  ⌊ α ⌋ ∈ P →
  RenOk (singleSealEnv α) (true ∷ P) P
RenOk-singleSealEnv-true α∈P {Zˢ} here = α∈P
RenOk-singleSealEnv-true α∈P {Sˢ β} (there p) = p

RenOk-singleSealEnv-false :
  ∀{Ψ}{P : Vec Bool Ψ} {α : Seal Ψ} →
  RenOk (singleSealEnv α) (false ∷ P) P
RenOk-singleSealEnv-false {α = α} {Zˢ} ()
RenOk-singleSealEnv-false {α = α} {Sˢ β} (there p) = p

renameᵗ-ground-ok :
  ∀ {Δ}{Δ′}{Ψ}{G : Ty Δ Ψ}
  (ρ : Renameᵗ Δ Δ′) (g : Ground G) {Ξ : Vec Bool Ψ} →
  ⊢ g ok Ξ →
  ⊢ renameᵗ-ground ρ g ok Ξ
renameᵗ-ground-ok ρ (｀ α) gok = gok
renameᵗ-ground-ok ρ (‵ ι) gok = gok
renameᵗ-ground-ok ρ ★⇒★ gok = gok

substᵗ-ground-ok :
  ∀ {Δ}{Δ′}{Ψ}{G : Ty Δ Ψ}
  (σ : Substᵗ Δ Δ′ Ψ) (g : Ground G) {Ξ : Vec Bool Ψ} →
  ⊢ g ok Ξ →
  ⊢ substᵗ-ground σ g ok Ξ
substᵗ-ground-ok σ (｀ α) gok = gok
substᵗ-ground-ok σ (‵ ι) gok = gok
substᵗ-ground-ok σ ★⇒★ gok = gok

renameˢ-ground-ok :
  ∀ {Δ}{Ψ}{Ψ′}{G : Ty Δ Ψ}
  (ρ : Renameˢ Ψ Ψ′) {Ξ : Vec Bool Ψ} {Ξ′ : Vec Bool Ψ′} →
  RenOk ρ Ξ Ξ′ →
  (g : Ground G) →
  ⊢ g ok Ξ →
  ⊢ renameˢ-ground ρ g ok Ξ′
renameˢ-ground-ok ρ ok (｀ α) gok = ok gok
renameˢ-ground-ok ρ ok (‵ ι) gok = gok
renameˢ-ground-ok ρ ok ★⇒★ gok = gok

cast⊑ :
  ∀ {Δ}{Ψ}
    {Σ Σ′ : Store Δ Ψ}
    {Φ Φ′ : Vec Bool Ψ}
    {Ξ Ξ′ : Vec Bool Ψ}
    {A A′ B B′ : Ty Δ Ψ} →
  Σ ≡ Σ′ →
  Φ ≡ Φ′ →
  Ξ ≡ Ξ′ →
  A ≡ A′ →
  B ≡ B′ →
  Σ ∣ Φ ∣ Ξ ⊢ A ⊑ B →
  Σ′ ∣ Φ′ ∣ Ξ′ ⊢ A′ ⊑ B′
cast⊑ refl refl refl refl refl p = p

cast⊒ :
  ∀ {Δ}{Ψ}
    {Σ Σ′ : Store Δ Ψ}
    {Φ Φ′ : Vec Bool Ψ}
    {Ξ Ξ′ : Vec Bool Ψ}
    {A A′ B B′ : Ty Δ Ψ} →
  Σ ≡ Σ′ →
  Φ ≡ Φ′ →
  Ξ ≡ Ξ′ →
  A ≡ A′ →
  B ≡ B′ →
  Σ ∣ Φ ∣ Ξ ⊢ A ⊒ B →
  Σ′ ∣ Φ′ ∣ Ξ′ ⊢ A′ ⊒ B′
cast⊒ refl refl refl refl refl p = p

------------------------------------------------------------------------
-- Type-variable renaming for widening and narrowing
------------------------------------------------------------------------

mutual
  ⊑-renameᵗ :
    ∀{Δ}{Δ′}{Ψ}{Σ : Store Δ Ψ}{Φ Ξ : Vec Bool Ψ}{A B}
    (ρ : Renameᵗ Δ Δ′) →
    Σ ∣ Φ ∣ Ξ ⊢ A ⊑ B →
    renameStoreᵗ ρ Σ ∣ Φ ∣ Ξ ⊢ renameᵗ ρ A ⊑ renameᵗ ρ B
  ⊑-renameᵗ ρ (tag g g∉Φ) =
    tag (renameᵗ-ground ρ g) (renameᵗ-ground-ok ρ g g∉Φ)
  ⊑-renameᵗ ρ (unseal h α∈Φ) = unseal (renameLookupᵗ ρ h) α∈Φ
  ⊑-renameᵗ ρ (p ↦ q) = (⊒-renameᵗ ρ p) ↦ (⊑-renameᵗ ρ q)
  ⊑-renameᵗ {Σ = Σ} {Φ = Φ} {Ξ = Ξ} ρ (∀ᵖ p) =
    ∀ᵖ (cast⊑ (renameStoreᵗ-ext-⟰ᵗ ρ Σ) refl refl refl refl (⊑-renameᵗ (extᵗ ρ) p))
  ⊑-renameᵗ {Σ = Σ} {Φ = Φ} {Ξ = Ξ} ρ (ν_ {A = A} {B = B} p) =
    ν (cast⊑
         (renameStoreᵗ-ν ρ Σ)
         refl
         refl
         (renameᵗ-ν-src ρ A)
         (renameᵗ-⇑ˢ ρ B)
         (⊑-renameᵗ ρ p))
  ⊑-renameᵗ ρ id = id
  ⊑-renameᵗ ρ (p ； q) = (⊑-renameᵗ ρ p) ； (⊑-renameᵗ ρ q)

  ⊒-renameᵗ :
    ∀{Δ}{Δ′}{Ψ}{Σ : Store Δ Ψ}{Φ Ξ : Vec Bool Ψ}{A B}
    (ρ : Renameᵗ Δ Δ′) →
    Σ ∣ Φ ∣ Ξ ⊢ A ⊒ B →
    renameStoreᵗ ρ Σ ∣ Φ ∣ Ξ ⊢ renameᵗ ρ A ⊒ renameᵗ ρ B
  ⊒-renameᵗ ρ (untag g g∉Φ ℓ) =
    untag (renameᵗ-ground ρ g) (renameᵗ-ground-ok ρ g g∉Φ) ℓ
  ⊒-renameᵗ ρ (seal h α∈Φ) = seal (renameLookupᵗ ρ h) α∈Φ
  ⊒-renameᵗ ρ (p ↦ q) = (⊑-renameᵗ ρ p) ↦ (⊒-renameᵗ ρ q)
  ⊒-renameᵗ {Σ = Σ} {Φ = Φ} {Ξ = Ξ} ρ (∀ᵖ p) =
    ∀ᵖ (cast⊒ (renameStoreᵗ-ext-⟰ᵗ ρ Σ) refl refl refl refl (⊒-renameᵗ (extᵗ ρ) p))
  ⊒-renameᵗ {Σ = Σ} {Φ = Φ} {Ξ = Ξ} ρ (ν_ {A = A} {B = B} p) =
    ν (cast⊒
         (renameStoreᵗ-ν ρ Σ)
         refl
         refl
         (renameᵗ-⇑ˢ ρ B)
         (renameᵗ-ν-src ρ A)
         (⊒-renameᵗ ρ p))
  ⊒-renameᵗ ρ id = id
  ⊒-renameᵗ ρ (p ； q) = (⊒-renameᵗ ρ p) ； (⊒-renameᵗ ρ q)

------------------------------------------------------------------------
-- Seal renaming for widening and narrowing
------------------------------------------------------------------------

mutual
  ⊑-renameˢ :
    ∀{Δ}{Ψ}{Ψ′}{Σ : Store Δ Ψ}
     {Φ Ξ : Vec Bool Ψ}{Φ′ Ξ′ : Vec Bool Ψ′}{A B}
    (ρ : Renameˢ Ψ Ψ′) →
    RenOk ρ Φ Φ′ →
    RenOk ρ Ξ Ξ′ →
    Σ ∣ Φ ∣ Ξ ⊢ A ⊑ B →
    renameStoreˢ ρ Σ ∣ Φ′ ∣ Ξ′ ⊢ renameˢ ρ A ⊑ renameˢ ρ B
  ⊑-renameˢ ρ okΦ okΞ (tag g gokΞ) =
    tag (renameˢ-ground ρ g) (renameˢ-ground-ok ρ okΞ g gokΞ)
  ⊑-renameˢ ρ okΦ okΞ (unseal h α∈Φ) =
    unseal (renameLookupˢ ρ h) (okΦ α∈Φ)
  ⊑-renameˢ ρ okΦ okΞ (p ↦ q) =
    (⊒-renameˢ ρ okΦ okΞ p) ↦ (⊑-renameˢ ρ okΦ okΞ q)
  ⊑-renameˢ {Σ = Σ} ρ okΦ okΞ (∀ᵖ p) =
    ∀ᵖ
      (cast⊑
        (renameStoreˢ-ext-⟰ᵗ ρ Σ)
        refl
        refl
        refl
        refl
        (⊑-renameˢ ρ okΦ okΞ p))
  ⊑-renameˢ {Σ = Σ} ρ okΦ okΞ (ν_ {A = A} {B = B} p) =
    ν
      (cast⊑
        (renameStoreˢ-ν ρ Σ)
        refl
        refl
        (renameˢ-ν-src ρ A)
        (renameˢ-ext-⇑ˢ ρ B)
        (⊑-renameˢ
          (extˢ ρ)
          (RenOk-ext-true okΦ)
          (RenOk-ext-false okΞ)
          p))
  ⊑-renameˢ ρ okΦ okΞ id = id
  ⊑-renameˢ ρ okΦ okΞ (p ； q) =
    (⊑-renameˢ ρ okΦ okΞ p) ； (⊑-renameˢ ρ okΦ okΞ q)

  ⊒-renameˢ :
    ∀{Δ}{Ψ}{Ψ′}{Σ : Store Δ Ψ}
     {Φ Ξ : Vec Bool Ψ}{Φ′ Ξ′ : Vec Bool Ψ′}{A B}
    (ρ : Renameˢ Ψ Ψ′) →
    RenOk ρ Φ Φ′ →
    RenOk ρ Ξ Ξ′ →
    Σ ∣ Φ ∣ Ξ ⊢ A ⊒ B →
    renameStoreˢ ρ Σ ∣ Φ′ ∣ Ξ′ ⊢ renameˢ ρ A ⊒ renameˢ ρ B
  ⊒-renameˢ ρ okΦ okΞ (untag g gokΞ ℓ) =
    untag (renameˢ-ground ρ g) (renameˢ-ground-ok ρ okΞ g gokΞ) ℓ
  ⊒-renameˢ ρ okΦ okΞ (seal h α∈Φ) =
    seal (renameLookupˢ ρ h) (okΦ α∈Φ)
  ⊒-renameˢ ρ okΦ okΞ (p ↦ q) =
    (⊑-renameˢ ρ okΦ okΞ p) ↦ (⊒-renameˢ ρ okΦ okΞ q)
  ⊒-renameˢ {Σ = Σ} ρ okΦ okΞ (∀ᵖ p) =
    ∀ᵖ
      (cast⊒
        (renameStoreˢ-ext-⟰ᵗ ρ Σ)
        refl
        refl
        refl
        refl
        (⊒-renameˢ ρ okΦ okΞ p))
  ⊒-renameˢ {Σ = Σ} ρ okΦ okΞ (ν_ {A = A} {B = B} p) =
    ν
      (cast⊒
        (renameStoreˢ-ν ρ Σ)
        refl
        refl
        (renameˢ-ext-⇑ˢ ρ B)
        (renameˢ-ν-src ρ A)
        (⊒-renameˢ
          (extˢ ρ)
          (RenOk-ext-false okΦ)
          (RenOk-ext-true okΞ)
          p))
  ⊒-renameˢ ρ okΦ okΞ id = id
  ⊒-renameˢ ρ okΦ okΞ (p ； q) =
    (⊒-renameˢ ρ okΦ okΞ p) ； (⊒-renameˢ ρ okΦ okΞ q)

------------------------------------------------------------------------
-- Type-variable substitution for widening and narrowing
------------------------------------------------------------------------

mutual
  ⊑-substᵗ :
    ∀{Δ}{Δ′}{Ψ}{Σ : Store Δ Ψ}{Φ Ξ : Vec Bool Ψ}{A B}
    (σ : Substᵗ Δ Δ′ Ψ) →
    Σ ∣ Φ ∣ Ξ ⊢ A ⊑ B →
    substStoreᵗ σ Σ ∣ Φ ∣ Ξ ⊢ substᵗ σ A ⊑ substᵗ σ B
  ⊑-substᵗ σ (tag g g∉Φ) =
    tag (substᵗ-ground σ g) (substᵗ-ground-ok σ g g∉Φ)
  ⊑-substᵗ σ (unseal h α∈Φ) = unseal (substLookupᵗ σ h) α∈Φ
  ⊑-substᵗ σ (p ↦ q) = (⊒-substᵗ σ p) ↦ (⊑-substᵗ σ q)
  ⊑-substᵗ {Σ = Σ} {Φ = Φ} {Ξ = Ξ} σ (∀ᵖ p) =
    ∀ᵖ (cast⊑ (substStoreᵗ-ext-⟰ᵗ σ Σ) refl refl refl refl (⊑-substᵗ (extsᵗ σ) p))
  ⊑-substᵗ {Σ = Σ} {Φ = Φ} {Ξ = Ξ} σ (ν_ {A = A} {B = B} p) =
    ν (cast⊑
         (substStoreᵗ-ν σ Σ)
         refl
         refl
         (substᵗ-ν-src σ A)
         (substᵗ-⇑ˢ σ B)
         (⊑-substᵗ (liftSubstˢ σ) p))
  ⊑-substᵗ σ id = id
  ⊑-substᵗ σ (p ； q) = (⊑-substᵗ σ p) ； (⊑-substᵗ σ q)

  ⊒-substᵗ :
    ∀{Δ}{Δ′}{Ψ}{Σ : Store Δ Ψ}{Φ Ξ : Vec Bool Ψ}{A B}
    (σ : Substᵗ Δ Δ′ Ψ) →
    Σ ∣ Φ ∣ Ξ ⊢ A ⊒ B →
    substStoreᵗ σ Σ ∣ Φ ∣ Ξ ⊢ substᵗ σ A ⊒ substᵗ σ B
  ⊒-substᵗ σ (untag g g∉Φ ℓ) =
    untag (substᵗ-ground σ g) (substᵗ-ground-ok σ g g∉Φ) ℓ
  ⊒-substᵗ σ (seal h α∈Φ) = seal (substLookupᵗ σ h) α∈Φ
  ⊒-substᵗ σ (p ↦ q) = (⊑-substᵗ σ p) ↦ (⊒-substᵗ σ q)
  ⊒-substᵗ {Σ = Σ} {Φ = Φ} {Ξ = Ξ} σ (∀ᵖ p) =
    ∀ᵖ (cast⊒ (substStoreᵗ-ext-⟰ᵗ σ Σ) refl refl refl refl (⊒-substᵗ (extsᵗ σ) p))
  ⊒-substᵗ {Σ = Σ} {Φ = Φ} {Ξ = Ξ} σ (ν_ {A = A} {B = B} p) =
    ν (cast⊒
         (substStoreᵗ-ν σ Σ)
         refl
         refl
         (substᵗ-⇑ˢ σ B)
         (substᵗ-ν-src σ A)
         (⊒-substᵗ (liftSubstˢ σ) p))
  ⊒-substᵗ σ id = id
  ⊒-substᵗ σ (p ； q) = (⊒-substᵗ σ p) ； (⊒-substᵗ σ q)

infixl 8 _[_]⊑ᵗ
_[_]⊑ᵗ :
  ∀ {Δ}{Ψ}{Σ : Store (suc Δ) Ψ}{Φ Ξ : Vec Bool Ψ}{A B : Ty (suc Δ) Ψ}
  → Σ ∣ Φ ∣ Ξ ⊢ A ⊑ B
  → (T : Ty Δ Ψ)
  → substStoreᵗ (singleTyEnv T) Σ ∣ Φ ∣ Ξ ⊢ A [ T ]ᵗ ⊑ B [ T ]ᵗ
p [ T ]⊑ᵗ = ⊑-substᵗ (singleTyEnv T) p

infixl 8 _[_]⊒ᵗ
_[_]⊒ᵗ :
  ∀ {Δ}{Ψ}{Σ : Store (suc Δ) Ψ}{Φ Ξ : Vec Bool Ψ}{A B : Ty (suc Δ) Ψ}
  → Σ ∣ Φ ∣ Ξ ⊢ A ⊒ B
  → (T : Ty Δ Ψ)
  → substStoreᵗ (singleTyEnv T) Σ ∣ Φ ∣ Ξ ⊢ A [ T ]ᵗ ⊒ B [ T ]ᵗ
p [ T ]⊒ᵗ = ⊒-substᵗ (singleTyEnv T) p

⊑-[]ᵗ-seal :
  ∀ {Δ}{Ψ}{Σ : Store (suc Δ) Ψ}{Φ Ξ : Vec Bool Ψ}{A B : Ty (suc Δ) Ψ}{α : Seal Ψ}
  → ⌊ α ⌋ ∈ Φ
  → Σ ∣ Φ ∣ Ξ ⊢ A ⊑ B
  → substStoreᵗ (singleTyEnv (｀ α)) Σ ∣ Φ ∣ Ξ ⊢ A [ ｀ α ]ᵗ ⊑ B [ ｀ α ]ᵗ
⊑-[]ᵗ-seal {α = α} α∈Φ p = p [ ｀ α ]⊑ᵗ

⊒-[]ᵗ-seal :
  ∀ {Δ}{Ψ}{Σ : Store (suc Δ) Ψ}{Φ Ξ : Vec Bool Ψ}{A B : Ty (suc Δ) Ψ}{α : Seal Ψ}
  → ⌊ α ⌋ ∈ Φ
  → Σ ∣ Φ ∣ Ξ ⊢ A ⊒ B
  → substStoreᵗ (singleTyEnv (｀ α)) Σ ∣ Φ ∣ Ξ ⊢ A [ ｀ α ]ᵗ ⊒ B [ ｀ α ]ᵗ
⊒-[]ᵗ-seal {α = α} α∈Φ p = p [ ｀ α ]⊒ᵗ
