module Coercions where

-- File Charter:
--   * Intrinsically typed coercion syntax and coercion-specific operations/proofs.
--   * Renaming/substitution actions on coercions and coercion composition laws.
--   * Reuse type-substitution/context/store lemmas from their home modules.
-- Note to self:
--   * New lemmas should stay here only if coercions are the main object; if the
--     theorem is fundamentally about `Ty`, `Ctx`, or `Store`, place it there.

open import Data.Nat using (ℕ; suc)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym; trans) renaming (subst to substEq)
open import Types
open import TypeSubst
open import Store using (Uniqueˢ; lookup-unique)

Label : Set
Label = ℕ

------------------------------------------------------------------------
-- Intrinsically typed polymorphic coercions

-- The representation is canonical with respect to associativity
-- of coercion sequencing.
------------------------------------------------------------------------

infixr 7 _↦_
infixl 6 _；_
infixr 6 _⨟_
infix 5 _⊢_⇨_
infix 5 _⊢_⇨ᵃ_

mutual
  data _⊢_⇨ᵃ_ {Δ}{Ψ} (Σ : Store Ψ) : Ty Δ Ψ → Ty Δ Ψ → Set where
    _`?_ : ∀{G}
      → Ground G
      → Label
      → Σ ⊢ `★ ⇨ᵃ G

    _! : ∀{G}
      → Ground G
      → Σ ⊢ G ⇨ᵃ `★

    `⊥ : ∀{A B}
      → Label
      → Σ ⊢ A ⇨ᵃ B

    _⁻ : ∀{α}{A}
      → Σ ∋ˢ α ⦂ A
      → Σ ⊢ wkTy0 A ⇨ᵃ ｀ α

    _⁺ : ∀{α}{A}
      → Σ ∋ˢ α ⦂ A
      → Σ ⊢ ｀ α ⇨ᵃ wkTy0 A

    _↦_ : ∀{A A′ B B′}
      → Σ ⊢ A′ ⇨ A
      → Σ ⊢ B ⇨ B′
      → Σ ⊢ (A ⇒ B) ⇨ᵃ (A′ ⇒ B′)

    ∀ᶜ : ∀{A B : Ty (suc Δ) Ψ}
      → Σ ⊢ A ⇨ B
      → Σ ⊢ (`∀ A) ⇨ᵃ (`∀ B)

    𝒢 : ∀{A}
      → Σ ⊢ (A [ `★ ]ᵗ) ⇨ᵃ (`∀ A)

    ℐ : ∀{A}
      → Σ ⊢ (`∀ A) ⇨ᵃ (A [ `★ ]ᵗ)

  data _⊢_⇨_ {Δ}{Ψ} (Σ : Store Ψ) : Ty Δ Ψ → Ty Δ Ψ → Set where
    id : ∀{A}
      → Σ ⊢ A ⇨ A

    _；_ : ∀{A B C}
      → Σ ⊢ A ⇨ B
      → Σ ⊢ B ⇨ᵃ C
      → Σ ⊢ A ⇨ C

_⨟_ : ∀{Δ}{Ψ}{Σ : Store Ψ}{A B C : Ty Δ Ψ}
  → Σ ⊢ A ⇨ B
  → Σ ⊢ B ⇨ C
  → Σ ⊢ A ⇨ C
c ⨟ id = c
c ⨟ (d ； a) = (c ⨟ d) ； a

------------------------------------------------------------------------
-- Type-variable renaming and substitution for coercions
------------------------------------------------------------------------

mutual
  renameAtomᶜᵗ :
    ∀{Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B}
    (ρ : Renameᵗ Δ Δ′) →
    Σ ⊢ A ⇨ᵃ B →
    Σ ⊢ renameᵗ ρ A ⇨ᵃ renameᵗ ρ B
  renameAtomᶜᵗ ρ (g `? ℓ) = renameᵗ-ground ρ g `? ℓ
  renameAtomᶜᵗ ρ (g !) = renameᵗ-ground ρ g !
  renameAtomᶜᵗ ρ (`⊥ ℓ) = `⊥ ℓ
  renameAtomᶜᵗ ρ (_⁻ {A = A₀} h) rewrite renameᵗ-wkTy0 ρ A₀ = h ⁻
  renameAtomᶜᵗ ρ (_⁺ {A = A₀} h) rewrite renameᵗ-wkTy0 ρ A₀ = h ⁺
  renameAtomᶜᵗ ρ (c ↦ d) = renameᶜᵗ ρ c ↦ renameᶜᵗ ρ d
  renameAtomᶜᵗ ρ (∀ᶜ c) = ∀ᶜ (renameᶜᵗ (extᵗ ρ) c)
  renameAtomᶜᵗ {Σ = Σ} ρ (𝒢 {A = A}) =
    substEq
      (λ T → Σ ⊢ T ⇨ᵃ (`∀ (renameᵗ (extᵗ ρ) A)))
      (sym (renameᵗ-inst★ ρ A))
      𝒢
  renameAtomᶜᵗ {Σ = Σ} ρ (ℐ {A = A}) =
    substEq
      (λ T → Σ ⊢ (`∀ (renameᵗ (extᵗ ρ) A)) ⇨ᵃ T)
      (sym (renameᵗ-inst★ ρ A))
      ℐ

  renameᶜᵗ :
    ∀{Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B}
    (ρ : Renameᵗ Δ Δ′) →
    Σ ⊢ A ⇨ B →
    Σ ⊢ renameᵗ ρ A ⇨ renameᵗ ρ B
  renameᶜᵗ ρ id = id
  renameᶜᵗ ρ (c ； a) = renameᶜᵗ ρ c ； renameAtomᶜᵗ ρ a

mutual
  substAtomᶜᵗ :
    ∀{Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B}
    (σ : Substᵗ Δ Δ′ Ψ) →
    Σ ⊢ A ⇨ᵃ B →
    Σ ⊢ substᵗ σ A ⇨ᵃ substᵗ σ B
  substAtomᶜᵗ σ (g `? ℓ) = substᵗ-ground σ g `? ℓ
  substAtomᶜᵗ σ (g !) = substᵗ-ground σ g !
  substAtomᶜᵗ σ (`⊥ ℓ) = `⊥ ℓ
  substAtomᶜᵗ σ (_⁻ {A = A₀} h) rewrite substᵗ-wkTy0 σ A₀ = h ⁻
  substAtomᶜᵗ σ (_⁺ {A = A₀} h) rewrite substᵗ-wkTy0 σ A₀ = h ⁺
  substAtomᶜᵗ σ (c ↦ d) = substᶜᵗ σ c ↦ substᶜᵗ σ d
  substAtomᶜᵗ σ (∀ᶜ c) = ∀ᶜ (substᶜᵗ (extsᵗ σ) c)
  substAtomᶜᵗ {Σ = Σ} σ (𝒢 {A = A}) =
    substEq
      (λ T → Σ ⊢ T ⇨ᵃ (`∀ (substᵗ (extsᵗ σ) A)))
      (sym (substᵗ-inst★ σ A))
      𝒢
  substAtomᶜᵗ {Σ = Σ} σ (ℐ {A = A}) =
    substEq
      (λ T → Σ ⊢ (`∀ (substᵗ (extsᵗ σ) A)) ⇨ᵃ T)
      (sym (substᵗ-inst★ σ A))
      ℐ

  substᶜᵗ :
    ∀{Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B}
    (σ : Substᵗ Δ Δ′ Ψ) →
    Σ ⊢ A ⇨ B →
    Σ ⊢ substᵗ σ A ⇨ substᵗ σ B
  substᶜᵗ σ id = id
  substᶜᵗ σ (c ； a) = substᶜᵗ σ c ； substAtomᶜᵗ σ a

infixl 8 _[_]ᶜᵗ
_[_]ᶜᵗ :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{A B : Ty (suc Δ) Ψ}
  → Σ ⊢ A ⇨ B
  → (T : Ty Δ Ψ)
  → Σ ⊢ (A [ T ]ᵗ) ⇨ (B [ T ]ᵗ)
c [ T ]ᶜᵗ = substᶜᵗ (singleTyEnv T) c

------------------------------------------------------------------------
-- Seal renaming for coercions
------------------------------------------------------------------------

mutual
  renameAtomᶜˢ :
    ∀{Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{A B : Ty Δ Ψ}
    (ρ : Renameˢ Ψ Ψ′) →
    Σ ⊢ A ⇨ᵃ B →
    renameStoreˢ ρ Σ ⊢ renameˢ ρ A ⇨ᵃ renameˢ ρ B
  renameAtomᶜˢ ρ (g `? ℓ) = renameˢ-ground ρ g `? ℓ
  renameAtomᶜˢ ρ (g !) = renameˢ-ground ρ g !
  renameAtomᶜˢ ρ (`⊥ ℓ) = `⊥ ℓ
  renameAtomᶜˢ {Σ = Σ} ρ (_⁻ {α = α} {A = A₀} h) =
    substEq
      (λ T → renameStoreˢ ρ Σ ⊢ T ⇨ᵃ ｀ (ρ α))
      (renameᵗ-renameˢ lift0ᵗ ρ A₀)
      ((renameLookupˢ ρ h) ⁻)
  renameAtomᶜˢ {Σ = Σ} ρ (_⁺ {α = α} {A = A₀} h) =
    substEq
      (λ T → renameStoreˢ ρ Σ ⊢ ｀ (ρ α) ⇨ᵃ T)
      (renameᵗ-renameˢ lift0ᵗ ρ A₀)
      ((renameLookupˢ ρ h) ⁺)
  renameAtomᶜˢ ρ (c ↦ d) = renameᶜˢ ρ c ↦ renameᶜˢ ρ d
  renameAtomᶜˢ ρ (∀ᶜ c) = ∀ᶜ (renameᶜˢ ρ c)
  renameAtomᶜˢ {Σ = Σ} ρ (𝒢 {A = A}) =
    substEq
      (λ T → renameStoreˢ ρ Σ ⊢ T ⇨ᵃ (`∀ (renameˢ ρ A)))
      (sym (renameˢ-inst★ ρ A))
      𝒢
  renameAtomᶜˢ {Σ = Σ} ρ (ℐ {A = A}) =
    substEq
      (λ T → renameStoreˢ ρ Σ ⊢ (`∀ (renameˢ ρ A)) ⇨ᵃ T)
      (sym (renameˢ-inst★ ρ A))
      ℐ

  renameᶜˢ :
    ∀{Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{A B : Ty Δ Ψ}
    (ρ : Renameˢ Ψ Ψ′) →
    Σ ⊢ A ⇨ B →
    renameStoreˢ ρ Σ ⊢ renameˢ ρ A ⇨ renameˢ ρ B
  renameᶜˢ ρ id = id
  renameᶜˢ ρ (c ； a) = renameᶜˢ ρ c ； renameAtomᶜˢ ρ a

------------------------------------------------------------------------
-- Coercion reduction
------------------------------------------------------------------------

infix 4 _︔_—→ᶜ_
infix 4 _—→ᶜᶜ_
infix 3 _∎ᶜᶜ
infixr 2 _—→ᶜᶜ⟨_⟩_
infix 2 _—↠ᶜᶜ_
infixr 2 _—↠ᶜᶜ⟨_⟩_

data HasBlame {Δ}{Ψ}{Σ : Store Ψ}
  : ∀{A B : Ty Δ Ψ} → Σ ⊢ A ⇨ᵃ B → Set where
  hb-proj : ∀ {G}{g : Ground G}{ℓ}
    → HasBlame (g `? ℓ)
  hb-err : ∀ {A B}{ℓ}
    → HasBlame (`⊥ {A = A} {B = B} ℓ)

data _︔_—→ᶜ_ {Δ}{Ψ}{Σ : Store Ψ}
  : ∀{A B C : Ty Δ Ψ}
  → Σ ⊢ A ⇨ᵃ B
  → Σ ⊢ B ⇨ᵃ C
  → Σ ⊢ A ⇨ C
  → Set where
  proj-inj-ok : ∀ {G}{g g′ : Ground G}{ℓ}
    → g ! ︔ g′ `? ℓ —→ᶜ id

  proj-inj-bad : ∀ {G H}{g : Ground G}{h : Ground H}{ℓ}
    → G ≢ H
    → g ! ︔ h `? ℓ —→ᶜ (id ； (`⊥ ℓ))

  seal-unseal : ∀ {α}{A B}
    {h : Σ ∋ˢ α ⦂ A}
    {h′ : Σ ∋ˢ α ⦂ B}
    (uΣ : Uniqueˢ Σ)
    → h ⁻ ︔ h′ ⁺ —→ᶜ
      (substEq
        (λ T → Σ ⊢ wkTy0 A ⇨ T)
        (cong wkTy0 (lookup-unique uΣ h h′))
        id)

  inst-gen : ∀ {A}
    → ℐ {A = A} ︔ 𝒢 {A = A} —→ᶜ (id {A = `∀ A})

  ↦-step : ∀ {A A′ A″ B B′ B″}
    {c : Σ ⊢ A′ ⇨ A}
    {d : Σ ⊢ B ⇨ B′}
    {c′ : Σ ⊢ A″ ⇨ A′}
    {d′ : Σ ⊢ B′ ⇨ B″}
    → c ↦ d ︔ c′ ↦ d′ —→ᶜ (id ； ((c′ ⨟ c) ↦ (d ⨟ d′)))

  all-dist : ∀ {A B C : Ty (suc Δ) Ψ}
    {c : Σ ⊢ A ⇨ B}
    {d : Σ ⊢ B ⇨ C}
    → ∀ᶜ c ︔ ∀ᶜ d —→ᶜ (id ； (∀ᶜ (c ⨟ d)))

  all-inst : ∀ {A B : Ty (suc Δ) Ψ}
    {c : Σ ⊢ A ⇨ B}
    → ∀ᶜ c ︔ ℐ —→ᶜ ((id ； ℐ) ⨟ c [ `★ ]ᶜᵗ)

  gen-all : ∀ {A B : Ty (suc Δ) Ψ}
    {c : Σ ⊢ A ⇨ B}
    → 𝒢 ︔ ∀ᶜ c —→ᶜ (c [ `★ ]ᶜᵗ ⨟ (id ； 𝒢))

  ⊥-left : ∀ {A B C}{ℓ}
    {b : Σ ⊢ B ⇨ᵃ C}
    → `⊥ {A = A} {B = B} ℓ ︔ b —→ᶜ (id ； (`⊥ {A = A} {B = C} ℓ))

  ⊥-right : ∀ {A B C}{ℓ}
    {a : Σ ⊢ A ⇨ᵃ B}
    → ¬ HasBlame a
    → a ︔ `⊥ {A = B} {B = C} ℓ —→ᶜ (id ； (`⊥ {A = A} {B = C} ℓ))

data _—→ᶜᶜ_ {Δ}{Ψ}{Σ : Store Ψ}
  : ∀{A B : Ty Δ Ψ} → Σ ⊢ A ⇨ B → Σ ⊢ A ⇨ B → Set where
  
  β-adjᶜ : ∀ {A B C D}
    {p : Σ ⊢ A ⇨ B}
    {a : Σ ⊢ B ⇨ᵃ C}
    {b : Σ ⊢ C ⇨ᵃ D}
    {r : Σ ⊢ B ⇨ D}
    → a ︔ b —→ᶜ r
    → ((p ； a) ； b) —→ᶜᶜ (p ⨟ r)

  ξ-；ᶜ : ∀ {A B C}
    {c c′ : Σ ⊢ A ⇨ B}
    {a : Σ ⊢ B ⇨ᵃ C}
    → c —→ᶜᶜ c′
    → (c ； a) —→ᶜᶜ (c′ ； a)

------------------------------------------------------------------------
-- Coercion multi-step reduction
------------------------------------------------------------------------

data _—↠ᶜᶜ_ {Δ}{Ψ}{Σ : Store Ψ}
  : ∀{A B : Ty Δ Ψ} → Σ ⊢ A ⇨ B → Σ ⊢ A ⇨ B → Set where
  _∎ᶜᶜ : ∀ {A B : Ty Δ Ψ} (c : Σ ⊢ A ⇨ B) → c —↠ᶜᶜ c

  _—→ᶜᶜ⟨_⟩_ : ∀ {A B : Ty Δ Ψ} (l : Σ ⊢ A ⇨ B) {m n : Σ ⊢ A ⇨ B}
    → l —→ᶜᶜ m
    → m —↠ᶜᶜ n
    → l —↠ᶜᶜ n

multi-transᶜᶜ : ∀ {Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ}
  {c d e : Σ ⊢ A ⇨ B}
  → c —↠ᶜᶜ d
  → d —↠ᶜᶜ e
  → c —↠ᶜᶜ e
multi-transᶜᶜ (_ ∎ᶜᶜ) ms2 = ms2
multi-transᶜᶜ (_ —→ᶜᶜ⟨ s ⟩ ms1′) ms2 =
  _ —→ᶜᶜ⟨ s ⟩ (multi-transᶜᶜ ms1′ ms2)

_—↠ᶜᶜ⟨_⟩_ : ∀ {Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ}
  (l : Σ ⊢ A ⇨ B)
  {m n : Σ ⊢ A ⇨ B}
  → l —↠ᶜᶜ m
  → m —↠ᶜᶜ n
  → l —↠ᶜᶜ n
l —↠ᶜᶜ⟨ l—↠m ⟩ m—↠n = multi-transᶜᶜ l—↠m m—↠n

