module TermNarrowing where

-- File Charter:
--   * Defines well-typed narrowing between GTPLC terms.
--   * Indexes term narrowing by two-context type narrowing.
--   * Uses one-context coercion narrowing and widening at casts.
--   * Checks cast-composition side conditions only by matching endpoints.
--   * Retains the quotient phase for paired narrowing and widening casts.

open import Data.List using (_∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)

open import Types hiding (_∋_⦂_)
open import TyStore
open import Ctx
open import Coercions hiding (_↦_; gen)
open import Coercions using () renaming (gen to genᶜ)
open import Terms
open import Primitives
open import TypeNarrow
open import NarrowWiden using
  ( _∣_∣_⊢_⦂_⊑_
  ; _∣_∣_⊢_⦂_⊒_
  )
open import EnvironmentNarrowing

------------------------------------------------------------------------
-- Endpoint matching
------------------------------------------------------------------------

infix 4 _⨟_≈_
infix 4 _⨟_≈_⨟_

data _⨟_≈_ : {X Y Z : Set} → X → Y → Z → Set₁ where

  endpointsˡⁿ :
      ∀ {μ Δᴸ Δᴿ Σᴸ s A B B′}
        {Φ : ImpCtx Δᴸ Δᴿ}
        {d : μ ∣ Δᴸ ∣ Σᴸ ⊢ s ⦂ A ⊒ B}
        {q : Φ ⊢ B ⊒ B′}
        {p : Φ ⊢ A ⊒ B′}
      ----------------
    → d ⨟ q ≈ p

  endpointsˡʷ :
      ∀ {μ Δᴸ Δᴿ Σᴸ s A B B′}
        {Φ : ImpCtx Δᴸ Δᴿ}
        {u : μ ∣ Δᴸ ∣ Σᴸ ⊢ s ⦂ A ⊑ B}
        {p : Φ ⊢ A ⊒ B′}
        {q : Φ ⊢ B ⊒ B′}
      ----------------
    → u ⨟ p ≈ q

  endpointsʳⁿ :
      ∀ {μ Δᴸ Δᴿ Σᴿ t A A′ B′}
        {Φ : ImpCtx Δᴸ Δᴿ}
        {p : Φ ⊢ A ⊒ A′}
        {d : μ ∣ Δᴿ ∣ Σᴿ ⊢ t ⦂ A′ ⊒ B′}
        {q : Φ ⊢ A ⊒ B′}
      ----------------
    → p ⨟ d ≈ q

  endpointsʳʷ :
      ∀ {μ Δᴸ Δᴿ Σᴿ t A A′ B′}
        {Φ : ImpCtx Δᴸ Δᴿ}
        {u : μ ∣ Δᴿ ∣ Σᴿ ⊢ t ⦂ A′ ⊑ B′}
        {p : Φ ⊢ A ⊒ A′}
        {q : Φ ⊢ A ⊒ B′}
      ----------------
    → q ⨟ u ≈ p

data _⨟_≈_⨟_ :
    {W X Y Z : Set} → W → X → Y → Z → Set₁ where

  endpointsⁿ :
      ∀ {μ μ′ Δᴸ Δᴿ Σᴸ Σᴿ s t A A′ B B′}
        {Φ : ImpCtx Δᴸ Δᴿ}
        {c : μ ∣ Δᴸ ∣ Σᴸ ⊢ s ⦂ A ⊒ B}
        {q : Φ ⊢ B ⊒ B′}
        {p : Φ ⊢ A ⊒ A′}
        {d : μ′ ∣ Δᴿ ∣ Σᴿ ⊢ t ⦂ A′ ⊒ B′}
      ---------------------
    → c ⨟ q ≈ p ⨟ d

  endpointsʷ :
      ∀ {μ μ′ Δᴸ Δᴿ Σᴸ Σᴿ s t A A′ B B′}
        {Φ : ImpCtx Δᴸ Δᴿ}
        {u : μ ∣ Δᴸ ∣ Σᴸ ⊢ s ⦂ B ⊑ A}
        {q : Φ ⊢ B ⊒ B′}
        {p : Φ ⊢ A ⊒ A′}
        {v : μ′ ∣ Δᴿ ∣ Σᴿ ⊢ t ⦂ B′ ⊑ A′}
      ---------------------
    → u ⨟ q ≈ p ⨟ v

------------------------------------------------------------------------
-- Term narrowing, with a quotient phase for paired casts
------------------------------------------------------------------------

variable
  Δᴸ Δᴿ : TyCtx
  Σᴸ Σᴿ : TyStore
  Γᴸ Γᴿ : Ctx
  L L′ M M′ N N′ V V′ : Term
  A A′ B B′ C C′ D D′ : Ty
  Φ : ImpCtx Δᴸ Δᴿ
  ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  s t : Coercion
  μ μ′ : ModeEnv

infix 4 _⊢ᴺ_⊒_∶_

data _⊢ᴺ_⊒_∶_ :
    ∀ (ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ})
  → Term → Term → ∀ {A B} → ρ ⊢ᵀ A ⊒ B → Set₁ where

  ⊒blame : ∀ {p : ρ ⊢ᵀ A ⊒ B}
    → ρ ⊢ᴸ M ⦂ A
      ------------------
    → ρ ⊢ᴺ M ⊒ blame ∶ p

  x⊒x : ∀ {x} {p : ρ ⊢ᵀ A ⊒ B}
    → ρ ∋ᵉ x ⦂ p
      ------------------
    → ρ ⊢ᴺ ` x ⊒ ` x ∶ p

  ƛ⊒ƛ : ∀ {p : ρ ⊢ᵀ A ⊒ A′}
      {q : ρ ,ᵍ p ⊢ᵀ B ⊒ B′}
    → ρ ⊢ᴸ A
    → ρ ⊢ᴿ A′
    → ρ ,ᵍ p ⊢ᴺ N ⊒ N′ ∶ q
      -------------------------
    → ρ ⊢ᴺ ƛ N ⊒ ƛ N′ ∶ (p ↦ q)

  ·⊒· : ∀ {p : ρ ⊢ᵀ A ⊒ A′}
      {q : ρ ⊢ᵀ B ⊒ B′}
    → ρ ⊢ᴺ L ⊒ L′ ∶ (p ↦ q)
    → ρ ⊢ᴺ M ⊒ M′ ∶ p
      ------------------------
    → ρ ⊢ᴺ L · M ⊒ L′ · M′ ∶ q

  Λ⊒Λ : ∀ {p : ⇑ᵉ ρ ⊢ᵀ A ⊒ B}
    → Value V
    → Value V′
    → ⇑ᵉ ρ ⊢ᴺ V ⊒ V′ ∶ p
      ----------------------
    → ρ ⊢ᴺ Λ V ⊒ Λ V′ ∶ ∀ⁿ p

  ⊒Λ : ∀ {Ψ : ImpCtx Δᴸ (suc Δᴿ)}
         {ρ′ : NarrowingEnv Ψ {Σᴸ} {⟰ᵗ Σᴿ} {Γᴸ} {⤊ᵗ Γᴿ}}
         {p : freshᴿ Φ ⊢ B ⊒ A}
         {q : ρ′ ⊢ᵀ B ⊒ A}
         {nvA z∈A B≢★}
    → SmartExtensionᵉ ρ ρ′
    → Value V′
    → ρ′ ⊢ᴺ N ⊒ V′ ∶ q
      ---------------------------------
    → ρ ⊢ᴺ N ⊒ Λ V′ ∶ gen nvA z∈A p B≢★

  ⊒⟨ν⟩ : ∀ {N V′ C c μ}
      {p : ⇑ᴿᵉ ρ ⊢ᵀ B ⊒ A} {nvA z∈A B≢★}
    → Value V′
    → ρ ⊢ᴿ V′ ⦂ C
    → ρ ⊢ᴿ C
    → genᵈ μ ∣ ⇑ᴿᵉ ρ ⊢ᴿ c ∶ ⇑ᵗ C =⇒ A
    → ⇑ᴿᵉ ρ ⊢ᴺ N ⊒ (⇑ᵗᵐ V′) ⟨ c ⟩ ∶ p
      ------------------------------------------
    → ρ ⊢ᴺ N ⊒ V′ ⟨ genᶜ c ⟩ ∶ gen nvA z∈A p B≢★

  ν⊒ν : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
          {Φ : ImpCtx Δᴸ Δᴿ}
          {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}}
          {p : ρ ⊢ᵀ B ⊒ B′}
          {q : bothᵢ Φ ⊢ C ⊒ C′}
          {s⦂ : μ ∣ suc Δᴸ ∣ ((zero , ⇑ᵗ A) ∷ ⟰ᵗ Σᴸ)
            ⊢ s ⦂ C ⊒ ⇑ᵗ B}
          {t⦂ : μ′ ∣ suc Δᴿ
            ∣ ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ Σᴿ)
            ⊢ t ⦂ C′ ⊒ ⇑ᵗ B′}
    → (a : ρ ⊢ᵀ A ⊒ A′)
    → ρ ⊢ᴺ L ⊒ L′ ∶ ∀ⁿ q
    → s⦂ ⨟ ⇑ᵀ p ≈ q ⨟ t⦂
      --------------------------------------------
    → ρ ⊢ᴺ ν A · L •⟨ s ⟩ ⊒
        ν A′ · L′ •⟨ t ⟩ ∶ p

  ⊒ν : ∀ {p : ρ ⊢ᵀ B ⊒ B′}
         {q : freshᴿ Φ ⊢ B ⊒ C′}
         {nvC′ zero∈C′ B≢★}
         {d : μ′ ∣ suc Δᴿ
           ∣ ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ Σᴿ)
           ⊢ t ⦂ C′ ⊒ ⇑ᵗ B′}
    → ρ ⊢ᴿ A′
    → ρ ⊢ᴺ N ⊒ L′ ∶ gen nvC′ zero∈C′ q B≢★
    → q ⨟ d ≈ ⇑ᴿᵀ p
      -----------------------------
    → ρ ⊢ᴺ N ⊒ ν A′ · L′ •⟨ t ⟩ ∶ p

  κ⊒κ : ∀ {n} {p : ρ ⊢ᵀ ‵ `ℕ ⊒ ‵ `ℕ}
      -----------------------------
    → ρ ⊢ᴺ $ (κℕ n) ⊒ $ (κℕ n) ∶ p

  ⊕⊒⊕ : ∀ {p : ρ ⊢ᵀ ‵ `ℕ ⊒ ‵ `ℕ}
    → ρ ⊢ᴺ L ⊒ L′ ∶ p
    → ρ ⊢ᴺ M ⊒ M′ ∶ p
      ----------------------------------------
    → ρ ⊢ᴺ L ⊕[ addℕ ] M ⊒ L′ ⊕[ addℕ ] M′ ∶ p

  castⁿ⊒ : ∀ {p : ρ ⊢ᵀ A ⊒ B′}
      {q : ρ ⊢ᵀ B ⊒ B′}
      {s⦂ : μ ∣ ρ ⊢ᴸ s ⦂ A ⊒ B}
    → ρ ⊢ᴺ M ⊒ M′ ∶ p
    → s⦂ ⨟ q ≈ p
      ---------------------
    → ρ ⊢ᴺ M ⟨ s ⟩ ⊒ M′ ∶ q

  castʷ⊒ : ∀ {p : ρ ⊢ᵀ A ⊒ B′}
      {q : ρ ⊢ᵀ B ⊒ B′}
      {s⦂ : μ ∣ ρ ⊢ᴸ s ⦂ A ⊑ B}
    → ρ ⊢ᴺ M ⊒ M′ ∶ p
    → s⦂ ⨟ p ≈ q
      ---------------------
    → ρ ⊢ᴺ M ⟨ s ⟩ ⊒ M′ ∶ q

  ⊒castⁿ : ∀ {p : ρ ⊢ᵀ A ⊒ A′}
      {q : ρ ⊢ᵀ A ⊒ B′}
      {t⦂ : μ′ ∣ ρ ⊢ᴿ t ⦂ A′ ⊒ B′}
    → ρ ⊢ᴺ M ⊒ M′ ∶ p
    → p ⨟ t⦂ ≈ q
      ---------------------
    → ρ ⊢ᴺ M ⊒ M′ ⟨ t ⟩ ∶ q

  ⊒castʷ : ∀ {p : ρ ⊢ᵀ A ⊒ A′}
      {q : ρ ⊢ᵀ A ⊒ B′}
      {t⦂ : μ′ ∣ ρ ⊢ᴿ t ⦂ A′ ⊑ B′}
    → ρ ⊢ᴺ M ⊒ M′ ∶ p
    → q ⨟ t⦂ ≈ p
      ---------------------
    → ρ ⊢ᴺ M ⊒ M′ ⟨ t ⟩ ∶ q
