module TermNarrowing where

-- File Charter:
--   * Defines well-typed narrowing between GTPLC terms.
--   * Indexes term narrowing by three-stage factored type narrowing.
--   * Uses one-context coercion narrowing and widening at casts.
--   * Checks cast squares by normalized composition of factored narrowings.
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
open import TypeRelocate
open import FactoredTypeNarrowing
open import NarrowWiden using
  ( _∣_∣_⊢_⦂_⊑_
  ; _∣_∣_⊢_⦂_⊒_
  ; _∣_∣_⊢_⊒_
  )
open import ImprecisionTheorems using (dualʷ)
open import EnvironmentNarrowing

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
  μ : ModeEnv

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
    → ρ ⊢ᴺ ƛ N ⊒ ƛ N′ ∶ (p ↦ᶠ q)

  ·⊒· : ∀ {p : ρ ⊢ᵀ A ⊒ A′}
      {q : ρ ⊢ᵀ B ⊒ B′}
    → ρ ⊢ᴺ L ⊒ L′ ∶ (p ↦ᶠ q)
    → ρ ⊢ᴺ M ⊒ M′ ∶ p
      ------------------------
    → ρ ⊢ᴺ L · M ⊒ L′ · M′ ∶ q

  Λ⊒Λ : ∀ {p : ⇑ᵉ ρ ⊢ᵀ A ⊒ B}
    → Value V
    → Value V′
    → ⇑ᵉ ρ ⊢ᴺ V ⊒ V′ ∶ p
      ----------------------
    → ρ ⊢ᴺ Λ V ⊒ Λ V′ ∶ ∀ᶠ p

  ⊒Λ : ∀ {Ψ : ImpCtx Δᴸ (suc Δᴿ)}
         {r : ρ ⊢ᵀ B ⊒ C}
         {d : ⇑ᴿᵉ ρ ⊢ᴿⁿ ⇑ᵗ C ⊒ A}
         {nvA z∈A B≢★}
    → (extension : SmartExtensionᵢ Φ Ψ)
    → Value V′
    → smart-⇑ᴿᵉ extension ρ ⊢ᴺ N ⊒ V′
        ∶ smart-extendᶠ extension r d
      ---------------------------------
    → ρ ⊢ᴺ N ⊒ Λ V′
        ∶ genᶠ nvA z∈A r d B≢★

  ⊒⟨ν⟩ : ∀ {N V′ C D c μ}
      {r : ρ ⊢ᵀ B ⊒ D}
      {d : ⇑ᴿᵉ ρ ⊢ᴿⁿ ⇑ᵗ D ⊒ A}
      {nvA z∈A B≢★}
    → Value V′
    → ρ ⊢ᴿ V′ ⦂ C
    → ρ ⊢ᴿ C
    → genᵈ μ ∣ ⇑ᴿᵉ ρ ⊢ᴿ c ∶ ⇑ᵗ C =⇒ A
    → ⇑ᴿᵉ ρ ⊢ᴺ N ⊒ (⇑ᵗᵐ V′) ⟨ c ⟩
        ∶ smart-extendᶠ freshᵢ r d
      ------------------------------------------
    → ρ ⊢ᴺ N ⊒ V′ ⟨ genᶜ c ⟩
        ∶ genᶠ nvA z∈A r d B≢★

  ν⊒ν : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
          {Φ : ImpCtx Δᴸ Δᴿ}
          {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}}
          {p : ρ ⊢ᵀ B ⊒ B′}
          {q : ⇑ᵉ ρ ⊢ᵀ C ⊒ C′}
          {s⦂ : instᵈ (modeᴸ ρ) ∣ suc Δᴸ
            ∣ ((zero , ⇑ᵗ A) ∷ ⟰ᵗ Σᴸ)
            ⊢ s ⦂ C ⊒ ⇑ᵗ B}
          {t⦂ : instᵈ (modeᴿ ρ) ∣ suc Δᴿ
            ∣ ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ Σᴿ)
            ⊢ t ⦂ C′ ⊒ ⇑ᵗ B′}
    → (a : ρ ⊢ᵀ A ⊒ A′)
    → ρ ⊢ᴺ L ⊒ L′ ∶ ∀ᶠ q
    → (s , s⦂) ⨟ⁿᶠ inst-extendᶠ (⇑ᶠ p)
        ≐ᶠ inst-extendᶠ q ⨟ᶠⁿ (t , t⦂)
      --------------------------------------------
    → ρ ⊢ᴺ ν A · L •⟨ s ⟩ ⊒
        ν A′ · L′ •⟨ t ⟩ ∶ p

  ⊒ν : ∀ {p : ρ ⊢ᵀ B ⊒ B′}
         {r : ρ ⊢ᵀ B ⊒ C}
         {e : ⇑ᴿᵉ ρ ⊢ᴿⁿ ⇑ᵗ C ⊒ C′}
         {nvC′ zero∈C′ B≢★}
         {d : ρ ⊢ᴿ⁺[ ⇑ᵗ A′ ] t ⦂ C′ ⊒ ⇑ᵗ B′}
    → ρ ⊢ᴿ A′
    → ρ ⊢ᴺ N ⊒ L′
        ∶ genᶠ nvC′ zero∈C′ r e B≢★
    → head-extendᴿᶠ (smart-extendᶠ freshᵢ r e)
        ⨟ᶠⁿ (t , d) ≐ᶠ head-extendᴿᶠ (⇑ᴿᶠ p)
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
      {s⦂ : ρ ⊢ᴸⁿ s ⦂ A ⊒ B}
    → ρ ⊢ᴺ M ⊒ M′ ∶ p
    → (s , s⦂) ⨟ⁿᶠ q ≐ᶠ p
      ---------------------
    → ρ ⊢ᴺ M ⟨ s ⟩ ⊒ M′ ∶ q

  castʷ⊒ : ∀ {p : ρ ⊢ᵀ A ⊒ B′}
      {q : ρ ⊢ᵀ B ⊒ B′}
      {s⦂ : ρ ⊢ᴸʷ s ⦂ A ⊑ B}
    → ρ ⊢ᴺ M ⊒ M′ ∶ p
    → dualʷ (s , s⦂) ⨟ⁿᶠ p ≐ᶠ q
      ---------------------
    → ρ ⊢ᴺ M ⟨ s ⟩ ⊒ M′ ∶ q

  ⊒castⁿ : ∀ {p : ρ ⊢ᵀ A ⊒ A′}
      {q : ρ ⊢ᵀ A ⊒ B′}
      {t⦂ : ρ ⊢ᴿⁿ t ⦂ A′ ⊒ B′}
    → ρ ⊢ᴺ M ⊒ M′ ∶ p
    → p ⨟ᶠⁿ (t , t⦂) ≐ᶠ q
      ---------------------
    → ρ ⊢ᴺ M ⊒ M′ ⟨ t ⟩ ∶ q

  ⊒castʷ : ∀ {p : ρ ⊢ᵀ A ⊒ A′}
      {q : ρ ⊢ᵀ A ⊒ B′}
      {t⦂ : ρ ⊢ᴿʷ t ⦂ A′ ⊑ B′}
    → ρ ⊢ᴺ M ⊒ M′ ∶ p
    → q ⨟ᶠⁿ dualʷ (t , t⦂) ≐ᶠ p
      ---------------------
    → ρ ⊢ᴺ M ⊒ M′ ⟨ t ⟩ ∶ q
