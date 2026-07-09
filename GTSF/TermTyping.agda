module TermTyping where

-- File Charter:
--   * Refined typing for GTSF NuTerms that separates compiled casts from
--     reveal/conceal conversions.
--   * The term syntax is `NuTerms.Term`; this file only defines a tighter
--     typing judgment for the compile image and its reduction successors.
--   * Casts are typed either by conversion evidence or by narrowing/widening
--     evidence in compile-generated cast modes.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; proj₁)

open import Types
open import Ctx
open import Coercions
open import Conversion
  using
    ( _∣_∣_⊢_∶_↑ˢ_
    ; _∣_∣_⊢_∶_↓ˢ_
    ; conversion↑⇒coercion
    ; conversion↓⇒coercion
    )
open import NarrowWiden
  using
    ( _∣_∣_⊢_∶_⊒_
    ; _∣_∣_⊢_∶_⊑_
    )
open import Primitives

import NuTerms as NT
open import NuTerms
  using
    ( Term
    ; Value
    ; No•
    ; ⇑ᵗᵐ
    ; `_
    ; ƛ_
    ; _·_
    ; Λ_
    ; _•
    ; ν
    ; $
    ; _⊕[_]_
    ; _⟨_⟩
    ; blame
    )

------------------------------------------------------------------------
-- Cast modes
------------------------------------------------------------------------

-- `tag-or-idᵈ` is the ordinary compile-cast mode.  `instᵈ` is included
-- because reducing an `inst` widening exposes its body under a fresh
-- ν-bound seal.  The weakened form is the mode expected after a surrounding
-- reduction allocates a newer store entry before the cast is reached; the
-- fresh entry is not mentioned by the shifted coercion, so it only permits id.
weakenCastᵈ : ModeEnv → ModeEnv
weakenCastᵈ μ zero = id-only
weakenCastᵈ μ (suc X) = μ X

data CastMode : ModeEnv → Set where
  cast-tag-or-id :
    CastMode tag-or-idᵈ

  cast-ext : ∀ {μ} →
    CastMode μ →
    CastMode (extᵈ μ)

  cast-gen : ∀ {μ} →
    CastMode μ →
    CastMode (genᵈ μ)

  cast-inst : ∀ {μ} →
    CastMode μ →
    CastMode (instᵈ μ)

  cast-weaken : ∀ {μ} →
    CastMode μ →
    CastMode (weakenCastᵈ μ)

SealModeStore★ : ModeEnv → Store → Set
SealModeStore★ μ Σ =
  ∀ α → sealModeAllowed (μ α) ≡ true → (α , ★) ∈ Σ

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

infix 4 _∣_∣_⊢_⦂_

data _∣_∣_⊢_⦂_ (Δ : TyCtx) (Σ : Store) (Γ : Ctx) :
    Term → Ty → Set₁ where

  ⊢` : ∀ {x A}
     → Γ ∋ x ⦂ A
      ----------------------
     → Δ ∣ Σ ∣ Γ ⊢ (` x) ⦂ A

  ⊢ƛ : ∀ {M A B}
     → WfTy Δ A
     → Δ ∣ Σ ∣ (A ∷ Γ) ⊢ M ⦂ B
      ----------------------------
     → Δ ∣ Σ ∣ Γ ⊢ (ƛ M) ⦂ (A ⇒ B)

  ⊢· : ∀ {L M A B}
     → Δ ∣ Σ ∣ Γ ⊢ L ⦂ (A ⇒ B)
     → Δ ∣ Σ ∣ Γ ⊢ M ⦂ A
      -------------------------
     → Δ ∣ Σ ∣ Γ ⊢ (L · M) ⦂ B

  ⊢Λ : ∀ {M A}
     → Value M
     → suc Δ ∣ ⟰ᵗ Σ ∣ ⤊ᵗ Γ ⊢ M ⦂ A
      ----------------------------
     → Δ ∣ Σ ∣ Γ ⊢ (Λ M) ⦂ (`∀ A)

  ⊢• : ∀ {Δ₀ Σ₀ V A C}
     → Δ ≡ suc Δ₀
     → Σ ≡ (zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ₀
     → WfTy (suc Δ₀) C
     → Value V
     → No• V
     → Δ₀ ∣ Σ₀ ∣ Γ ⊢ V ⦂ `∀ C
      ----------------------------------------
     → Δ ∣ Σ ∣ Γ ⊢ (⇑ᵗᵐ V) • ⦂ C

  ⊢ν↑ : ∀ {L A B C c μ}
     → WfTy Δ A
     → Δ ∣ Σ ∣ Γ ⊢ L ⦂ `∀ C
     → μ ∣ suc Δ ∣ (zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ ⊢ c ∶ C ↑ˢ ⇑ᵗ B
      --------------------------------------------
     → Δ ∣ Σ ∣ Γ ⊢ ν A L c ⦂ B

  ⊢ν⊑ : ∀ {L B C c μ}
     → CastMode μ
     → SealModeStore★ (instᵈ μ) ((zero , ★) ∷ ⟰ᵗ Σ)
     → Δ ∣ Σ ∣ Γ ⊢ L ⦂ `∀ C
     → instᵈ μ ∣ suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ ⊢ c ∶ C ⊑ ⇑ᵗ B
      --------------------------------------------
     → Δ ∣ Σ ∣ Γ ⊢ ν ★ L c ⦂ B

  ⊢$ : ∀ (κ : Const)
      -------------------------------
     → Δ ∣ Σ ∣ Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ : ∀ {L M}
     → Δ ∣ Σ ∣ Γ ⊢ L ⦂ (‵ `ℕ)
     → (op : Prim)
     → Δ ∣ Σ ∣ Γ ⊢ M ⦂ (‵ `ℕ)
      -----------------------------------
     → Δ ∣ Σ ∣ Γ ⊢ (L ⊕[ op ] M) ⦂ (‵ `ℕ)

  ⊢⟨⟩↑ : ∀ {M A B c μ}
      → μ ∣ Δ ∣ Σ ⊢ c ∶ A ↑ˢ B
      → Δ ∣ Σ ∣ Γ ⊢ M ⦂ A
      -------------------------
      → Δ ∣ Σ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B

  ⊢⟨⟩↓ : ∀ {M A B c μ}
      → μ ∣ Δ ∣ Σ ⊢ c ∶ A ↓ˢ B
      → Δ ∣ Σ ∣ Γ ⊢ M ⦂ A
      -------------------------
      → Δ ∣ Σ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B

  ⊢⟨⟩⊒ : ∀ {M A B c μ}
      → CastMode μ
      → SealModeStore★ μ Σ
      → μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B
      → Δ ∣ Σ ∣ Γ ⊢ M ⦂ A
      -------------------------
      → Δ ∣ Σ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B

  ⊢⟨⟩⊑ : ∀ {M A B c μ}
      → CastMode μ
      → SealModeStore★ μ Σ
      → μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B
      → Δ ∣ Σ ∣ Γ ⊢ M ⦂ A
      -------------------------
      → Δ ∣ Σ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B

  ⊢blame : ∀ {A}
      → WfTy Δ A
      ----------------------------
      → Δ ∣ Σ ∣ Γ ⊢ blame ⦂ A

------------------------------------------------------------------------
-- Forgetting the refined cast classes
------------------------------------------------------------------------

forget :
  ∀ {Δ Σ Γ M A} →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  NT._∣_∣_⊢_⦂_ Δ Σ Γ M A
forget (⊢` x∈) =
  NT.⊢` x∈
forget (⊢ƛ hA M⊢) =
  NT.⊢ƛ hA (forget M⊢)
forget (⊢· L⊢ M⊢) =
  NT.⊢· (forget L⊢) (forget M⊢)
forget (⊢Λ vM M⊢) =
  NT.⊢Λ vM (forget M⊢)
forget (⊢• refl refl hC vV noV V⊢) =
  NT.⊢• refl refl hC vV noV (forget V⊢)
forget (⊢ν↑ hA L⊢ c⊢) =
  NT.⊢ν hA (forget L⊢) (conversion↑⇒coercion c⊢)
forget (⊢ν⊑ mode seal★ L⊢ c⊢) =
  NT.⊢ν wf★ (forget L⊢) (proj₁ c⊢)
forget (⊢$ κ) =
  NT.⊢$ κ
forget (⊢⊕ L⊢ op M⊢) =
  NT.⊢⊕ (forget L⊢) op (forget M⊢)
forget (⊢⟨⟩↑ c⊢ M⊢) =
  NT.⊢⟨⟩ (conversion↑⇒coercion c⊢) (forget M⊢)
forget (⊢⟨⟩↓ c⊢ M⊢) =
  NT.⊢⟨⟩ (conversion↓⇒coercion c⊢) (forget M⊢)
forget (⊢⟨⟩⊒ mode seal★ c⊢ M⊢) =
  NT.⊢⟨⟩ (proj₁ c⊢) (forget M⊢)
forget (⊢⟨⟩⊑ mode seal★ c⊢ M⊢) =
  NT.⊢⟨⟩ (proj₁ c⊢) (forget M⊢)
forget (⊢blame hA) =
  NT.⊢blame hA
