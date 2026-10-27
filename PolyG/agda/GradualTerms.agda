module GradualTerms where

-- File Charter:
--   * The surface language PolyGν of Max New's thesis (Ch. 10, Fig. 10.1
--     and 10.3), ∀ν fragment: ascription, seal/unseal at known type
--     variables, tag checks, booleans, functions, let, Λν, and the
--     instantiation form `let x = M {X ≅ B}; N`.
--   * Typing uses consistency, gradual meet, and the partial functions
--     dom/cod and un∀ν "up to ?" (as relations AsFun and AsForall).

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)

open import Types
open import Typing using (Ctx; _∋_⦂_; Z; S; ⤊) public

------------------------------------------------------------------------
-- Surface terms
------------------------------------------------------------------------

infixl 7 _·_
infix 9 `_
infixl 6 _⦂⦂_

data GTerm : Set where
  `_     : ℕ → GTerm
  _⦂⦂_   : GTerm → Ty → GTerm
  seal   : Var → GTerm → GTerm
  unseal : Var → GTerm → GTerm
  is     : Ground → GTerm → GTerm
  true   : GTerm
  false  : GTerm
  if     : GTerm → GTerm → GTerm → GTerm
  ƛ      : Ty → GTerm → GTerm
  _·_    : GTerm → GTerm → GTerm
  letv   : GTerm → GTerm → GTerm
  Λν     : GTerm → GTerm
  inst   : GTerm → Ty → GTerm → GTerm   -- let x = M {X ≅ B}; N

------------------------------------------------------------------------
-- Consistency, meet, and elimination shapes up to ?
------------------------------------------------------------------------

infix 4 _∼_

data _∼_ : Ty → Ty → Set where
  ∼★L : ∀ {A} → ★ ∼ A
  ∼★R : ∀ {A} → A ∼ ★
  ∼‵  : ∀ {α} → ‵ α ∼ ‵ α
  ∼𝔹  : 𝔹 ∼ 𝔹
  ∼⇒  : ∀ {A A′ B B′} → A ∼ A′ → B ∼ B′ → A ⇒ B ∼ A′ ⇒ B′
  ∼∀  : ∀ {A B} → A ∼ B → ∀ν A ∼ ∀ν B

-- Meet A B C: C is the gradual meet A ⊓ B
data Meet : Ty → Ty → Ty → Set where
  m★L : ∀ {A} → Meet ★ A A
  m★R : ∀ {A} → Meet A ★ A
  m‵  : ∀ {α} → Meet (‵ α) (‵ α) (‵ α)
  m𝔹  : Meet 𝔹 𝔹 𝔹
  m⇒  : ∀ {A A′ A″ B B′ B″} →
        Meet A A′ A″ → Meet B B′ B″ → Meet (A ⇒ B) (A′ ⇒ B′) (A″ ⇒ B″)
  m∀  : ∀ {A B C} → Meet A B C → Meet (∀ν A) (∀ν B) (∀ν C)

-- dom and cod up to ?
data AsFun : Ty → Ty → Ty → Set where
  as-fun : ∀ {A B} → AsFun (A ⇒ B) A B
  as-fun★ : AsFun ★ ★ ★

-- un∀ν up to ?: the body, read under the bound variable
data AsForall : Ty → Ty → Set where
  as-∀ : ∀ {A} → AsForall (∀ν A) A
  as-∀★ : AsForall ★ ★

------------------------------------------------------------------------
-- Typing (thesis Fig. 10.3)
------------------------------------------------------------------------

infix 4 _∣_⊢ᴳ_⦂_

data _∣_⊢ᴳ_⦂_ (Δ : TyEnv) : Ctx → GTerm → Ty → Set where
  ⊢` : ∀ {Γ x A} →
    Γ ∋ x ⦂ A →
    Δ ∣ Γ ⊢ᴳ ` x ⦂ A

  ⊢⦂⦂ : ∀ {Γ M A B} →
    Δ ∣ Γ ⊢ᴳ M ⦂ A →
    A ∼ B →
    WfTy (tsize Δ) B →
    Δ ∣ Γ ⊢ᴳ M ⦂⦂ B ⦂ B

  ⊢seal : ∀ {Γ X M A B} →
    Δ ∋ X ≅ A →
    Δ ∣ Γ ⊢ᴳ M ⦂ B →
    B ∼ A →
    Δ ∣ Γ ⊢ᴳ seal X M ⦂ ‵ tvar X

  ⊢unseal : ∀ {Γ X M A B} →
    Δ ∋ X ≅ A →
    Δ ∣ Γ ⊢ᴳ M ⦂ B →
    B ∼ ‵ tvar X →
    Δ ∣ Γ ⊢ᴳ unseal X M ⦂ A

  ⊢is : ∀ {Γ G M A} →
    WfGround (tsize Δ) G →
    Δ ∣ Γ ⊢ᴳ M ⦂ A →
    Δ ∣ Γ ⊢ᴳ is G M ⦂ 𝔹

  ⊢true : ∀ {Γ} →
    Δ ∣ Γ ⊢ᴳ true ⦂ 𝔹

  ⊢false : ∀ {Γ} →
    Δ ∣ Γ ⊢ᴳ false ⦂ 𝔹

  ⊢if : ∀ {Γ L M N A Bt Bf B} →
    Δ ∣ Γ ⊢ᴳ L ⦂ A →
    A ∼ 𝔹 →
    Δ ∣ Γ ⊢ᴳ M ⦂ Bt →
    Δ ∣ Γ ⊢ᴳ N ⦂ Bf →
    Meet Bt Bf B →
    Δ ∣ Γ ⊢ᴳ if L M N ⦂ B

  ⊢ƛ : ∀ {Γ A B M} →
    WfTy (tsize Δ) A →
    Δ ∣ (A ∷ Γ) ⊢ᴳ M ⦂ B →
    Δ ∣ Γ ⊢ᴳ ƛ A M ⦂ A ⇒ B

  ⊢· : ∀ {Γ L M A A₁ A₂ B} →
    Δ ∣ Γ ⊢ᴳ L ⦂ A →
    AsFun A A₁ A₂ →
    Δ ∣ Γ ⊢ᴳ M ⦂ B →
    B ∼ A₁ →
    Δ ∣ Γ ⊢ᴳ L · M ⦂ A₂

  ⊢letv : ∀ {Γ M N A B} →
    Δ ∣ Γ ⊢ᴳ M ⦂ A →
    Δ ∣ (A ∷ Γ) ⊢ᴳ N ⦂ B →
    Δ ∣ Γ ⊢ᴳ letv M N ⦂ B

  ⊢Λν : ∀ {Γ M A} →
    (abs ∷ Δ) ∣ ⤊ Γ ⊢ᴳ M ⦂ A →
    Δ ∣ Γ ⊢ᴳ Λν M ⦂ ∀ν A

  ⊢inst : ∀ {Γ M N A A′ B C} →
    Δ ∣ Γ ⊢ᴳ M ⦂ A →
    AsForall A A′ →
    WfTy (tsize Δ) B →
    (known B ∷ Δ) ∣ (A′ ∷ ⤊ Γ) ⊢ᴳ N ⦂ ⇑ᵗ C →
    WfTy (tsize Δ) C →
    Δ ∣ Γ ⊢ᴳ inst M B N ⦂ C
