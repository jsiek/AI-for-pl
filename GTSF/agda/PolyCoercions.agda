module PolyCoercions where

open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; _<_; zero; suc)
open import Data.Bool using (Bool)
open import PolyTypes public

------------------------------------------------------------------------
-- Coercions (Fig. 1)
------------------------------------------------------------------------

infixr 7 _↦_
infixr 7 ∀ᶜ_
infixr 6 _⨟_
infixr 6 _`?_
infixr 6 _!

data Coercion : Set where
  idᶜ : Ty → Coercion
  _!  : Ty → Coercion
  _`?_ : Ty → Label → Coercion
  _⁻ : Name → Coercion
  _⁺ : Name → Coercion
  _↦_ : Coercion → Coercion → Coercion
  ∀ᶜ_ : Coercion → Coercion
  _⨟_ : Coercion → Coercion → Coercion
  ⊥ᶜ_⦂_⇨_ : Label → Ty → Ty → Coercion

------------------------------------------------------------------------
-- Coercion typing (Fig. 2)
------------------------------------------------------------------------

infix 4 _∣_⊢_⦂_⇨_

data _∣_⊢_⦂_⇨_ (Σ : Store) (Δ : TyCtx) : Coercion → Ty → Ty → Set where
  ⊢idᶜ : ∀ {A}
    → WfTy Δ Σ A
    → Σ ∣ Δ ⊢ idᶜ A ⦂ A ⇨ A

  ⊢! : ∀ {G}
    → WfTy Δ Σ G
    → Ground G
    → Σ ∣ Δ ⊢ G ! ⦂ G ⇨ `★

  ⊢? : ∀ {G p}
    → WfTy Δ Σ G
    → Ground G
    → Σ ∣ Δ ⊢ G `? p ⦂ `★ ⇨ G

  ⊢↦ : ∀ {A A′ B B′ c d}
    → Σ ∣ Δ ⊢ c ⦂ A′ ⇨ A
    → Σ ∣ Δ ⊢ d ⦂ B ⇨ B′
    → Σ ∣ Δ ⊢ c ↦ d ⦂ (A ⇒ B) ⇨ (A′ ⇒ B′)

  ⊢⨟ : ∀ {A B C c d}
    → Σ ∣ Δ ⊢ c ⦂ A ⇨ B
    → Σ ∣ Δ ⊢ d ⦂ B ⇨ C
    → Σ ∣ Δ ⊢ c ⨟ d ⦂ A ⇨ C

  ⊢conceal : ∀ {U A}
    → Σ ∋ᵁ U ⦂ A
    → Σ ∣ Δ ⊢ U ⁻ ⦂ A ⇨ `U U

  ⊢reveal : ∀ {U A}
    → Σ ∋ᵁ U ⦂ A
    → Σ ∣ Δ ⊢ U ⁺ ⦂ `U U ⇨ A

  ⊢∀ᶜ : ∀ {A B c}
    → renameΣ suc Σ ∣ suc Δ ⊢ c ⦂ A ⇨ B
    → Σ ∣ Δ ⊢ ∀ᶜ c ⦂ `∀ A ⇨ `∀ B

  ⊢⊥ : ∀ {p A B}
    → WfTy Δ Σ A
    → WfTy Δ Σ B
    → Σ ∣ Δ ⊢ (⊥ᶜ p ⦂ A ⇨ B) ⦂ A ⇨ B

coerce : Label → ∀ {A B} → A ~ B → Coercion
coerce p (~-X {X = X}) = idᶜ (` X)
coerce p ~-ℕ = idᶜ `ℕ
coerce p ~-Bool = idᶜ `Bool
coerce p ~-Str = idᶜ `Str
coerce p ~-★ = idᶜ `★
coerce p (~-U {U = U}) = idᶜ (`U U)
coerce p ★~ℕ = `ℕ `? p
coerce p ℕ~★ = `ℕ !
coerce p ★~Bool = `Bool `? p
coerce p Bool~★ = `Bool !
coerce p ★~Str = `Str `? p
coerce p Str~★ = `Str !
coerce p (★~U {U = U}) = (`U U) `? p
coerce p (U~★ {U = U}) = (`U U) !
coerce p (★~⇒ c d) = ((`★ ⇒ `★) `? p) ⨟ (coerce p c ↦ coerce p d)
coerce p (⇒~★ c d) = (coerce p c ↦ coerce p d) ⨟ ((`★ ⇒ `★) !)
coerce p (★~∀ c) = ((`∀ `★) `? p) ⨟ (∀ᶜ (coerce p c))
coerce p (∀~★ c) = (∀ᶜ (coerce p c)) ⨟ ((`∀ `★) !)
coerce p (~-⇒ c d) = coerce p c ↦ coerce p d
coerce p (~-∀ c) = ∀ᶜ (coerce p c)
