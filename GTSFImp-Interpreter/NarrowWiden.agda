module NarrowWiden where

-- File Charter:
--   * Defines polarized widening and narrowing derivations for the intrinsic
--     GTSFImp type language.
--   * Treats ordinary imprecision as their common structural skeleton.
--   * Makes function-domain polarity explicit: widening contains a narrowing
--     domain derivation, while narrowing contains a widening domain derivation.

open import Data.Fin using (zero)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
import Imprecision as I
open I using (ImpEnv; VarImp; extᵐ; instᵐ; X⊑★)

private
  variable
    Δ : TyCtx
    μ : ImpEnv Δ
    A A′ B B′ : Ty Δ

mutual
  data Widening {Δ : TyCtx} (μ : ImpEnv Δ) : Ty Δ → Ty Δ → Set where
    w-id★ : Widening μ ★ ★

    w-idι : ∀ {ι} → Widening μ (‵ ι) (‵ ι)

    w-idˣ : ∀ {X} → Widening μ (＇ X) (＇ X)

    w-⇒ : ∀ {A A′ B B′}
      → Narrowing μ A′ A
      → Widening μ B B′
      → Widening μ (A ⇒ B) (A′ ⇒ B′)

    w-∀ : ∀ {A B}
      → Widening (extᵐ μ) A B
      → Widening μ (`∀ A) (`∀ B)

    w-⇒★ : ∀ {A B}
      → Narrowing μ ★ A
      → Widening μ B ★
      → Widening μ (A ⇒ B) ★

    w-ι★ : ∀ {ι} → Widening μ (‵ ι) ★

    w-X★ : ∀ {X}
      → μ X ≡ X⊑★
      → Widening μ (＇ X) ★

    w-∀-elim : ∀ {A B}
      → NonVar A
      → zero ∈ᵗ A
      → Widening (instᵐ μ) A (⇑ᵗ B)
      → Widening μ (`∀ A) B

    w-∀★-elim : Widening μ (`∀ ★) ★

    w-∀★ : ∀ {A}
      → NonStar A
      → Widening (extᵐ μ) A ★
      → Widening μ (`∀ A) ★

    w-bot-elim : Widening μ (`∀ (＇ zero)) (`∀ ★)

    w-bot★ : Widening μ (`∀ (＇ zero)) ★

  data Narrowing {Δ : TyCtx} (μ : ImpEnv Δ) : Ty Δ → Ty Δ → Set where
    n-id★ : Narrowing μ ★ ★

    n-idι : ∀ {ι} → Narrowing μ (‵ ι) (‵ ι)

    n-idˣ : ∀ {X} → Narrowing μ (＇ X) (＇ X)

    n-⇒ : ∀ {A A′ B B′}
      → Widening μ A A′
      → Narrowing μ B′ B
      → Narrowing μ (A′ ⇒ B′) (A ⇒ B)

    n-∀ : ∀ {A B}
      → Narrowing (extᵐ μ) B A
      → Narrowing μ (`∀ B) (`∀ A)

    n-★⇒ : ∀ {A B}
      → Widening μ A ★
      → Narrowing μ ★ B
      → Narrowing μ ★ (A ⇒ B)

    n-★ι : ∀ {ι} → Narrowing μ ★ (‵ ι)

    n-★X : ∀ {X}
      → μ X ≡ X⊑★
      → Narrowing μ ★ (＇ X)

    n-∀-intro : ∀ {A B}
      → NonVar A
      → zero ∈ᵗ A
      → Narrowing (instᵐ μ) (⇑ᵗ B) A
      → Narrowing μ B (`∀ A)

    n-∀★-intro : Narrowing μ ★ (`∀ ★)

    n-★∀ : ∀ {A}
      → NonStar A
      → Narrowing (extᵐ μ) ★ A
      → Narrowing μ ★ (`∀ A)

    n-bot-intro : Narrowing μ (`∀ ★) (`∀ (＇ zero))

    n-★bot : Narrowing μ ★ (`∀ (＇ zero))
