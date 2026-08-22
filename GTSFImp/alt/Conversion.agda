module alt.Conversion where

-- File Charter:
--   * Defines raw, endpoint-free reveal and conceal conversion shapes.
--   * Defines the self-contained scoped conversion-typing judgments.
--   * Provides type-directed shape generators and their typing proofs.
--   * Depends only on Types: stores, anchors, and classifiers are node data.

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no)

open import Types

private
  variable
    Δ : TyCtx

------------------------------------------------------------------------
-- Inserting one scoped-variable slot
------------------------------------------------------------------------

punchIn : ∀ {Δ} → Fin (Nat.suc Δ) → Fin Δ → Fin (Nat.suc Δ)
punchIn zero Y = suc Y
punchIn (suc X) zero = zero
punchIn (suc X) (suc Y) = suc (punchIn X Y)

wkᵗ : ∀ {Δ} → Fin (Nat.suc Δ) → Ty Δ → Ty (Nat.suc Δ)
wkᵗ X = renameᵗ (punchIn X)

------------------------------------------------------------------------
-- Replacing one abstract type by its representation
------------------------------------------------------------------------

replaceTy : TyVar Δ → Ty Δ → Ty Δ → Ty Δ
replaceTy X R (＇ Y) with X ≟ Y
replaceTy X R (＇ .X) | yes refl = R
replaceTy X R (＇ Y) | no X≠Y = ＇ Y
replaceTy X R (‵ ι) = ‵ ι
replaceTy X R ★ = ★
replaceTy X R (A ⇒ B) = replaceTy X R A ⇒ replaceTy X R B
replaceTy X R (`∀ A) = `∀ (replaceTy (suc X) (⇑ᵗ R) A)

------------------------------------------------------------------------
-- Raw conversion shapes
------------------------------------------------------------------------

infixr 7 _↦↑_ _↦↓_

mutual
  data Reveal : Set where
    unseal : Reveal
    _↦↑_ : Conceal → Reveal → Reveal
    `∀↑_ : Reveal → Reveal
    id↑ : Reveal

  data Conceal : Set where
    seal : Conceal
    _↦↓_ : Reveal → Conceal → Conceal
    `∀↓_ : Conceal → Conceal
    id↓ : Conceal

------------------------------------------------------------------------
-- Scoped conversion typing
------------------------------------------------------------------------

-- Read `⊢↑[ X ⦂ R ] c ⦂ A ↝ B` as: at pivot X, whose scoped
-- representation is R, the raw reveal shape c converts A to B.  The
-- conceal judgment is dual.  Neither judgment mentions a store, anchor,
-- or scoped-variable classifier.

infix 4 ⊢↑[_⦂_]_⦂_↝_ ⊢↓[_⦂_]_⦂_↝_

mutual
  data ⊢↑[_⦂_]_⦂_↝_ {Δ : TyCtx} :
      TyVar Δ → Ty Δ → Reveal → Ty Δ → Ty Δ → Set where
    ⊢unseal : ∀ {X R}
      → ⊢↑[ X ⦂ R ] unseal ⦂ ＇ X ↝ R

    ⊢↑-⇒ : ∀ {X R c d A A′ B B′}
      → ⊢↓[ X ⦂ R ] c ⦂ A′ ↝ A
      → ⊢↑[ X ⦂ R ] d ⦂ B ↝ B′
      → ⊢↑[ X ⦂ R ] c ↦↑ d ⦂ A ⇒ B ↝ A′ ⇒ B′

    ⊢↑-∀ : ∀ {X R c A B}
      → ⊢↑[ suc X ⦂ ⇑ᵗ R ] c ⦂ A ↝ B
      → ⊢↑[ X ⦂ R ] `∀↑ c ⦂ `∀ A ↝ `∀ B

    ⊢id↑ : ∀ {X R A}
      → Atom A
      → ⊢↑[ X ⦂ R ] id↑ ⦂ A ↝ A

  data ⊢↓[_⦂_]_⦂_↝_ {Δ : TyCtx} :
      TyVar Δ → Ty Δ → Conceal → Ty Δ → Ty Δ → Set where
    ⊢seal : ∀ {X R}
      → ⊢↓[ X ⦂ R ] seal ⦂ R ↝ ＇ X

    ⊢↓-⇒ : ∀ {X R c d A A′ B B′}
      → ⊢↑[ X ⦂ R ] c ⦂ A′ ↝ A
      → ⊢↓[ X ⦂ R ] d ⦂ B ↝ B′
      → ⊢↓[ X ⦂ R ] c ↦↓ d ⦂ A ⇒ B ↝ A′ ⇒ B′

    ⊢↓-∀ : ∀ {X R c A B}
      → ⊢↓[ suc X ⦂ ⇑ᵗ R ] c ⦂ A ↝ B
      → ⊢↓[ X ⦂ R ] `∀↓ c ⦂ `∀ A ↝ `∀ B

    ⊢id↓ : ∀ {X R A}
      → Atom A
      → ⊢↓[ X ⦂ R ] id↓ ⦂ A ↝ A

------------------------------------------------------------------------
-- Structural conversion generation
------------------------------------------------------------------------

mutual
  〖_,_↑_〗 : TyVar Δ → Ty Δ → Ty Δ → Reveal
  〖 X , R ↑ (＇ Y) 〗 with X ≟ Y
  〖 X , R ↑ (＇ .X) 〗 | yes refl = unseal
  〖 X , R ↑ (＇ Y) 〗 | no X≠Y = id↑
  〖 X , R ↑ (‵ ι) 〗 = id↑
  〖 X , R ↑ ★ 〗 = id↑
  〖 X , R ↑ (A ⇒ B) 〗 =
    makeConceal X R A ↦↑ 〖 X , R ↑ B 〗
  〖 X , R ↑ (`∀ A) 〗 = `∀↑ 〖 suc X , ⇑ᵗ R ↑ A 〗

  makeConceal : TyVar Δ → Ty Δ → Ty Δ → Conceal
  makeConceal X R (＇ Y) with X ≟ Y
  makeConceal X R (＇ .X) | yes refl = seal
  makeConceal X R (＇ Y) | no X≠Y = id↓
  makeConceal X R (‵ ι) = id↓
  makeConceal X R ★ = id↓
  makeConceal X R (A ⇒ B) =
    〖 X , R ↑ A 〗 ↦↓ makeConceal X R B
  makeConceal X R (`∀ A) =
    `∀↓ makeConceal (suc X) (⇑ᵗ R) A

mutual
  generator-typed↑ : (X : TyVar Δ) (R B : Ty Δ)
    → ⊢↑[ X ⦂ R ] 〖 X , R ↑ B 〗 ⦂ B ↝ replaceTy X R B
  generator-typed↑ X R (＇ Y) with X ≟ Y
  generator-typed↑ X R (＇ .X) | yes refl = ⊢unseal
  generator-typed↑ X R (＇ Y) | no X≠Y = ⊢id↑ (＇ Y)
  generator-typed↑ X R (‵ ι) = ⊢id↑ (‵ ι)
  generator-typed↑ X R ★ = ⊢id↑ ★
  generator-typed↑ X R (A ⇒ B) =
    ⊢↑-⇒ (generator-typed↓ X R A) (generator-typed↑ X R B)
  generator-typed↑ X R (`∀ B) =
    ⊢↑-∀ (generator-typed↑ (suc X) (⇑ᵗ R) B)

  generator-typed↓ : (X : TyVar Δ) (R B : Ty Δ)
    → ⊢↓[ X ⦂ R ] makeConceal X R B ⦂ replaceTy X R B ↝ B
  generator-typed↓ X R (＇ Y) with X ≟ Y
  generator-typed↓ X R (＇ .X) | yes refl = ⊢seal
  generator-typed↓ X R (＇ Y) | no X≠Y = ⊢id↓ (＇ Y)
  generator-typed↓ X R (‵ ι) = ⊢id↓ (‵ ι)
  generator-typed↓ X R ★ = ⊢id↓ ★
  generator-typed↓ X R (A ⇒ B) =
    ⊢↓-⇒ (generator-typed↑ X R A) (generator-typed↓ X R B)
  generator-typed↓ X R (`∀ B) =
    ⊢↓-∀ (generator-typed↓ (suc X) (⇑ᵗ R) B)

------------------------------------------------------------------------
-- Structural delimiters
------------------------------------------------------------------------

mutual
  δ↑ : Ty Δ → Reveal
  δ↑ (＇ X) = id↑
  δ↑ (‵ ι) = id↑
  δ↑ ★ = id↑
  δ↑ (A ⇒ B) = δ↓ A ↦↑ δ↑ B
  δ↑ (`∀ A) = `∀↑ δ↑ A

  δ↓ : Ty Δ → Conceal
  δ↓ (＇ X) = id↓
  δ↓ (‵ ι) = id↓
  δ↓ ★ = id↓
  δ↓ (A ⇒ B) = δ↑ A ↦↓ δ↓ B
  δ↓ (`∀ A) = `∀↓ δ↓ A

mutual
  delimiter-typed↑ : (X : TyVar Δ) (R A : Ty Δ)
    → ⊢↑[ X ⦂ R ] δ↑ A ⦂ A ↝ A
  delimiter-typed↑ X R (＇ Y) = ⊢id↑ (＇ Y)
  delimiter-typed↑ X R (‵ ι) = ⊢id↑ (‵ ι)
  delimiter-typed↑ X R ★ = ⊢id↑ ★
  delimiter-typed↑ X R (A ⇒ B) =
    ⊢↑-⇒ (delimiter-typed↓ X R A) (delimiter-typed↑ X R B)
  delimiter-typed↑ X R (`∀ A) =
    ⊢↑-∀ (delimiter-typed↑ (suc X) (⇑ᵗ R) A)

  delimiter-typed↓ : (X : TyVar Δ) (R A : Ty Δ)
    → ⊢↓[ X ⦂ R ] δ↓ A ⦂ A ↝ A
  delimiter-typed↓ X R (＇ Y) = ⊢id↓ (＇ Y)
  delimiter-typed↓ X R (‵ ι) = ⊢id↓ (‵ ι)
  delimiter-typed↓ X R ★ = ⊢id↓ ★
  delimiter-typed↓ X R (A ⇒ B) =
    ⊢↓-⇒ (delimiter-typed↑ X R A) (delimiter-typed↓ X R B)
  delimiter-typed↓ X R (`∀ A) =
    ⊢↓-∀ (delimiter-typed↓ (suc X) (⇑ᵗ R) A)
