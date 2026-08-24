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
-- Total conversion endpoints
------------------------------------------------------------------------

-- On the typed fragment, a reveal's source and a conceal's target need no
-- representation: `unseal` fixes its source to the pivot and `seal` fixes
-- its target to the pivot.  Ill-shaped shape/type pairs are junk inputs;
-- returning the supplied endpoint keeps these functions total without
-- assigning them any dynamic meaning.

mutual
  src↑ : TyVar Δ → Reveal → Ty Δ → Ty Δ
  src↑ X unseal T = ＇ X
  src↑ X (c ↦↑ d) (A ⇒ B) = tgt↓ X c A ⇒ src↑ X d B
  src↑ X (c ↦↑ d) (＇ Y) = ＇ Y
  src↑ X (c ↦↑ d) (‵ ι) = ‵ ι
  src↑ X (c ↦↑ d) ★ = ★
  src↑ X (c ↦↑ d) (`∀ B) = `∀ B
  src↑ X (`∀↑ c) (`∀ B) = `∀ (src↑ (suc X) c B)
  src↑ X (`∀↑ c) (＇ Y) = ＇ Y
  src↑ X (`∀↑ c) (‵ ι) = ‵ ι
  src↑ X (`∀↑ c) ★ = ★
  src↑ X (`∀↑ c) (A ⇒ B) = A ⇒ B
  src↑ X id↑ T = T

  tgt↓ : TyVar Δ → Conceal → Ty Δ → Ty Δ
  tgt↓ X seal A = ＇ X
  tgt↓ X (c ↦↓ d) (A ⇒ B) = src↑ X c A ⇒ tgt↓ X d B
  tgt↓ X (c ↦↓ d) (＇ Y) = ＇ Y
  tgt↓ X (c ↦↓ d) (‵ ι) = ‵ ι
  tgt↓ X (c ↦↓ d) ★ = ★
  tgt↓ X (c ↦↓ d) (`∀ A) = `∀ A
  tgt↓ X (`∀↓ c) (`∀ A) = `∀ (tgt↓ (suc X) c A)
  tgt↓ X (`∀↓ c) (＇ Y) = ＇ Y
  tgt↓ X (`∀↓ c) (‵ ι) = ‵ ι
  tgt↓ X (`∀↓ c) ★ = ★
  tgt↓ X (`∀↓ c) (A ⇒ B) = A ⇒ B
  tgt↓ X id↓ A = A

-- The other two directions must know the pivot's representation: it is the
-- source of `seal` and the target of `unseal`.  They use the same junk-total
-- convention on shape/type mismatches.

mutual
  src↓ : TyVar Δ → Ty Δ → Conceal → Ty Δ → Ty Δ
  src↓ X R seal T = R
  src↓ X R (c ↦↓ d) (A ⇒ B) =
    tgt↑ X R c A ⇒ src↓ X R d B
  src↓ X R (c ↦↓ d) (＇ Y) = ＇ Y
  src↓ X R (c ↦↓ d) (‵ ι) = ‵ ι
  src↓ X R (c ↦↓ d) ★ = ★
  src↓ X R (c ↦↓ d) (`∀ B) = `∀ B
  src↓ X R (`∀↓ c) (`∀ B) =
    `∀ (src↓ (suc X) (⇑ᵗ R) c B)
  src↓ X R (`∀↓ c) (＇ Y) = ＇ Y
  src↓ X R (`∀↓ c) (‵ ι) = ‵ ι
  src↓ X R (`∀↓ c) ★ = ★
  src↓ X R (`∀↓ c) (A ⇒ B) = A ⇒ B
  src↓ X R id↓ T = T

  tgt↑ : TyVar Δ → Ty Δ → Reveal → Ty Δ → Ty Δ
  tgt↑ X R unseal A = R
  tgt↑ X R (c ↦↑ d) (A ⇒ B) =
    src↓ X R c A ⇒ tgt↑ X R d B
  tgt↑ X R (c ↦↑ d) (＇ Y) = ＇ Y
  tgt↑ X R (c ↦↑ d) (‵ ι) = ‵ ι
  tgt↑ X R (c ↦↑ d) ★ = ★
  tgt↑ X R (c ↦↑ d) (`∀ A) = `∀ A
  tgt↑ X R (`∀↑ c) (`∀ A) =
    `∀ (tgt↑ (suc X) (⇑ᵗ R) c A)
  tgt↑ X R (`∀↑ c) (＇ Y) = ＇ Y
  tgt↑ X R (`∀↑ c) (‵ ι) = ‵ ι
  tgt↑ X R (`∀↑ c) ★ = ★
  tgt↑ X R (`∀↑ c) (A ⇒ B) = A ⇒ B
  tgt↑ X R id↑ A = A

------------------------------------------------------------------------
-- Structural conversion generation
------------------------------------------------------------------------

-- Raw shapes carry no endpoints, so the generators depend only on the
-- pivot and the target type's structure; the representation argument of
-- the earlier intrinsic generators is gone.
mutual
  〖_↑_〗 : TyVar Δ → Ty Δ → Reveal
  〖 X ↑ (＇ Y) 〗 with X ≟ Y
  〖 X ↑ (＇ .X) 〗 | yes refl = unseal
  〖 X ↑ (＇ Y) 〗 | no X≠Y = id↑
  〖 X ↑ (‵ ι) 〗 = id↑
  〖 X ↑ ★ 〗 = id↑
  〖 X ↑ (A ⇒ B) 〗 = 〖 X ↓ A 〗 ↦↑ 〖 X ↑ B 〗
  〖 X ↑ (`∀ A) 〗 = `∀↑ 〖 suc X ↑ A 〗

  〖_↓_〗 : TyVar Δ → Ty Δ → Conceal
  〖 X ↓ (＇ Y) 〗 with X ≟ Y
  〖 X ↓ (＇ .X) 〗 | yes refl = seal
  〖 X ↓ (＇ Y) 〗 | no X≠Y = id↓
  〖 X ↓ (‵ ι) 〗 = id↓
  〖 X ↓ ★ 〗 = id↓
  〖 X ↓ (A ⇒ B) 〗 = 〖 X ↑ A 〗 ↦↓ 〖 X ↓ B 〗
  〖 X ↓ (`∀ A) 〗 = `∀↓ 〖 suc X ↓ A 〗

mutual
  generator-typed↑ : (X : TyVar Δ) (R B : Ty Δ)
    → ⊢↑[ X ⦂ R ] 〖 X ↑ B 〗 ⦂ B ↝ replaceTy X R B
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
    → ⊢↓[ X ⦂ R ] 〖 X ↓ B 〗 ⦂ replaceTy X R B ↝ B
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
