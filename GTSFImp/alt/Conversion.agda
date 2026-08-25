module alt.Conversion where

-- File Charter:
--   * Defines raw, endpoint-free reveal and conceal conversion shapes.
--   * Defines the self-contained scoped conversion-typing judgments.
--   * Provides type-directed shape generators and their typing proofs.
--   * Depends only on Types: stores, anchors, and classifiers are node data.

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; trans)
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

punchOut : ∀ {n} (Y X : Fin (Nat.suc n)) → Y ≢ X → Fin n
punchOut zero zero Y≢X = ⊥-elim (Y≢X refl)
punchOut zero (suc X) Y≢X = X
punchOut {n = Nat.suc n} (suc Y) zero Y≢X = zero
punchOut {n = Nat.suc n} (suc Y) (suc X) Y≢X =
  suc (punchOut Y X (λ Y≡X → Y≢X (cong suc Y≡X)))

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
-- Resolving one scoped-variable slot
------------------------------------------------------------------------

-- Resolution removes Y and replaces it by the representation C.  This lives
-- with insertion because telescope deletion and the dynamic rules share the
-- same scoped substitution.

private
  resolved-punchIn≢ : ∀ {n} (Y : Fin (Nat.suc n)) (X : Fin n)
    → Y ≢ punchIn Y X
  resolved-punchIn≢ zero X ()
  resolved-punchIn≢ (suc Y) zero ()
  resolved-punchIn≢ (suc Y) (suc X) eq =
    resolved-punchIn≢ Y X (suc-injective eq)
    where
    suc-injective : ∀ {m} {Z W : Fin m} → suc Z ≡ suc W → Z ≡ W
    suc-injective refl = refl

  resolved-punchOut-punchIn : ∀ {n} (Y : Fin (Nat.suc n))
      (X : Fin n)
      (Y≢X : Y ≢ punchIn Y X)
    → punchOut Y (punchIn Y X) Y≢X ≡ X
  resolved-punchOut-punchIn zero X Y≢X = refl
  resolved-punchOut-punchIn (suc Y) zero Y≢X = refl
  resolved-punchOut-punchIn (suc Y) (suc X) Y≢X =
    cong suc (resolved-punchOut-punchIn Y X _)

  punchIn-resolved-punchOut : ∀ {n} (Y X : Fin (Nat.suc n))
      (Y≢X : Y ≢ X)
    → punchIn Y (punchOut Y X Y≢X) ≡ X
  punchIn-resolved-punchOut zero zero Y≢X = ⊥-elim (Y≢X refl)
  punchIn-resolved-punchOut zero (suc X) Y≢X = refl
  punchIn-resolved-punchOut {n = Nat.suc n} (suc Y) zero Y≢X = refl
  punchIn-resolved-punchOut {n = Nat.suc n} (suc Y) (suc X) Y≢X =
    cong suc (punchIn-resolved-punchOut Y X _)

resolveSubᵗ : ∀ {Δ} → TyVar (Nat.suc Δ) → Ty Δ → Nat.suc Δ ⇒ˢ Δ
resolveSubᵗ Y C X with Y ≟ X
resolveSubᵗ Y C .Y | yes refl = C
resolveSubᵗ Y C X | no Y≢X = ＇ punchOut Y X Y≢X

resolveSub-punchIn : ∀ {Δ} (Y : TyVar (Nat.suc Δ)) (C : Ty Δ)
    (X : TyVar Δ)
  → resolveSubᵗ Y C (punchIn Y X) ≡ ＇ X
resolveSub-punchIn Y C X with Y ≟ punchIn Y X
resolveSub-punchIn Y C X | yes eq =
  ⊥-elim (resolved-punchIn≢ Y X eq)
resolveSub-punchIn Y C X | no Y≢X
    rewrite resolved-punchOut-punchIn Y X Y≢X =
  refl

resolveSub-here : ∀ {Δ} (Y : TyVar (Nat.suc Δ)) (C : Ty Δ)
  → resolveSubᵗ Y C Y ≡ C
resolveSub-here Y C with Y ≟ Y
resolveSub-here Y C | yes refl = refl
resolveSub-here Y C | no Y≢Y = ⊥-elim (Y≢Y refl)

resolveSub-reembed : ∀ {Δ} (Y : TyVar (Nat.suc Δ)) (C : Ty Δ)
    (X : TyVar (Nat.suc Δ))
  → renameᵗ (punchIn Y) (resolveSubᵗ Y C X)
    ≡ replaceTy Y (wkᵗ Y C) (＇ X)
resolveSub-reembed Y C X with Y ≟ X
resolveSub-reembed Y C .Y | yes refl = refl
resolveSub-reembed Y C X | no Y≢X
    rewrite punchIn-resolved-punchOut Y X Y≢X =
  refl

resolveSub-ext : ∀ {Δ} (Y : TyVar (Nat.suc Δ)) (C : Ty Δ)
    (X : TyVar (Nat.suc (Nat.suc Δ)))
  → resolveSubᵗ (suc Y) (⇑ᵗ C) X ≡ extsᵗ (resolveSubᵗ Y C) X
resolveSub-ext Y C zero = refl
resolveSub-ext Y C (suc X) with Y ≟ X
resolveSub-ext Y C (suc .Y) | yes refl = refl
resolveSub-ext Y C (suc X) | no Y≢X = refl

resolve-wkᵗ : ∀ {Δ} (Y : TyVar (Nat.suc Δ)) (C A : Ty Δ)
  → substᵗ (resolveSubᵗ Y C) (wkᵗ Y A) ≡ A
resolve-wkᵗ Y C A =
  trans (substᵗ-rename (resolveSubᵗ Y C) (punchIn Y) A)
    (trans (substᵗ-cong A (resolveSub-punchIn Y C))
      (substᵗ-id A))

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
