module
  proof.Target.SealTag.NuImprecisionTargetGroundUniqueness where

-- File Charter:
--   * Proves uniqueness of a ground target selected by one source type.
--   * Uses source-name exclusivity at variable leaves.
--   * Contains no term relation, simulation result, or operational proof.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (zero)
open import ImprecisionWf using
  ( NonVar
  ; id★
  ; idˣ
  ; idι
  ; nonvar-all
  ; nonvar-base
  ; nonvar-fun
  ; nonvar-star
  ; tag_
  ; tag_⇛_
  ; tagˣ
  ; ν
  ; _↦_
  ; _∣_⊢_⊑_⊣_
  )
open import Types using
  (Ground; Ty; occurs; ★; ★⇒★; ＇_; ‵_; _⇒_; `∀)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityProof using
  (source-name-exclusive-source-only-head)
open import proof.Compilation.GenSafeProperties using
  (GenSafeShape; shape-all; shape-fun)


target-ground-unique :
  ∀ {Φ Δᴸ Δᴿ A G H} →
  SourceNameExclusive Φ →
  Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ G ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ H ⊣ Δᴿ →
  Ground G →
  Ground H →
  G ≡ H
target-ground-unique exclusive id★ id★ r () gH
target-ground-unique exclusive (tag ι) idι idι
    (‵ .ι) (‵ .ι) =
  refl
target-ground-unique exclusive
    (tag p ⇛ q) (r ↦ s) (t ↦ u) ★⇒★ ★⇒★ =
  refl
target-ground-unique exclusive
    (tagˣ source-only α<) (idˣ matched source< β<) r
    (＇ β) gH =
  ⊥-elim (exclusive source-only matched)
target-ground-unique exclusive
    (ν safe occ p) (ν safeG occG q) (ν safeH occH r)
    gG gH =
  target-ground-unique
    (source-name-exclusive-source-only-head exclusive)
    p q r gG gH


nonvar-occurs-star-to-function :
  ∀ {Φ Δᴸ Δᴿ A} →
  NonVar A →
  occurs zero A ≡ true →
  Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ ★ ⇒ ★ ⊣ Δᴿ
nonvar-occurs-star-to-function nonvar-base () p
nonvar-occurs-star-to-function nonvar-star () p
nonvar-occurs-star-to-function nonvar-fun occ
    (tag p ⇛ q) =
  p ↦ q
nonvar-occurs-star-to-function nonvar-all occ
    (ν safe inner-occ p) =
  ν safe inner-occ
    (nonvar-occurs-star-to-function safe inner-occ p)


nonvar-occurs-ground-function :
  ∀ {Φ Δᴸ Δᴿ A H} →
  NonVar A →
  occurs zero A ≡ true →
  Φ ∣ Δᴸ ⊢ A ⊑ H ⊣ Δᴿ →
  Ground H →
  H ≡ ★ ⇒ ★
nonvar-occurs-ground-function nonvar-base () q gH
nonvar-occurs-ground-function nonvar-star () q gH
nonvar-occurs-ground-function nonvar-fun occ
    (p ↦ q) ★⇒★ =
  refl
nonvar-occurs-ground-function nonvar-all occ
    (ν safe inner-occ p) gH =
  nonvar-occurs-ground-function safe inner-occ p gH


gen-safe-shape-star-to-function :
  ∀ {Φ Δᴸ Δᴿ A} →
  GenSafeShape A →
  Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ ★ ⇒ ★ ⊣ Δᴿ
gen-safe-shape-star-to-function shape-fun
    (tag p ⇛ q) =
  p ↦ q
gen-safe-shape-star-to-function shape-all
    (ν safe occ p) =
  ν safe occ
    (nonvar-occurs-star-to-function safe occ p)


gen-safe-shape-ground-function :
  ∀ {Φ Δᴸ Δᴿ A H} →
  GenSafeShape A →
  Φ ∣ Δᴸ ⊢ A ⊑ H ⊣ Δᴿ →
  Ground H →
  H ≡ ★ ⇒ ★
gen-safe-shape-ground-function shape-fun
    (p ↦ q) ★⇒★ =
  refl
gen-safe-shape-ground-function shape-all
    (ν safe occ p) gH =
  nonvar-occurs-ground-function safe occ p gH


universal-star-to-function :
  ∀ {Φ Δᴸ Δᴿ A} →
  Φ ∣ Δᴸ ⊢ `∀ A ⊑ ★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ `∀ A ⊑ ★ ⇒ ★ ⊣ Δᴿ
universal-star-to-function (ν safe occ p) =
  ν safe occ
    (nonvar-occurs-star-to-function safe occ p)


universal-ground-function :
  ∀ {Φ Δᴸ Δᴿ A H} →
  Φ ∣ Δᴸ ⊢ `∀ A ⊑ H ⊣ Δᴿ →
  Ground H →
  H ≡ ★ ⇒ ★
universal-ground-function (ν safe occ p) gH =
  nonvar-occurs-ground-function safe occ p gH
