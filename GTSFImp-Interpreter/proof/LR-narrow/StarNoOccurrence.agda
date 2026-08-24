module proof.LR-narrow.StarNoOccurrence where

-- File Charter:
--   * A paired semantic slot's center variable cannot occur in a type
--     that is imprecise below `★`: every rule deriving `A ⊑ ★` either
--     stops at a non-variable form or requires the variable's mode to be
--     `X⊑★`, which contradicts the paired mode `X⊑X`.
--   * Consequently the structural reveal at a paired slot leaves such a
--     type unchanged: `replaceTy X R B ≡ B`.

open import Data.Nat using (suc)
import Data.Fin as Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)
open import Data.Fin.Properties using (_≟_)

open import Types
open import LR-narrow.World using
  (World; Future; future-refl; future-paired; future-precise;
   future-imprecise; liftCenterTy; liftCenterVariable)
open import Conversion using (replaceTy)
open import proof.ImprecisionConsistency using
  (ext-injective; fin-suc-injective)
import Imprecision as I

------------------------------------------------------------------------
-- No occurrence below ★
------------------------------------------------------------------------

star-no-occurrence : ∀ {Δ} {μ : I.ImpEnv Δ} (Z : TyVar Δ) {A : Ty Δ}
  → μ Z ≡ I.X⊑X
  → μ I.⊢ A ⊑ ★
  → Z ∉ᵗ A
star-no-occurrence Z mode I.★⊑★ = ∉-star
star-no-occurrence Z mode I.ι⊑★ = ∉-base
star-no-occurrence Z mode (I.X⊑★ {X = X} eq) with Z ≟ X
star-no-occurrence Z mode (I.X⊑★ eq) | yes refl
    with trans (sym mode) eq
star-no-occurrence Z mode (I.X⊑★ eq) | yes refl | ()
star-no-occurrence Z mode (I.X⊑★ eq) | no Z≢X =
  ∉-var (≢→≢ᶠ Z≢X)
star-no-occurrence Z mode (I.⇒⊑★ p q) =
  ∉-fun (star-no-occurrence Z mode p) (star-no-occurrence Z mode q)
star-no-occurrence Z mode (I.∀⊑ nonvar occurs p) =
  ∉-all (star-no-occurrence (Fin.suc Z) mode p)
star-no-occurrence Z mode I.∀★⊑★ = ∉-all ∉-star
star-no-occurrence Z mode (I.∀⊑★ nonstar p) =
  ∉-all (star-no-occurrence (Fin.suc Z) mode p)
star-no-occurrence Z mode I.bot⊑★ =
  ∉-all (∉-var (≢→≢ᶠ (λ ())))

------------------------------------------------------------------------
-- Absent variables are not replaced
------------------------------------------------------------------------

replaceTy-absent : ∀ {Δ} (X : TyVar Δ) (R : Ty Δ) {B : Ty Δ}
  → X ∉ᵗ B
  → replaceTy X R B ≡ B
replaceTy-absent X R {B = ＇ Y} (∉-var X≢Y) with X ≟ Y
replaceTy-absent X R (∉-var X≢Y) | yes refl = ⊥-elim (≢ᶠ→≢ X≢Y refl)
replaceTy-absent X R (∉-var X≢Y) | no _ = refl
replaceTy-absent X R ∉-base = refl
replaceTy-absent X R ∉-star = refl
replaceTy-absent X R (∉-fun absentA absentB) =
  cong₂ _⇒_ (replaceTy-absent X R absentA) (replaceTy-absent X R absentB)
replaceTy-absent X R (∉-all absentB) =
  cong `∀ (replaceTy-absent (Fin.suc X) (⇑ᵗ R) absentB)

------------------------------------------------------------------------
-- Renaming and non-occurrence
------------------------------------------------------------------------

renameᵗ-∉ᵗ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′)
    (injective : ∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
    {X : TyVar Δ} {A : Ty Δ}
  → X ∉ᵗ A → ρ X ∉ᵗ renameᵗ ρ A
renameᵗ-∉ᵗ ρ injective (∉-var X≢Y) =
  ∉-var (≢→≢ᶠ (λ eq → ≢ᶠ→≢ X≢Y (injective eq)))
renameᵗ-∉ᵗ ρ injective ∉-base = ∉-base
renameᵗ-∉ᵗ ρ injective ∉-star = ∉-star
renameᵗ-∉ᵗ ρ injective (∉-fun absentA absentB) =
  ∉-fun (renameᵗ-∉ᵗ ρ injective absentA)
    (renameᵗ-∉ᵗ ρ injective absentB)
renameᵗ-∉ᵗ ρ injective (∉-all absentA) =
  ∉-all (renameᵗ-∉ᵗ (extᵗ ρ) (ext-injective injective) absentA)

-- Non-occurrence is reflected by renaming.

renameᵗ-reflects-∉ᵗ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) {X : TyVar Δ} (A : Ty Δ)
  → ρ X ∉ᵗ renameᵗ ρ A → X ∉ᵗ A
renameᵗ-reflects-∉ᵗ ρ (＇ Y) (∉-var ρX≢ρY) =
  ∉-var (≢→≢ᶠ (λ eq → ≢ᶠ→≢ ρX≢ρY (cong ρ eq)))
renameᵗ-reflects-∉ᵗ ρ (‵ ι) no-occur = ∉-base
renameᵗ-reflects-∉ᵗ ρ ★ no-occur = ∉-star
renameᵗ-reflects-∉ᵗ ρ (A ⇒ B) (∉-fun absentA absentB) =
  ∉-fun (renameᵗ-reflects-∉ᵗ ρ A absentA)
    (renameᵗ-reflects-∉ᵗ ρ B absentB)
renameᵗ-reflects-∉ᵗ ρ (`∀ A) (∉-all absentA) =
  ∉-all (renameᵗ-reflects-∉ᵗ (extᵗ ρ) A absentA)



------------------------------------------------------------------------
-- No occurrence opposite an absent variable
------------------------------------------------------------------------

-- A variable at the paired mode `X⊑X` can occur on the left of an
-- imprecision derivation only opposite an occurrence of itself on the
-- right: the only atomic form at mode `X⊑X` is `X⊑X` itself, whose
-- right-hand side is the same variable; the `⊑ ★` forms are covered by
-- `star-no-occurrence`.  This generalizes `star-no-occurrence` from
-- the right-hand side `★` to any right-hand side avoiding the
-- variable.

paired-no-occurrence : ∀ {Δ} {μ : I.ImpEnv Δ} (Z : TyVar Δ)
    {A B : Ty Δ}
  → μ Z ≡ I.X⊑X
  → μ I.⊢ A ⊑ B
  → Z ∉ᵗ B
  → Z ∉ᵗ A
paired-no-occurrence Z mode I.★⊑★ avoid = ∉-star
paired-no-occurrence Z mode I.ι⊑ι avoid = ∉-base
paired-no-occurrence Z mode I.X⊑X avoid = avoid
paired-no-occurrence Z mode (I.⇒⊑⇒ p q) (∉-fun absentA absentB) =
  ∉-fun (paired-no-occurrence Z mode p absentA)
    (paired-no-occurrence Z mode q absentB)
paired-no-occurrence Z mode (I.∀⊑∀ p) (∉-all absentB) =
  ∉-all (paired-no-occurrence (Fin.suc Z) mode p absentB)
paired-no-occurrence Z mode (I.⇒⊑★ p q) avoid =
  star-no-occurrence Z mode (I.⇒⊑★ p q)
paired-no-occurrence Z mode I.ι⊑★ avoid = ∉-base
paired-no-occurrence Z mode (I.X⊑★ eq) avoid =
  star-no-occurrence Z mode (I.X⊑★ eq)
paired-no-occurrence Z mode (I.∀⊑ nonvar occurs p) avoid =
  ∉-all (paired-no-occurrence (Fin.suc Z) mode p
    (renameᵗ-∉ᵗ Fin.suc fin-suc-injective avoid))
paired-no-occurrence Z mode I.∀★⊑★ avoid = ∉-all ∉-star
paired-no-occurrence Z mode (I.∀⊑★ nonstar p) avoid =
  ∉-all (star-no-occurrence (Fin.suc Z) mode p)
paired-no-occurrence Z mode I.bot-elim avoid =
  ∉-all (∉-var (≢→≢ᶠ (λ ())))
paired-no-occurrence Z mode I.bot⊑★ avoid =
  ∉-all (∉-var (≢→≢ᶠ (λ ())))

------------------------------------------------------------------------
-- Non-occurrence is preserved by center lifting
------------------------------------------------------------------------

liftCenter-∉ᵗ : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {Z : TyVar Δᶜ} {A : Ty Δᶜ}
  → Z ∉ᵗ A
  → liftCenterVariable W≼W′ Z ∉ᵗ liftCenterTy W≼W′ A
liftCenter-∉ᵗ future-refl avoid = avoid
liftCenter-∉ᵗ (future-paired W≼W′ related) avoid =
  renameᵗ-∉ᵗ Fin.suc fin-suc-injective (liftCenter-∉ᵗ W≼W′ avoid)
liftCenter-∉ᵗ (future-precise W≼W′ related) avoid =
  renameᵗ-∉ᵗ Fin.suc fin-suc-injective (liftCenter-∉ᵗ W≼W′ avoid)
liftCenter-∉ᵗ (future-imprecise W≼W′) avoid =
  renameᵗ-∉ᵗ Fin.suc fin-suc-injective (liftCenter-∉ᵗ W≼W′ avoid)

------------------------------------------------------------------------
-- Impossible right-hand sides for right-universal imprecision
------------------------------------------------------------------------

-- A non-variable type is never imprecise below a variable: the only
-- atomic derivation at a variable right-hand side is `X⊑X`, whose left
-- is the same variable, and the only compound one is `∀⊑`, whose
-- premise repeats the situation with a non-variable left.

⊑-var-right-nonvar : ∀ {Δ} {μ : I.ImpEnv Δ} {A : Ty Δ} {Y : TyVar Δ}
  → μ I.⊢ A ⊑ ＇ Y
  → NonVar A
  → ⊥
⊑-var-right-nonvar I.X⊑X ()
⊑-var-right-nonvar (I.∀⊑ nonvar occurs p) nv =
  ⊑-var-right-nonvar p nonvar

-- A type imprecise below a base type contains no variables at all.

⊑-base-right-no-var : ∀ {Δ} {μ : I.ImpEnv Δ} {A : Ty Δ} {ι}
    {Z : TyVar Δ}
  → μ I.⊢ A ⊑ ‵ ι
  → Z ∈ᵗ A
  → ⊥
⊑-base-right-no-var (I.∀⊑ nonvar occurs p) (∈-all occ) =
  ⊑-base-right-no-var p occ
