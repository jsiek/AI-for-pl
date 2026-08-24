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
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)
open import Data.Fin.Properties using (_≟_)

open import Types
open import Conversion using (replaceTy)
open import proof.ImprecisionConsistency using (ext-injective)
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


