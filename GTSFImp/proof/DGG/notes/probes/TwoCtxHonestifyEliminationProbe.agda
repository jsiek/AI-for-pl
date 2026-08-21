{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxHonestifyEliminationProbe where

-- File Charter:
--   * Checks that every raw two-Ctx world is already honest: a center without
--     a target occupant has a dynamic imprecision mark.
--   * Eliminates honestification as a world transformation; the original
--     world itself retains its endpoints, projections, marks, and invariants.
--   * Uses only induction over constructor-form raw history and introduces no
--     post-world witness, premise rebuilding, or invariant input.

import Data.Fin as Fin
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong)

open import Types using (TyVar)
open import Consistency using (toRenameᵗ)
open import Imprecision using (X⊑★)
open import CastTerms using (Ctx; Δᵉ)
open import proof.DGG.notes.probes.TwoCtxWorldSkeletonProbe
open import proof.DGG.notes.probes.TwoCtxWorldInvariantsProbe


target-unaligned-markᶜ₀ : ∀ {Cᴸ Cᴿ : Ctx}
    (W : Cᴸ ⊑ᶜ₀ Cᴿ) (Z : TyVar (centerᶜ₀ W))
  → (∀ Xᴿ → toRenameᵗ (ηᴿᶜ₀ W) Xᴿ ≢ Z)
  → marksᶜ₀ W Z ≡ X⊑★
target-unaligned-markᶜ₀ emptyᶜ₀ () no-target
target-unaligned-markᶜ₀ (skip-centerᶜ₀ W) Fin.zero no-target = refl
target-unaligned-markᶜ₀ (skip-centerᶜ₀ W) (Fin.suc Z) no-target =
  target-unaligned-markᶜ₀ W Z
    (λ Xᴿ eq → no-target Xᴿ (cong Fin.suc eq))
target-unaligned-markᶜ₀
    (lift-both-rawᶜ₀ W v Γᴸ⁺≡ Γᴿ⁺≡) Fin.zero no-target =
  ⊥-elim (no-target Fin.zero refl)
target-unaligned-markᶜ₀
    (lift-both-rawᶜ₀ W v Γᴸ⁺≡ Γᴿ⁺≡) (Fin.suc Z) no-target =
  target-unaligned-markᶜ₀ W Z
    (λ Xᴿ eq → no-target (Fin.suc Xᴿ) (cong Fin.suc eq))
target-unaligned-markᶜ₀
    (lift-left-rawᶜ₀ W Γᴸ⁺≡) Fin.zero no-target = refl
target-unaligned-markᶜ₀
    (lift-left-rawᶜ₀ W Γᴸ⁺≡) (Fin.suc Z) no-target =
  target-unaligned-markᶜ₀ W Z
    (λ Xᴿ eq → no-target Xᴿ (cong Fin.suc eq))
target-unaligned-markᶜ₀
    (bind-left-rawᶜ₀ W A Γᴸ⁺≡) Fin.zero no-target = refl
target-unaligned-markᶜ₀
    (bind-left-rawᶜ₀ W A Γᴸ⁺≡) (Fin.suc Z) no-target =
  target-unaligned-markᶜ₀ W Z
    (λ Xᴿ eq → no-target Xᴿ (cong Fin.suc eq))
target-unaligned-markᶜ₀
    (bind-right-rawᶜ₀ W B fresh Γᴿ⁺≡) Fin.zero no-target =
  ⊥-elim (no-target Fin.zero refl)
target-unaligned-markᶜ₀
    (bind-right-rawᶜ₀ W B fresh Γᴿ⁺≡) (Fin.suc Z) no-target =
  target-unaligned-markᶜ₀ W Z
    (λ Xᴿ eq → no-target (Fin.suc Xᴿ) (cong Fin.suc eq))
target-unaligned-markᶜ₀
    (bind-both-rawᶜ₀ W represented Γᴸ⁺≡ Γᴿ⁺≡)
    Fin.zero no-target =
  ⊥-elim (no-target Fin.zero refl)
target-unaligned-markᶜ₀
    (bind-both-rawᶜ₀ W represented Γᴸ⁺≡ Γᴿ⁺≡)
    (Fin.suc Z) no-target =
  target-unaligned-markᶜ₀ W Z
    (λ Xᴿ eq → no-target (Fin.suc Xᴿ) (cong Fin.suc eq))
target-unaligned-markᶜ₀
    (bind-both-star-rawᶜ₀ W represented A≠★ Γᴸ⁺≡ Γᴿ⁺≡)
    Fin.zero no-target =
  ⊥-elim (no-target Fin.zero refl)
target-unaligned-markᶜ₀
    (bind-both-star-rawᶜ₀ W represented A≠★ Γᴸ⁺≡ Γᴿ⁺≡)
    (Fin.suc Z) no-target =
  target-unaligned-markᶜ₀ W Z
    (λ Xᴿ eq → no-target (Fin.suc Xᴿ) (cong Fin.suc eq))
target-unaligned-markᶜ₀
    (bind-termᶜ₀ W represented) Z no-target =
  target-unaligned-markᶜ₀ W Z no-target


honestification-eliminatedᶜ₀ : ∀ {Cᴸ Cᴿ : Ctx}
    (W : Cᴸ ⊑ᶜ₀ Cᴿ)
  → (∀ Z
      → (∀ Xᴿ → toRenameᵗ (ηᴿᶜ₀ W) Xᴿ ≢ Z)
      → marksᶜ₀ W Z ≡ X⊑★)
    × DirectWorldInvariantsᶜ₀ W
honestification-eliminatedᶜ₀ W =
  target-unaligned-markᶜ₀ W , directInvariantsᶜ₀ W
