module M5UnderLiftRevealScratch where

-- File Charter:
--   * Scratch for the M5 depth-1 under-lift generated reveal question.
--   * Checks the non-moving `sameWorldRebaseAt` route for the first target
--     reveal, then records the finite post-type obstruction in the same world.
--   * This file is not imported by the live development.

open import Data.Empty using (⊥)
open import Data.Maybe using (just)
open import Data.Nat using (suc)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; ★; ＇_; _⇒_; ⇑ᵗ; var-∈; ∈-fun-left)
open import TyStore using (Z∋)
open import Conversion using (replaceTy; 〖_,_↑_〗)
open import Consistency using (_↪ᵗ_; keep; skip; toRenameᵗ)
open import Reduction using (applyBody; bind)
import Imprecision as I
open import Imprecision using (_⊢_⊑_)
open import proof.ImprecisionConsistency using (fin-suc-injective)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.Catchup.InstInversionProof as IIP
import proof.DGG.TargetBindLift as TBL


depth1-inner-sameWorld-rebaseᴿ : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → CTI2.RebaseAtᴿ
      (TBL.ΛLiftToBindFreshWorldᴸ I.X⊑★ W)
      (TBL.ΛLiftToBindFreshWorldᴸ I.X⊑★ W)
      (just Fin.zero)
depth1-inner-sameWorld-rebaseᴿ W =
  CTI2.rebase-varᴿ
    (CTI2.sameWorldRebaseAt refl
      (CTI2.store-rep-imp (I.X⊑★ refl)))


depth1-inner-sameWorld-reveal-⊢↑ : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → CTI2.targetStoreʷ (TBL.ΛLiftToBindFreshWorldᴸ I.X⊑★ W)
      CTI2.⊢↑[ just Fin.zero ]
        〖 Fin.zero , ⇑ᵗ (＇ Fin.zero)
          ↑ applyBody (bind ★) (＇ Fin.zero ⇒ ★) 〗
depth1-inner-sameWorld-reveal-⊢↑ W =
  IIP.generated-reveal-⊢↑-present (∈-fun-left var-∈) (Z∋ refl)


no-var1⊑var3 : ∀ {Δ}
    {μ : I.ImpEnv (suc (suc (suc (suc Δ))))}
  → μ ⊢ ＇ (Fin.suc Fin.zero)
      ⊑ ＇ (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
  → ⊥
no-var1⊑var3 ()


no-ope-0↦1-1↦0 : ∀ {Δ Δ′}
    {η : suc (suc Δ) ↪ᵗ suc (suc Δ′)}
  → toRenameᵗ η Fin.zero ≡ Fin.suc Fin.zero
  → toRenameᵗ η (Fin.suc Fin.zero) ≡ Fin.zero
  → ⊥
no-ope-0↦1-1↦0 {η = keep η} ()
no-ope-0↦1-1↦0 {η = skip η} eq₀ ()


no-ope-0↦2-1↦1 : ∀ {Δ Δ′}
    {η : suc (suc Δ) ↪ᵗ suc (suc (suc Δ′))}
  → toRenameᵗ η Fin.zero ≡ Fin.suc (Fin.suc Fin.zero)
  → toRenameᵗ η (Fin.suc Fin.zero) ≡ Fin.suc Fin.zero
  → ⊥
no-ope-0↦2-1↦1 {η = keep η} ()
no-ope-0↦2-1↦1 {η = skip η} eq₀ eq₁ =
  no-ope-0↦1-1↦0 (fin-suc-injective eq₀) (fin-suc-injective eq₁)


no-ope-0↦3-1↦2 : ∀ {Δ Δ′}
    {η : suc (suc Δ) ↪ᵗ suc (suc (suc (suc Δ′)))}
  → toRenameᵗ η Fin.zero
      ≡ Fin.suc (Fin.suc (Fin.suc Fin.zero))
  → toRenameᵗ η (Fin.suc Fin.zero)
      ≡ Fin.suc (Fin.suc Fin.zero)
  → ⊥
no-ope-0↦3-1↦2 {η = keep η} ()
no-ope-0↦3-1↦2 {η = skip η} eq₀ eq₁ =
  no-ope-0↦2-1↦1 (fin-suc-injective eq₀) (fin-suc-injective eq₁)


depth1-inner-sameWorld-q-empty : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → (＇ Fin.zero ⇒ ★) CTI2.⊑ᵂ⟨
      TBL.ΛLiftToBindFreshWorldᴸ I.X⊑★ W
    ⟩
    replaceTy Fin.zero (⇑ᵗ (＇ Fin.zero))
      (applyBody (bind ★) (＇ Fin.zero ⇒ ★))
  → ⊥
depth1-inner-sameWorld-q-empty (I.⇒⊑⇒ bad _) = no-var1⊑var3 bad
