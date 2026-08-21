{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxDirectCTIAcceptanceProbe where

-- File Charter:
--   * Exercises the direct term-imprecision conversion rules in the smallest
--     matched-star and genuinely source-only worlds.
--   * Checks that the paired pivot-position gate accepts aligned atomic
--     reveal/conceal conversions while one-sided rules remain independent of
--     that gate.
--   * Contains no live relation changes or compatibility wrappers.

open import Data.Fin using (zero)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (refl)

open import Types using (★; ＇_; ‵_; `ℕ)
open import TyStore using (store-empty; Z∋)
import Conversion as Conv
open import CastTerms using
  (Ctx; ⟨_,_,_⟩; _,ˢ_; _↑_; _↓_; blame; ⊢blame)
import Imprecision as I
open import proof.DGG.World
open import proof.DGG.SourceRebasePlan using
  (source-rebase-id)
import proof.DGG.notes.probes.TwoCtxDirectCTIProbe as Direct
open Direct using (_⊢ᴰ_⊑_∶_)


base : Ctx
base = ⟨ 0 , store-empty , [] ⟩

source-only-world : (base ,ˢ ‵ `ℕ) ⊑ᶜ base
source-only-world = bindLeftᶜ emptyᶜ (‵ `ℕ)

matched-star-world : (base ,ˢ ‵ `ℕ) ⊑ᶜ (base ,ˢ ★)
matched-star-world = bindBothStarᶜ emptyᶜ I.ι⊑★ (λ ())


------------------------------------------------------------------------
-- Genuinely source-only reveal and conceal
------------------------------------------------------------------------

source-only-variable-base :
  source-only-world ⊢ᴰ blame ⊑ blame ∶ I.X⊑★ {X = zero} refl
source-only-variable-base =
  Direct.blame⊑ᴰ ⊢blame (I.X⊑★ {X = zero} refl)

source-only-reveal :
  source-only-world ⊢ᴰ (blame ↑ Conv.unseal zero (‵ `ℕ))
    ⊑ blame ∶ I.ι⊑★ {ι = `ℕ}
source-only-reveal =
  Direct.source-revealᴰ
    (Direct.source-reveal-only {Xᴸ = zero} refl (λ ())
      (I.ι⊑★ {ι = `ℕ}) (Conv.⊢↑-unseal (Z∋ refl)) (λ ()))
    source-only-variable-base (I.ι⊑★ {ι = `ℕ})

source-only-representation-base :
  source-only-world ⊢ᴰ blame ⊑ blame ∶ I.ι⊑★ {ι = `ℕ}
source-only-representation-base =
  Direct.blame⊑ᴰ ⊢blame (I.ι⊑★ {ι = `ℕ})

source-only-conceal :
  source-only-world ⊢ᴰ (blame ↓ Conv.seal zero (‵ `ℕ))
    ⊑ blame ∶ I.X⊑★ {X = zero} refl
source-only-conceal =
  Direct.source-concealᴰ
    (Direct.source-conceal-only {Xᴸ = zero} refl (λ ())
      (I.ι⊑★ {ι = `ℕ}) (Conv.⊢↓-seal (Z∋ refl)) (λ ()))
    source-only-representation-base (I.X⊑★ {X = zero} refl)


------------------------------------------------------------------------
-- Matched reveal and conceal
------------------------------------------------------------------------

matched-variable-base :
  matched-star-world ⊢ᴰ blame ⊑ blame ∶ I.X⊑X {X = zero}
matched-variable-base =
  Direct.blame⊑ᴰ ⊢blame (I.X⊑X {X = zero})

matched-reveal :
  matched-star-world ⊢ᴰ (blame ↑ Conv.unseal zero (‵ `ℕ))
    ⊑ (blame ↑ Conv.unseal zero ★) ∶ I.ι⊑★ {ι = `ℕ}
matched-reveal =
  Direct.paired-revealᴰ
    (Direct.paired-reveal-action {Xᴸ = zero} {Xᴿ = zero}
      (source-rebase-id refl) (I.ι⊑★ {ι = `ℕ})
      (Conv.⊢↑-unseal (Z∋ refl))
      (Conv.⊢↑-unseal (Z∋ refl)) refl (λ ()))
    matched-variable-base
    (I.ι⊑★ {ι = `ℕ})

matched-representation-base :
  matched-star-world ⊢ᴰ blame ⊑ blame ∶ I.ι⊑★ {ι = `ℕ}
matched-representation-base =
  Direct.blame⊑ᴰ ⊢blame (I.ι⊑★ {ι = `ℕ})

matched-conceal :
  matched-star-world ⊢ᴰ (blame ↓ Conv.seal zero (‵ `ℕ))
    ⊑ (blame ↓ Conv.seal zero ★) ∶ I.X⊑X {X = zero}
matched-conceal =
  Direct.paired-concealᴰ
    (Direct.paired-conceal-action {Xᴸ = zero} {Xᴿ = zero}
      (source-rebase-id refl) refl (I.ι⊑★ {ι = `ℕ})
      (Conv.⊢↓-seal (Z∋ refl))
      (Conv.⊢↓-seal (Z∋ refl)) refl (λ ()))
    matched-representation-base
    (I.X⊑X {X = zero})
