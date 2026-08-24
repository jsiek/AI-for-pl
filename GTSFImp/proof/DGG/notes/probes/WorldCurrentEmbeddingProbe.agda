{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.WorldCurrentEmbeddingProbe where

-- File Charter:
--   * Checks the live World source-rebase change directly, with no mirror
--     relation or boundary-state wrapper.
--   * Checks the current source embedding at the alpha and beta boundaries
--     of Examples 4 and 12, before and after the runtime allocation.
--   * Confirms that representation comparison belongs to the world before a
--     reveal while recursive body comparison belongs to the rebased world.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types using (★; ＇_; ‵_; `ℕ)
open import Consistency using (_↪ᵗ_; empty; keep; skip; toRenameᵗ)
import Imprecision as I
open import CastTerms using (_,ˢ_; ⇑ᵉᵗ)
open import proof.DGG.World
import proof.DGG.notes.probes.WorldChangeSequenceProbe as Hist


------------------------------------------------------------------------
-- Example 4 needs no source rebase
------------------------------------------------------------------------

example4-pivots-aligned :
  toRenameᵗ (ηᴸᶜ Hist.example4-world) Fin.zero
    ≡ toRenameᵗ (ηᴿᶜ Hist.example4-world) Fin.zero
example4-pivots-aligned = refl

example4-representation :
  (‵ `ℕ) ⊑ᵀ⟨ Hist.example4-world ⟩ ★
example4-representation = I.ι⊑★

example4-no-rebase : sourceRebaseCountᶜ Hist.example4-world ≡ 0
example4-no-rebase = refl


------------------------------------------------------------------------
-- Example 12 source positions
------------------------------------------------------------------------

source-outside : 1 ↪ᵗ 3
source-outside = keep (skip (skip empty))

source-at-alpha : 1 ↪ᵗ 3
source-at-alpha = skip (skip (keep empty))

source-at-beta : 1 ↪ᵗ 3
source-at-beta = skip (keep (skip empty))


------------------------------------------------------------------------
-- Example 12 at checkpoint C1
------------------------------------------------------------------------

c1-outside :
  ⇑ᵉᵗ Hist.base ⊑ᶜ ((Hist.base ,ˢ ★) ,ˢ ＇ Fin.zero)
c1-outside = Hist.example12-c1-world

c1-alpha :
  ⇑ᵉᵗ Hist.base ⊑ᶜ ((Hist.base ,ˢ ★) ,ˢ ＇ Fin.zero)
c1-alpha =
  rebaseSourceᶜ c1-outside Fin.zero (Fin.suc Fin.zero)
    (can-rebase-sourceᵗ outside-not-alpha
      (insert-skipᵗ (insert-skipᵗ insert-hereᵗ)))
    (I.X⊑★ refl)
  where
  outside-not-alpha :
    toRenameᵗ (ηᴸᶜ c1-outside) Fin.zero ≢
      toRenameᵗ (ηᴿᶜ c1-outside) (Fin.suc Fin.zero)
  outside-not-alpha ()

c1-beta :
  ⇑ᵉᵗ Hist.base ⊑ᶜ ((Hist.base ,ˢ ★) ,ˢ ＇ Fin.zero)
c1-beta =
  rebaseSourceᶜ c1-alpha Fin.zero Fin.zero
    (can-rebase-sourceᵗ alpha-not-beta
      (insert-skipᵗ insert-hereᵗ))
    I.X⊑X
  where
  alpha-not-beta :
    toRenameᵗ (ηᴸᶜ c1-alpha) Fin.zero ≢
      toRenameᵗ (ηᴿᶜ c1-alpha) Fin.zero
  alpha-not-beta ()

c1-alpha-current : ηᴸᶜ c1-alpha ≡ source-at-alpha
c1-alpha-current = refl

c1-beta-current : ηᴸᶜ c1-beta ≡ source-at-beta
c1-beta-current = refl

c1-target-frozen : ηᴿᶜ c1-beta ≡ ηᴿᶜ c1-outside
c1-target-frozen = refl

c1-marks-frozen : marksᶜ c1-beta ≡ marksᶜ c1-outside
c1-marks-frozen = refl

c1-rebase-count : sourceRebaseCountᶜ c1-beta ≡ 2
c1-rebase-count = refl

c1-alpha-representation-before :
  (＇ Fin.zero) ⊑ᵀ⟨ c1-outside ⟩ ★
c1-alpha-representation-before = I.X⊑★ refl

c1-alpha-body :
  (＇ Fin.zero) ⊑ᵀ⟨ c1-alpha ⟩ (＇ (Fin.suc Fin.zero))
c1-alpha-body = I.X⊑X

c1-beta-representation-before :
  (＇ Fin.zero) ⊑ᵀ⟨ c1-alpha ⟩ (＇ (Fin.suc Fin.zero))
c1-beta-representation-before = I.X⊑X

c1-beta-body : (＇ Fin.zero) ⊑ᵀ⟨ c1-beta ⟩ (＇ Fin.zero)
c1-beta-body = I.X⊑X

------------------------------------------------------------------------
-- Example 12 after the paired runtime allocation at checkpoint C5
------------------------------------------------------------------------

c5-outside :
  (Hist.base ,ˢ ‵ `ℕ) ⊑ᶜ
    (((Hist.base ,ˢ ★) ,ˢ ＇ Fin.zero) ,ˢ ‵ `ℕ)
c5-outside = Hist.example12-c5-world

c5-alpha :
  (Hist.base ,ˢ ‵ `ℕ) ⊑ᶜ
    (((Hist.base ,ˢ ★) ,ˢ ＇ Fin.zero) ,ˢ ‵ `ℕ)
c5-alpha =
  rebaseSourceᶜ c5-outside Fin.zero
    (Fin.suc (Fin.suc Fin.zero))
    (can-rebase-sourceᵗ outside-not-alpha
      (insert-skipᵗ (insert-skipᵗ insert-hereᵗ)))
    (I.X⊑★ refl)
  where
  outside-not-alpha :
    toRenameᵗ (ηᴸᶜ c5-outside) Fin.zero ≢
      toRenameᵗ (ηᴿᶜ c5-outside) (Fin.suc (Fin.suc Fin.zero))
  outside-not-alpha ()

c5-beta :
  (Hist.base ,ˢ ‵ `ℕ) ⊑ᶜ
    (((Hist.base ,ˢ ★) ,ˢ ＇ Fin.zero) ,ˢ ‵ `ℕ)
c5-beta =
  rebaseSourceᶜ c5-alpha Fin.zero (Fin.suc Fin.zero)
    (can-rebase-sourceᵗ alpha-not-beta
      (insert-skipᵗ insert-hereᵗ))
    I.X⊑X
  where
  alpha-not-beta :
    toRenameᵗ (ηᴸᶜ c5-alpha) Fin.zero ≢
      toRenameᵗ (ηᴿᶜ c5-alpha) (Fin.suc Fin.zero)
  alpha-not-beta ()

c5-alpha-current : ηᴸᶜ c5-alpha ≡ source-at-alpha
c5-alpha-current = refl

c5-beta-current : ηᴸᶜ c5-beta ≡ source-at-beta
c5-beta-current = refl

c5-rebase-count : sourceRebaseCountᶜ c5-beta ≡ 2
c5-rebase-count = refl

c5-alpha-representation-before :
  (＇ Fin.zero) ⊑ᵀ⟨ c5-outside ⟩ ★
c5-alpha-representation-before = I.X⊑★ refl

c5-alpha-body :
  (＇ Fin.zero) ⊑ᵀ⟨ c5-alpha ⟩
    (＇ (Fin.suc (Fin.suc Fin.zero)))
c5-alpha-body = I.X⊑X

c5-beta-representation-before :
  (＇ Fin.zero) ⊑ᵀ⟨ c5-alpha ⟩
    (＇ (Fin.suc (Fin.suc Fin.zero)))
c5-beta-representation-before = I.X⊑X

c5-beta-body :
  (＇ Fin.zero) ⊑ᵀ⟨ c5-beta ⟩ (＇ (Fin.suc Fin.zero))
c5-beta-body = I.X⊑X

c5-direct-representations-before :
  (‵ `ℕ) ⊑ᵀ⟨ c5-outside ⟩ (‵ `ℕ)
c5-direct-representations-before = I.ι⊑ι

c5-beta-direct-representations-impossible :
  (‵ `ℕ) ⊑ᵀ⟨ c5-beta ⟩
    (＇ (Fin.suc (Fin.suc Fin.zero)))
  → ⊥
c5-beta-direct-representations-impossible ()
