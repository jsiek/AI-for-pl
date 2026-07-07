module proof.DGGBetaCastValueCommonMediated where

-- File Charter:
--   * Target-cast shape contradictions for the mediated beta-cast value proof.
--   * Split out to keep the value proof module smaller and cheaper to check.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)

open import Types
open import Coercions
open import NarrowWiden using
  ( cross
  ; id-＇
  ; id-‵
  ; id★
  ; sealⁿ
  ; untag
  ; _︔seal_
  ; _？︔_
  ; _∣_∣_⊢_∶_⊒_
  )
  renaming (`∀ to `∀ⁿʷ; gen to genⁿʷ)
open import MediatedNarrowing

dual-id-not-fun :
  ∀ {η Δ Σ X A B c d} →
  (e : η ∣ Δ ∣ Σ ⊢ id X ∶ A ⊒ B) →
  narrowing-dual¹ e ≡ c ↦ d →
  ⊥
dual-id-not-fun (_ , cross (id-＇ α)) ()
dual-id-not-fun (_ , cross (id-‵ ι)) ()
dual-id-not-fun (_ , id★) ()

dual-seq-not-fun :
  ∀ {η Δ Σ t₁ t₂ A B c d} →
  (e : η ∣ Δ ∣ Σ ⊢ t₁ ︔ t₂ ∶ A ⊒ B) →
  narrowing-dual¹ e ≡ c ↦ d →
  ⊥
dual-seq-not-fun (_ , (＇ α) ？︔ gⁿ) ()
dual-seq-not-fun (_ , (‵ ι) ？︔ gⁿ) ()
dual-seq-not-fun (_ , ★⇒★ ？︔ gⁿ) ()
dual-seq-not-fun (_ , sⁿ ︔seal α) ()

dual-all-not-fun :
  ∀ {η Δ Σ t A B c d} →
  (e : η ∣ Δ ∣ Σ ⊢ `∀ t ∶ A ⊒ B) →
  narrowing-dual¹ e ≡ c ↦ d →
  ⊥
dual-all-not-fun (_ , cross (`∀ⁿʷ tⁿ)) ()

dual-untag-not-fun :
  ∀ {η Δ Σ G A B c d} →
  (e : η ∣ Δ ∣ Σ ⊢ G ？ ∶ A ⊒ B) →
  narrowing-dual¹ e ≡ c ↦ d →
  ⊥
dual-untag-not-fun (_ , untag (＇ α)) ()
dual-untag-not-fun (_ , untag (‵ ι)) ()
dual-untag-not-fun (_ , untag ★⇒★) ()

dual-seal-not-fun :
  ∀ {η Δ Σ X α A B c d} →
  (e : η ∣ Δ ∣ Σ ⊢ seal X α ∶ A ⊒ B) →
  narrowing-dual¹ e ≡ c ↦ d →
  ⊥
dual-seal-not-fun (_ , sealⁿ X α) ()

dual-gen-not-fun :
  ∀ {η Δ Σ X t A B c d} →
  (e : η ∣ Δ ∣ Σ ⊢ gen X t ∶ A ⊒ B) →
  narrowing-dual¹ e ≡ c ↦ d →
  ⊥
dual-gen-not-fun (_ , genⁿʷ tⁿ) ()

tag-narrowing-impossible :
  ∀ {η Δ Σ G A B} →
  η ∣ Δ ∣ Σ ⊢ G ! ∶ A ⊒ B →
  ⊥
tag-narrowing-impossible (_ , cross ())

unseal-narrowing-impossible :
  ∀ {η Δ Σ α X A B} →
  η ∣ Δ ∣ Σ ⊢ unseal α X ∶ A ⊒ B →
  ⊥
unseal-narrowing-impossible (_ , cross ())

inst-narrowing-impossible :
  ∀ {η Δ Σ X t A B} →
  η ∣ Δ ∣ Σ ⊢ inst X t ∶ A ⊒ B →
  ⊥
inst-narrowing-impossible (_ , cross ())
