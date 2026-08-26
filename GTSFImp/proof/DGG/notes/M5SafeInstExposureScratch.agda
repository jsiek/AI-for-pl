module proof.DGG.notes.M5SafeInstExposureScratch where

-- File Charter:
--   * Checks that `safe-inst` is reachable beneath a generated value cast.
--   * Shows that the cast exposed by `β-gen` need not itself form a value.

import Data.Fin as Fin
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

open import Types
open import Consistency
open import CastTerms
  using (Term; Value; GenSafe; Inert; safe-inst; genᵥ; _⟨_⟩; _《_》)
open import proof.Consistency using (subst-left-gen-safe)
μ₀ : Env∼ 0
μ₀ ()

A : Ty 0
A = `∀ (＇ Fin.zero ⇒ ★)

A-body : Ty 2
A-body = ＇ Fin.zero ⇒ ★

B : Ty 1
B = ★ ⇒ ＇ Fin.zero

instance
  B-nonvar : NonVar B
  B-nonvar = nonvar-fun

  zero∈B : Fin.zero ∈ᵗ B
  zero∈B = ∈-fun-right ∉-star var-∈

  zero∈A-body : Fin.zero {n = 1} ∈ᵗ A-body
  zero∈A-body = ∈-fun-left var-∈

B≠★ : B ≢ ★
B≠★ ()

body : instᵐ (genᵐ μ₀) ⊢
    A-body ∼ (★ ⇒ ＇ (Fin.suc Fin.zero))
body =
  ？_ ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ ★∼G = ★∼Xᵍ refl ⦄
      (id (＇ Fin.zero)) ⦃ nonstar-X ⦄
  ↦
  ？_ ⦃ Gᵍ = ＇ (Fin.suc Fin.zero) ⦄ ⦃ ★∼G = ★∼Xᵍ refl ⦄
      (id (＇ (Fin.suc Fin.zero))) ⦃ nonstar-X ⦄

raw-exposed : genᵐ μ₀ ⊢ `∀ A-body ∼ B
raw-exposed = inst_ ⦃ Anv = nonvar-fun ⦄ ⦃ z∈A = zero∈A-body ⦄
  body B≠★

shift-A : `∀ A-body ≡ ⇑ᵗ A
shift-A = refl

exposed : genᵐ μ₀ ⊢ ⇑ᵗ A ∼ B
exposed = subst-left-∼ shift-A raw-exposed

exposed-safe : GenSafe exposed
exposed-safe = subst-left-gen-safe shift-A
  (safe-inst ⦃ Anv = nonvar-fun ⦄
    ⦃ z∈A = zero∈A-body ⦄ B≠★)

A≠★ : A ≢ ★
A≠★ ()

outer-value : ∀ {V : Term 0}
  → Value V
  → Value (V ⟨ (gen exposed) A≠★ ⟩)
outer-value vV = vV 《 genᵥ A≠★ exposed-safe 》

exposed-not-inert : ¬ Inert exposed
exposed-not-inert ()

exposed-not-value : ∀ {V : Term 1}
  → Value V
  → ¬ Value (V ⟨ exposed ⟩)
exposed-not-value vV (vV′ 《 inert 》) = exposed-not-inert inert
