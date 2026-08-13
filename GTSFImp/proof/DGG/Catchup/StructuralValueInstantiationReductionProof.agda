module
  proof.DGG.Catchup.StructuralValueInstantiationReductionProof where

-- File Charter:
--   * Lifts one allocating reduction through a typed pending spine.
--   * Maps every surrounding frame across the fresh binding.

open import Data.Nat using (suc)
open import Types using (Ty)
open import Conversion using (Conv↑; Conv↓; rename↑; rename↓)
open import CastTerms using (Term; _↑_; _↓_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Reduction using
  (keep; bind; _—→[_]_; ξ-•; ξ-⟨⟩; ξ-reveal; ξ-conceal)
open import proof.TypeInTermSubst using (renameᵗ-id)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef


renamed↑-to-normalized-term : ∀ {Δ} {A B : Ty Δ}
    (M : Term Δ) (c : Conv↑ Δ A B)
  → M ↑ rename↑ (λ X → X) c ≡ M ↑ normalize-renamed↑ c
renamed↑-to-normalized-term {A = A} {B = B} M c =
  reveal-subst-term (renameᵗ-id A) (renameᵗ-id B) M
    (rename↑ (λ X → X) c)
  where
  reveal-subst-term : ∀ {A₀ A₁ B₀ B₁ : Ty _}
    → (eqA : A₀ ≡ A₁) → (eqB : B₀ ≡ B₁)
    → (M : Term _) → (d : Conv↑ _ A₀ B₀)
    → M ↑ d ≡ M ↑ subst (Conv↑ _ A₁) eqB
        (subst (λ A′ → Conv↑ _ A′ B₀) eqA d)
  reveal-subst-term refl refl M d = refl


renamed↓-to-normalized-term : ∀ {Δ} {A B : Ty Δ}
    (M : Term Δ) (c : Conv↓ Δ A B)
  → M ↓ rename↓ (λ X → X) c ≡ M ↓ normalize-renamed↓ c
renamed↓-to-normalized-term {A = A} {B = B} M c =
  conceal-subst-term (renameᵗ-id A) (renameᵗ-id B) M
    (rename↓ (λ X → X) c)
  where
  conceal-subst-term : ∀ {A₀ A₁ B₀ B₁ : Ty _}
    → (eqA : A₀ ≡ A₁) → (eqB : B₀ ≡ B₁)
    → (M : Term _) → (d : Conv↓ _ A₀ B₀)
    → M ↓ d ≡ M ↓ subst (Conv↓ _ A₁) eqB
        (subst (λ A′ → Conv↓ _ A′ B₀) eqA d)
  conceal-subst-term refl refl M d = refl


lift-instantiation-frame-keep : ∀ {Δ A B}
    {M M′ : Term Δ}
  → M —→[ keep ] M′
  → (frame : InstantiationFrame A B)
  → applyInstantiationFrame M frame —→[ keep ]
      applyInstantiationFrame M′ (mapInstantiationFrame keep frame)
lift-instantiation-frame-keep step (type-transport-frame eq) = step
lift-instantiation-frame-keep step
    (name-type-app-frame B X eqA eqC) =
  ξ-• step refl refl
lift-instantiation-frame-keep step (cast-frame c) = ξ-⟨⟩ step refl
lift-instantiation-frame-keep {M = M} {M′ = M′} step (reveal-frame c) =
  subst (λ N → M ↑ c —→[ keep ] N)
    (renamed↑-to-normalized-term M′ c) (ξ-reveal step refl)
lift-instantiation-frame-keep {M = M} {M′ = M′} step (conceal-frame c) =
  subst (λ N → M ↓ c —→[ keep ] N)
    (renamed↓-to-normalized-term M′ c) (ξ-conceal step refl)


lift-instantiation-spine-keep : ∀ {Δ A B}
    {M M′ : Term Δ}
  → M —→[ keep ] M′
  → (spine : InstantiationSpine A B)
  → applyInstantiationSpine M spine —→[ keep ]
      applyInstantiationSpine M′ (mapInstantiationSpine keep spine)
lift-instantiation-spine-keep step []ⁱ = step
lift-instantiation-spine-keep step (frame ▻ⁱ spine) =
  lift-instantiation-spine-keep
    (lift-instantiation-frame-keep step frame) spine


lift-instantiation-frame-bind : ∀ {Δ A B}
    {M : Term Δ} {M′ : Term (suc Δ)} {R : Ty Δ}
  → M —→[ bind R ] M′
  → (frame : InstantiationFrame A B)
  → applyInstantiationFrame M frame —→[ bind R ]
      applyInstantiationFrame M′ (mapInstantiationFrame (bind R) frame)
lift-instantiation-frame-bind step (type-transport-frame eq) = step
lift-instantiation-frame-bind step
    (name-type-app-frame B X eqA eqC) =
  ξ-• step refl refl
lift-instantiation-frame-bind step (cast-frame c) =
  ξ-⟨⟩ step refl
lift-instantiation-frame-bind step (reveal-frame c) =
  ξ-reveal step refl
lift-instantiation-frame-bind step (conceal-frame c) =
  ξ-conceal step refl


lift-instantiation-spine-bind : ∀ {Δ A B}
    {M : Term Δ} {M′ : Term (suc Δ)} {R : Ty Δ}
  → M —→[ bind R ] M′
  → (spine : InstantiationSpine A B)
  → applyInstantiationSpine M spine —→[ bind R ]
      applyInstantiationSpine M′
        (mapInstantiationSpine (bind R) spine)
lift-instantiation-spine-bind step []ⁱ = step
lift-instantiation-spine-bind step (frame ▻ⁱ spine) =
  lift-instantiation-spine-bind
    (lift-instantiation-frame-bind step frame) spine
