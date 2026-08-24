module proof.LR-narrow.ImprecisionSize where

-- File Charter:
--   * The size of a center imprecision derivation, and its
--     preservation by renaming and future lifting.
--   * The measure of the (index, derivation) lexicographic recursion
--     of the structural reveal: the `∀⊑` case recurses at the same
--     step index into the strictly smaller body derivation.

open import Data.Nat using (ℕ; suc; _+_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)
import Data.Fin as Fin

open import Types
import Imprecision as I
open import proof.ImprecisionConsistency using (rename-⊑)
open import LR-narrow.World

sizeᵖ : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ} → μ I.⊢ A ⊑ B → ℕ
sizeᵖ I.★⊑★ = 1
sizeᵖ I.ι⊑ι = 1
sizeᵖ I.X⊑X = 1
sizeᵖ (I.⇒⊑⇒ p q) = suc (sizeᵖ p + sizeᵖ q)
sizeᵖ (I.∀⊑∀ p) = suc (sizeᵖ p)
sizeᵖ (I.⇒⊑★ p q) = suc (sizeᵖ p + sizeᵖ q)
sizeᵖ I.ι⊑★ = 1
sizeᵖ (I.X⊑★ eq) = 1
sizeᵖ (I.∀⊑ nonvar occurs p) = suc (sizeᵖ p)
sizeᵖ I.∀★⊑★ = 1
sizeᵖ (I.∀⊑★ nonstar p) = suc (sizeᵖ p)
sizeᵖ I.bot-elim = 1
sizeᵖ I.bot⊑★ = 1

size-subst-right : ∀ {Δ} {μ : I.ImpEnv Δ} {A B B′ : Ty Δ}
    (eq : B ≡ B′) (p : μ I.⊢ A ⊑ B)
  → sizeᵖ (subst≡ (λ T → μ I.⊢ A ⊑ T) eq p) ≡ sizeᵖ p
size-subst-right refl p = refl

rename-⊑-size : ∀ {Δ Δ′} {μ : I.ImpEnv Δ} {μ′ : I.ImpEnv Δ′}
    {A B : Ty Δ}
    (ρ : Δ ⇒ʳ Δ′)
    (injective : ∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
    (h : ∀ X → μ X ≡ I.X⊑★ → μ′ (ρ X) ≡ I.X⊑★)
    (p : μ I.⊢ A ⊑ B)
  → sizeᵖ (rename-⊑ {μ = μ} {μ′ = μ′} ρ injective h p) ≡ sizeᵖ p
rename-⊑-size ρ injective h I.★⊑★ = refl
rename-⊑-size ρ injective h I.ι⊑ι = refl
rename-⊑-size ρ injective h I.X⊑X = refl
rename-⊑-size ρ injective h (I.⇒⊑⇒ p q) =
  cong suc (cong₂ _+_ (rename-⊑-size ρ injective h p)
    (rename-⊑-size ρ injective h q))
rename-⊑-size ρ injective h (I.∀⊑∀ p) =
  cong suc (rename-⊑-size _ _ _ p)
rename-⊑-size ρ injective h (I.⇒⊑★ p q) =
  cong suc (cong₂ _+_ (rename-⊑-size ρ injective h p)
    (rename-⊑-size ρ injective h q))
rename-⊑-size ρ injective h I.ι⊑★ = refl
rename-⊑-size ρ injective h (I.X⊑★ eq) = refl
rename-⊑-size ρ injective h (I.∀⊑ nonvar occurs p) =
  cong suc (trans (size-subst-right (renameᵗ-shift ρ _) _)
    (rename-⊑-size _ _ _ p))
rename-⊑-size ρ injective h I.∀★⊑★ = refl
rename-⊑-size ρ injective h (I.∀⊑★ nonstar p) =
  cong suc (rename-⊑-size _ _ _ p)
rename-⊑-size ρ injective h I.bot-elim = refl
rename-⊑-size ρ injective h I.bot⊑★ = refl

lift-center-size : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Aᴾ Aᴵ : Ty Δᶜ}
    (W≼W′ : Future W W′)
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → sizeᵖ (liftCenterImprecision W≼W′ p) ≡ sizeᵖ p
lift-center-size future-refl p = refl
lift-center-size (future-paired W≼W′ r) p =
  trans (rename-⊑-size Fin.suc _ _ (liftCenterImprecision W≼W′ p))
    (lift-center-size W≼W′ p)
lift-center-size (future-precise W≼W′ r) p =
  trans (rename-⊑-size Fin.suc _ _ (liftCenterImprecision W≼W′ p))
    (lift-center-size W≼W′ p)
lift-center-size (future-imprecise W≼W′) p =
  trans (rename-⊑-size Fin.suc _ _ (liftCenterImprecision W≼W′ p))
    (lift-center-size W≼W′ p)
