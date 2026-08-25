module proof.ImprecisionComposition where

-- File Charter:
--   * Proves transitivity of type imprecision under a fixed imprecision
--     environment.
--   * Handles structural, instantiating, dynamic, and bottom universal cases.
--   * Depends on the structural transport lemmas for type imprecision.

open import Data.Fin using (suc)

open import Types
open import Imprecision
open import proof.Imprecision using (imprecision-to-fresh)
open import proof.ImprecisionConsistency using
  ( ext-to-inst-star-map
  ; fin-suc-injective
  ; imp-env-weaken
  ; rename-⊑
  ; source-nonvar-from-target
  ; target-occurs-source
  ; universal-right-to-star
  )


source-nonstar-from-target : ∀ {Δ} {μ : ImpEnv Δ} {A B : Ty Δ}
  → μ ⊢ A ⊑ B
  → NonStar B
  → NonStar A
source-nonstar-from-target ★⊑★ ()
source-nonstar-from-target ι⊑ι nonstar-ι = nonstar-ι
source-nonstar-from-target X⊑X nonstar-X = nonstar-X
source-nonstar-from-target (⇒⊑⇒ p q) nonstar-⇒ = nonstar-⇒
source-nonstar-from-target (∀⊑∀ p) nonstar-∀ = nonstar-∀
source-nonstar-from-target (⇒⊑★ p q) ()
source-nonstar-from-target ι⊑★ ()
source-nonstar-from-target (X⊑★ eq) ()
source-nonstar-from-target (∀⊑ Anv zero∈A p) Bns = nonstar-∀
source-nonstar-from-target ∀★⊑★ ()
source-nonstar-from-target (∀⊑★ Ans p) ()
source-nonstar-from-target bot-elim nonstar-∀ = nonstar-∀
source-nonstar-from-target bot⊑★ ()


⊑-trans : ∀ {Δ} {μ : ImpEnv Δ} {A B C : Ty Δ}
  → μ ⊢ A ⊑ B
  → μ ⊢ B ⊑ C
  → μ ⊢ A ⊑ C
⊑-trans ★⊑★ ★⊑★ = ★⊑★
⊑-trans ι⊑ι ι⊑ι = ι⊑ι
⊑-trans ι⊑ι ι⊑★ = ι⊑★
⊑-trans X⊑X X⊑X = X⊑X
⊑-trans X⊑X (X⊑★ eq) = X⊑★ eq
⊑-trans (⇒⊑⇒ p₁ p₂) (⇒⊑⇒ q₁ q₂) =
  ⇒⊑⇒ (⊑-trans p₁ q₁) (⊑-trans p₂ q₂)
⊑-trans (⇒⊑⇒ p₁ p₂) (⇒⊑★ q₁ q₂) =
  ⇒⊑★ (⊑-trans p₁ q₁) (⊑-trans p₂ q₂)
⊑-trans (∀⊑∀ p) (∀⊑∀ q) = ∀⊑∀ (⊑-trans p q)
⊑-trans (∀⊑∀ p) (∀⊑ Bnv zero∈B q) =
  ∀⊑ (source-nonvar-from-target p Bnv zero∈B)
    (target-occurs-source p zero∈B)
    (⊑-trans (imp-env-weaken ext-to-inst-star-map p) q)
⊑-trans (∀⊑∀ p) ∀★⊑★ = universal-right-to-star (∀⊑∀ p)
⊑-trans (∀⊑∀ p) (∀⊑★ Bns q) =
  ∀⊑★ (source-nonstar-from-target p Bns) (⊑-trans p q)
⊑-trans (∀⊑∀ p) bot-elim
    rewrite imprecision-to-fresh p =
  bot-elim
⊑-trans (∀⊑∀ p) bot⊑★
    rewrite imprecision-to-fresh p =
  bot⊑★
⊑-trans (⇒⊑★ p q) ★⊑★ = ⇒⊑★ p q
⊑-trans ι⊑★ ★⊑★ = ι⊑★
⊑-trans (X⊑★ eq) ★⊑★ = X⊑★ eq
⊑-trans (∀⊑ Anv zero∈A p) q =
  ∀⊑ Anv zero∈A
    (⊑-trans p
      (rename-⊑ suc fin-suc-injective (λ X eq → eq) q))
⊑-trans ∀★⊑★ ★⊑★ = ∀★⊑★
⊑-trans (∀⊑★ Ans p) ★⊑★ = ∀⊑★ Ans p
⊑-trans bot-elim (∀⊑∀ ★⊑★) = bot-elim
⊑-trans bot-elim ∀★⊑★ = bot⊑★
⊑-trans bot⊑★ ★⊑★ = bot⊑★
