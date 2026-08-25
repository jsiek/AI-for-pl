module proof.ImprecisionComposition where

-- File Charter:
--   * Proves transitivity of type imprecision under a fixed imprecision
--     environment.
--   * Handles structural, instantiating, dynamic, and bottom universal cases.
--   * Depends on the structural transport lemmas for type imprecision.

open import Data.Fin using (suc)

open import Types
import Imprecision as I
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


source-nonstar-from-target : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
  → I._⊢_⊑_ μ A B
  → NonStar B
  → NonStar A
source-nonstar-from-target I.★⊑★ ()
source-nonstar-from-target I.ι⊑ι nonstar-ι = nonstar-ι
source-nonstar-from-target I.X⊑X nonstar-X = nonstar-X
source-nonstar-from-target (I.⇒⊑⇒ p q) nonstar-⇒ = nonstar-⇒
source-nonstar-from-target (I.∀⊑∀ p) nonstar-∀ = nonstar-∀
source-nonstar-from-target (I.⇒⊑★ p q) ()
source-nonstar-from-target I.ι⊑★ ()
source-nonstar-from-target (I.X⊑★ eq) ()
source-nonstar-from-target (I.∀⊑ Anv zero∈A p) Bns = nonstar-∀
source-nonstar-from-target I.∀★⊑★ ()
source-nonstar-from-target (I.∀⊑★ Ans p) ()
source-nonstar-from-target I.bot-elim nonstar-∀ = nonstar-∀
source-nonstar-from-target I.bot⊑★ ()


⊑-trans : ∀ {Δ} {μ : I.ImpEnv Δ} {A B C : Ty Δ}
  → I._⊢_⊑_ μ A B
  → I._⊢_⊑_ μ B C
  → I._⊢_⊑_ μ A C
⊑-trans I.★⊑★ I.★⊑★ = I.★⊑★
⊑-trans I.ι⊑ι I.ι⊑ι = I.ι⊑ι
⊑-trans I.ι⊑ι I.ι⊑★ = I.ι⊑★
⊑-trans I.X⊑X I.X⊑X = I.X⊑X
⊑-trans I.X⊑X (I.X⊑★ eq) = I.X⊑★ eq
⊑-trans (I.⇒⊑⇒ p₁ p₂) (I.⇒⊑⇒ q₁ q₂) =
  I.⇒⊑⇒ (⊑-trans p₁ q₁) (⊑-trans p₂ q₂)
⊑-trans (I.⇒⊑⇒ p₁ p₂) (I.⇒⊑★ q₁ q₂) =
  I.⇒⊑★ (⊑-trans p₁ q₁) (⊑-trans p₂ q₂)
⊑-trans (I.∀⊑∀ p) (I.∀⊑∀ q) = I.∀⊑∀ (⊑-trans p q)
⊑-trans (I.∀⊑∀ p) (I.∀⊑ Bnv zero∈B q) =
  I.∀⊑ (source-nonvar-from-target p Bnv zero∈B)
    (target-occurs-source p zero∈B)
    (⊑-trans (imp-env-weaken ext-to-inst-star-map p) q)
⊑-trans (I.∀⊑∀ p) I.∀★⊑★ =
  universal-right-to-star (I.∀⊑∀ p)
⊑-trans (I.∀⊑∀ p) (I.∀⊑★ Bns q) =
  I.∀⊑★ (source-nonstar-from-target p Bns) (⊑-trans p q)
⊑-trans (I.∀⊑∀ p) I.bot-elim
    rewrite imprecision-to-fresh p =
  I.bot-elim
⊑-trans (I.∀⊑∀ p) I.bot⊑★
    rewrite imprecision-to-fresh p =
  I.bot⊑★
⊑-trans (I.⇒⊑★ p q) I.★⊑★ = I.⇒⊑★ p q
⊑-trans I.ι⊑★ I.★⊑★ = I.ι⊑★
⊑-trans (I.X⊑★ eq) I.★⊑★ = I.X⊑★ eq
⊑-trans (I.∀⊑ Anv zero∈A p) q =
  I.∀⊑ Anv zero∈A
    (⊑-trans p
      (rename-⊑ suc fin-suc-injective (λ X eq → eq) q))
⊑-trans I.∀★⊑★ I.★⊑★ = I.∀★⊑★
⊑-trans (I.∀⊑★ Ans p) I.★⊑★ = I.∀⊑★ Ans p
⊑-trans I.bot-elim (I.∀⊑∀ I.★⊑★) = I.bot-elim
⊑-trans I.bot-elim I.∀★⊑★ = I.bot⊑★
⊑-trans I.bot⊑★ I.★⊑★ = I.bot⊑★
