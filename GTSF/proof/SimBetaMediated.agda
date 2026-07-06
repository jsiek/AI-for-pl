{-# OPTIONS --allow-unsolved-metas #-}

module proof.SimBetaMediated where

-- File Charter:
--   * The beta simulation over the mediated narrowing relation: the
--     source function position catches up to a lambda and the
--     application steps, transporting the relation across the
--     accumulated left store changes.
--   * Port of `proof.SimBetaSeparated.sim-beta`.  The statement sheds
--     the index rewriting: the old conclusion was at
--     `applyCoercions χs q`, forcing the applyCoercions-++ and
--     dual-commutation plumbing (and the approved
--     `left-change-fun-coercion-narrowing` postulate) through every
--     cast branch; the mediated conclusion keeps the original `q`,
--     since source store changes never touch a mediated index raw
--     (`left-changes-transportᵐ`).  The proof skeleton splits on the
--     function relation like the old proof; the branch bodies migrate
--     incrementally from SimBetaSeparated.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Types
open import Coercions
open import NuTerms
open import NuReduction
open import StoreCorrespondence
open import Mediation
open import MediatedNarrowing
open import proof.CatchupSeparated using (applyLeftChanges)
open import proof.CatchupMediated using (catchup-lemmaᵐ)
open import proof.MediationProperties using
  ( left-changes-transportᵐ
  )

sim-betaᵐ :
  ∀ {ΔL ΔR ρ WL NL WR VR p q A A′ B B′ μsim} →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ WL ⊒ ƛ NL ∶ p ↦ q
    ⦂ A ⇒ B ⊒ᵐ A′ ⇒ B′ →
  Value WL →
  No• WL →
  (p↦q-sim⊒ : μsim ∣ ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q
                ∶ (A ⇒ B) ⊒ᵐ (A′ ⇒ B′)) →
  ΔL ∣ ΔR ∣ ρ
    ⊢ fun-narrow-domain-dualᵐ p↦q-sim⊒ ∶ᶜ A ⊒ᵐ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ []
    ⊢ WR ⊒ VR ∶ fun-narrow-domain-dualᵐ p↦q-sim⊒ ⦂ A ⊒ᵐ A′ →
  Value WR →
  No• WR →
  Value VR →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ]
    (WL · WR —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ NL [ VR ] ∶ q ⦂ applyTys χs B ⊒ᵐ B′
sim-betaᵐ (ƛ⊒ƛᵗ p↦qᶜ N⊒NL)
    vWL noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR =
  {! sim-beta-mediated-lambda !}
sim-betaᵐ (cast+⊒ᵗ qᶜ r⊒ s⊒ˡ comp V⊒ƛ)
    vWL noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR =
  {! sim-beta-mediated-source-cast-plus !}
sim-betaᵐ (cast-⊒ᵗ qᶜ r⊒ s⊒ˡ comp V⊒ƛ)
    vWL noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR =
  {! sim-beta-mediated-source-cast-minus !}
