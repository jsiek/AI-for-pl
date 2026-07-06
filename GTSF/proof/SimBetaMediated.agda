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
open import NarrowWiden using (cross) renaming (_↦_ to _↦ⁿʷ_)
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
-- Source-cast branches.  The one-store cast evidence carried by the
-- mediated constructors makes the shape analysis local: the deriv and
-- witness in the premise refute the impossible coercion shapes
-- directly, where the old proof routed every shape through
-- canonical-⇒/FunView on the term typing.
--
-- cast+⊒ᵗ: the source term is V ⟨ narrowing-dual¹ s⊒ˡ ⟩ with
-- s ∶ (A ⇒ B) ⊒ C.  A source-typed narrowing witness at an arrow
-- source is either an arrow cross witness or refuted.
sim-betaᵐ
  (cast+⊒ᵗ {s = id X} qᶜ r⊒ (cast-id _ _ , cross ()) comp V⊒ƛ)
sim-betaᵐ (cast+⊒ᵗ {s = s₁ ︔ s₂} qᶜ r⊒ s⊒ˡ comp V⊒ƛ)
    vWL noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR =
  {! sim-beta-mediated-cast-plus-seq !}
sim-betaᵐ (cast+⊒ᵗ {s = unseal α X} qᶜ r⊒ s⊒ˡ comp V⊒ƛ)
    vWL noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR =
  {! sim-beta-mediated-cast-plus-unseal !}
sim-betaᵐ (cast+⊒ᵗ {s = inst X s} qᶜ r⊒ s⊒ˡ comp V⊒ƛ)
    vWL noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR =
  {! sim-beta-mediated-cast-plus-inst !}
sim-betaᵐ (cast+⊒ᵗ {s = gen X s} qᶜ r⊒ s⊒ˡ comp V⊒ƛ)
    vWL noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR =
  {! sim-beta-mediated-cast-plus-gen !}
sim-betaᵐ (cast+⊒ᵗ {s = seal X α} qᶜ r⊒ s⊒ˡ comp V⊒ƛ)
    vWL noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR =
  {! sim-beta-mediated-cast-plus-seal !}
sim-betaᵐ (cast+⊒ᵗ {s = X !} qᶜ r⊒ s⊒ˡ comp V⊒ƛ)
    vWL noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR =
  {! sim-beta-mediated-cast-plus-tag !}
sim-betaᵐ
    (cast+⊒ᵗ {s = cₛ ↦ dₛ} qᶜ r⊒
      (cast-fun c⊢ d⊢ , cross (cʷ ↦ⁿʷ dⁿ)) comp V⊒ƛ)
    vWL noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR =
  {! sim-beta-mediated-cast-plus-fun !}
  -- obligations: β-↦ on (V ⟨ dual cₛ ↦ dual dₛ ⟩) · WR, cast-⊒ᵗ node
  -- for WR ⟨ dual cₛ ⟩ against the inner domain, recursive sim-betaᵐ
  -- on V⊒ƛ via catchup-lemmaᵐ, and the ⊒cast-ᵗ tail at dual dₛ; the
  -- composition side conditions come from `comp`'s left-store record
  -- projected to domain/codomain.
--
-- cast-⊒ᵗ: the source term is V ⟨ s ⟩ with s ∶ A₀ ⊒ (A ⇒ B); the
-- value premise (Inert s) and the witness refute the non-arrow
-- shapes.
sim-betaᵐ
  (cast-⊒ᵗ {s = id X} qᶜ r⊒ (cast-id _ _ , cross ()) comp V⊒ƛ)
sim-betaᵐ (cast-⊒ᵗ {s = s₁ ︔ s₂} qᶜ r⊒ s⊒ˡ comp V⊒ƛ)
    (vV ⟨ () ⟩)
sim-betaᵐ (cast-⊒ᵗ {s = X ？} qᶜ r⊒ s⊒ˡ comp V⊒ƛ)
    (vV ⟨ () ⟩)
sim-betaᵐ (cast-⊒ᵗ {s = unseal α X} qᶜ r⊒ s⊒ˡ comp V⊒ƛ)
    (vV ⟨ () ⟩)
sim-betaᵐ (cast-⊒ᵗ {s = inst X s} qᶜ r⊒ s⊒ˡ comp V⊒ƛ)
    (vV ⟨ () ⟩)
sim-betaᵐ
    (cast-⊒ᵗ {s = cₛ ↦ dₛ} qᶜ r⊒
      (cast-fun c⊢ d⊢ , cross (cʷ ↦ⁿʷ dⁿ)) comp V⊒ƛ)
    vWL noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR =
  {! sim-beta-mediated-cast-minus-fun !}
  -- obligations: β-↦ on (V ⟨ cₛ ↦ dₛ ⟩) · WR, cast-⊒ᵗ node for
  -- WR ⟨ cₛ ⟩ against the inner domain, recursive sim-betaᵐ on V⊒ƛ
  -- via catchup-lemmaᵐ, and the ⊒cast-ᵗ tail at dₛ; compositions from
  -- `comp` projected to domain/codomain.
