module proof.Source.Core.NuImprecisionSourceGenTargetGroundAgreementDef where

-- File Charter:
--   * Defines the static agreement needed when target untagging meets a
--     terminal source `gen` value.
--   * Connects the ground label stored by the target tag to the requested
--     ground endpoint of the source universal.
--   * Retained as a refuted boundary: the repaired strict counterexample shows
--     that the current contract lacks the source-value premise needed to
--     exclude an active source untag around the target tag.
--   * Contains no implementation, simulation result, view, or outcome.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])

open import Coercions using (Coercion; ModeEnv; gen; _!)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ground; Ty; ★; `∀)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)


SourceGenTargetGroundAgreementᵀ : Set₁
SourceGenTargetGroundAgreementᵀ =
  ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W : Term} {A B G H : Ty} {c : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ} →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  Ground H →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ gen A c ∶ A ⊒ `∀ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ W ⟨ G ! ⟩ ⦂ A ⊑ ★ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ H ⊣ Δᴿ) →
  G ≡ H
