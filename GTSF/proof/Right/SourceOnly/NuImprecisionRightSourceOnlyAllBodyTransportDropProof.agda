module
  proof.Right.SourceOnly.NuImprecisionRightSourceOnlyAllBodyTransportDropProof
  where

-- File Charter:
--   * Proves target-only matched-body transport below a source-only binder
--     can be dropped to the base world.
--   * Commutes the source-only binder through the matched binder, transports,
--     commutes back, removes the fresh name, and cancels the lift.
--   * Contains no simulation result, catch-up carrier, postulate, hole,
--     permissive option, termination bypass, or broad simulation import.

open import Relation.Binary.PropositionalEquality using (subst)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  ( ∀ᵢᶜ
  ; νᵢᶜ
  ; open-unusedᵢ
  ; renameᵗ-swap01-involutiveᵢ
  ; ⊑-source-liftνᵢ
  ; ⊑-∀ν-to-ν∀ᵢ
  ; ⊑-ν∀-to-∀νᵢ
  )
open import
  proof.Right.SourceOnly.NuImprecisionRightSourceOnlyAllBodyTransportDropDef
  using (RightSourceOnlyAllBodyTransportDropᵀ)
open import proof.Core.Properties.TypeProperties using
  (occurs-raise-fresh; renameᵗ-single-suc-cancel)


right-source-only-all-body-transport-drop-proofᵀ :
  RightSourceOnlyAllBodyTransportDropᵀ
right-source-only-all-body-transport-drop-proofᵀ
    {Ψ = Ψ} {χs = χs} transport {C = C} {D = D} q =
  subst
    (λ S → ∀ᵢᶜ Ψ ∣ _ ⊢ S ⊑ _ ⊣ _)
    (renameᵗ-single-suc-cancel _ C)
    (open-unusedᵢ
      (occurs-raise-fresh _ C)
      unswapped)
  where
  unswapped =
    subst
      (λ S → νᵢᶜ (∀ᵢᶜ Ψ) ∣ _ ⊢ S ⊑ _ ⊣ _)
      (renameᵗ-swap01-involutiveᵢ _)
      (⊑-∀ν-to-ν∀ᵢ
        (transport
          (⊑-ν∀-to-∀νᵢ
            (⊑-source-liftνᵢ q))))
