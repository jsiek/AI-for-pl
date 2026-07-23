module
  proof.NuImprecisionRightSourceOnlyTransportDropProof
  where

-- File Charter:
--   * Proves target-only transport below a source-only binder can be dropped
--     to the base world.
--   * Lifts the input relation, applies the supplied transport, removes the
--     fresh unused source name, and cancels the lift.
--   * Contains no simulation result, catch-up carrier, postulate, hole,
--     permissive option, termination bypass, or broad simulation import.

open import Relation.Binary.PropositionalEquality using (subst)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import proof.MaximalLowerBoundsWf using
  (open-unusedᵢ; ⊑-source-liftνᵢ)
open import
  proof.NuImprecisionRightSourceOnlyTransportDropDef
  using (RightSourceOnlyTransportDropᵀ)
open import proof.TypeProperties using
  (occurs-raise-fresh; renameᵗ-single-suc-cancel)


right-source-only-transport-drop-proofᵀ :
  RightSourceOnlyTransportDropᵀ
right-source-only-transport-drop-proofᵀ
    {Ψ = Ψ} {χs = χs} transport {C = C} {D = D} q =
  subst
    (λ S → Ψ ∣ _ ⊢ S ⊑ _ ⊣ _)
    (renameᵗ-single-suc-cancel _ C)
    (open-unusedᵢ
      (occurs-raise-fresh _ C)
      (transport (⊑-source-liftνᵢ q)))
