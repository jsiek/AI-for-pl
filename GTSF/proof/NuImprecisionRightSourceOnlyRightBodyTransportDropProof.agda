module
  proof.NuImprecisionRightSourceOnlyRightBodyTransportDropProof
  where

-- File Charter:
--   * Proves target-only right-body transport below a source-only binder can
--     be dropped to the base world.
--   * Commutes the source-only binder through the target lift, transports,
--     commutes back, removes the fresh name, and cancels the lift.
--   * Contains no simulation result, catch-up carrier, postulate, hole,
--     permissive option, termination bypass, or broad simulation import.

open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; _ˣ⊑★; ⇑ᴸᵢ; ⇑ᴿᵢ)
open import Types using (⇑ᵗ)
open import proof.MaximalLowerBoundsWf using
  (νᵢᶜ; open-unusedᵢ; ⊑-source-liftνᵢ)
open import proof.NuImprecisionRightContextAction using
  (⇑ᴸᵢ-⇑ᴿᵢ-commute)
open import
  proof.NuImprecisionRightSourceOnlyRightBodyTransportDropDef
  using (RightSourceOnlyRightBodyTransportDropᵀ)
open import proof.ReductionProperties using (applyTysUnderTyBinders)
open import proof.TypeProperties using
  (occurs-raise-fresh; renameᵗ-single-suc-cancel)


right-source-only-right-body-transport-drop-proofᵀ :
  RightSourceOnlyRightBodyTransportDropᵀ
right-source-only-right-body-transport-drop-proofᵀ
    {Φ = Φ} {Ψ = Ψ}
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {Θᴿ = Θᴿ} {χs = χs}
    transport {C = C} {D = D} q =
  subst
    (λ S → ⇑ᴿᵢ Ψ ∣ Δᴸ
      ⊢ S ⊑ applyTysUnderTyBinders χs D ⊣ suc Θᴿ)
    (renameᵗ-single-suc-cancel zero C)
    (open-unusedᵢ
      (occurs-raise-fresh zero C)
      transported)
  where
  lifted :
    ⇑ᴿᵢ (νᵢᶜ Φ)
      ∣ suc Δᴸ ⊢ ⇑ᵗ C ⊑ D ⊣ suc Δᴿ
  lifted =
    subst
      (λ Ω → Ω ∣ suc Δᴸ ⊢ ⇑ᵗ C ⊑ D ⊣ suc Δᴿ)
      (cong ((zero ˣ⊑★) ∷_) (⇑ᴸᵢ-⇑ᴿᵢ-commute Φ))
      (⊑-source-liftνᵢ q)

  transported :
    νᵢᶜ (⇑ᴿᵢ Ψ)
      ∣ suc Δᴸ
      ⊢ ⇑ᵗ C ⊑ applyTysUnderTyBinders χs D
      ⊣ suc Θᴿ
  transported =
    subst
      (λ Ω → Ω ∣ suc Δᴸ
        ⊢ ⇑ᵗ C ⊑ applyTysUnderTyBinders χs D
        ⊣ suc Θᴿ)
      (sym
        (cong
          ((zero ˣ⊑★) ∷_)
          (⇑ᴸᵢ-⇑ᴿᵢ-commute Ψ)))
      (transport lifted)
