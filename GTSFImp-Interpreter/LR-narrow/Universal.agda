module LR-narrow.Universal where

-- File Charter:
--   * Exposes symmetric universal-introduction compatibility.
--   * Exposes the binder-specific body relation and its LR constructor.
--   * Keeps evaluator and endpoint proof scripts in the proof namespace.

open import Data.Nat using (ℕ; suc; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import CastTerms
import Consistency
import Imprecision as I
import proof.DGG.CastTermImprecision2 as CTI
open CTI using (_∣_⊢²_⊑_∶_)
open import LR-narrow.World
open import LR-narrow.LogicalRelation
open import LR-narrow.ClosingSubstitution
open import LR-narrow.ClosingSubstitutionProperties
open import LR-narrow.TermRelation
import proof.LR-narrow.Universal as Proof

universal-body-imprecision : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Aᴾ : Ty (suc Δᴾ)} {Aᴵ : Ty (suc Δᴵ)}
  → Aᴾ CTI.⊑ᵂ⟨ CTI.liftWorldBoth I.X⊑X (forgetWorld W) ⟩ Aᴵ
  → I.extᵐ (impEnv (core W)) I.⊢
      renameᵗ (extᵗ (Consistency.toRenameᵗ
        (preciseEmbedding (core W)))) Aᴾ
      ⊑ renameᵗ (extᵗ (Consistency.toRenameᵗ
        (impreciseEmbedding (core W)))) Aᴵ
universal-body-imprecision {W = W} p =
  Proof.universal-body-imprecision {W = W} p

universals-related-from-body : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {p : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)}
    {Nᴾ : Term (suc Δᴾ)} {Nᴵ : Term (suc Δᴵ)}
  → Value Nᴾ
  → Value Nᴵ
  → (∀ i → i ≤ k →
      CompiledUniversalBodyRelation p Bᴾ Bᴵ i Γ Nᴾ Nᴵ)
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      (W≼W′ : Future W W′)
      (γ : RelatedClosingSubstitutions W′ k
        (liftContextImprecision W≼W′ (compiledContext W Γ)))
      (j : ℕ)
  → j ≤ k
  → UniversalsRelated W′ (liftCenterBodyImprecision W≼W′ p)
      (liftPreciseBody W≼W′ Bᴾ) (liftImpreciseBody W≼W′ Bᴵ) j
      (close (impreciseClosingSubstitution γ)
        (liftImpreciseTerm W≼W′ (Λ Nᴵ)))
      (close (preciseClosingSubstitution γ)
        (liftPreciseTerm W≼W′ (Λ Nᴾ)))
universals-related-from-body = Proof.universals-related-from-body

universal-compatible : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Aᴾ : Ty (suc Δᴾ)} {Aᴵ : Ty (suc Δᴵ)}
    {p : Aᴾ CTI.⊑ᵂ⟨ CTI.liftWorldBoth I.X⊑X (forgetWorld W) ⟩ Aᴵ}
    {Γ′ : CTI.CtxImp
      (CTI.liftWorldBoth I.X⊑X (forgetWorld W))}
    {Vᴾ : Term (suc Δᴾ)}
    {Vᴵ : Term (suc Δᴵ)}
  → (liftΓ : CTI.LiftCtx I.X⊑X Γ Γ′)
  → (vVᴾ : Value Vᴾ)
  → (vVᴵ : Value Vᴵ)
  → CTI.liftWorldBoth I.X⊑X (forgetWorld W) ∣ Γ′
      ⊢² Vᴾ ⊑ Vᴵ ∶ p
  → (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ `∀ Aᴵ)
  → (∀
      (q-body : I.extᵐ (impEnv (core W)) I.⊢
        renameᵗ (extᵗ (Consistency.toRenameᵗ
          (preciseEmbedding (core W)))) Aᴾ
        ⊑ renameᵗ (extᵗ (Consistency.toRenameᵗ
          (impreciseEmbedding (core W)))) Aᴵ)
      → q ≡ I.∀⊑∀ q-body
      → ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
          (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
          (W≼W′ : Future W W′)
          (γ : RelatedClosingSubstitutions W′ k
            (liftContextImprecision W≼W′ (compiledContext W Γ)))
          (j : ℕ)
      → j ≤ k
      → UniversalsRelated W′
          (liftCenterBodyImprecision W≼W′ q-body)
          (liftPreciseBody W≼W′ Aᴾ)
          (liftImpreciseBody W≼W′ Aᴵ) j
          (close (impreciseClosingSubstitution γ)
            (liftImpreciseTerm W≼W′ (Λ Vᴵ)))
          (close (preciseClosingSubstitution γ)
            (liftPreciseTerm W≼W′ (Λ Vᴾ))))
  → CompiledTermRelation {W = W} q k Γ (Λ Vᴾ) (Λ Vᴵ)
universal-compatible = Proof.universal-compatible

universal-compatible-from-body : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Aᴾ : Ty (suc Δᴾ)} {Aᴵ : Ty (suc Δᴵ)}
    {p : Aᴾ CTI.⊑ᵂ⟨
      CTI.liftWorldBoth I.X⊑X (forgetWorld W) ⟩ Aᴵ}
    {Γ′ : CTI.CtxImp
      (CTI.liftWorldBoth I.X⊑X (forgetWorld W))}
    {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term (suc Δᴵ)}
  → (liftΓ : CTI.LiftCtx I.X⊑X Γ Γ′)
  → (vVᴾ : Value Vᴾ)
  → (vVᴵ : Value Vᴵ)
  → CTI.liftWorldBoth I.X⊑X (forgetWorld W) ∣ Γ′
      ⊢² Vᴾ ⊑ Vᴵ ∶ p
  → (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ `∀ Aᴵ)
  → (∀ i → i ≤ k → CompiledUniversalBodyRelation
      (universal-body-imprecision {W = W} p)
      Aᴾ Aᴵ i Γ Vᴾ Vᴵ)
  → CompiledTermRelation {W = W} q k Γ (Λ Vᴾ) (Λ Vᴵ)
universal-compatible-from-body = Proof.universal-compatible-from-body
