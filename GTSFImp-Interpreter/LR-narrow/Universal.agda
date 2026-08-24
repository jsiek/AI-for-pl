module LR-narrow.Universal where

-- File Charter:
--   * Exposes paired and one-sided universal-introduction infrastructure.
--   * Exposes binder-specific body relations and their LR constructors.
--   * Reconstructs one-sided universal types from left-lifted body types.
--   * Bridges ordinary universal term relations to target-first body phases.
--   * Keeps evaluator and endpoint proof scripts in the proof namespace.

open import Data.Nat using (ℕ; suc; _≤_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import CastTerms
import Consistency
import Imprecision as I
import proof.DGG.CtxImp as CTI
import proof.DGG.CastTermImprecision as CTIR
open CTIR using (_∣_⊢²_⊑_∶_)
open import LR-narrow.World
open import LR-narrow.LogicalRelation
open import LR-narrow.UniversalFamily using (RightUniversalFamilyKit)
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

right-universal-body-imprecision : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Aᴾ : Ty (suc Δᴾ)} {Aᴵ : Ty Δᴵ}
  → Aᴾ CTI.⊑ᵂ⟨ CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ⟩ Aᴵ
  → I.instᵐ (impEnv (core W)) I.⊢
      renameᵗ (extᵗ (Consistency.toRenameᵗ
        (preciseEmbedding (core W)))) Aᴾ
      ⊑ ⇑ᵗ (embedImprecise (core W) Aᴵ)
right-universal-body-imprecision {W = W} p =
  Proof.right-universal-body-imprecision {W = W} p

right-universal-type-from-body : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Aᴾ : Ty (suc Δᴾ)} {Aᴵ : Ty Δᴵ}
  → NonVar Aᴾ
  → Fin.zero ∈ᵗ Aᴾ
  → Aᴾ CTI.⊑ᵂ⟨
      CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ⟩ Aᴵ
  → `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ
right-universal-type-from-body {W = W} nonvar occurs body-related =
  Proof.right-universal-type-from-body {W = W}
    nonvar occurs body-related

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
universals-related-from-body {p = p} =
  Proof.universals-related-from-body {p = p}

right-universals-related-from-body : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {p : I.instᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Nᴾ : Term (suc Δᴾ)} {Mᴵ : Term Δᴵ}
  → Value Nᴾ
  → (∀ i → i ≤ k →
      CompiledRightUniversalTestRelation {W = W}
        p Bᴾ Bᴵ i Γ Nᴾ Mᴵ)
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      (W≼W′ : Future W W′)
      (γ : RelatedClosingSubstitutions W′ k
        (liftContextImprecision W≼W′ (compiledContext W Γ)))
      (j : ℕ)
  → j ≤ k
  → RightUniversalsRelated W′
      (liftCenterDynamicBodyImprecision W≼W′ p)
      (liftPreciseBody W≼W′ Bᴾ) (liftImpreciseTy W≼W′ Bᴵ) j
      (close (impreciseClosingSubstitution γ)
        (liftImpreciseTerm W≼W′ Mᴵ))
      (close (preciseClosingSubstitution γ)
        (liftPreciseTerm W≼W′ (Λ Nᴾ)))
right-universals-related-from-body {W = W} {p = p} =
  Proof.right-universals-related-from-body {W = W} {p = p}

right-universal-body-phase-from-relation : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Vᴾ : Term (suc Δᴾ)} {Mᴵ : Term Δᴵ}
  → Value Vᴾ
  → (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
  → CompiledTermRelation {W = W} q k Γ (Λ Vᴾ) Mᴵ
  → CompiledRightUniversalBodyRelation q k Γ Vᴾ Mᴵ
right-universal-body-phase-from-relation =
  Proof.right-universal-body-phase-from-relation

right-universal-phase-compatible : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Vᴾ : Term (suc Δᴾ)} {Mᴵ : Term Δᴵ}
  → Value Vᴾ
  → (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
  → CompiledRightUniversalBodyRelation q k Γ Vᴾ Mᴵ
  → CompiledTermRelation {W = W} q k Γ (Λ Vᴾ) Mᴵ
right-universal-phase-compatible =
  Proof.right-universal-phase-compatible

right-universal-compatible-from-body : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {p : Aᴾ CTI.⊑ᵂ⟨
      CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ⟩ Bᴵ}
    {Γ′ : CTI.CtxImp
      (CTI.liftWorldLeft I.X⊑★ (forgetWorld W))}
    {Vᴾ : Term (suc Δᴾ)} {Mᴵ : Term Δᴵ}
  → (nonvar : NonVar Aᴾ)
  → (occurs : Fin.zero ∈ᵗ Aᴾ)
  → (liftΓ : CTI.LiftCtxᴸ I.X⊑★ Γ Γ′)
  → (vVᴾ : Value Vᴾ)
  → ⟨ Δᴵ , CTI.targetStoreʷ (forgetWorld W) ,
        CTI.tgtCtxʷ Γ ⟩ ⊢ Mᴵ ⦂ Bᴵ
  → CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ∣ Γ′
      ⊢² Vᴾ ⊑ Mᴵ ∶ p
  → (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
  → CompiledRightUniversalBodyRelation q k Γ Vᴾ Mᴵ
  → CompiledTermRelation {W = W} q k Γ (Λ Vᴾ) Mᴵ
right-universal-compatible-from-body =
  Proof.right-universal-compatible-from-body

right-universal-smart-compatible-from-body : ∀ {Δᴾ Δᴵ Δᶜ Δᵐ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Wᵐ : CTI.World (suc Δᴾ) Δᴵ Δᵐ}
    {Γᵐ : CTI.CtxImp Wᵐ}
    {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {p : Aᴾ CTI.⊑ᵂ⟨ Wᵐ ⟩ Bᴵ}
    {Vᴾ : Term (suc Δᴾ)} {Mᴵ : Term Δᴵ}
  → (nonvar : NonVar Aᴾ)
  → (occurs : Fin.zero ∈ᵗ Aᴾ)
  → (smart : CTI.SmartCommaLiftᴸ (forgetWorld W) Wᵐ)
  → (liftΓ : CTI.SmartLiftCtxᴸ Γ Γᵐ)
  → (vVᴾ : Value Vᴾ)
  → ⟨ Δᴵ , CTI.targetStoreʷ (forgetWorld W) ,
        CTI.tgtCtxʷ Γ ⟩ ⊢ Mᴵ ⦂ Bᴵ
  → Wᵐ ∣ Γᵐ ⊢² Vᴾ ⊑ Mᴵ ∶ p
  → (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
  → CompiledRightUniversalBodyRelation q k Γ Vᴾ Mᴵ
  → CompiledTermRelation {W = W} q k Γ (Λ Vᴾ) Mᴵ
right-universal-smart-compatible-from-body =
  Proof.right-universal-smart-compatible-from-body

right-universal-value-phase-from-body : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {p : Aᴾ CTI.⊑ᵂ⟨
      CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ⟩ Bᴵ}
    {Γ′ : CTI.CtxImp
      (CTI.liftWorldLeft I.X⊑★ (forgetWorld W))}
    {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term Δᴵ}
  → (kit : RightUniversalFamilyKit)
  → (nonvar : NonVar Aᴾ)
  → (occurs : Fin.zero ∈ᵗ Aᴾ)
  → (liftΓ : CTI.LiftCtxᴸ I.X⊑★ Γ Γ′)
  → (vVᴾ : Value Vᴾ)
  → (vVᴵ : Value Vᴵ)
  → ⟨ Δᴵ , CTI.targetStoreʷ (forgetWorld W) ,
        CTI.tgtCtxʷ Γ ⟩ ⊢ Vᴵ ⦂ Bᴵ
  → CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ∣ Γ′
      ⊢² Vᴾ ⊑ Vᴵ ∶ p
  → (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
  → (∀ i → i ≤ k → CompiledRightUniversalTestRelation {W = W}
      (right-universal-body-imprecision {W = W} p)
      Aᴾ Bᴵ i Γ Vᴾ Vᴵ)
  → CompiledRightUniversalBodyRelation
      {W = W} {Bᴾ = Aᴾ} {Bᴵ = Bᴵ} q k Γ Vᴾ Vᴵ
right-universal-value-phase-from-body =
  Proof.right-universal-value-phase-from-body

right-universal-value-compatible-from-body : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {p : Aᴾ CTI.⊑ᵂ⟨
      CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ⟩ Bᴵ}
    {Γ′ : CTI.CtxImp
      (CTI.liftWorldLeft I.X⊑★ (forgetWorld W))}
    {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term Δᴵ}
  → (kit : RightUniversalFamilyKit)
  → (nonvar : NonVar Aᴾ)
  → (occurs : Fin.zero ∈ᵗ Aᴾ)
  → (liftΓ : CTI.LiftCtxᴸ I.X⊑★ Γ Γ′)
  → (vVᴾ : Value Vᴾ)
  → (vVᴵ : Value Vᴵ)
  → ⟨ Δᴵ , CTI.targetStoreʷ (forgetWorld W) ,
        CTI.tgtCtxʷ Γ ⟩ ⊢ Vᴵ ⦂ Bᴵ
  → CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ∣ Γ′
      ⊢² Vᴾ ⊑ Vᴵ ∶ p
  → (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
  → (∀ i → i ≤ k → CompiledRightUniversalTestRelation {W = W}
      (right-universal-body-imprecision {W = W} p)
      Aᴾ Bᴵ i Γ Vᴾ Vᴵ)
  → CompiledTermRelation {W = W} q k Γ (Λ Vᴾ) Vᴵ
right-universal-value-compatible-from-body =
  Proof.right-universal-value-compatible-from-body

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
