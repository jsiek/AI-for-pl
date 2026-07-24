module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetFusedPairedUniversalFactorDef
  where

-- File Charter:
--   * States the paired universal-head factor retained by a fused target
--     instantiation from a generic origin universal imprecision index.
--   * Exposes the origin body and equates the ambient paired final index with
--     the canonical renamed target lift of the origin.
--   * Contains no term relation, implementation, result/view/outcome type,
--     postulate, hole, permissive option, termination bypass, or broad DGG
--     import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Imprecision using
  (ImpCtx; _ˣ⊑ˣ_; ⇑ᵢ; ⇑ᴿᵢ)
open import ImprecisionWf using
  (ImpAssm; _∣_⊢_⊑_⊣_; ∀ⁱ_)
open import Types using
  (Renameᵗ; Ty; TyCtx; renameᵗ; `∀; ⇑ᵗ)
open import proof.Core.Properties.TypeProperties using (TyRenameWf)
open import
  proof.EndpointMLB.Core.MaximalLowerBoundsWf
  using (rename-assm²ᵢ; ⊑-rename-at²ᵢ; ⊑-target-lift-rightᵢ)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)


WorldCoherentRightTargetFusedPairedUniversalFactorᵀ : Set
WorldCoherentRightTargetFusedPairedUniversalFactorᵀ =
  ∀ {Φ₀ Φ : ImpCtx} {Θᴸ Θᴿ Δᴸ Δᴿ : TyCtx}
    {τ σ : Renameᵗ} {A B C D : Ty}
    (f : Φ₀ ∣ Θᴸ ⊢ `∀ D ⊑ B ⊣ Θᴿ)
    (assm : ∀ {a : ImpAssm} → a ∈ ⇑ᴿᵢ Φ₀ →
      rename-assm²ᵢ τ σ a ∈ Φ)
    (hτ : TyRenameWf Θᴸ Δᴸ τ)
    (hσ : TyRenameWf (suc Θᴿ) Δᴿ σ)
    (source-type-eq : renameᵗ τ (`∀ D) ≡ `∀ A)
    (target-type-eq : renameᵗ σ (⇑ᵗ B) ≡ `∀ C)
    (p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ C ⊣ suc Δᴿ) →
  AssumptionMembershipUnique Φ →
  Σ[ E ∈ Ty ]
    Σ[ B-eq ∈ B ≡ `∀ E ]
    Σ[ g ∈
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
        ∣ suc Θᴸ ⊢ D ⊑ E ⊣ suc Θᴿ ]
      (subst
          (λ T → Φ₀ ∣ Θᴸ ⊢ `∀ D ⊑ T ⊣ Θᴿ)
          B-eq
          f
        ≡ ∀ⁱ g)
      ×
      (∀ⁱ p ≡
        ⊑-rename-at²ᵢ assm hτ hσ
          (sym source-type-eq)
          (sym target-type-eq)
          (⊑-target-lift-rightᵢ f))
