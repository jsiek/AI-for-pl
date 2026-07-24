module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetFusedSourceOnlyUniversalFactorDef
  where

-- File Charter:
--   * States the type-level source-only factor retained by a fused target
--     instantiation when its renamed final target type is universal.
--   * Keeps the arbitrary final precision proof while exposing the separately
--     computed canonical index and its renamed source-only body.
--   * Contains no term relation, implementation, result/view/outcome type,
--     postulate, hole, permissive option, termination bypass, or broad DGG
--     import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (refl; subst; sym; trans)

open import Imprecision using
  ( ImpCtx
  ; NonVar
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ; ⇑ᴿᵢ
  ; renameNonVar
  )
open import ImprecisionWf using
  (ImpAssm; _∣_⊢_⊑_⊣_; ν)
open import Types using
  ( Renameᵗ
  ; Ty
  ; TyCtx
  ; extᵗ
  ; occurs
  ; renameᵗ
  ; `∀
  ; ⇑ᵗ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  (⊑-target-under-leftᵢ)
open import proof.Core.Properties.TypeProperties using
  (TyRenameWf; TyRenameWf-ext; occurs-zero-rename-ext)
open import
  proof.EndpointMLB.Core.MaximalLowerBoundsWf
  using
  ( rename-assm²ᵢ
  ; rename-assm²-⇑ᴸᵢ
  ; ⊑-rename-at²ᵢ
  ; ⊑-target-lift-rightᵢ
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)


WorldCoherentRightTargetFusedSourceOnlyUniversalFactorᵀ : Set
WorldCoherentRightTargetFusedSourceOnlyUniversalFactorᵀ =
  ∀ {Φ₀ Φ : ImpCtx} {Θᴸ Θᴿ Δᴸ Δᴿ : TyCtx}
    {τ σ : Renameᵗ} {A B C D : Ty}
    {{safe : NonVar D}}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ₀)
      ∣ suc Θᴸ ⊢ D ⊑ B ⊣ Θᴿ}
    {occ : occurs zero D ≡ true}
    (assm : ∀ {a : ImpAssm} → a ∈ ⇑ᴿᵢ Φ₀ →
      rename-assm²ᵢ τ σ a ∈ Φ)
    (hτ : TyRenameWf Θᴸ Δᴸ τ)
    (hσ : TyRenameWf (suc Θᴿ) Δᴿ σ)
    (source-type-eq : renameᵗ τ (`∀ D) ≡ A)
    (target-type-eq : renameᵗ σ (⇑ᵗ B) ≡ `∀ C)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ `∀ C ⊣ Δᴿ) →
  AssumptionMembershipUnique Φ →
  Σ[ E ∈ Ty ]
    (B ≡ `∀ E)
    ×
    Σ[ r ∈
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ renameᵗ (extᵗ τ) D ⊑ `∀ C ⊣ Δᴿ ]
      (r ≡
        ⊑-rename-at²ᵢ
          (rename-assm²-⇑ᴸᵢ assm)
          (TyRenameWf-ext hτ)
          hσ
          refl
          (sym target-type-eq)
          (⊑-target-under-leftᵢ q))
      ×
      (p ≡
        ⊑-rename-at²ᵢ assm hτ hσ
          (sym source-type-eq)
          (sym target-type-eq)
          (⊑-target-lift-rightᵢ (ν safe occ q)))
      ×
      (⊑-rename-at²ᵢ assm hτ hσ
          (sym source-type-eq)
          (sym target-type-eq)
          (⊑-target-lift-rightᵢ (ν safe occ q))
        ≡
        subst
          (λ S → Φ ∣ Δᴸ ⊢ S ⊑ `∀ C ⊣ Δᴿ)
          source-type-eq
          (ν
            (renameNonVar (extᵗ τ) safe)
            (trans (occurs-zero-rename-ext τ D) occ)
            r))
