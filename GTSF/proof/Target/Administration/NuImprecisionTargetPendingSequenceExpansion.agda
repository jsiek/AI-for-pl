module
  proof.Target.Administration.NuImprecisionTargetPendingSequenceExpansion
  where

-- File Charter:
--   * Expands one sequence-headed hereditary target-administration plan into
--     its two evidence-preserving component plans.
--   * Uses the exact replacement, cast-shape, and composition evidence stored
--     in those component plans instead of reconstructing a midpoint.
--   * Contains no recursive worker, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import Coercions using
  (Coercion; ModeEnv; _∣_∣_⊢_∶_=⇒_)
open import Data.List using (List; _∷_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import Types using (Ty; TyCtx)
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationPlanDef
  using (TargetAdministrationPlan)
open import
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using (TargetAdministrationSpine; pending-cons)


TargetAdministrationSequenceSpineExpansionᵀ : Set
TargetAdministrationSequenceSpineExpansionᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {A B C D E : Ty} {μ : ModeEnv}
    {s t : Coercion} {cs : List Coercion}
    {s⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ s ∶ B =⇒ C}
    {t⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ t ∶ C =⇒ D}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ}
    {u : Φ ∣ Δᴸ ⊢ A ⊑ E ⊣ Δᴿ} →
  TargetAdministrationPlan ρ A s⊢ p r →
  TargetAdministrationPlan ρ A t⊢ r q →
  TargetAdministrationSpine ρ A q u cs →
  TargetAdministrationSpine ρ A p u (s ∷ t ∷ cs)


target-administration-sequence-spine-expansionᵀ :
  TargetAdministrationSequenceSpineExpansionᵀ
target-administration-sequence-spine-expansionᵀ
    s-plan t-plan tail =
  pending-cons s-plan (pending-cons t-plan tail)
