module
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentOutcomeTransportProof
  where

-- File Charter:
--   * Transports a world-coherent indexed one-step outcome across explicit
--     equalities of both endpoint types and the proof-relevant index.
--   * Keeps the full transported judgment visible at the use site.
--   * Contains no simulation implementation, postulate, hole, permissive
--     option, compatibility alias, or specialized natural-number case.

open import Agda.Builtin.Equality using (refl)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using (StoreChange)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import NuTerms using (Term)
open import Types using
  ( Ty
  ; TyCtx
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)


world-coherent-indexed-outcome-transport-typesᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M N′ : Term} {A B C D : Ty}
    {χ : StoreChange}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ} →
  (source-eq : A ≡ C) →
  (target-eq : B ≡ D) →
  subst
    (λ T → Φ ∣ Δᴸ ⊢ C ⊑ T ⊣ Δᴿ)
    target-eq
    (subst
      (λ S → Φ ∣ Δᴸ ⊢ S ⊑ B ⊣ Δᴿ)
      source-eq p)
    ≡ q →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {A = C} {B = D}
    {χ = χ} {ρ = ρ} q →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {A = A} {B = B}
    {χ = χ} {ρ = ρ} p
world-coherent-indexed-outcome-transport-typesᵀ
    refl refl refl outcome =
  outcome
