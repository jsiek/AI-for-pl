module
  proof.WorldCoherent.Quotient.InstPath.NuImprecisionWorldCoherentQuotientRepresentativeInstPathSourceStepCatchupProof
  where

-- File Charter:
--   * Reduces the full leading-source-step contract to its typed `inst` path
--     view.
--   * Eliminates both impossible arrow-context steps before invoking the
--     semantic worker.
--   * Contains no operational branch implementation or permissive option.

open import proof.Quotient.NuImprecisionQuotientInstPathProperties using
  (source-inst-step-view)
open import
  proof.WorldCoherent.Quotient.InstPath.NuImprecisionWorldCoherentQuotientRepresentativeInstPathSourceStepCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathSourceStepCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPath.NuImprecisionWorldCoherentQuotientRepresentativeInstPathSourceStepViewCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathSourceStepViewCatchupᵀ)


world-coherent-quotient-representative-inst-path-source-step-catchup-proofᵀ :
  WorldCoherentQuotientRepresentativeInstPathSourceStepViewCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathSourceStepCatchupᵀ
world-coherent-quotient-representative-inst-path-source-step-catchup-proofᵀ
    view
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {V = V} {V′ = V′}
    {B = B} {D = D} {E = E} {D′ = D′} {C = C} {C′ = C′}
    {A = A} {A′ = A′} {d = d} {d′ = d′} {s = s} {u′ = u′}
    {ρ = ρ} {D≈C = D≈C} {C⊑C′ = C⊑C′} {C′≈D′ = C′≈D′}
    {pA = pA} {step = step} {rest = rest} {targetPath = targetPath}
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down widening =
  view
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {V = V} {V′ = V′}
    {B = B} {D = D} {E = E} {D′ = D′} {C = C} {C′ = C′}
    {A = A} {A′ = A′} {d = d} {d′ = d′} {s = s} {u′ = u′}
    {ρ = ρ} {D≈C = D≈C} {C⊑C′ = C⊑C′} {C′≈D′ = C′≈D′}
    {pA = pA} {step = step} {rest = rest} {targetPath = targetPath}
    (source-inst-step-view step widening)
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down widening
