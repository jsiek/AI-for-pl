# Paired universal-cast application boundary

The strict statement is
`PairedUniversalCastApplicationBoundaryᵀ` in
`PairedUniversalCastApplicationBoundaryProbe.agda`. It isolates the first
open nonstructural `β-∀` branch of `SimPairedAllValuesProof.agda` without
changing CTI or assuming arbitrary transport.

## The obstructed square

Let the inner value relation use

`I.∀⊑ non-var occurs body : (∀X. D) ⊑ (∀X. D′)`.

Here `body` states

`I.instᵐ (marksᶜ γ) ⊢ ηᴸD ⊑ ⇑ᵗ (∀X. ηᴿD′)`.

It does not state the structural body comparison needed to open both
universals. Consequently, mirroring the source `β-∀` step on the target
does not permit direct reconstruction with the paired type-application CTI
rule.

Diagram:

    (M ⟨ ∀ᶜ c ⟩) ⦂∀ C [ A ]    ⊑    (M′ ⟨ ∀ᶜ c′ ⟩) ⦂∀ C′ [ A′ ]
              │ β-∀                              │ β-∀
              ▼                                  ▼
    (M ⦂∀ D [ A ]) ⟨ c [ A ]ᶜ ⟩       (M′ ⦂∀ D′ [ A′ ]) ⟨ c′ [ A′ ]ᶜ ⟩
              │ 0 steps                          │ target catchup
              │                                  ▼
              │                      W′ ⟨ χsᴿ ▶ᶜ (c′ [ A′ ]ᶜ) ⟩
              ▼                                  │
    (M ⦂∀ D [ A ]) ⟨ c [ A ]ᶜ ⟩       ⊑       W′ ⟨ χsᴿ ▶ᶜ (c′ [ A′ ]ᶜ) ⟩

The source checkpoint is fixed because the simulated source change is
`keep`. The target continuation begins at `M′ ⦂∀ D′ [ A′ ]`; its trace is
lifted through the distributed result cast. The total evolution therefore
has source history `keep ∷ []` and target history `keep ∷ χsᴿ`.

## Why existing interfaces do not close it

`SimSourceLambdaApplicationᵀ` advances the source application too. Its
conclusion has source change `bind A` and source term
`V ↑ 〖 zero , ⇑ᵗ A ↑ D 〗`. Neither matches this checkpoint.

`TransportTermImprecisionᵀ` cannot help. Transport requires a CTI derivation
before evolution, while this branch is missing the post-`β-∀` derivation
itself.

`MorePreciseTargetInstantiationValueCatchupᵀ` has the right asymmetry but a
different redex. It reduces a target instantiation cast while preserving a
source value; this boundary reduces a target type application while
preserving a source type-application checkpoint under a result cast.

## Dependency and promotion audit

The strict boundary directly matches the hole at the first nonstructural
universal inversion in `SimPairedAllValuesProof.agda`. It does not directly
match the later target-only-cast or source-only-cast variants: those have a
different outer result-cast shape.

For that reason the statement remains a notes-only probe rather than a
canonical `Def` module. Promotion should wait until the target-continuation
induction determines the smallest common operation for all three variants.
That induction may use the contextual forward worker internally, but its
public conclusion must remain the direct target trace, evolution, and final
CTI shown here; it must not expose a generic whole-simulation wrapper.
