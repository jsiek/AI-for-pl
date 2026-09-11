# Paired universal-cast application boundary

The strict statements are in
`PairedUniversalCastApplicationBoundaryProbe.agda`. They isolate the three
open nonstructural `β-∀` branches of `SimPairedAllValuesProof.agda` without
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

### Boundary 1. Both values have outer universal casts

`PairedUniversalCastApplicationBoundaryᵀ` matches the first hole. The inner
relation is `M ⊑ M′`. Both source and target distribute a cast, so the final
terms retain both result casts. Its histories are
`keep ∷ []` and `keep ∷ χsᴿ`.

### Boundary 2. The related source head is already a cast

`NestedSourceUniversalCastApplicationBoundaryᵀ` matches the second
nonstructural hole. Its relation is `V ⟨ ∀ᶜ c ⟩ ⊑ M′`, while its source
checkpoint contains `V`, not the whole related source head:

`(V ⦂∀ D [ A ]) ⟨ c [ A ]ᶜ ⟩`.

The target still distributes a universal cast. Its histories are again
`keep ∷ []` and `keep ∷ χsᴿ`.

### Boundary 3. Only the source has an outer universal cast

`SourceUniversalCastApplicationBoundaryᵀ` matches the third hole. The
target begins directly at `V′ ⦂∀ C′ [ A′ ]`, and no target result cast is
available in the final CTI. Its histories are `keep ∷ []` and `χsᴿ`; there
is no leading target `keep`.

### No direct common public interface

A single direct statement cannot abstract these differences without hiding
semantic syntax. An optional target result cast would be a classifier. An
arbitrary source checkpoint and arbitrary target closing context would merely
package a whole simulation result.

Removing the casts before invoking a common induction is not sound from the
available premises. The paired boundaries would require an intermediate edge
such as `C [ A ]ᵗ ⊑ D′ [ A′ ]ᵗ` or
`D [ A ]ᵗ ⊑ D′ [ A′ ]ᵗ`. Neither follows from consistency of `c` and `c′`
together with the final outer relation. The casts therefore have to remain in
the conclusion, as they do in the strict probes.

The smallest genuine common induction is internal contextual target
continuation: keep the complete root CTI path, reduce the selected target type
application, and return the final whole-root CTI. That is the operation the
contextual simulation redesign is already intended to perform. Exposing it
again here would create a parallel whole-simulation wrapper.

The three statements therefore remain notes-only probes rather than a new
canonical `Def` module. The live proof should consume the contextual worker
and reconstruct each explicit target chain at its own branch boundary.
