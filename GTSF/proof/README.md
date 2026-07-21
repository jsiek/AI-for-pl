# GTSF proof-module organization

Use the following three-file convention for major proof boundaries.  The
common stem should be the mathematical role of the result, so all three files
sort together.

| File | Responsibility | May import implementations? |
|---|---|---|
| `<Stem>Def.agda` | Defines the complete theorem contract as a `Set` or `Set₁` | No |
| `<Stem>Proof.agda` | Proves the contract from whole dependency contracts | No |
| `<Stem>Lemma.agda` | Supplies the canonical completed dependency lemmas | Yes |

For example, the backward target-value boundary is organized as:

- `NuDGGTerminalBackwardValueDef.agda`;
- `NuDGGTerminalBackwardValueProof.agda`; and
- `NuDGGTerminalBackwardValueLemma.agda`.

The `Def` module should import only the language definitions and judgment or
result types needed to state the theorem.  The `Proof` module should take
major dependencies as ordinary higher-order arguments.  Prefer a
parameterized module only when several exported proofs share the same
dependency telescope.  The `Lemma` module should be a small application of
the generic proof to canonical dependency lemmas.

Apply this split at architectural joins, not to every helper.  Keep genuinely
mutual proofs in one strongly connected proof module and give their combined
result one contract.

## Strictness policy

`Def` and `Proof` modules must never enable `--allow-unsolved-metas` or
`--allow-incomplete-matches`.  A `Lemma` module enters the strict proof surface
only after every dependency it supplies is itself strict.  Until then, use the
`Def` contracts and higher-order `Proof` to check architectural fit; do not put
a hole in the generic proof merely because a dependency implementation is
unfinished.

This is also a reason for the split, not merely a promotion rule.  An
unfinished canonical dependency is confined to its implementation and
`Lemma` assembly, while the theorem contract and higher-order proof remain
independently strict.  Completed architectural work therefore does not need a
temporary file-level `--allow-unsolved-metas` just because a supplied leaf is
still under construction.

A command-line `--no-allow-unsolved-metas` is not sufficient when a source
module locally enables `--allow-unsolved-metas`.  Completion therefore
requires removing the local option and checking the owned module again, as
well as confirming that no holes remain.

Do not retain `Assembly` or `Integration` compatibility modules after a stem
has been converted.  This is a closed-world repository, so update consumers to
the canonical `Def`/`Proof`/`Lemma` names and remove the superseded files.

## Backward-value pilot benchmark

The representative conversion was measured locally with Agda 2.7.0.1 and
`agda -v0`, using focused module checks rather than `All.agda`.

| Check | Time |
|---|---:|
| Old `Assembly`, proof file invalidated with dependencies warm | 5.89 s |
| New `Proof`, same proof body with dependencies warm | 5.08 s |
| Old `Integration`, live scratch dependency stale | 275.02 s |
| New `Lemma`, live scratch dependency stale | 264.21 s |
| New `Lemma`, dependencies warm | 5.55 s |

The small difference between the two stale-dependency runs is not evidence of
a major speedup.  The demonstrated benefit is invalidation isolation: changes
to dependency implementations do not force `Def` or `Proof` to recheck.

The pilot exposed a second checking-time boundary: both dependency contracts
imported the large `NuImprecisionSimulationCore` module just to name result
types.  That result algebra now lives in the strict 506-line
`NuImprecisionSimulationResultDef` module.  Consumers import moved names there
directly; the core imports it non-publicly, with no compatibility re-export.

The move reduced a focused `NuImprecisionSimulationCore` rebuild to 47.24
seconds and made the two dependency contracts check in 3.16 and 3.39 seconds.
Most importantly, after invalidating the core again,
`NuDGGTerminalBackwardValueProof` still checked in 3.23 seconds without
rebuilding it.  This is the intended invalidation boundary.  The batched
scratch-dispatcher consumer passed in 288.55 seconds; neither
`NuDGGStrictSpine` nor `All.agda` was run for that migration.

Apply the same rule to trivial result constructors.  The canonical
relation-to-keep-step builders live in `NuImprecisionOneStepRelated`, above the
result definitions and below the simulation core.  Root proofs should import
that module directly; importing `NuImprecisionSimulationCore` merely to build
an unchanged related outcome defeats the `Def`/`Proof` invalidation boundary.

## Invariant layers above generic results

Keep semantic induction invariants above
`NuImprecisionSimulationResultDef` when the generic result algebra does not
itself justify them.  The world/store-name coherence work follows this shape:

- `NuImprecisionWorldCoherenceDef` defines the invariant;
- `NuImprecisionWorldCoherenceProof` proves structural preservation;
- `NuImprecisionWorldCoherenceLemma` assembles concrete reachable-world
  operations;
- `NuImprecisionWorldCoherentResultDef` adds the invariant only to continuing
  result branches; and
- the world-coherent one-step and catch-up `Def` modules state the strengthened
  major dependencies.

Do not derive a coherent result from an arbitrary generic result.  Generic
`WeakOneStepResult` deliberately permits an independently chosen result world,
so preservation must be proved where the concrete result store is constructed.
This separation keeps both definition layers strict and avoids importing the
dispatcher into either one.

Terminal target-seal cancellation follows the same file convention:

- `NuImprecisionTargetSealCancellationDef` states the complete exact-world
  contract;
- `NuImprecisionTargetSealCancellationProof` owns the quotient/value inversion;
  and
- `NuImprecisionTargetSealCancellationLemma` exposes the canonical inhabitant
  once the proof is strict.

The terminal `Def` includes world coherence, target-store well-formedness,
physical target-store membership, and both proof-relevant indices.  Keep those
premises visible: hiding them in the target-conversion dispatcher would make it
easy to type-check a leaf that cannot be composed after catch-up changes the
world.  The dispatcher should consume the canonical `Lemma`; neither the `Def`
nor the `Proof` should import the dispatcher or inherit its permissive options.
