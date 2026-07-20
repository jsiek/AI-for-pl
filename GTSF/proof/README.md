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

The pilot also exposed the next checking-time boundary.  Both dependency
contracts currently import the large `NuImprecisionSimulationCore` module just
to name `WeakOneStepIndexedOutcome` and `LeftCatchupIndexedResult`.  Extracting
those result records and their prerequisite definitions into a stable,
definition-only module is the next modularization experiment.
