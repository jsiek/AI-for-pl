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

Treat avoiding `--allow-unsolved-metas` as an architectural objective of the
split.  New top-level skeleton work should represent missing proofs as explicit
higher-order contract parameters, not as holes.  A partial legacy dispatcher
may remain permissive while it is being decomposed, but no new `Def`, `Proof`,
or leaf module should need that option merely to expose the rest of the proof
shape.

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

Canonical store lifting follows the same closed-world rule.
`NuImprecisionStoreLift` is the sole definition site for
`lift-left-store-result` and `lift-right-store-result`.  Allocation proofs and
other direct consumers import it explicitly; the simulation core does not
re-export those names.  This keeps coherent catch-up allocation leaves outside
the large core's invalidation cone.

Structural prefix operations live beside it in
`NuImprecisionStorePrefix`: projected left/right store inclusion and prefix
transitivity are defined there and imported directly by catch-up consumers.
Do not move these names back into, or re-export them through, the simulation
core; doing so would reconnect stable catch-up structure to the largest proof
implementation file.

The first strict catch-up implementation island lives in
`NuImprecisionCatchupPrefixSupport`.  It owns silent-result composition, the
five target-cast prefix frames, and the terminal source value/blame builders.
These nine definitions were moved out of the permissive scratch dispatcher;
new coherent catch-up proofs should import this module and must not recover
them by importing `NuImprecisionCatchupScratch`.

The remaining hole-free down/up transport block should likewise move into
`NuImprecisionCatchupQuotientSupport` before the strict prefix proof is
written.  Keep the two ordinary/generated down-up drivers out of that support
module: their quotient-`inst` residual is the semantic hole represented by
`WorldCoherentQuotientInstCatchupᵀ`, not mechanical transport support.

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

World-coherent value catch-up needs one additional genuine induction contract.
`NuImprecisionWorldCoherentValueCatchupPrefixDef` permits the current relation
to be exposed in a smaller world `ρ₀`, but carries `WorldCoherent ρ⁺` for the
ambient world that owns the final result.  Coherence is not generally
downward-closed through an arbitrary `StoreImpPrefix`, so it cannot be attached
after running the ordinary catch-up theorem.

`NuImprecisionWorldCoherentValueCatchupProof` already proves the public
catch-up contract from this prefix contract using `prefix-reflⁱ`.  The future
prefix implementation should take its unfinished allocation and quotient
leaves as higher-order contracts.  It must not import
`NuImprecisionCatchupScratch` merely to reuse its partial dispatcher.

The structural prefix proof has two major semantic dependencies.  Keep the
source bullet, allocation, cast, and conversion handlers together in
`NuImprecisionWorldCoherentSourceRuntimeCatchup*`; source `inst` catch-up and
`ν ★` allocation are mutually dependent and should not be split into fake leaf
modules.  Put the shared ordinary/gen quotient-`inst` final-state theorem in
`NuImprecisionWorldCoherentQuotientInstCatchup*`.  The prefix `Proof` should
take those two whole contracts as higher-order arguments, with all target
frames and ordinary terminal cases handled structurally.

The source-runtime record is an assembly boundary, not permission to assume
its fields recursively.  Its current proof decomposition is:

- `source-conceal` is the first independent leaf: conceal coercions are inert
  except for identity, which takes one administrative step;
- `source-bullet`, `source-ν`, `source-νcast`, and the widening-`inst`
  case form one genuine recursive allocation SCC;
- `source-reveal` needs exact source-side seal cancellation for active
  `unseal`;
- active narrowing/widening need source tag/untag classification in addition
  to the existing inert and blame frames; and
- `source-paired-cast` needs prefix and accumulated-change transport for
  `PairedCast` evidence.

Prove the independent conceal leaf first, then freeze and prove source seal
cancellation and tag cancellation as explicit contracts.  Next prove reveal,
non-`inst` narrow/widen cases, and paired-cast transport.  Only then implement
the allocation SCC as a visibly structural mutual proof (or with an explicit
administrative measure) and assemble the eight-field record.  Do not make the
record itself a higher-order input to its own `Proof`; that would encode the
missing recursion circularly while still appearing strict to Agda.

The target reveal-unseal root is the next higher-order boundary:

- `NuImprecisionWorldCoherentTargetRevealRootDef` states the complete root
  contract;
- `NuImprecisionWorldCoherentTargetRevealRootProof` proves it from the whole
  world-coherent value-catch-up and target-seal-cancellation contracts; and
- `NuImprecisionWorldCoherentTargetRevealRootLemma` should be created only
  after the live coherent value-catch-up contract has a strict inhabitant.

This intentionally leaves the `Lemma` file absent while its canonical catch-up
dependency is unfinished.  The checked `Proof` already establishes that the
dependency statements compose; adding a permissive assembly would weaken the
strict boundary without supplying new evidence.

Target coercion sequencing has a separate local-evidence boundary.
`NuImprecisionTargetCastSequenceMidpointDef` defines an indexed family for the
midpoint witness attached to one quotiented target-cast node.  Do not replace
it with a global `RightCastCtxCompatible` assumption: matched `gen` and `inst`
worlds need not satisfy that condition.  Root helpers should consume the local
witness explicitly, while the quotient constructor is responsible for
retaining it when the node is built.

`NuImprecisionOneStepTargetCastSequenceRoots` is the corresponding strict leaf
proof: given that local midpoint, it constructs both ordinary narrowing and
widening β-sequence outcomes without importing the dispatcher or simulation
core.  This separates the remaining constructor-plumbing change from the
already-checked operational root argument.
