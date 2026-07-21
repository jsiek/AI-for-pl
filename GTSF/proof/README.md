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

Strict checking is also a contract audit.  Check each `Def` before writing its
implementation and check each higher-order `Proof` before any canonical
dependency is supplied.  If a proposed contract is false or too broad, record
the strict counterexample and repair the `Def`; never hide the mismatch behind
an unsolved meta in a downstream assembly.  The initial source-seal
cancellation contract was rejected this way: a source-only name may also occur
in a matched row unless source-name role exclusivity is carried explicitly.

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

The remaining hole-free down/up transport block is split between
`NuImprecisionCatchupQuotientSupport` and the focused
`NuImprecisionQuotientWideningTransport`.  The former owns paired double-cast
framing, runtime recovery, narrowing transport, ordinary/generated down
transport, and final silent framing; the latter owns transport of one quotient
widening pair.  Its lower-level store-change cast transport lives in
`NuWideningTransport`, and `modeRename-id-only` lives with `ModeRename` in
`CoercionProperties`.  This keeps the small paired-widening leaf out of the
simulation-core dependency cone.  Keep the two
ordinary/generated down-up drivers out of that support module: their
quotient-`inst` residual is the semantic hole represented by
`WorldCoherentQuotientInstCatchupᵀ`, not mechanical transport support.

World-coherent silent resumption is defined separately in
`NuImprecisionWorldCoherentCatchupComposition`.  Its final coherence witness
comes from the resumed catch-up result, whose final store is also the composed
result store.  The same result package carries final left `StoreWf`, which the
composition theorem preserves definitionally.  This makes ownership of both
semantic invariants explicit and avoids any attempt to infer them from generic
result transport fields.

Target-only prefix frames have a parallel strict wrapper layer in
`NuImprecisionWorldCoherentCatchupPrefixFrames`.  It pattern matches the raw
catch-up package before applying a frame, so Agda can see that the result world
and left store are unchanged.  The structural dispatcher imports these small
wrappers instead of repeating dependent transports for coherence and
well-formedness in each target-cast case.

## Invariant layers above generic results

Keep semantic induction invariants above
`NuImprecisionSimulationResultDef` when the generic result algebra does not
itself justify them.  The world/store-name coherence work follows this shape:

- `NuImprecisionWorldCoherenceDef` defines the invariant;
- `NuImprecisionWorldCoherenceProof` proves structural preservation;
- `NuImprecisionWorldCoherenceLemma` assembles concrete reachable-world
  operations;
- `NuImprecisionContextExclusivityDef` separately rules out assigning one
  source name both source-only and matched roles;
- `NuImprecisionContextExclusivityProof` preserves that invariant through all
  canonical allocation-context transformations;
- `NuImprecisionWorldCoherentResultDef` adds the invariant only to continuing
  result branches, together with final source-name exclusivity and final
  left-store well-formedness on catch-up results;
  and
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
ambient world that owns the final result.  It also consumes initial left
`StoreWf` and `SourceNameExclusive Φ`; every coherent catch-up result exposes
the transported final left `StoreWf` and final context exclusivity.  Coherence
is not generally downward-closed through an arbitrary `StoreImpPrefix`, and
active source unseal needs both final-store uniqueness and exclusion of a
matched row for a source-only name, so none of these invariants can safely be
attached after running the ordinary catch-up theorem.

`NuImprecisionWorldCoherentValueCatchupProof` already proves the public
catch-up contract from this prefix contract using `prefix-reflⁱ`.  The future
prefix implementation should take its unfinished allocation and quotient
leaves as higher-order contracts.  It must not import
`NuImprecisionCatchupScratch` merely to reuse its partial dispatcher.

The strict structural prefix proof has exactly two direct semantic
dependencies: `WorldCoherentSourceRuntimeCatchupᵀ` and
`WorldCoherentQuotientFinalCatchupᵀ`.  The latter means "finish this complete
terminal down/up quotient node" and deliberately owns classification of the
source endpoint.  The narrower
`WorldCoherentQuotientInstCatchupᵀ` remains a leaf contract used while proving
that final quotient capability; it is not strong enough to let the dispatcher
attach coherence to an arbitrary classifier result.  This distinction was
found by strict-checking the complete prefix skeleton, before any unfinished
leaf was assembled.

The structural bridge is
`WorldCoherentQuotientClassificationᵀ`.  It classifies a terminal quotient
node as either a complete coherent catch-up or the unique outer-`inst`
residual, packaging `Value (V ⟨ d ⟩)` and `No• (V ⟨ d ⟩)` evidence
for the inner down-cast value that is ready to fire the outer `inst`.  The
strict `NuImprecisionWorldCoherentQuotientFinalCatchupProof` then needs only
this classifier and `WorldCoherentQuotientInstCatchupᵀ`; source-runtime
handlers are not a dependency of quotient-final assembly.  Keep the
classifier implementation separate so ordinary store-neutral quotient leaves
retain coherence and left `StoreWf` instead of erasing them behind a generic
`LeftCatchupIndexedResult`.

`WorldCoherentQuotientInstCatchupᵀ` is an independent semantic capability,
not a consequence of `WorldCoherentSourceRuntimeCatchupᵀ`.  Source-runtime
handlers start from an ordinary relation, whereas the quotient-`inst` leaf
must handle the permutation directly.  Generic quotient-to-ordinary
alignment is false: `NuImprecisionQuotientToOrdinaryCounterexample` gives an
empty-context adjacent-`∀` swap that is quotient-related but not ordinarily
related.  The missing hard boundary is therefore compositional catch-up over
the `≈∀` derivation, using the specialized swap/allocation machinery in its
swap case.

`NuImprecisionWorldCoherentQuotientRepresentativeInstCatchupDef` now exposes
the two arbitrary `≈∀` derivations and their ordinary representative relation
without claiming an ordinary relation between physical quotient endpoints.
The canonical `NuImprecisionWorldCoherentQuotientInstCatchupProof` strictly
reduces the existing contract to that direct capability.  Its canonical
`Lemma` must remain absent until a representative-level `Proof` handles
`sym`, `trans`, congruence, and the primitive adjacent swap compositionally.

Keep source bullet, allocation, cast, and conversion handlers together in
`NuImprecisionWorldCoherentSourceRuntimeCatchup*`; source `inst` catch-up and
`ν ★` allocation are mutually dependent and should not be split into fake leaf
modules.  Put the complete quotient join in
`NuImprecisionWorldCoherentQuotientFinalCatchup*`, and the shared ordinary/gen
quotient-`inst` final-state leaf in
`NuImprecisionWorldCoherentQuotientInstCatchup*`.  The checked prefix `Proof`
handles all target frames and ordinary terminal cases structurally and takes
only the two complete contracts as higher-order arguments.

The source-runtime record is an assembly boundary, not permission to assume
its fields recursively.  Its current proof decomposition is:

- `source-conceal` is complete in
  `NuImprecisionWorldCoherentSourceConcealCatchup`: conceal coercions are inert
  except for identity, which takes one administrative step;
- `source-bullet`, `source-ν`, `source-νcast`, and the widening-`inst`
  case form one genuine recursive allocation SCC;
- `source-reveal` needs exact source-side seal cancellation for active
  `unseal`; the first cancellation contract was strictly refuted because it
  omitted source-only-versus-matched name exclusivity.  Its replacement uses
  a separate imprecision-context invariant rather than being folded into
  `WorldCoherent`, because empty-store coherence is valid for
  arbitrary contexts.  The repaired `Def`/`Proof`/`Lemma` triples for
  `NuImprecisionSourceSealCancellation` and
  `NuImprecisionWorldCoherentSourceUnsealCatchup` are strict and complete.
  The source-reveal `Def`/`Proof`/`Lemma` triple is also complete: its
  higher-order proof dispatches all reveal forms and delegates only active
  unseal to the canonical unseal lemma;
- active narrowing/widening need quotient-aware source tag/untag
  classification in addition to the existing inert and blame frames.  The
  first source-tag proof attempt exposed an `up⊑upᵀ` premise that retains only
  a quotiented inner relation.  The contract is nevertheless sound because its
  ground/value hypotheses support the restricted
  `GroundValueQuotientEliminationᵀ` theorem; no global dequotienting is used.
  The raw two-seal obstruction in
  `NuImprecisionSourceCastSequenceMidpointCounterexample` does not satisfy
  `SealModeStore★`: `seal-enabled-store-entry-star` proves from store
  uniqueness that every seal-enabled source entry has payload `★`.  Thus the
  strict `NuImprecisionSourceCastSequenceMidpoint` triple derives the positive,
  restricted midpoint from the full prefix, seal-mode, and store-uniqueness
  hypotheses; and
- `source-paired-cast` needs prefix and accumulated-change transport for
  `PairedCast` evidence.  Its contract retains the target cast's `Inert`
  witness because every structural caller already has it.  The strict
  `NuImprecisionWorldCoherentSourcePairedCastCatchupProof` now composes two
  explicit dependencies: accumulated left-silent paired-cast transport and
  exact-final-world paired-cast catch-up.  Rebuilding final `StoreCorresponds`
  after arbitrary source changes remains the hard transport step.  Full
  transport is itself assembled from separate paired-widening and
  paired-conversion capabilities, so the store-neutral widening proof can run
  independently on Ginger.  Exact-final-world catch-up is likewise assembled
  from separate paired-conversion and paired-widening semantic contracts,
  keeping the active `inst` allocation case visible instead of assuming the
  source-runtime record recursively.  Exact-final paired conversion is now
  complete.  Accumulated paired-conversion transport reduces to an explicit
  `LeftSilentStoreCorrespondsTransportᵀ` boundary because linked relational
  store entries appear in neither projected store and cannot be recovered from
  final `WorldCoherent` alone.  The smallest implementation invariant is a
  `WeakOneStepStoreLineage` package: a relational-store embedding from the
  initial store into an intermediate renamed store, followed by a
  `StoreImpPrefix` into the result store.  Add this only to coherent catch-up
  results, where it is universally needed; identity/frame cases preserve it,
  composition composes it, and allocation constructors already expose the
  required lift embeddings.

The independent conceal, active-unseal, and source-reveal leaves are now
complete.  Next use completed source tag cancellation and the source
cast-sequence midpoint in the non-`inst`
narrow/widen cases, and prove the remaining paired-cast dependencies.  Only
then implement
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
