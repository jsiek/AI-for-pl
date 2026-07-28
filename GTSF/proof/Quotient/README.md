# Quotient-imprecision migration status

## Authoritative state

**MIGRATION IN PROGRESS — paired-down elimination invariant tested**

This directory is a temporary mixed staging area during the controlled
replacement of `QuotientedTermImprecision`. This file is the authoritative
status marker for every quotient-imprecision prototype and migration module.
Do not infer a module's status from whether it still type-checks or is still
imported.

The migration has not finished. Do not open the migration pull request until
this heading says **MIGRATION FINISHED** and every completion condition below
holds.

## Status meanings

- **canonical**: intended to remain after the migration, although its name or
  location may still be improved.
- **selected migration source**: evidence for the selected smaller relation.
  Promote its contents into canonical live modules, then delete the
  experimental source file.
- **retiring live**: still required by the current live import cone, but based
  on constructors that the selected relation removes. Do not add new clients.
- **obsolete, quarantined**: belongs to a rejected design. Do not import,
  extend, or add it to a check root. Remove its last migration-only imports,
  remove it from the regression surface, and delete it in phase 1.

## Obsolete alternative deleted in phase 1

The compositional quotient alternative and its finite-narrowing-spine
diagnostic were rejected for the live migration. Phase 1 removed their last
selected-example dependency and deleted:

- `NuImprecisionCompositionalQuotientDef.agda`;
- `NuImprecisionCompositionalQuotientExamples.agda`;
- `NuImprecisionSingleNarrowingBoundaryExamples.agda`; and
- `../DGG/Design/NuImprecisionCompositionalQuotientDesign.md`.

`NuImprecisionReductionClosedQuotientExamples.agda` now owns its selected
cast fixtures and imports neutral quotient-boundary support directly. The
focused strict check passed before deletion. The Makefile no longer contains
the obsolete roots. Git history is the only fallback for the discarded
design.

## Selected migration source

The selected grammar and its general support are:

- `NuImprecisionReductionClosedQuotientDef.agda`;
- `NuImprecisionQuotientCompatibilityRename.agda`;
- `NuImprecisionTargetInstantiationCreationDef.agda`; and
- `NuImprecisionEmbeddedTargetInstantiationCreationProperties.agda`.

The selected metatheory sources are:

- `NuImprecisionReductionClosedQuotientTypingExperiment.agda`;
- `NuImprecisionReductionClosedQuotientValueExperiment.agda`;
- `NuImprecisionReductionClosedQuotientTermContextShiftExperiment.agda`;
- `NuImprecisionReductionClosedQuotientSubstitutionExperiment.agda`;
- `NuImprecisionReductionClosedQuotientSingleSubstitutionExperiment.agda`;
- `NuImprecisionReductionClosedWorldEmbeddingExperiment.agda`;
- `NuImprecisionReductionClosedWorldRenameExperiment.agda`;
- `NuImprecisionReductionClosedQuotientIdOnlyCastAudit.agda`; and
- `NuImprecisionReductionClosedQuotientTransientAudit.agda`.

The selected consumer and reduction regressions are:

- `NuImprecisionReductionClosedQuotientExamples.agda`;
- `NuImprecisionCambridge26Example14Experiment.agda`;
- `NuImprecisionTargetInstantiationCreationExamples.agda`;
- `NuImprecisionTargetInstantiationTransportExperiment.agda`;
- `NuImprecisionTargetInstantiationTransportTerminalExperiment.agda`;
- `NuImprecisionTargetInstantiationTransportSpineExperiment.agda`;
- `NuImprecisionTargetInstantiationConsumerMigrationExperiment.agda`;
- `NuImprecisionTargetInstantiationFramedConsumerMigrationExperiment.agda`;
- `NuImprecisionTargetInstantiationSimulationExperiment.agda`.

These modules are migration evidence, not a second public API. New live work
must not create a compatibility layer that lets old and selected term
relations coexist indefinitely. As each result is moved into the live
relation or a canonical proof module, remove its experimental check root and
delete the superseded source.

## Retiring live surface

`../../QuotientedTermImprecision.agda` is the live smaller relation. Phase 3
removed target-only type application, target-only `ν`, target-only casted
`ν`, and the two casted-`ν` shortcuts. Phase 4 has also removed these
constructor families from the live grammar:

- quotient-indexed application;
- fused `down·up⊑down·upᵀ`; and
- the old quotient-boundary presentation superseded by one paired narrowing
  introduction and one compatible closing widening.

The following modules remain live clients or helpers for retired source
names. They may be edited only to migrate or delete those dependencies:

- `NuImprecisionQuotientArrowComponents.agda`;
- `NuImprecisionQuotientFunctionPairedNarrowingApplicationDef.agda`;
- `NuImprecisionQuotientFunctionPairedNarrowingApplicationProof.agda`;
- `NuImprecisionQuotientFunctionPairedNarrowingApplicationLemma.agda`;
- `NuImprecisionQuotientInstPathProperties.agda`;
- `NuImprecisionQuotientInstView.agda`;
- `NuImprecisionQuotientValue.agda`;
- `NuImprecisionQuotientWideningTransport.agda`;
- `NuImprecisionSourceDownApplicationCompatibleOuter.agda`.

`NuImprecisionQuotientToOrdinaryCounterexample.agda` is canonical: it guards
the still-relevant fact that a general quotient edge cannot be converted to
ordinary type imprecision.

The frozen Phase 4 pre-edit source inventory is:

- `down·up⊑down·upᵀ`: 14 Agda files;
- `quotient-id-down-applicationᵖᵀ`: 9 Agda files;
- `quotient-down-applicationᵖᵀ`: 9 Agda files;
- `up⊑upᵀ`: 46 Agda files;
- `down⊑downᵀ`: 27 Agda files; and
- `gen-down⊑gen-downᵀ`: 26 Agda files.

These are direct source-reference counts, not transitive capability counts.
The exact file lists are reproducible from the migration checkpoint with:

    rg -l 'down·up⊑down·upᵀ' -g '*.agda'
    rg -l 'quotient-id-down-applicationᵖᵀ' -g '*.agda'
    rg -l 'quotient-down-applicationᵖᵀ' -g '*.agda'
    rg -l 'up⊑upᵀ' -g '*.agda'
    rg -l 'down⊑downᵀ' -g '*.agda'
    rg -l 'gen-down⊑gen-downᵀ' -g '*.agda'

During the grammar edit, a file leaves this inventory only by migrating to
`paired-downᵀ` or compatible `closeᵀ`, by switching to an up-to-reduction
simulation, or by being deleted with its obsolete helper family. No
compatibility constructor or wrapper may preserve one of these six names.

## Controlled phases

### Phase 0. Control and inventory

- work only on `codex/live-qti-migration`;
- keep this file and
  `../DGG/Design/NuImprecisionDGGProgress.md` as the two authoritative views:
  this file owns module lifecycle, and the ledger owns proof progress;
- make no grammar edits concurrently;
- run only the source import audit for documentation and Makefile changes.

### Phase 1. Isolate the selected design

Completed:

- removed the selected example's imports of the quarantined compositional
  modules;
- removed obsolete design roots from the Makefile;
- strictly checked only the affected selected example root;
- confirmed that no other Agda module imported the obsolete family;
- deleted the quarantined Agda files and design note.

### Phase 2. Replace target-instantiation creation

Completed:

- replaced fused `Λ⊑instβᵀ` with one live `target-instantiationᵀ`
  constructor carrying `EmbeddedTargetInstantiationCreation`;
- exposed the invariant that the source endpoint is headed by `∀`, in
  addition to the already visible source `Λ` and target cast syntax;
- migrated direct, exhaustive, and incomplete consumers in typing, value,
  substitution, world embedding, allocation transport, seal/tag
  cancellation, catch-up, paired-lambda views, continuation handlers, and
  the target-widening post-beta context;
- replaced long positional handler and capability interfaces with the single
  embedded residual and renamed their local “inst-beta” surface to
  “target-instantiation”;
- added only reusable residual projections for source/target typing, value,
  no-bullet, and target `GenSafeShape`;
- deleted the obsolete final-target-atomic helper trilogy after its generic
  replacement passed;
- deleted the two unused universal-fusion-spine Def/Proof/Lemma families
  after source search confirmed that their only importers were within their
  own islands; arbitrary residual embedding now carries the composition they
  attempted to expose;
- removed all Agda references to `Λ⊑instβᵀ` and all imports of the deleted
  helpers;
- passed the focused migrated leaves, the source import/strict-cone audit, and
  `make dgg-check`.

The permissive catch-up scratch clauses were migrated, but a full refresh of
that scratch root was stopped after several silent minutes; it is not a
strict phase gate. The independent paired-lambda frame-closing handler
assembly remains blocked in its pre-existing
`NuImprecisionPairedLambdaTargetClosingGenLeafNuClosingProof` dependency by a
proof-relevant index transport mismatch. Its target-instantiation view,
handler definitions, interpreters, continuation assembly, and capability
definition all pass focused checks.

### Phase 3. Remove asymmetric administrative shortcuts

Completed:

- deleted exactly `⊑αᵀ`, `⊑νᵀ`, `⊑νcastᵀ`, `νcast⊑ᵀ`, and
  `νcast⊑νcastᵀ` from the live grammar;
- removed the first three as uninhabited under the strict index-cycle
  invariant;
- removed the cast-specialized source cases and their transitive allocation,
  frame, catch-up, runtime-sibling, target-bullet, transport, and dispatcher
  capabilities rather than preserving compatibility wrappers;
- migrated the remaining structural folds, typings, substitutions,
  exclusions, embeddings, transports, frame views, and schedulers;
- deleted the permissive catch-up scratch, the left-source target-bullet
  allocation trilogy and commutation proof, the source target-`ν` frame
  trilogy, the source casted-`ν` catch-up families, the obsolete right
  allocation context seed, and the superseded paired-post-beta
  counterexample; and
- passed the focused migrated leaves and the source import/strict-cone audit.

The frozen pre-edit list was the complete set of files that mentioned a
retired constructor directly. It was not the complete transitive consumer
set. During migration, source search followed every helper field and record
capability into allocation, frame, catch-up, and scheduling consumers before
the helper was deleted. No retired live-QTI constructor remains in source.
The obsolete first-draft `../../NuTermImprecision.agda` judgment has now been
deleted at a stable source-outcome checkpoint.

The Phase 3 public-DGG gate reaches two already-existing Phase 4 boundaries
rather than a removed constructor:

- `../WorldCoherent/Source/RuntimeSteps/NuImprecisionWorldCoherentSourceCastFrameStepProof.agda`
  has no principled case for the fused `down·up⊑down·upᵀ` rule; Phase 4
  removes that rule instead of adding another ad hoc handler.
- `../WorldCoherent/Right/OneStep/Roots/NuImprecisionWorldCoherentRightOneStepTargetAllocationRootsProof.agda`
  accepts an arbitrary matched-`ν` step where its implementation handles only
  the allocation root. Phase 4 must tighten or split this contract before its
  focused root can pass.

The retained infrastructure formerly sharing
`../../NuTermImprecision.agda` now lives in
`../Store/Core/NuImprecisionRelationalStoreDef.agda`,
`../NuCore/Relations/NuImprecisionTermContextDef.agda`, and
`../Store/Correspondence/NuImprecisionCrossedStore.agda`; its three general
cast-mode witnesses moved to the existing cast-properties module. A complete
direct-client audit found no consumer of the first-draft relation, so all 647
imports were partitioned atomically and the obsolete file was deleted without
a compatibility re-export.

### Phase 4. Replace the quotient boundary

- promote the single paired-narrowing quotient introduction and compatible
  closing widening (**live grammar and typing projections checked**);
- connect the allocation-aware function-cast simulation up to reduction;
- migrate the two live source-widening instantiation paths in
  `../WorldCoherent/Source/CastCatchup/NuImprecisionWorldCoherentSourceWidenCatchupCasesProof.agda`
  and
  `../WorldCoherent/Source/CastCatchup/NuImprecisionWorldCoherentSourceWidenRuntimeSiblingCatchupProof.agda`
  (**completed checkpoint**);
- tighten or split the matched target-allocation root contract so it states
  the reduction that its proof actually handles (**completed checkpoint**);
- migrate value, typing, substitution, world-embedding, and catch-up clients
  (**parallel substitution, term-context shift, world embedding, bullet-free
  left renaming, and source-allocation runtime transport checked**);
- delete quotient application, finite-spine support, and
  `down·up⊑down·upᵀ` (**deleted from the live grammar; downstream references
  remain frozen migration obligations**);
- check the focused source and target function-cast roots before the public
  DGG phase gate.

The completed source-tail checkpoint replaces the former relation at the
transient casted-`ν` term with this operational sequence:

1. frame the completed operand catch-up;
2. take source type beta to `ν ★`;
3. allocate the fresh source seal with `bind ★`;
4. establish ordinary term imprecision for the allocated bullet and
   instantiation cast; and
5. resume value catch-up.

The runtime-sibling path transports its independent relation through the same
chosen store lift as the primary allocation. Both focused source-widening
leaves pass, and no source reference to
`weak-one-step-source-νcast-frameᵀ` remains. This checkpoint does not yet
change the live quotient grammar or remove any of its regression roots.

The live grammar checkpoint on 2026-07-27 promoted `paired-downᵀ`, `closeᵀ`,
and the direct paired reveal, conceal, and compatible-widening constructors.
It deleted the fused cast/application constructor, quotient-indexed
application constructors, the split narrowing introductions, and the
`PairedCast` wrapper from the canonical definitions. Focused checks pass for
the live relation, store-prefix evidence, parallel substitution, and
term-context shift. Other files in the frozen inventory still contain
retired names and must be migrated or deleted before a phase gate.

The world/left-transport checkpoint on 2026-07-27 promoted the selected
compatibility-renaming proof to
`NuImprecisionQuotientCompatibilityRename.agda`. The canonical simulation
core now transports `closeᵀ`, the three direct paired conversion cases, and
the single `paired-downᵀ` boundary. Focused checks pass for the world
embedding, bullet-free left renaming, and source-allocation runtime
transport. Relative to the frozen inventory, direct source-file counts have
fallen from `14/9/9/46/27/26` to `8/3/3/39/20/19` for fused
down/up, identity quotient application, gradual quotient application,
closing widening, identity down, and gradual down respectively.

The same checkpoint exposed and removed a duplicate copy of
`QuotientImprecisionCompatibility` that remained in
`proof/Quotient/`. All selected clients now import the canonical top-level
definition directly; no alias or compatibility re-export was retained. The
canonical quotient round-trip regression passes with `paired-downᵀ` and
compatible `closeᵀ`.

`QuotientedTermImprecisionTest.agda` was also deleted: its sole incomparable
intermediate-type round trip is now covered, with explicit compatibility, by
the strictly checked canonical quotient examples.

`NuImprecisionQuotientDownTransportProof.agda` now has one general
`quotient-down-transportᵀ` instead of separate identity/generated theorems.
It transports arbitrary `SpineCastMode` evidence through both sides of a
completed target-leading weak step and reconstructs `paired-downᵀ`; its
focused check passes. `apply-spine-narrows-typing` owns the reusable
identity/gradual split, so the endpoint transport is uniform. The remaining
direct source-file counts are `8/2/2/37/16/17`. Its sole enclosing frame
consumer must next transport the `closeᵀ` compatibility witness into the
final world; this is a proof obligation, not grounds for restoring the
deleted closing constructor.

The matched target-allocation checkpoint on 2026-07-27 removed the contract's
arbitrary target reduct and broad target runtime premise. The root now takes
the exact target value and no-bullet evidence required by allocation, exposes
the resulting bullet-and-cast term directly, and makes the allocated
source/target type-imprecision evidence an explicit premise instead of a
hidden proof index. Its lineage proof now lives beside the indexed allocation
result that determines the two component steps.

Migration through this dependency also removed an unreferenced paired-all
allocation helper island from `NuImprecisionSimulation.agda`, replaced two
live generic paired-conversion wrappers with direct `paired-revealᵀ`, and
replaced the matched post-allocation generated downcast with `paired-downᵀ`.
The focused target-allocation `Def` and `Proof` checks pass. The remaining
direct source-file counts are `8/2/2/37/16/16`.

The final focused proof check initially took roughly five minutes although
its root module was only 246 lines. It imported two results from the
2,860-line `NuImprecisionAllocationSimulation.agda`, which itself imports the
15,096-line simulation core and the 4,762-line simulation module.

The first dependency cut now places the complete post-value world-coherent
allocation contract in
`../WorldCoherent/Right/OneStep/Allocation/NuImprecisionWorldCoherentMatchedNuAllocationAfterValueCatchupDef.agda`.
The target-allocation `Proof` imports only that 118-line contract and no
longer imports the legacy allocation module; after invalidation it checks in
about six seconds. The canonical 91-line `Lemma` alone supplies the legacy
implementation and exposes the catch-up invariant constructor needed for
definitional reduction. Both `Proof` and `Lemma` check strictly.

This is an invalidation boundary, not the final implementation split.
`NuImprecisionAllocationSimulation.agda` still has three external consumers:
the target-allocation `Lemma`, source allocation-step proof, and source-`ν`
runtime-sibling catch-up proof. Move their retained implementation slices to
chartered allocation modules as those consumers migrate, then delete the
obsolete legacy remainder by Phase 5. A new wrapper that merely re-exports the
monolith would not complete that task.

The next Phase 4 checkpoint completed the quotient-close and target
terminalization path. Reduction-closed compatibility is transported through
the final world by the canonical weak-step compatibility theorem. The
quotient-down frame and root families, exact narrowing and conversion
transport, atomic target reindexing, target seal cancellation, and target tag
cancellation all pass focused checks. The overly broad target-ground quotient
elimination claim was found to be false for gradual seal-mode narrowing and
was replaced by the exact function-ground theorem required by target tag
cancellation.

The target-allocation bullet pair now uses `closeᵀ`, the three direct paired
constructors, and the generic target-widening constructor. Its two real
pending-allocation callers also pass. The SourceAll closing slice no longer
uses the retired `PairedCast` carrier: paired reveal, conceal, and widening
are three direct residual capabilities, and quotient closing exposes its
reduction-closed compatibility premise. The separate target-id-widening
capability became unreferenced after all SourceAll consumers moved to the
generic widening constructor, so its `Def` and `Proof` were deleted.

`NuDGGUnassembledProofsStrictSpine.agda` now checks completely. The broader
terminal-forward spine next stops at the still-retiring source
function-cast-beta paired-values interface, whose statement directly mentions
the deleted `PairedCast` carrier. This is the current migration boundary.
The remaining direct retired-name counts are `7/2/2/29/12/12` for fused
down/up, identity quotient application, gradual quotient application,
closing widening, identity down, and gradual down respectively.

A dependency audit also identified the next useful invalidation cuts.
`NuImprecisionSimulationCore.agda` remains the largest high-fanout module;
its generic narrowing and conversion transport have already moved to focused
property modules, reducing one invalidated frame check from about 58 seconds
to about 8 seconds. The next candidates are QTI typing projections and the
store/context infrastructure still bundled with the obsolete first-draft
relation in `NuTermImprecision.agda`. Make those cuts only at a checkpoint,
not concurrently with a grammar edit.

The QTI typing-projection cut is now complete.
`QuotientedTermImprecision.agda` contains the 627-line live grammar and
support definitions, while the 395-line
`../NuCore/Relations/NuImprecisionQuotientedTyping.agda` owns the five
recursive ordinary/quotiented source and target typing projections. Every
direct projection consumer imports that proof-support module explicitly;
the grammar does not import or re-export it. The focused typing module checks
in about three seconds warm, a representative allocation consumer in about
eight seconds warm, and the unassembled strict DGG spine in about seven
seconds warm. The one-time import-boundary rebuilds took roughly one minute
for the representative consumer and up to three minutes for the strict
aggregate after removing seven empty grammar imports. The source/import audit
passes.

A fresh check of the separate public `NuDGGSpine.agda` exposed a stale cached
dependency in compiler monotonicity:
`proof/Compilation/CompileTermImprecision.agda` still constructs the deleted
`up⊑upᵀ`. That public spine is not the unassembled strict aggregate checked
above.

The first proposed repair was to replace the closing constructor by `closeᵀ`
and derive its reduction-closed compatibility premise from canonical compiled
cast plans. That compatibility claim is false. Compiling the source cast from
`∀ X. X ⇒ X` to `★` produces an active instantiation followed by a tag, while
the related target cast from `★ ⇒ ★` to `★` is an inert tag. Compatibility
would require the impossible type-imprecision bridge `★ ⊑ ★ ⇒ ★`. Therefore
the compiler case must use an up-to-reduction simulation boundary, or the
closing design must change semantically; a plan field, wrapper, or restored
fused constructor would only hide the obstruction.

The direct source function-beta paired-values slice is now checked. Its
interface no longer mentions the deleted `PairedCast` carrier. It exposes
paired reveal, conceal, widening, and quotient cases directly; paired
widening and quotient closing retain their reduction-closed compatibility
premises. The paired reveal and conceal cases distribute function beta
through direct paired residuals, while the widening proof handles the
reduction-closed active/inert distinction exhaustively. Focused checks pass
for the two new case contracts, the combined `Def`/`Proof`/`Lemma`, both
paired-widening proof layers, both paired-quotient proof layers, the target
function-cast dispatcher, and `NuDGGUnassembledProofsStrictSpine.agda`. The
source/import audit also passes.

The terminal-forward strict spine now advances to
`NuImprecisionQuotientFunctionPairedNarrowingApplicationProof.agda`, whose
entire implementation is the deleted quotient-application constructor. The
live quotient syntax has only `paired-downᵀ`; it cannot produce an
application-headed quotient bottom edge. This is the concrete operational
boundary for an up-to-reduction source simulation result, not a reason to add
another congruence or fused QTI rule.

The existing `WorldCoherentSourceOneStepIndexedResult` fixes the whole source
trace to exactly one distinguished step. Its underlying weak-step result
already permits arbitrary source catch-up and a target tail. The next design
checkpoint will test the smallest result contract in which the distinguished
source step is a prefix of the returned source trace. Only after that
replacement covers the old pure quotient-application family may that family
leave the regression surface and be deleted.

That smallest result-contract experiment is checked. The completed-step
record now keeps the distinguished change at the head of the total source
changes and carries an arbitrary source reduction tail from the immediate
reduct to the final source term. The public source simulation exposes both
that source tail and the target tail before its final ordinary-QTI edge.
Exact leaves use the empty tail, while binary, source-cast, and source-`ν`
frames lift arbitrary tails through their whole-term contexts. All former
exact-result clients have migrated.

Terminal-forward consumes the stronger operational result using fuel bounded
by the observed source trace length. The existing aligned-residual theorem
proves the recursive source trace strictly shorter after the distinguished
step and its returned tail are reconciled. Focused checks pass for the result
contract, public projection, terminal-forward proof, source-silent
composition, direct lambda and primitive schedulers, and all migrated frame
families. The terminal-forward strict spine reaches the obsolete pure
quotient-application proof exactly as expected.

The pure quotient-application family remains on the regression surface for
one more operational replacement. The paired-quotient beta leaf must
terminalize its exposed source and target domain casts after the distinguished
function-beta step. Because the source tail may reach blame, this path must
propagate the existing source-step outcome rather than promise a related
result unconditionally. After that outcome path passes its focused and
terminal-forward gates, delete the obsolete quotient-application and paired
quotient-relation families in the same checkpoint.

The outcome path to that leaf is now checked. The direct function-beta
contract, target-value rank recursion, target cast/conversion frames,
application root, pure-step dispatcher, and full source one-step dispatcher
all preserve the same two alternatives: a final ordinary-QTI edge after
bilateral tails, or a source trace to blame. Exact leaves inject the first
alternative; recursive target frames map only the related result and carry
source blame through unchanged. The stale target-id widening branches were
deleted because the live grammar has only the generic target-widening
constructor. Focused checks pass through
`NuImprecisionWorldCoherentSourceOneStepProof.agda`.

The terminal-forward strict spine still stops at, and only at, the obsolete
pure `NuImprecisionQuotientFunctionPairedNarrowingApplicationProof.agda`.
The next checkpoint must replace the paired-quotient beta leaf operationally
before deleting that pure family.

The stable dependency cut preceding that operational replacement is checked.
The old 1,213-line mixed `NuTermImprecision.agda` module no longer exists.
The relational-store, term-context, crossed-store, and cast-mode support
modules pass focused checks; the live QTI join and source one-step proof pass;
and `make audit` reports no unresolved or unsafe strict imports. The
terminal-forward spine still reaches the same obsolete pure
quotient-application proof, confirming that the split did not move the
semantic boundary.

The accompanying hotspot cut moved `seal★-tag-or-id` from the 1,276-line
cast-imprecision module into the focused 15-line
`../Core/Properties/SealModeProperties.agda`. Its 35 direct clients now
import the small module explicitly; no re-export preserves the old dependency
edge. The live QTI join and source one-step root pass after the rewrite.

The next semantic invariant has been tested before changing the live grammar.
`NuImprecisionQuotientNarrowingEliminationCompatibility.agda` records
recursive elimination safety for a quotient-producing paired narrowing:
function coercions carry reduction-closed compatibility for their
contravariant domain widenings and recurse through their codomain narrowings;
a pair with a non-function coercion has no function-elimination obligation.
The focused definition and the existing two-function-cast/permuted-`∀`
regression pass. This checkpoint does not yet add the premise to
`paired-downᵀ`.

The remaining direct retired-name counts are `7/2/2/28/12/12` for fused
down/up, identity quotient application, gradual quotient application, closing
widening, identity down, and gradual down respectively.

### Phase 5. Collapse the migration surface

- move or rename retained theorems and regressions to canonical names;
- remove every `Experiment` migration root from the Makefile;
- delete the selected prototype and every superseded helper rather than
  retaining wrappers or re-exports;
- confirm that `proof/Quotient/` contains only canonical support, proofs, and
  retained regressions.

### Phase 6. Finish the migration

- confirm no obsolete module or constructor name remains outside Git history;
- run the source audit, strict public DGG cone, focused forward and backward
  terminal spines, and the final canonical quotient regressions;
- update the proof ledger and change the heading of this file to exactly
  **MIGRATION FINISHED**;
- only then create the migration pull request.

## Regression and deletion policy

An obsolete module leaves the regression surface as soon as a strict
replacement covers the same live obligation. During an active phase, a
retiring live module stays on the regression surface until its replacement
passes; an already rejected alternative may be marked **obsolete,
quarantined** and removed from check roots immediately. An obsolete file is
deleted in that same phase after:

1. its importers have moved;
2. `rg` finds no remaining source references;
3. the focused replacement root passes; and
4. either its focused family gate passes or the current phase gate confirms
   the complete replacement.

For already rejected alternatives, phase 1 is the replacement gate; Git
history is sufficient archival evidence. For migration experiments, the
corresponding live theorem is the replacement gate. For retiring live
helpers, the last migrated consumer is the replacement gate. No obsolete
source survives merely as a compatibility aid. A phase checkpoint may retain
only migration-active source needed by the next phase, never a replaced
obsolete island. Phase 5 removes the experimental migration surface, and
Phase 6 verifies that no obsolete file remains before **MIGRATION FINISHED**.

## Agda checking policy

- Do not run Agda for documentation-only or Makefile-only changes.
- Edit a high-fanout grammar module at most once per phase before its focused
  checks.
- Batch consumers by constructor family and check the smallest changed leaf
  roots first.
- Run only one integration root at a phase gate; do not repeatedly run
  `All.agda`.
- Run Agda serially so concurrent processes do not contend for or refresh the
  same interfaces.
- Re-run the full migration surface only at phase gates and at
  **MIGRATION FINISHED**.

## Coordination policy

The live grammar has one writer at a time. Parallel agents, if deliberately
used later, receive disjoint consumer batches only after the grammar for that
phase is frozen, and their prompt must name the active phase and this file.
No agent may add a constructor, wrapper, alias, or check root outside its
assigned batch. Before merging a batch, the primary agent reconciles it
against the manifest and runs its focused check.

## Migration-finished conditions

All of the following are required:

- the live term relation is the selected smaller grammar;
- all live consumers use that relation directly;
- the old constructor families listed above are absent;
- all experimental and obsolete source files are deleted or promoted under
  canonical names;
- the Makefile contains only canonical regressions and proof roots;
- source search finds no obsolete imports, constructor uses, wrappers, or
  aliases;
- the final focused and integration checks pass; and
- both this file and the proof ledger say **MIGRATION FINISHED**.
