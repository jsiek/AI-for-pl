# Quotient-imprecision migration status

## Authoritative state

**MIGRATION IN PROGRESS — replacing operational quotient boundaries**

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
- `NuImprecisionQuotientEliminationCompatibilityRename.agda`;
- `NuImprecisionPairedDownRenameDef.agda`;
- `NuImprecisionPairedDownRenameProof.agda`;
- `NuImprecisionPairedDownRenameLemma.agda`;
- `NuImprecisionTargetInstantiationCreationDef.agda`; and
- `NuImprecisionEmbeddedTargetInstantiationCreationProperties.agda`.

The selected metatheory sources are:

- `NuImprecisionReductionClosedQuotientStorePrefixExperiment.agda`;
- `NuImprecisionReductionClosedQuotientTypingExperiment.agda`;
- `NuImprecisionReductionClosedQuotientValueExperiment.agda`;
- `NuImprecisionReductionClosedQuotientTermContextShiftExperiment.agda`;
- `NuImprecisionReductionClosedQuotientSubstitutionExperiment.agda`;
- `NuImprecisionReductionClosedQuotientSingleSubstitutionExperiment.agda`;
- `NuImprecisionReductionClosedWorldEmbeddingExperiment.agda`;
- `NuImprecisionReductionClosedWorldRenameExperiment.agda`;
- `NuImprecisionReductionClosedQuotientIdOnlyCastAudit.agda`; and
- `NuImprecisionReductionClosedQuotientTransientAudit.agda`;
- `NuImprecisionMutualQuotientEliminationExperiment.agda`.

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

## Store-prefix admissibility

The ordinary live and prototype judgments are now syntax directed: neither
grammar contains a generic relational-store prefix constructor. The canonical
live interface is the `NuImprecisionTermStorePrefixDef/Proof/Lemma` family in
`../Store/Prefix/`; the independent prototype theorem remains in
`NuImprecisionReductionClosedQuotientStorePrefixExperiment.agda`.

Both proofs are mutual over the ordinary and quotient judgments. They keep
the terms, endpoint types, term context, and imprecision index fixed while
moving from `ρ₀` to `ρ⁺`, given endpoint typing in `ρ⁺`. Runtime-bullet
constructors retain the prefix from their canonical allocation store to their
ambient store, and embedded target-instantiation creation retains the exact
post-allocation lineage. Applying general weakening composes that stored
lineage; it does not add a term-relation wrapper.

Consequently typing, value classification, terminal inversion, world
embedding, context shift, and substitution reach the constructor selected by
the endpoint syntax directly. Allocation/frame consumers call the admissible
theorem only when an unchanged sibling must be rebuilt in an enlarged world.

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
- `NuImprecisionQuotientInstView.agda`;
- `NuImprecisionQuotientWideningTransport.agda`.

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

The world/left-transport checkpoint on 2026-07-27 promoted compatibility
renaming behind the strict
`NuImprecisionPairedDownRenameDef/Proof/Lemma` boundary. The canonical
simulation core transports `closeᵀ` and the three direct paired conversion
cases, so future changes to recursive elimination compatibility do not
invalidate the 14,878-line core. Focused checks pass for the generic boundary,
its canonical assembly, world embedding, bullet-free left renaming, and
source-allocation runtime transport. Relative to the frozen inventory, direct
source-file counts have fallen from `14/9/9/46/27/26` to `8/3/3/39/20/19`
for fused down/up, identity quotient application, gradual quotient
application, closing widening, identity down, and gradual down respectively.

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

The next semantic invariant was tested before changing the live grammar. The
standalone prototype recorded recursive elimination safety for a
quotient-producing paired narrowing:
function coercions carry reduction-closed compatibility for their
contravariant domain widenings and recurse through their codomain narrowings;
a pair with a non-function coercion has no function-elimination obligation.
The focused definition and the existing two-function-cast/permuted-`∀`
regression pass.

That invariant is now a premise of the live `paired-downᵀ`. Focused checks
pass for structural consumers, substitution, store-prefixing, bilateral and
source-only renaming, allocation transport, quotient-down weak-step
transport, right active roots and frames, active synchronization, and target
function-ground elimination. The weak-step transport includes target
allocation and preserves the exact recursive quotient-arrow components.

The 573-line
`../Core/Properties/NuImprecisionQuotientWeakTransportProperties.agda`
centralizes that quotient-arrow naturality result. Its former keep-only copy
was deleted from the right-value transport monolith, removing 429 duplicated
lines. Paired-down renaming now lives in the strict
`NuImprecisionPairedDownRenameDef/Proof/Lemma` family, and the 14,878-line
simulation core no longer owns or imports the recursive invariant. The
combined compatibility-renaming module was split by responsibility and
deleted without a shim. `make audit` passes.

The next Phase 4 gate is operational: replace the pure paired-quotient
function-beta leaf with bilateral terminalization driven by the recursive
elimination evidence. Only after that replacement passes may the obsolete
quotient-application and paired-quotient-relation families leave the
regression surface and be deleted.

The first operational construction exposed a genuine higher-order gap in the
new evidence. Suppose the closing function widenings have domain narrowings
`c` and `c′`, while the quotient-producing function narrowings have domain
widenings `a` and `a′`. After the two function-beta steps, the argument must be
related by

`closeᵀ (paired-downᵀ ... c ... c′ ...) ... a ... a′ ...`.

The current `function-elimination` evidence supplies reduction-closed
compatibility for `a` and `a′`, plus recursive codomain elimination evidence,
but it does not supply
`QuotientNarrowingEliminationCompatible ... c c′ ...`. The outer
`ReductionClosedQuotientWideningCompatible` function case also keeps only its
codomain compatibility. The quotient component equation and the two shape
squares determine the domain indices, but they cannot reconstruct the missing
operational evidence.

This omission is hidden when the argument type is first order because
`non-function-elimination` closes the new domain boundary. At a higher-order
argument type, the newly exposed `c` and `c′` are function coercions and the
proof stops. Therefore the current transported invariant is not yet the final
live design. The next grammar checkpoint must make narrowing and widening
function-elimination evidence mutually recursive, so a closing function
widening retains elimination evidence for its contravariant domain narrowing
as well as widening compatibility for its codomain. A strict higher-order
regression must pass before the operational beta leaf resumes.

That side experiment succeeded, and the mutual relation is now live in
`QuotientImprecisionCompatibility.agda`. Its quotient-widening representative
constructor explicitly excludes paired function coercions, so the generic
case cannot bypass recursive domain evidence. Function widening retains
domain narrowing-elimination evidence and recursive codomain widening
evidence; function narrowing retains domain widening evidence and recursive
codomain narrowing evidence.

The two former rename modules are now one
`NuImprecisionQuotientEliminationCompatibilityRename.agda` with mutually
recursive bilateral and source-only proofs. Weak-step transport is likewise
mutual, and quotient-down imports that canonical transport instead of owning
a private copy. The superseded standalone definition and both old rename
files were deleted without shims. Strict checks pass for the unified rename
module, paired-down rename assembly, both weak-step transport roots, target
tag cancellation, the canonical quotient examples, the higher-order
regression, and the right quotient-down cases. `make audit` passes.

The next semantic task is the operational quotient-down value catch-up leaf.
It must use the live hereditary evidence to return either bilateral traces
ending in ordinary QTI or a source trace to blame. This remains the gate for
deleting the obsolete pure quotient-application and paired-quotient-relation
families.

The migration also treats checking-time boundaries as part of cleanup. The
former 2,873-line `../NuCore/Misc/NuImprecisionAllocationSimulation.agda`
now has only two direct consumers. Its seven shared source-`ν` lift/replacement
properties now live in the 497-line
`../Core/Properties/NuImprecisionSourceNuLiftProperties.agda`; the allocation
monolith is 2,444 lines and does not re-export them. Retained
source-only and matched-allocation capabilities will then move to chartered
`Source/Allocation` and `OneStep/Allocation` contracts. The unused allocation
branches and the monolith itself will be deleted after those consumers move.

The source-only allocation cut is now complete. The two real bottom-edge
relations live in the strict
`../Source/Allocation/NuImprecisionSourceNuAllocationRelationDef/Proof/Lemma`
family and no longer bundle the immediate source `ν` step or target
reflexivity. The world-coherent caller constructs those reductions directly
and takes both relation contracts as higher-order dependencies. The unused
paired-widening-under-binder transport and its private shape support were
deleted rather than extracted. The three new modules and the reduced
allocation monolith pass strict checks; the source allocation proof reaches
only its already-known retired `⊑cast⊑idᵀ` case. This cut reduces the monolith
to 2,168 lines.

Matched allocation is now isolated in the strict
`../OneStep/Allocation/NuImprecisionMatchedNuAllocationStepDef/Proof/Lemma`
and
`NuImprecisionMatchedNuAllocationAfterValueCatchupDef/Proof/Lemma`
families. Their contracts couple each indexed result to its store lineage and
one homogeneous equality for the fully packed final context and exact
matched-head store. The world-coherent layer transports coherence,
source-name exclusivity, and assumption uniqueness across that single
equality. The target allocation root is assembly only, while the source
allocation proof receives the base matched step as a higher-order dependency.

All six lower modules, the world proof and lemma, the target allocation root,
and the reduced legacy module pass focused strict checks. The source
allocation proof checks through every migrated case before the existing
retired `⊑cast⊑idᵀ` branch. Deleting the moved matched-allocation, value
catch-up, blame, and dispatcher islands reduced
`../NuCore/Misc/NuImprecisionAllocationSimulation.agda` from 2,168 to 665
lines and reduced its focused check to 4.70 seconds.

The four zero-consumer residuals were then audited against the incomplete
runtime-bullet and simulation cases. Three fused allocation-plus-reduction
wrappers are obsolete under simulation up to reduction and were deleted. The
one future runtime-bullet obligation is the bilateral paired-narrowing edge
after post-allocation `β-gen•`; it now lives without either operational step
in the strict
`../OneStep/RuntimeBullet/NuImprecisionMatchedBetaGenNarrowingDef/Proof/Lemma`
family. Generic allocation transport is a higher-order proof dependency and
is supplied only by the canonical lemma. All three focused checks pass.
`../NuCore/Misc/NuImprecisionAllocationSimulation.agda` is now deleted, with
no remaining Agda references to it or its former declarations.

The post-target function-beta boundary now has a strict contract. The source
paired-quotient wrapper depends on that contract instead of the obsolete pure
relation, prepends the target beta step, and passes focused strict checking.
This is a successful architectural fit, not yet a completed semantic leaf.

The attempted direct inhabitant correctly inverted the outer function values
but incorrectly treated their contravariant component casts as inert. The
component casts on the related arguments may be active, so the finite
two-beta construction was rejected. Closing those paired domain narrowings
with the inner domain widenings produces an ordinary QTI edge. The existing
quotient-down synchronization handles its first active target step, and
left-value catch-up can finish the source once the target becomes a value.
The missing reusable dependency is the recursive canonical
`WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ` dispatcher: its strict
case, frame, and root proofs exist, but no assembled lemma is exported.

The next gate is to assemble that right one-step dispatcher without
duplicating it privately in the beta proof, then use it in the post-target
worker and amend the right-oriented beta contract with the outer
reduction-closed widening compatibility. Only after that worker, both beta
orientations, and terminal-forward integration pass will the two pure
quotient-application theorem families be deleted.

The dispatcher assembly audit found prerequisite migration work rather than
a missing wiring file. Value catch-up, the old paired-cast aggregate,
target-cast semantics, and parts of function beta still pattern-match retired
QTI constructors. The ordinary and source-down application families will be
deleted, not adapted, because live QTIP contains only `paired-downᵀ`.
Migration proceeds through live value catch-up, explicit paired
reveal/conceal/widening cases, removal of identity-only target widening,
runtime-bullet leaves, and quotient-frame recursion. Only then will one small
well-founded SCC assemble prefix dispatch, quotient-frame recursion, and the
post-target quotient-beta worker. Its measure is lexicographic:
pending-administration/function-cast-spine potential first, then structural
QTI/QTIP derivation height.

The source-allocation proof has completed this consumer migration. Deleting
its retired `⊑cast⊑idᵀ` case exposed three constructions using the former
exact source-result interface; each now gives an explicit empty
administrative tail and reflexive tail reduction. The focused strict check
passes in 22.22 seconds.

The source-`ν` frame, lambda-beta scheduler, primitive-delta dispatcher, and
target-function-cast value scheduler also deleted their identity-only target
widening cases and pass focused strict checks. The live generic target
widening constructor now supplies the only such branch.

The checking-time cleanup reduced
`../Catchup/Simulation/NuImprecisionSimulation.agda` from 4,769 to 4,273
lines. Three live polymorphic reduction helpers moved to the canonical
`../Source/Core/NuImprecisionSourcePolymorphicValueBase.agda`; the unused
administrative trace and mini-square remainder was deleted without
re-exports. Matched allocation localized its private lift/prefix support and
no longer imports the broad simulation module. The focused canonical helper,
matched-allocation, target-allocation consumer, and reduced-simulation checks
pass. Two redirected source-widen consumers remain blocked earlier by the
retired `PairedCast` surface now being migrated.

Right-lift prefixing now has the focused
`../Right/AllocationRuntime/NuImprecisionRightLiftPrefixBodyDef/Proof`
boundary. Its four consumers use the canonical theorem directly, and the
three old right-lift helpers were deleted from the simulation module without
re-export. The new boundary, all redirected allocation consumers, and the
reduced simulation module pass strict checks.
`NuImprecisionSimulation.agda` is now 4,216 lines, 553 lines smaller than
before the three checking-time cuts.

The left value-catch-up prerequisite is now live. Its source-runtime contract
has separate reveal, conceal, and paired-widening fields instead of the
retired `PairedCast` aggregate. The prefix proof analyzes `paired-downᵀ`,
`closeᵀ`, `paired-revealᵀ`, `paired-concealᵀ`, and
`paired-wideningᵀ` directly, and its old fused down/up, identity-only
target-widening, and generic conversion branches have been deleted. Focused
strict checks pass through the canonical left value-catch-up proof.

The runtime-sibling proof validated the same close-frame interface. It now
lives in the strict
`../Catchup/Core/NuImprecisionCatchupPrefixCloseDef/Proof/Lemma` family and
serves both ordinary and runtime-sibling value catch-up. The old quotient
catch-up support module had no semantic consumers left; its inventory-spine
import and the obsolete file were deleted without a wrapper.

The runtime-sibling quotient contract now has one generic close field instead
of identity and generated narrowing variants. Its source-runtime contract
uses explicit paired reveal, conceal, and widening fields. The value consumer
analyzes the live close, paired narrowing, and paired cast constructors; its
fused down/up, identity-only target-widening, and generic conversion cases
are gone. All new boundaries and the higher-order consumer pass focused
strict checks. The unused old quotient-final provider and its terminal
classifier have now been deleted with the retiring quotient-value cone.

The revised source-runtime record still has no canonical Proof/Lemma
provider; the obsolete `SourcePairedCastCatchup` aggregate must not be
retained as a compatibility wrapper.

The right-value no-bullet transport proof now has a stable invalidation
boundary. Three focused modules own its term/runtime facts, prefix transport,
fixed narrowing transport, and quotient-index transport. They pass strict
checks in about five to six seconds, two unused private helpers are deleted,
and the constructor-sensitive monolith is 370 lines smaller. The monolith
still reaches the already-known removed-`PairedCast` blocker; this cut does
not preserve that obsolete aggregate.

The eventual source-runtime provider must be a visible well-founded
source-administration dispatcher, not a cyclic record assembly. Before it can
be built, tighten the broad source-widening field to the admissible case view
already established by the checked widening cases, whose source-inst branch
requires a `ν` index. Then add the explicit paired reveal, conceal, and
widening leaves. The old `SourcePairedCastCatchup` graph is obsolete and will
be deleted after its two right-root clients are classified against the live
constructors. Migration-aligned checking-time cuts should split the
source-widening cases and source-conceal monolith; the retiring quotient-value
case analysis should shrink by deletion instead.

The broad source-widening field has now been removed. Four exact contracts
cover inert widening, atomic identity, coercion sequences, and source-only
`ν` instantiation. Their common transport core and focused proofs replace the
old 1,435-line proof; the sequence and `ν`-indexed leaves and the
inert/identity leaf pass strict checks. The live-value consumer now performs
the exhaustive dispatch directly. Its source-instantiation clause requires
the `ν` index, instantiation shape, and `comp-ν` equation simultaneously;
bare unseal requires its reveal replacement equation. Agda accepts the
sequence and instantiation recursion without a termination pragma.

Atomic source reindexing has migrated completely to the live constructors.
The strict focused theorem handles `closeᵀ`, target creation, generalization,
and explicit paired reveal, conceal, and widening. Its private old-QTI copy
and `../NuCore/Relations/NuImprecisionPairedCastResultShape.agda` were deleted.
The four source-cast result framers similarly moved from the broad simulation
module to the focused strict
`../OneStep/NuImprecisionWeakOneStepSourceCastFrame.agda`.

The right active and inert source-value roots and active-value
synchronization now consume explicit paired reveal, conceal, and widening
evidence. Their focused case modules and aggregate Lemmas pass strictly.
Consequently the old source `PairedCast` catch-up Def/Proof pair has zero
consumers and was deleted. The subsequent audit examined the paired-value
root and paired outer-cast dispatcher as the next aggregate-based clients.

That next audit classified both aggregates as dead, not migration targets.
The standalone paired-value proof, mixed outer-cast Def/Proof/Lemma,
superseded active-value-roots Def, paired-cast frame proof, and its transport
Lemma were removed together with their inventory-spine imports. The separate
ordinary reveal/conceal/widening roots, quotient recursion contract, and
active synchronization contract remain. The zero-consumer
source-`ν` paired-all target-closing Def/Proof/assembly triple was also
deleted from its strict-only spine. The zero-consumer
`NuImprecisionSourceDownApplicationCompatibleOuter.agda` helper belonged to
the removed source-down application grammar and was deleted as well.

The matching right-dispatch islands were inventory-only: ten
ordinary-down-application and source-down-application scheduling,
synchronization, frame, root, and cases modules had no semantic consumers.
Because live QTIP has only `paired-downᵀ`, the whole bundle and its
terminal-backward spine imports were deleted rather than migrated.

The three live `PairedCast` joins have now been replaced by exact constructor
interfaces. Right value-catch-up exposes separate reveal, conceal, and
widening frame fields. Source one-step framing does the same. Function-cast
beta exposes reveal, conceal, live widening, and the separate quotient-close
case, with the implementation split into focused conversion, widening, and
quotient proofs. The focused definitions and case proofs pass strictly.
Their larger dispatchers now stop only at other retired constructor clauses;
no compatibility carrier or provider was introduced.

The right paired-frame contract has reached terminal-forward integration as
an explicit higher-order dependency. Its canonical provider remains
intentionally absent: transporting the evidence and building a neutral
paired frame does not terminalize an active transported target cast. That
semantic step belongs in the operational right-dispatch SCC.

Store-correspondence transport was also corrected and moved out of the
left-silent namespace. The strict generic lineage theorem has no silent-result
premise and now supports paired reveal and conceal transport for a
keep-leading result. Quotient-down transport similarly exposes a strict
evidence theorem whose caller supplies the recursively transported body,
while the indexed-result wrapper remains a small corollary. These are stable
dependency cuts for the right no-bullet proof rather than wrappers around the
retired relation.

The right no-bullet migration is complete. The 1,766-line proof has one live
`paired-downᵀ` quotient-prefix case, two `closeᵀ` active cases, and explicit
reveal, conceal, and widening cases. It and its direct Lemma pass strictly.
The generic/right-silent paired-cast transport family was then deleted as a
zero-consumer obsolete graph. The right value dispatcher also passes against
its single exact quotient-down/up frame.

Both final source-`ν` source-only proof roots now pass strictly. Membership
uniqueness is explicit, all ten source-lift coherence fields are present, and
the `ν ★` cast branch exposes the real recursive post-allocation value-catchup
edge rather than narrowing the cast to instantiation alone. The strict audit
now lists only two incomplete Proof roots.

Canonical compilation supplied a decisive counterexample rather than the
missing compatibility theorem. Actual cast plans for `∀ X. X ⇒ X` and
`★ ⇒ ★` violate `ReductionClosedQuotientWideningCompatible`, so
`CompileTermImprecision` cannot close every compiled pair with `closeᵀ`.
`WorldCoherentQuotientFinalCatchupᵀ` handles the operational value case up to
reduction, but boundaries under lambdas and around open variables cannot
reduce. The remaining design choice is a restricted compiler-origin
pending-close boundary versus a semantic or ground-final DGG statement;
neither `up⊑upᵀ` nor a false `CastPlan` field is acceptable.

The stale pure quotient-application family remains a live migration gate for
function-cast beta. Its replacement is the operational
`WorldCoherentSourceFunctionCastBetaPairedQuotientPostTargetᵀ` path, which
still needs the recursive right-dispatch/quotient-frame SCC.

The detailed post-target audit rules out a finite two-beta shortcut. After
the outer beta steps, the inner redexes remain blocked until
`W ⟨ c ⟩` and `R′ ⟨ e ⟩` become values. The ranked worker must administer
those exposed arguments, invoke left value catch-up when the target becomes
a value, and then take the inner beta steps. The final bottom edge is two
nested live `closeᵀ (paired-downᵀ ...)` relations. Existing mutual
compatibility already provides the two domain-elimination and two
codomain-widening facts; the missing work is operational synchronization, not
a new relation constructor.

Assemble the dispatcher and post-target worker as one ranked SCC, decreasing
ordinary QTI structure, target function-spine rank, or
`pendingAdministrationRank` as appropriate. The old quotient-frame recursion
and quotient active-value contracts still mention retired `up⊑upᵀ`, omit live
closing compatibility, and have no semantic consumers. Replace only the
exact live-close contracts needed by the SCC and delete the rest. When the
source, right, and terminal-forward orientations pass, delete the pure
quotient-application and pure paired-quotient relation families.

The five-module obsolete outer-quotient island has now been deleted. It
contained the old quotient-frame recursion definition plus quotient
active-value roots and synchronization Def/Proof/Lemma; its only external
importer was the terminal-backward inventory spine. This removes 481 lines
without changing the live `QuotientDownActive*` path. The focused live
quotient-down synchronization check and the source/import audit pass. The
backward spine next reaches the separately live source-seal cancellation
proof, whose retired-constructor cases must be migrated because reveal and
unseal catch-up still consume the theorem.

Source-seal cancellation is now live-QTI exact. Its public contract is
unchanged; the proof uses `closeᵀ (paired-downᵀ ...)`, direct paired reveal,
conceal, and widening cases, and no retired identity-cast shortcut. The
Proof, Lemma, and both immediate source catch-up consumers pass strict checks.

The three remaining live quotient-down root fields cannot be filled by the
existing target identity, sequence, and untag context lemmas alone. Those
lemmas assume ordinary QTI and a completed right-value catch-up result,
whereas a quotient-down root starts inside `paired-downᵀ`; its target root
step erases or splits the downcast. The ranked SCC must first perform
compatibility-directed representative elimination and target
administration. Its next exact boundary is paired-down value catch-up with
the closing widening evidence provided by the mutual function-elimination
invariant, not a nonrecursive adapter record.

The strict
`NuImprecisionWorldCoherentRightOneStepQuotientDownValueAccDef` now records
that exact two-cast entry boundary at one coherent value world. It retains
both composition squares, both compatibility witnesses, and accessibility at
the target down/up pending spine. It is an entry contract, not yet a recursive
implementation. Target `β-id` supplies the first decisive residual: the
admissible
`non-function-elimination (target-non-function non-function-id)` case removes
the target downcast, so the remaining target widening is no longer related by
ordinary QTI and cannot be fed to the ordinary target pending-cast worker.

The corresponding sequence and successful-untag residuals likewise retain
the original source down/up boundary while the target pending list changes.
All three residual ranks decrease. The missing SCC state must therefore range
over an arbitrary target pending-cast list, preserve the original quotient
boundary and compatibility evidence, and either expose an ordinary
representative for the existing administration worker or descend through
`compatible-quotient-functionᴿ`. Keep the two-cast `Def` as the public entry
to that generic residual worker; do not revive the deleted outer
quotient-frame contracts or fabricate one adapter per residual length.

That state is now frozen by the strict
`NuImprecisionWorldCoherentRightOneStepQuotientDownResidualAccDef`. It records
an arbitrary current value and pending list together with a trace from the
original two-cast target. The trace begins with the target step being
simulated, and all remaining steps are `keep`. This supplies an exact
operational origin for identity, sequence, and successful-untag residuals
without postulating an ordinary intermediate imprecision index. Its statement
checks in 5.17 seconds.

Allocation and blame stay outside this exact-world keep-only worker as leaf
handoffs. The implementation experiment must now determine whether
compatibility inversion closes or hands off every residual. If an ordinary
target-administration spine is needed before an ordinary representative is
available, introduce a genuine quotient residual plan indexed by this
boundary; do not add a QTI constructor or manufacture the missing index.

The entry-adapter experiment confirms that identity, sequence, and successful
untag are exact value residuals with strict rank decreases. Instantiation and
seal/unseal roots are impossible under target narrowing, and a blame body is
not a value. Failed untag is the sole terminal exception:
`((V′ ⟨ G ! ⟩) ⟨ H ？ ⟩) ⟨ u′ ⟩` reduces to
`blame ⟨ u′ ⟩`. It cannot inhabit the value-residual contract, and the retained
close evidence alone does not construct the necessary source reduction to
`blame`; the only analogous implementation still depends on the obsolete
relation.

Keep the recursive residual worker value-only. Supply a focused live
quotient-down bad-untag/source-blame leaf, and make the two-cast entry adapter
depend on that leaf and the generic residual worker. A terminal blame
alternative does not belong in every recursive residual state.

The repair is now strict. The dedicated
`NuImprecisionWorldCoherentRightOneStepQuotientDownBadUntagRootDef` concludes
with exactly the source-to-blame trace. The exhaustive
`*QuotientDownValueAccProof` consumes that leaf plus the whole keep-only
residual contract, constructs all three value residuals with strict rank
decreases, and eliminates every impossible root. Focused checks pass in 5.60
and 7.00 seconds. The Proof is inventoried in the unassembled strict spine,
and the source/import audit has no uninventoried Proof modules. The updated
366-module strict spine passes after an approximately 209-second interface
refresh; it remains a phase gate, not an inner development check.

Next implement the value-residual worker and lower bad-untag theorem, then
assemble the two-cast entry. These are operational proof obligations, not
reasons to add syntax to term imprecision.

The bad-untag obligation now has that smaller strict boundary.
`NuImprecisionWorldCoherentQuotientDownBadUntagSourceBlameDef` stops before
the closing widening and concludes that the source downcast reaches blame.
`NuImprecisionWorldCoherentRightOneStepQuotientDownBadUntagRootProof` lifts
that trace through the closing cast and appends the enclosing blame step. The
repaired source-`gen` ground-agreement theorem adds exactly the value and
no-runtime-bullet premises needed to exclude its earlier counterexample.
Both completed Proof modules are registered in the unassembled strict spine;
their focused checks take about six seconds.

The lower theorem's remaining proof dependency is a coherent ordinary-tag
synchronization result. In the live quotient-down modes, source seal cases are
impossible. Source-only variables contradict context exclusivity, and the
base, function, universal, and `gen` cases reduce to shape inversion plus
canonical target-tag cancellation.

The earlier constructor-form `QuotientDownResidualCorePlan` separated
ordinary bottom, ordinary opening, keep steps, and source blame, but it could
not reconstruct the current logical quartet. Its zero-consumer definition and
the corresponding opaque allocation residual are deleted. Function frames
still stay at the whole-application root, while allocation crosses the
world-changing typed target path rather than an operational trace.

The attempted two-way allocation classifier is refuted by the checked
round-trip example with source quotient type `∀X. ∀Y. X ⇒ Y`, target quotient
type `∀Y. ∀X. X ⇒ Y`, and common outside type `∀X. X ⇒ ★`. The target closing
widening instantiates while the source is still framed by two inert casts.
Ordinary opening would require the impossible edge
`∀X. X ⇒ ★ ⊑ ∀Y. ∀X. X ⇒ Y`; bare-`Λ` target-instantiation creation also
does not apply to the quotient-framed source. An earlier opaque-trace
allocation residual recorded the reduction but could not reconstruct the
paired-down/closing evidence, composition square, compatibility, and
universal permutation after `bind`, so its zero-consumer definition is
deleted. The replacement must be a right-oriented typed target-instantiation
path view with a path-aware accessibility decrease. It is not a QTI
constructor or a compatibility broadening.

The source narrowing proof now carries membership uniqueness through all
three framed branches and reconstructs all ten source-lift coherence fields.
It passes strictly and is imported by the unassembled strict spine. The
right target-allocation source-bullet proof also now matches the actual
`lift-left-ctx-[]` constructor rather than a shadowing pattern variable, so
context inversion recovers the required empty source body context. Its two
immediate Lemma consumers and the full unassembled spine pass strictly.

The audit passes at this checkpoint: local proof imports resolve, the five
strict safety roots are safe, the one known-incomplete Proof module remains
explicitly inventoried, and every other strict-looking Proof has a transitive
Lemma consumer or an unassembled-proof spine import.

The deleted compiler-origin pending-close experiment passed three decisive
checks before retirement: actual polymorphic-identity/dynamic-function plans
inhabited its boundary, compatible cases closed through live `closeᵀ`, and
operational final values needed no widening compatibility. Its negative
conclusion remains: a top-level pending node with an ordinary-QTI inner premise
is not compositional under lambdas, type lambdas, `ν`, or either application
child. The compiler needs a recursive syntax-directed relation, not that
retired root alternative.

The strict canonical-down experiment also refutes universal
`QuotientNarrowingEliminationCompatible` for pending compiler casts. For
every quotient index, actual canonical function downcasts expose the known
active-source/inert-target widening mismatch in their contravariant domains
and force `★ ⊑ A₁ ⇒ A₂`. The minimized regression checks in 3.12 seconds
without importing endpoint completeness; the unnecessary import had caused
two ten-minute checks. A recursive compiler relation therefore needs a
weaker direct operational pending-down boundary, or distinct compatible and
incompatible pending cases. It must remain separate from live QTI and feed a
compiler-specific operational DGG theorem.

The first canonical checking-time cut is complete. A focused 477-line
`NuImprecisionIndexedRenamingProperties.agda` now owns syntax-directed
indexed-imprecision renaming and binder lifts. `MaximalLowerBoundsWf.agda`
shrinks from 20,373 to 19,945 lines and from 174 direct importers to 22; 164
consumers now depend directly on the focused module. The new module and
reduced MLB file check in about four and five seconds with warm dependencies,
and the strict unassembled DGG aggregate passes after its one-time cold
rebuild.

The second cut is complete. A 489-line
`NuImprecisionWeakOneStepResultTransport.agda` now owns weak-result transport
and reindexing, while a 29-line heterogeneous-equality module removes
duplicate local transport helpers. The simulation core shrinks from 14,880
to 14,418 lines and from 85 direct importers to 71; fourteen consumers drop
it entirely. Focused strict checks and the source/import audit pass. The
historical quotient-final provider that still reached the obsolete
quotient-value analysis has since left the regression surface and been
deleted.

The store-invariant cut is also complete. A 30-line Def owns `StoreUnique`
and `StoreDetWf`, and a 133-line Proof constructs and preserves them using
canonical `NuStoreProperties` facts. The duplicate `StoreUnique-inst` is
gone. `NarrowWidenProperties.agda` shrinks from 4,385 to 4,230 lines, twelve
consumers import the focused boundary directly, and representative
compilation, narrowing, store, and cast checks pass. The independent
`CompileTermImprecision` failure remains its retired `up⊑upᵀ` use.

Binder allocation/opening is now a fourth stable cut. The 91-line
`NarrowWidenBinderProperties.agda` owns the seven opening/allocation lemmas
with no re-export from `NarrowWidenProperties.agda`. The monolith shrinks from
4,230 to 4,156 lines and from eight direct importers to four; the other four
consumers now depend only on the focused binder module. Strict checks pass for
the new module, invalidated monolith, matched-`β-gen` consumer, and source
inert-bullet consumer.

The fifth stable cut moves generic type-constructor and injective-rename facts
to the 93-line `TypeInjectivityProperties.agda` and deletes the zero-consumer
type-renamed-reduction API. `ReductionProperties.agda` shrinks from 1,242 to
1,051 lines. The focused module, reduced monolith, paired-reveal consumer, and
source/import audit pass. Rechecking the other two consumers exposed unrelated
migration debt: the paired-lambda widening dispatcher is incomplete and
belongs to the retiring paired-lambda surface, while the live source paired
post-beta path still reaches a retired `PairedConversion` dependency. Delete
the former with its surface and migrate the latter; do not restore a
`ReductionProperties` re-export.

The sixth stable cut extracts the 389-line
`NuImprecisionTransitivityProperties.agda` from
`MaximalLowerBoundsWf.agda`. It owns indexed context composition,
binder-aware transitivity, and the needed occurrence/non-variable support.
Five external consumers now import the focused module directly; the endpoint
selector imports it non-publicly and does not re-export it. The selector
shrinks from 19,945 to 19,606 lines and from twenty direct importers to
eighteen. Focused strict checks pass for the new module, the invalidated
selector, imprecision composition, endpoint maximality, and endpoint
quotienting.

The seventh stable cut extracts the 262-line
`NuImprecisionWfBridgeProperties.agda`. It owns legacy/indexed forgetting and
reconstruction, target lifting, and target-context dropping. Nine clients
import it directly; the selector keeps only a non-public transition import.
The selector shrinks from 19,606 to 19,402 lines and from eighteen direct
importers to thirteen. The focused module, invalidated selector,
cast-compatibility counterexample, endpoint maximality, and factorization
shape pass focused strict checks.

The eighth stable cut extracts the 784-line
`NuImprecisionBinderPermutationProperties.agda`. It owns indexed context
permutation, its type renamings, and permutation transport for well-formed
indexed imprecision. Four external consumers import it directly; the selector
keeps only a non-public transition import and shrinks from 19,402 to 18,665
lines. The focused module, selector, and two small representative consumers
pass strict checks. Broad simulation modules remain deferred to the migration
phase gate.

The ninth stable cut extracts the 333-line
`NuImprecisionBinderDropProperties.agda`. It owns the 298-line source-only
and paired binder-drop island, including membership transport and unused
opening. Eight external consumers import it directly; the selector again
keeps only a non-public transition import and shrinks from 18,665 to 18,367
lines, with five direct external importers left. Strict checks pass for the
focused module in 2.33 seconds, the invalidated selector in 48.43 seconds,
and two small consumers in 2.23 and 1.93 seconds. `make audit` passes.

The endpoint-selector retirement is complete. `CommonLowerBoundᵢ` now lives
in the 19-line `EndpointLowerBoundDef.agda`, and the generic variable-occurrence
fact lives in `TypeProperties.agda`. The no-GLB counterexample remains as a
112-line strict, selector-independent regression. The evidence-directed
counterexample tail, the 18,367-line selector, its 136-line obsolete postulate
experiment, and its 3,728-line work log are deleted. The new Def,
`TypeProperties`, retained counterexample, completeness, maximality,
factorization shape, and `make audit` all pass.

The tenth stable cut extracts the 375-line
`NuCastModeRenamerProperties.agda`. It owns left-insertion, adjacent-swap,
identity, and composition algebra for coercion-mode renamers, independent of
term imprecision and relational worlds. Seven external consumers import it
directly; `NuImprecisionSimulationCore.agda` keeps one non-public import and
shrinks from 14,421 to 14,095 lines. The focused module, reduced core, and two
small representative clients pass strict checks in 24–28 seconds.

The isolated raw-imprecision selector is retired too. Its only Agda client
was the standalone `MlbTypeTest`; the live compiler uses
`EndpointCanonicalMLBSimple` and `MLB-monotoneᵖ`. The 4,604-line
`MaximalLowerBounds.agda`, 253-line test, and stale 308-line `CompilePlan.md`
are deleted, and the standalone-root inventory is updated. `make audit`
passes.

The eleventh stable cut extracts the 142-line
`proof/Core/Permutation/ForallPermutationPath.agda`. It owns normalized
`∀`-permutation paths, their elementary steps and algebra, structural lifting,
and normalization from raw permutations. The world-coherence instantiation
path Def shrinks from 202 to 81 lines and no longer acts as a re-export
surface. Exact consumers import the focused Core module directly. Strict
checks pass for the path module in 3.34 seconds, the reduced Def in 6.05
seconds, the path properties in 6.18 seconds, and a representative cases proof
in 3.64 seconds.

The twelfth stable cut extracts the 614-line
`proof/Catchup/Simulation/NuImprecisionIndexedIdentityTransport.agda`.
It owns indexed identity renaming, replacement transport, endpoint transport,
and the associated shape refinements. Thirteen external consumers import it
directly; two drop `NuImprecisionSimulationCore` entirely. The core keeps only
five non-public uses, shrinks from 14,095 to 13,584 lines, and falls from 71
to 69 direct importers. Strict checks pass for the focused module in 4.42
seconds, the invalidated core in 61.71 seconds, and three representative
consumers in 7.91, 9.93, and 9.17 seconds. The remaining large live files are
either cohesive and low-fan-out or have a later explicit stable cut; the
retiring 2,090-line quotient-value monolith must be deleted rather than split.

Target-only allocation under a proof-relevant quotient now has a direct
active-`inst` contract in the 164-line
`NuImprecisionWorldCoherentRightTargetQuotientDownPendingNuAllocationPathAccDef`.
It retains both normalized paths and their raw-path equalities, the current
quotiented term derivation and representative, widening pair, composition
square, active reduction-closed compatibility, typed outer administration
spine, and the world/store invariants needed by allocation. Its result is the
existing world-coherent indexed right-value catch-up package plus the exact
right-context action and right-only store prefix. The Def checks strictly in
3.51 seconds.

The keep-only operational residual does not by itself reconstruct the current
quotient derivation, widening pair, composition square, or active
compatibility. The next proof must produce those four witnesses as it processes
the residual, or narrow its caller to the direct active-`inst` state. This gap
must remain explicit; it is not an ordinary pre-instantiation QTI edge and is
not a reason to add another relation constructor.

The producer side is now explicit in the 136-line
`NuImprecisionWorldCoherentRightTargetQuotientDownPendingCastsAccDef`. The
worker accepts the current quotient derivation, widening pair, composition
square, active compatibility, and ordinary outer administration tail
directly. The `closeᵀ (paired-downᵀ ...)` frame transports that quartet through
inner catch-up and passes it to the worker. The active target cast is not
folded into the ordinary tail: an `inst` branch takes its reduction and calls
the allocation-path leaf, while other active cases preserve or update the
quartet structurally. The Def checks strictly in 6.27 seconds.

`QuotientDownResidualCorePlan` and its opaque-trace allocation residual could
not manufacture the current logical quartet and had zero importers once the
typed worker boundary existed, so both definitions are deleted. Keep at most
the still-used thin value-residual adapter until its one-step caller is
connected to the typed worker.

The typed worker's inert layer is now proved strictly. It decides inertness of
the active target cast, constructs `closeᵀ` from the current quartet in the
terminal branch, and invokes ordinary pending administration only for the
outer tail. The 83-line Proof checks in 6.71 seconds and delegates exactly the
non-inert active-cast residual.

The active target-`inst` cell is also strict: its 140-line Def and 111-line
Proof normalize the source and target quotient paths, derive the smaller
post-beta rank, invoke the direct allocation-path leaf, and prepend `β-inst`
under the outer tail. The Proof checks in 7.95 seconds. The pending dispatcher
now classifies a non-inert widening exactly as identity, sequence, unseal, or
instantiation, invokes the checked instantiation cell, and leaves only the
first three in its residual contract. Untag is a narrowing/cancellation case
below this boundary, not a target closing-widening case. The allocation-path
contract still needs its strict inhabitant.

The 2,090-line `NuImprecisionQuotientValue.agda` retirement is complete.
After removing the historical InstFunTag/classification/final-provider block
from `NuDGGStrictSpine`, the source/import audit confirmed that no public DGG,
terminal strict spine, or unassembled-proof spine reached that 21-file cone,
so it was deleted. A fresh strict-spine check correctly reaches the
independent live `CompileTermImprecision` failure at retired `up⊑upᵀ`; an
earlier cached 26-second pass did not expose that invalidated consumer.

The separate 37-file quotient-instantiation path/provider experiment is also
deleted. It had no public DGG or terminal consumer: the strict inventory spine
and one Makefile check were its only roots.

Both temporary
`NuImprecisionWorldCoherentQuotientFinal*CatchupDef` capabilities are now
deleted. The replacement boundary is
`../WorldCoherent/Source/Terminalization/NuImprecisionWorldCoherentSourceQuotientCloseAccDef.agda`:
one accessibility-ranked, sibling-preserving source terminalizer over the
live proof-relevant quotient edge. Its accumulated-prefix adapter transports
the complete quotient quartet through the inner catch-up, calls the ranked
worker only in the source-value branch, and handles source blame with the two
cast-blame reductions. The Def and adapter pass focused strict checks.

The runtime-sibling value-prefix proof now consumes this ranked boundary
directly and passes strictly. The ordinary 644-line recursive value-prefix
implementation failed a fresh termination check at allocation-prefix re-entry
and the source sequence callback; its earlier passing interface was
cache-stale. Ordinary value catch-up is now a 45-line nonrecursive corollary
of the stronger sibling-preserving contract, using a dummy
`blame ⊑ blame` sibling. This removes the duplicate dispatcher instead of
adding a termination bypass.

The typed source-administration spine lives in
`../Source/Administration/NuImprecisionSourceAdministrationSpine.agda`. It
carries the live QTI derivation at `casts`, `bullet`, and `ν` states, rather
than inventing a false ordinary index between quotient narrowing and
widening. The spine checks strictly. The ranked quotient-close contract still
needs its semantic Proof: source identity, sequence, cancellation,
instantiation allocation, bullet, and terminal-inert leaves remain the next
source-side gate.

The structural `RuntimeOK` projections have also moved from
`../DGG/Core/NuPreservation.agda` to the focused 58-line
`../Core/Properties/NuRuntimeProperties.agda`. Forty-eight consumers now
import the small module directly. This is a canonical invalidation cut, not a
re-exporting wrapper.

The remaining legacy `ν` pattern failure and removed `up⊑upᵀ` consumer are
independent migration/deletion debt, not reasons to restore obsolete
constructors. The isolated non-well-formed selector remains a deletion
candidate once its single test client is classified.

Store-relation structure and endpoint shape remain later stable cuts, but the
operational quotient SCC and the three selector evacuations are higher
priority. Retiring
quotient/experiment files should be deleted rather than split. The
zero-consumer
`MaximalLowerBoundsJunk.agda` has been removed; Git history is the archive.

The remaining direct retired-name counts are `2/1/1/12/7/0` for fused
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
