# Quotient-imprecision migration status

## Authoritative state

**MIGRATION IN PROGRESS — phase 2 complete; phase 3 not started**

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
- `NuImprecisionQuotientBoundarySupport.agda`;
- `NuImprecisionTargetInstantiationCreationDef.agda`; and
- `NuImprecisionEmbeddedTargetInstantiationCreationProperties.agda`.

The selected metatheory sources are:

- `NuImprecisionReductionClosedQuotientTypingExperiment.agda`;
- `NuImprecisionReductionClosedQuotientValueExperiment.agda`;
- `NuImprecisionReductionClosedQuotientTermContextShiftExperiment.agda`;
- `NuImprecisionReductionClosedQuotientSubstitutionExperiment.agda`;
- `NuImprecisionReductionClosedQuotientSingleSubstitutionExperiment.agda`;
- `NuImprecisionReductionClosedCompatibilityRenameExperiment.agda`;
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

`../../QuotientedTermImprecision.agda` is still the live relation, but these
constructor families are marked for removal:

- target-only type application, `ν`, and casted `ν`;
- casted-`ν` shortcuts that ordinary `ν` plus cast rules supersede;
- quotient-indexed application;
- fused `down·up⊑down·upᵀ`; and
- the old quotient-boundary presentation superseded by one paired narrowing
  introduction and one compatible closing widening.

The following modules are live clients or helpers for that retiring grammar.
They may be edited only to migrate or delete their old dependencies:

- `NuImprecisionQuotientArrowComponents.agda`;
- `NuImprecisionQuotientFunctionPairedNarrowingApplicationDef.agda`;
- `NuImprecisionQuotientFunctionPairedNarrowingApplicationProof.agda`;
- `NuImprecisionQuotientFunctionPairedNarrowingApplicationLemma.agda`;
- `NuImprecisionQuotientInstPathProperties.agda`;
- `NuImprecisionQuotientInstView.agda`;
- `NuImprecisionQuotientValue.agda`;
- `NuImprecisionQuotientWideningTransport.agda`;
- `NuImprecisionSourceDownApplicationCompatibleOuter.agda`; and
- `QuotientedTermImprecisionTest.agda`.

`NuImprecisionQuotientToOrdinaryCounterexample.agda` is canonical: it guards
the still-relevant fact that a general quotient edge cannot be converted to
ordinary type imprecision.

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

- delete uninhabited target-only type application, `ν`, and casted-`ν` cases;
- replace source casted-`ν` shortcuts with ordinary source `ν` and cast
  structure;
- migrate exhaustive transports and inversions using the selected prototype
  as the coverage checklist;
- check focused metatheory roots, followed by one public-DGG phase gate.

### Phase 4. Replace the quotient boundary

- promote the single paired-narrowing quotient introduction and compatible
  closing widening;
- connect the allocation-aware function-cast simulation up to reduction;
- migrate value, typing, substitution, world-embedding, and catch-up clients;
- delete quotient application, finite-spine support, and
  `down·up⊑down·upᵀ`;
- check the focused source and target function-cast roots before the public
  DGG phase gate.

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
replacement covers the same live obligation. It is deleted after:

1. its importers have moved;
2. `rg` finds no remaining source references;
3. the focused replacement root passes; and
4. the current phase gate passes.

For already rejected alternatives, phase 1 is the replacement gate; Git
history is sufficient archival evidence. For migration experiments, the
corresponding live theorem is the replacement gate. For retiring live
helpers, the last migrated consumer is the replacement gate. No obsolete
source survives merely as a compatibility aid.

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
