# GTSF repository checks

Scripts in this directory inspect the GTSF development without modifying proof
sources.  Run them from `GTSF/`; each script also resolves the same directory
when invoked elsewhere.

## Agda import audit

Run:

    python3 scripts/check_agda_imports.py

Or run the audit together with the completed higher-order DGG proof aggregate:

    make dgg-check

The audit parses imports among canonical GTSF `.agda` files: top-level
language modules and the `proof/` tree.  Local experiment directories such as
`ignore/` are outside this surface.  The audit performs four checks:

1. It fails if a canonical module imports a missing local `proof.*` module.
   This catches obsolete imports left behind by a rename or deletion.
2. It fails if a canonical strict DGG root transitively imports a module whose
   `OPTIONS` pragma enables `--allow-unsolved-metas` or
   `--allow-incomplete-matches`.  This is a source audit: passing
   `--no-allow-unsolved-metas` on an Agda command line does not make a local
   permissive option harmless.
3. It reports, but does not fail for, proof modules with zero in-repository
   importers.  These are review candidates, not automatic deletion targets.
4. It fails if a strict-looking `*Proof.agda` module is neither transitively
   consumed by a canonical `Lemma` nor reachable from an explicit strict proof
   inventory spine. Importer-free modules known to fail strict Agda checking
   are instead listed explicitly as
   `KNOWN_INCOMPLETE_PROOF_MODULES`; the audit fails if another module starts
   importing one of them before it is repaired.

The canonical strict DGG roots are:

- `DynamicGradualGuarantee.agda`;
- `proof/DGG/Core/NuDGGStrictSpine.agda`;
- `proof/DGG/Core/NuDGGUnassembledProofsStrictSpine.agda`;
- `proof/DGG/TerminalBackward/NuDGGTerminalBackwardStrictSpine.agda`; and
- `proof/DGG/TerminalForward/NuDGGTerminalForwardStrictSpine.agda`.

`NuDGGUnassembledProofsStrictSpine` is the explicit aggregate for completed
higher-order proof modules whose semantic dependencies are still theorem
parameters and which therefore do not yet have canonical `Lemma` consumers.
The aggregate itself is a strict Agda check, not a source-only classification.
Remove an import from it when the corresponding proof is promoted.

The proof-inventory audit also recognizes the focused DGG, terminal-forward,
terminal-backward, paired-lambda, and right/source-`∀` strict spines. Reachable
inventory membership prevents a proof from being lost, but does not by itself
claim completion: each spine still needs a focused Agda check. In particular,
the paired-lambda spine currently exposes a missing
`down·up⊑down·upᵀ` frame-view case.

The known-incomplete list currently records one importer-free `Proof`
module that a filename/source scan had misclassified as completed:

- `proof/DGG/TerminalForward/NuDGGTerminalForwardIntegrationProof.agda`;

The audit excludes the following intended independent roots from its
zero-importer report.  This list is explicit rather than inferred from
filenames, so retaining a regression or counterexample remains a reviewed
decision:

- `proof/Compilation/CompileCanonicalDownCompatibilityExperiment.agda`;
- `proof/Compilation/CompileCanonicalPendingCloseExperiment.agda`;
- `proof/Compilation/CompileDynamicApplicationTest.agda`;
- `proof/Compilation/GenSafeMismatchBlameRegression.agda`;
- `proof/Core/Permutation/ForallPermutationTest.agda`;
- `proof/DGG/Design/EndpointMLBSelectedRouteShapeSquareCounterexample.agda`;
- `proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`;
- `proof/EndpointMLB/Core/MLBGlbCounterexample.agda`;
- `proof/EndpointMLB/Core/MLBGlbExample.agda`;
- `proof/EndpointMLB/Core/MlbTypeTest.agda`;
- `proof/EndpointMLB/Simple/EndpointCanonicalMLBSimpleFactorCounterexample.agda`;
- `proof/EndpointMLB/Simple/EndpointCanonicalMLBSimpleTest.agda`;
- `proof/PairedLambda/Conversions/NuImprecisionPairedLambdaTargetClosingLambdaLambdaConversionRotationCounterexample.agda`;
- `proof/PairedLambda/Core/NuImprecisionPairedLambdaTargetClosingRelationCounterexample.agda`;
- `proof/PairedLambda/Terminal/NuImprecisionPairedTargetClosingStrictSpine.agda`;
- `proof/Quotient/NuImprecisionQuotientToOrdinaryCounterexample.agda`;
- `proof/Right/Core/NuImprecisionRightOpenedInstantiationIndexCounterexample.agda`;
- `proof/Right/SourceAll/ClosingValues/NuImprecisionRightSourceAllStrictSpine.agda`;
- `proof/Source/CastSequence/NuImprecisionSourceCastSequenceMidpointCounterexample.agda`;
- `proof/Source/Core/NuImprecisionSourceGenTargetGroundAgreementCounterexample.agda`;
- `proof/Source/Core/NuImprecisionSourceOnlyContextFactorCounterexample.agda`;
- `proof/Source/SealTag/NuImprecisionSourceSealCancellationCounterexample.agda`;
- `proof/WorldCoherent/Right/Target/WidenNarrow/NuImprecisionWorldCoherentRightTargetNarrowUntagRootCounterexample.agda`;
- `proof/WorldCoherent/Right/Target/WidenNarrow/NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedPostBetaCatchupRegression.agda`; and
- the five canonical strict DGG roots listed above.

Both configured lists are also constants near the top of
`check_agda_imports.py`.  The audit fails when a listed module is missing, so a
rename or deliberate deletion must update the reviewed list and this
documentation together.
