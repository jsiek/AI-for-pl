# Nu-imprecision DGG progress

This is the current dashboard for the proof from
[`QuotientedTermImprecision`](../../../QuotientedTermImprecision.agda) to the
public [`GradualDGG`](../../../DynamicGradualGuarantee.agda) statement. It is
deliberately not an append-only proof-search transcript. Superseded attempts
are removed from this file and remain available through Git history.

Here, **completed** means that the owned declaration has passed a focused Agda
check without holes or permissive options. **Conditional** means that a strict
higher-order proof is complete but one or more supplied semantic contracts do
not yet have canonical strict inhabitants. **Partial** means that explicit
holes or incomplete coverage remain.

## Current objective

Construct a strict inhabitant of `GradualDGG` by completing the world-coherent
forward and backward simulations over the repaired QTI grammar. The public
statement and compiler boundary are checked, but no complete theorem inhabitant
exists yet.

The current proof uses these invariants:

- `GenSafe` and `InstSafe` keep eager projections and tags outside
  generalization and instantiation.
- `PairedWideningCompatible` records the exact cross-cast compatibility needed
  by paired widening.
- source-only `ν` indices remain source-only through ordinary source
  allocation; matched `∀ⁱ` indices are introduced only by a justified
  replacement boundary.
- world-coherent results preserve source-name exclusivity, assumption
  membership uniqueness, store well-formedness, and relational-store lineage.
- no strict spine may transitively import a module enabling
  `--allow-unsolved-metas` or `--allow-incomplete-matches`.

## Trusted proof boundaries

| Boundary | Status | Role |
|---|---|---|
| [`DynamicGradualGuarantee.agda`](../../../DynamicGradualGuarantee.agda) | **completed statement** | Public gradual-term observation theorem type |
| [`NuDGGStrictSpine.agda`](../Core/NuDGGStrictSpine.agda) | **completed strict architecture** | Hole-free operational DGG contracts and shared support |
| [`NuDGGUnassembledProofsStrictSpine.agda`](../Core/NuDGGUnassembledProofsStrictSpine.agda) | **completed strict aggregate** | Eleven checked higher-order `Proof` roots plus the completed right/source-`∀` aggregate, all awaiting canonical `Lemma` consumers |
| [`NuDGGTerminalForwardStrictSpine.agda`](../TerminalForward/NuDGGTerminalForwardStrictSpine.agda) | **partial strict architecture** | Source-safe forward cone; its paired-widening value dependency has an uncovered compatibility case |
| [`NuDGGTerminalBackwardStrictSpine.agda`](../TerminalBackward/NuDGGTerminalBackwardStrictSpine.agda) | **completed strict architecture** | Backward target-trace contracts and completed semantic leaves |
| [`NuImprecisionOneStepDef.agda`](../../OneStep/NuImprecisionOneStepDef.agda) | **completed `Def`** | Target-oriented indexed one-step simulation contract |
| [`NuImprecisionWorldCoherentOneStepDef.agda`](../../WorldCoherent/Core/NuImprecisionWorldCoherentOneStepDef.agda) | **completed `Def`** | World-coherent one-step contract used by the terminal proof |
| [`NuDGGTerminalForwardIntegrationProof.agda`](../TerminalForward/NuDGGTerminalForwardIntegrationProof.agda) | **partial** | Intended route from forward/backward contracts to `GradualDGG`; currently reaches an uncovered paired-widening compatibility case |
| [`NuDGGTerminalBackwardValueProof.agda`](../TerminalBackward/NuDGGTerminalBackwardValueProof.agda) | **conditional** | Fuel induction for target-value traces |
| [`NuDGGTerminalBackwardBlameWorldCoherentProof.agda`](../TerminalBackward/NuDGGTerminalBackwardBlameWorldCoherentProof.agda) | **conditional** | Fuel induction for target-blame traces |

The strict architecture modules state exactly what remains without importing
the permissive legacy dispatcher. Passing one of these spines proves interface
fit, not that every semantic contract has a canonical inhabitant.

## Active partial modules

Only these DGG-path proof modules are intentionally permissive:

| Module | Remaining work |
|---|---|
| [`NuImprecisionCatchupScratch.agda`](../../Catchup/Core/NuImprecisionCatchupScratch.agda) | Twelve explicit value-catch-up holes plus an incomplete generic one-step coverage audit |
| [`NuImprecisionOneStepTargetCastRoots.agda`](../../OneStep/NuImprecisionOneStepTargetCastRoots.agda) | Eight generic target-cast root holes |
| [`NuImprecisionOneStepTargetConversionRoots.agda`](../../OneStep/NuImprecisionOneStepTargetConversionRoots.agda) | One generic target-conversion root hole |

These modules are outside all canonical strict cones. New strict work must use
their `Def` contracts or extracted strict leaves, never import them merely to
make a theorem facade appear complete.

Seven non-permissive, importer-free `Proof` modules had been classified as
completed by filenames and source scans but fail focused strict Agda checks.
They are excluded from `NuDGGUnassembledProofsStrictSpine` and recorded by
`KNOWN_INCOMPLETE_PROOF_MODULES` in the import audit:

| Module | Exposed obligation |
|---|---|
| [`NuDGGTerminalForwardIntegrationProof.agda`](../TerminalForward/NuDGGTerminalForwardIntegrationProof.agda) | `compatible-source-inert` is uncovered in paired-widening function beta |
| [`NuImprecisionWorldCoherentFinalPairedWideningCatchupProof.agda`](../../WorldCoherent/Final/Paired/NuImprecisionWorldCoherentFinalPairedWideningCatchupProof.agda) | Uses compatibility constructors removed by the current `PairedWideningCompatible` definition |
| [`NuImprecisionWorldCoherentFinalSourceNuCastSourceOnlyIndexCatchupProof.agda`](../../WorldCoherent/Final/SourceNu/NuImprecisionWorldCoherentFinalSourceNuCastSourceOnlyIndexCatchupProof.agda) | Supplies store well-formedness where assumption-membership uniqueness is now required |
| [`NuImprecisionWorldCoherentFinalSourceNuSourceOnlyIndexCatchupProof.agda`](../../WorldCoherent/Final/SourceNu/NuImprecisionWorldCoherentFinalSourceNuSourceOnlyIndexCatchupProof.agda) | Supplies store well-formedness where assumption-membership uniqueness is now required |
| [`NuImprecisionWorldCoherentSourceNarrowCatchupProof.agda`](../../WorldCoherent/Source/CastCatchup/NuImprecisionWorldCoherentSourceNarrowCatchupProof.agda) | Omits the new assumption-membership uniqueness component of world-coherent catch-up |
| [`NuImprecisionWorldCoherentSourceNuCastCatchupProof.agda`](../../WorldCoherent/Source/NuCatchup/NuImprecisionWorldCoherentSourceNuCastCatchupProof.agda) | Uses ordinary coercion transport where transport under type binders is required |
| [`NuImprecisionWorldCoherentSourceNuCastRuntimeSiblingCatchupProof.agda`](../../WorldCoherent/Source/NuCatchup/NuImprecisionWorldCoherentSourceNuCastRuntimeSiblingCatchupProof.agda) | Reaches an uncovered `down·up⊑down·upᵀ` allocation-transport case |

The separate
[`NuImprecisionPairedTargetClosingStrictSpine.agda`](../../PairedLambda/Terminal/NuImprecisionPairedTargetClosingStrictSpine.agda)
is also source-safe but not currently a completed aggregate. Its focused check
reaches an uncovered `down·up⊑down·upᵀ` case in
`NuImprecisionPairedLambdaTargetClosingFrameViewProof`. This proof is not in
the importer-free list because later paired-lambda proofs import it.

The scratch declaration `weak-one-step-indexed-simulationᵀ` is typed directly
by `WeakOneStepIndexedSimulationᵀ`. Its permanent implementation belongs in
`proof/OneStep/NuImprecisionOneStepProof.agda` and must:

1. take already-terminal value catch-up and unfinished semantic root families
   through complete higher-order contracts;
2. contain no permissive option;
3. pass exhaustive QTI/reduction coverage checking;
4. move each scratch clause exactly once; and
5. support a canonical `Lemma` only after every supplied implementation is
   strict.

The twelve scratch holes are not hidden one-step statement holes. Four are the
plain and eager quotient-`inst` residuals for ordinary and generated down/up
catch-up. The other eight are source `α`, source-only `ν`, source-only
`νcast`, source narrowing, source widening, paired conversion, reveal
conversion, and conceal conversion value-catch-up cases.

## Completed recent work

- The QTI repair added the exact post-`β-inst` relation needed after paired
  target allocation. The positive closed regression is now named
  [`NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedPostBetaCatchupRegression.agda`](../../WorldCoherent/Right/Target/WidenNarrow/NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedPostBetaCatchupRegression.agda).
- Source-inert paired widening now carries an explicit compatibility witness,
  with rename, allocation, and atomic-reindex transport.
- Paired active-value, quotient active-value, and quotient target-down
  dispatchers reduce their reduction grammars to explicit exact semantic root
  records. They do not claim those remaining records are inhabited.
- The `down·up⊑down·upᵀ` value cases close by value inversion.
- The generic one-step scratch implementation now references the canonical
  `WeakOneStepIndexedSimulationᵀ` contract instead of duplicating its
  statement.
- The repaired source-`gen`/target-ground negative regression remains in
  [`NuImprecisionSourceGenTargetGroundAgreementCounterexample.agda`](../../Source/Core/NuImprecisionSourceGenTargetGroundAgreementCounterexample.agda).
- The first strict importer-free `Proof` aggregate now type-checks. Building it
  distinguished eleven genuinely completed higher-order roots from seven
  stale files that only looked complete to a source scan, and it incorporates
  the independently checked right/source-`∀` strict aggregate.

## Counterexample policy and audit

Checked counterexamples are retained when they guard a live premise or refute a
tempting but false factorization. They are not obsolete merely because no
module imports them.

The 2026-07-25 audit retained the live endpoint-MLB, quotient-to-ordinary,
paired-lambda closing, right-opening, source midpoint, source exclusivity,
paired-widening compatibility, target-untag uniqueness, and immediate
post-`β-inst` negative regressions. The repaired post-`β-inst` catch-up example
was renamed from `Counterexample` to `Regression` because it now constructs the
positive relation.

The old mismatched `gen`/untag counterexamples were deleted. Their narrowing
witnesses are not constructible under `GenSafe`, and the compiler-level
behavior is covered by
[`GenSafeMismatchBlameRegression.agda`](../../Compilation/GenSafeMismatchBlameRegression.agda).

## Repository cleanup completed on 2026-07-25

- Deleted the obsolete permissive `TermNarrowing`-based DGG proof and its
  private catch-up, store-narrowing, term-substitution, seal-inversion, and
  proof-search note cluster.
- Deleted the old terminal skeleton, permissive forward shell, milestone
  wrapper, and scratch-dependent backward theorem facades. The strict
  `Def`/higher-order `Proof` boundaries remain.
- Deleted five mismatch counterexample modules invalidated by `GenSafe`.
- Renamed the positive paired post-`β-inst` catch-up regression.
- Added [`scripts/check_agda_imports.py`](../../../scripts/check_agda_imports.py)
  to enforce strict-cone import safety and report importer-free review
  candidates.
- Added `NuDGGUnassembledProofsStrictSpine` for the eleven strictly checked
  higher-order `Proof` roots that previously lacked a canonical consumer, plus
  the completed right/source-`∀` aggregate. Seven other importer-free
  candidates failed focused checks and are tracked explicitly as incomplete.
  The audit now fails if a new completed strict `Proof` is left unaggregated or
  if a known-incomplete proof acquires an importer before repair.
- Compacted this ledger. The former 14,000-line chronology remains available
  in Git history rather than on the active proof surface.

## Current proof plan

1. Restore hereditary `PairedWideningCompatible`: replace the broad
   `compatible-source-inert` fallback with the target-active case, preserve
   function and universal compatibility recursively, and retain the
   target-inert bridge. Then restore both function-beta consumers and the
   terminal-forward integration check.
2. Add the missing paired-lambda frame-view
   `down·up⊑down·upᵀ` case and restore its focused strict-spine check.
3. Migrate the other six known-incomplete strict proofs to the current
   uniqueness, binder-transport, compatibility, and `down·up⊑down·upᵀ`
   interfaces.
4. Finish quotient transport normalization and the crossed binary
   runtime-sibling catch-up invariant.
5. Prove the source-down-application `β` and `β-↦` value roots.
6. Inhabit the remaining exact active-synchronization root records.
7. Assemble the exhaustive prefix-aware world-coherent backward one-step
   dispatcher and restore a practical green backward strict-spine check.
8. Supply that strict dispatcher to both backward terminal engines.
9. Complete the remaining forward engine contracts, invoke the strict terminal
   integration proof, and construct `GradualDGG`.
10. Promote any still-needed generic scratch clauses through strict
   `Def`/`Proof`/`Lemma` boundaries and delete the scratch module.

## Validation

Routine source audits:

    make dgg-check
    agda -v0 proof/OneStep/NuImprecisionOneStepDef.agda
    agda -v0 proof/DGG/TerminalBackward/NuDGGTerminalBackwardStrictSpine.agda

The import audit currently checks five canonical strict roots and fails if
their transitive local cones contain a permissive module, if a local
`proof.*` import does not resolve, or if a completed strict `Proof` is neither
consumed nor aggregated. Its general importer-free list is review-only:
independent strict regressions, examples, and check roots must be classified
explicitly rather than deleted mechanically.

The aggregate and import audit pass. The terminal-forward strict spine is
source-safe but its focused Agda check currently fails at the
`compatible-source-inert` paired-widening function-beta case recorded above.
The source inventory sees 369 strict-looking `Proof` modules: 156 have no
transitive canonical `Lemma` consumer, 149 are reachable from an explicit
strict inventory spine, seven are explicitly known incomplete, and none are
uninventoried. Focused Agda checks, not these source counts, establish
completion.

Do not use `All.agda` as the DGG completion criterion. It includes independent
and historical development surfaces. The final completion check is the strict
public DGG dependency cone plus the focused forward and backward terminal
spines.
