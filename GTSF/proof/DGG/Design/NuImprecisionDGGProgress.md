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
forward and backward simulations over a quotient grammar that is stable under
repeated function casts. The live DGG assembly is paused at a quotient-design
checkpoint. Both the compositional prototype and the smaller
up-to-reduction prototype are strict. The smaller prototype now passes the
relation-level two-function-cast and arbitrary-substitution tests. It now
permits exactly one paired narrowing cast, not a finite spine. A
same-polarity stress test separates an unconditionally expressible
two-narrowing residual from residuals reachable from the live ordinary
relation; the remaining operational test is the allocation-aware catch-up
forced by the active `inst` cast on one permutation route. Neither prototype
has replaced `QuotientedTermImprecision`. The public statement and compiler
boundary are checked, but no complete theorem inhabitant exists yet.

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
- in the compositional candidate, quotient application closure is graded so a
  derivation introduced by the new application rule cannot appear as a source
  or target value.
- in the compositional candidate, repeated paired narrowings are represented
  by a finite cast spine with one total quotient boundary square.
- in the smaller candidate, a quotient boundary contains exactly one paired
  narrowing cast. Additional casts must already be related at an ordinary
  intermediate index or be consumed by bilateral reduction.

## Active up-to-reduction design hypothesis

The compositional quotient prototype is no longer the only candidate for the
live relation.  The smaller-relation hypothesis is:

> Keep quotient imprecision only at one paired narrowing cast and at the
> paired widening boundary that closes its quotient. Do not add
> quotient-indexed application congruence or a fused
> `down·up⊑down·upᵀ` term rule.  Instead, use the existing bilateral weak
> simulation result to reduce through function-cast administration until the
> residuals return to the smaller relation.

The current result algebra already has the required operational shape:
`sourceCatchup` permits multiple source steps and `targetTail` permits multiple
target steps after the leading target step.  The paired function-cast proof
currently chooses a reflexive target tail and relates the immediate
post-`β-↦` applications, which is what creates pressure for the fused rule.
The intended replacement follows the `sim-beta-cast` organization from the
GTLC DGG proof: peel a function cast, catch up the casted argument, recurse on
the underlying function, and restore the result cast.

This hypothesis is successful only if a quotient-aware beta lemma can cross
the lambda endpoint.  In particular, after reducing

$$
((V\langle c_1\mapsto d_1\rangle)
  \langle c_2\mapsto d_2\rangle)\,W
$$

through both function casts and the underlying beta-redex, the substituted
residual must be related using only ordinary imprecision, paired narrowing
casts, and quotient-closing widenings. If an irreducible quotient can remain
embedded in an arbitrary lambda body without reaching such a closing
boundary, reduction alone is insufficient; that is the falsification
criterion for the smaller relation and evidence that a compatible quotient
closure is genuinely necessary.

The first test is isolated from `QuotientedTermImprecision`.  It must cover:

1. a nontrivial paired quotient between differently ordered `∀` types;
2. two successive function casts, not just one;
3. reduction through the underlying identity lambda, so the quotient argument
   is actually substituted;
4. a final derivation in the smaller relation with no quotient-application or
   fused down/application/up constructor; and
5. a negative or blocked arbitrary-body test if the identity case succeeds.

Current result: the relation-level portion succeeds more strongly than
expected. The initial applications, both paired function boundaries, the
twice-closed identity result, and substitution into an arbitrary related
lambda body are all derivable without `down·up⊑down·upᵀ` and without either
quotient-application constructor. After each down/up round trip, the existing
`up⊑upᵀ` rule returns the argument to ordinary QTI, so the existing strict
single-substitution theorem applies directly.

The symmetric pure-reduction picture does not hold, however. For the concrete
`glb-lower-XY`/`glb-lower-YX` routes, the `XY` closing cast is an inert
universal cast while the `YX` closing cast is an active `inst`. Therefore:

$$
\begin{aligned}
((\lambda x.x)\langle\mathit{inner}_{XY}\rangle
  \langle\mathit{outer}_{XY}\rangle)\,W
&\longrightarrow^{3}
W\langle\mathit{down}_{XY}\rangle
 \langle\mathit{up}_{XY}\rangle
 \langle\mathit{down}_{XY}\rangle
 \langle\mathit{up}_{XY}\rangle,\\
((\lambda x.x)\langle\mathit{inner}_{YX}\rangle
  \langle\mathit{outer}_{YX}\rangle)\,W'
&\longrightarrow
((\lambda x.x)\langle\mathit{inner}_{YX}\rangle)
  (W'\langle\mathit{down}_{YX}\rangle)
  \langle\mathit{up}_{YX}\rangle,
\end{aligned}
$$

and the second line must allocate before its next function beta. This does not
falsify the smaller-relation hypothesis: `WeakOneStepResult` already permits
the required target tail and store changes. It identifies the next proof
obligation precisely as the existing quotient-`inst` allocation catch-up
boundary, rather than a missing term-imprecision constructor.

### Single-boundary stress test

The smaller prototype was tightened from a finite narrowing spine to exactly
one paired narrowing cast. All earlier two-function-cast and substitution
examples still pass.

A stronger same-polarity example uses two genuine narrowing stages. Reduction
of the two widening function casts exposes:

$$
\begin{aligned}
W\langle d_1\rangle\langle d_2\rangle
  \langle u_2\rangle\langle u_1\rangle
\quad\text{and}\quad
W'\langle d'_1\rangle\langle d'_2\rangle
  \langle u'_2\rangle\langle u'_1\rangle .
\end{aligned}
$$

The checked results are:

1. both applications reduce to these residuals in three pure steps;
2. the paired prefixes after `d₁,d₂` are related by the compositional
   length-two `NarrowingSpine`;
3. those same prefixes cannot be related by the one-paired-narrowing
   prototype; inversion would require ordinary imprecision between
   `∀X.∀Y.X→Y` and `∀Y.∀X.X→Y`, which is impossible; and
4. the adversarial top pair is not generated by the live ordinary relation.
   Its intermediate function types have exactly the same missing ordinary
   imprecision. Relating the top would already require a
   quotient-to-quotient cast rule.

Therefore this test does **not** yet justify finite narrowing spines in the
simulation invariant. It shows that finite spines add expressiveness, but the
extra example lies outside the current relation's reachable top squares. For
a reachable sequence of ordinary paired function casts, every earlier
narrowing prefix has an ordinary intermediate index and can remain inside the
ordinary premise of the final single paired narrowing.

The normal-coercion `β-seq` audit also supports one narrowing boundary.
Arbitrary sequences of function coercions are normalized by coercion
composition. The surviving quotient-producing narrowing sequences begin with
an active function untag. The existing strict
`inner-sequence-residualᵀ` proof factors that untag into an ordinary cast
relation and reconstructs exactly one quotient-producing tail cast; the
seal-tail alternative is proved impossible. Thus source sequence expansion
does not leave a reachable irreducible two-narrowing quotient.

Target ordinary sequence roots likewise rebuild the two casts through
ordinary imprecision. The still-uninhabited quotient active-value sequence
root concerns a sequence in the *closing widening*, not repeated narrowing.
It should use the target tail and the existing sequence-resume midpoint
machinery; it is not evidence for `NarrowingSpine`.

Conclusion of this checkpoint: retain exactly one paired narrowing cast in the
smaller prototype. Finite narrowing spines remain only in the alternative
compositional prototype and are not currently justified for a reachable DGG
square.

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
| [`NuImprecisionCompositionalQuotientDef.agda`](../../Quotient/NuImprecisionCompositionalQuotientDef.agda) | **completed prototype** | Graded quotient relation, finite narrowing spines, symmetric application, and compatible quotient closing |
| [`NuImprecisionCompositionalQuotientExamples.agda`](../../Quotient/NuImprecisionCompositionalQuotientExamples.agda) | **completed examples** | Exact, nested-application, nontrivial permutation, repeated-cast, quotient-function/argument, and two-function-cast residual checks |
| [`NuImprecisionReductionClosedQuotientDef.agda`](../../Quotient/NuImprecisionReductionClosedQuotientDef.agda) | **completed prototype** | Smaller relation with one paired narrowing boundary, no quotient application, and no fused down/application/up rule |
| [`NuImprecisionReductionClosedQuotientExamples.agda`](../../Quotient/NuImprecisionReductionClosedQuotientExamples.agda) | **completed diagnostic** | Nontrivial two-function-cast relation, identity reduction, arbitrary substitution, and checked active-`inst` allocation boundary |
| [`NuImprecisionSingleNarrowingBoundaryExamples.agda`](../../Quotient/NuImprecisionSingleNarrowingBoundaryExamples.agda) | **completed diagnostic** | Same-polarity three-step reductions, a positive length-two spine, and a checked impossibility result for the single-boundary relation |
| [`NuImprecisionReductionClosedQuotientDesign.md`](NuImprecisionReductionClosedQuotientDesign.md) | **current design hypothesis** | Complete small-relation sketch: one quotient boundary, ordinary-only congruence and substitution, bilateral reduction closure, reachability criterion, and remaining `sim-beta-cast` obligations |
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
- The quotient redesign now has a strict prototype and a focused checked
  example suite. `NarrowingSpine` handles any positive number of paired
  downcasts, both application premises use the quotient relation, and the
  ordinary closing layer retains a quotient boundary square plus hereditary
  compatibility through the selected representatives.
- The examples check exact embedding, left- and right-nested applications,
  quotient closing after application, one and two casts through the
  incomparable `D`/`E` routes, a quotient-related function consuming the
  two-cast quotient argument, representative-aware closing of a nontrivial
  `E ≈∀ D` quotient, and the complete residual shape produced by two
  successive function-cast reductions.
- The endpoint-MLB fixture now supplies the explicit `NonVar` witness required
  by the strengthened `ν` imprecision constructor; this removes a stale-source
  failure that had been hidden by an older Agda interface.
- The rationale, formal rules, tested reduction shape, and remaining
  quotient-to-quotient cast-square question are recorded in
  [`NuImprecisionCompositionalQuotientDesign.md`](NuImprecisionCompositionalQuotientDesign.md).
- The smaller quotient prototype has no quotient-indexed application
  constructor, no fused down/application/up constructor, and now no finite
  narrowing spine. Its quotient constructor contains exactly one paired
  narrowing cast. The earlier strict example still constructs the initial
  two-function-cast application with ordinary application, constructs both
  function boundaries from paired down/up rules, reduces the identity route
  through three beta steps, and relates the final twice-closed argument.
- The same example feeds that twice-closed argument to the canonical strict
  single-substitution theorem for an arbitrary related lambda body. This
  discharges the original substitution falsification test: once a quotient is
  closed, it is ordinary QTI and does not require a compositional quotient
  premise inside the body.
- The example also proves that the permuted `YX` closing cast is not inert.
  Its evaluation must enter the allocation-aware quotient-`inst` catch-up
  machinery before the second function beta. The operational hypothesis
  remains open exactly at that already-known semantic boundary.
- The same-polarity stress test proves that two genuine narrowing prefixes
  require a finite spine if considered without a reachability premise.
  It also exposes why this is not yet a counterexample to the smaller
  simulation relation: the top pair already needs an absent
  quotient-to-quotient cast rule. The checked negative result therefore
  rejects that pair as a simulation counterexample.
- The reachable source `β-seq` case is already handled by the strict
  `inner-sequence-residualᵀ` factorization: an active untag becomes ordinary
  imprecision and the remaining tail uses one paired narrowing boundary.
  The target quotient sequence obligation lies on the closing-widening side
  and belongs to target-tail resumption, not to finite narrowing spines.
- The revised whole-design sketch is recorded in
  [`NuImprecisionReductionClosedQuotientDesign.md`](NuImprecisionReductionClosedQuotientDesign.md).
  It treats quotient imprecision as a scoped intermediate judgment with one
  paired narrowing introduction and one compatible paired widening
  elimination. Application, polymorphism, ordinary casts, and substitution
  remain in the ordinary relation; the simulation conclusion permits
  bilateral reduction before requiring its final ordinary horizontal edge.
  The note also records that the same-polarity two-narrowing stress test lacks
  an ordinarily related top row and therefore does not refute this smaller
  design.

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

1. State the allocation-aware quotient `sim-beta-cast` contract directly in
   terms of the existing world-coherent weak result: the inert route supplies
   the source catch-up, while the active `inst` route uses the target tail and
   transports the quotient through the resulting store extension.
2. Connect that contract to the existing paired-widening target
   pending-allocation machinery. The immediate leaf is the quotient-`inst`
   residual already counted among the four ordinary/generated down/up holes in
   `NuImprecisionCatchupScratch`; do not add a term rule to bypass it.
3. Complete the two-function-cast operational square and confirm that its
   related endpoint is the ordinary QTI derivation consumed by
   `two-round-trips-substitutionᵀ`.
4. Discharge the target quotient closing-widening `β-seq` root through the
   existing target-tail sequence-resume midpoint machinery. Do not add a
   narrowing spine for this widening-side obligation.
5. If these succeed, derive the live function-cast simulation without
   `down·up⊑down·upᵀ` or quotient application and begin removing those
   constructors in a separate migration. If allocation catch-up instead
   produces an irreducible quotient embedded outside a closing boundary,
   record that strict counterexample and return to the compositional design.
6. Prove source and target typing projections for the smaller ordinary and
   one-boundary quotient judgments. Re-run value, `No•`, and terminal
   inversion using the fact that the quotient judgment has exactly one
   constructor.
7. Test the smaller design on valid ordinary top rows with arbitrary lambda
   bodies, nested reachable function casts, source and target cast sequences,
   and active target `inst`. Every test must exhibit its initial ordinary term
   imprecision derivation before its reduction endpoints are considered.
8. Keep the compositional quotient prototype as the fallback. Reintroduce
   quotient application, finite narrowing spines, or a quotient-to-quotient
   cast square only after a strict counterexample shows a derivable ordinary
   top row whose reductions cannot reach an ordinary-related join.
9. Restore hereditary `PairedWideningCompatible`: replace the broad
   `compatible-source-inert` fallback with the target-active case, preserve
   function and universal compatibility recursively, and retain the
   target-inert bridge. Then restore both function-beta consumers and the
   terminal-forward integration check.
10. Add the missing paired-lambda frame-view
   `down·up⊑down·upᵀ` case and restore its focused strict-spine check.
11. Migrate the other six known-incomplete strict proofs to the current
   uniqueness, binder-transport, compatibility, and `down·up⊑down·upᵀ`
   interfaces.
12. Finish quotient transport normalization and the crossed binary
   runtime-sibling catch-up invariant.
13. Prove the source function-cast `β` and `β-↦` value roots using the
   up-to-reduction `sim-beta-cast` argument rather than a quotient application
   or spine-length-specific term rule.
14. Inhabit the remaining exact active-synchronization root records.
15. Assemble the exhaustive prefix-aware world-coherent backward one-step
   dispatcher and restore a practical green backward strict-spine check.
16. Supply that strict dispatcher to both backward terminal engines.
17. Complete the remaining forward engine contracts, invoke the strict terminal
   integration proof, and construct `GradualDGG`.
18. Promote any still-needed generic scratch clauses through strict
   `Def`/`Proof`/`Lemma` boundaries and delete the scratch module.

## Validation

Routine source audits:

    make quotient-design-check
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
