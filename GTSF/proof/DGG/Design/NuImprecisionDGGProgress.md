# Nu-imprecision DGG progress

This is the current dashboard for the proof from
[`QuotientedTermImprecision`](../../../QuotientedTermImprecision.agda) to the
public [`GradualDGG`](../../../DynamicGradualGuarantee.agda) statement. It is
deliberately not an append-only proof-search transcript. Superseded attempts
are removed from this file and remain available through Git history.

## Obsidian math rendering convention

Use `$$` delimiters for every LaTeX display. Keep each display to one ordinary
formula: do not use multiline environments such as `aligned`, `array`, or
`gathered`, because they fail in at least one of Obsidian and the Codex app.
Present a reduction/imprecision diagram as consecutive single-formula
displays, with the top relation, each reduction step, and the final relation
shown separately. Write `\leftarrow` instead of `\mapsfrom`, and keep a blank
line before and after each display.

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
relation. The allocation-aware target-`inst` test is now complete: the valid
top row and target trace need no fused final edge, but the final stable values
cannot be related by ordinary source-only-lambda and target-cast rules. The
matched body relation, creation equation, and allocation lineage form the
smallest checked residual. The smaller relation is now definitionally
independent of live QTI: its former `ordinaryᴿ` embedding has been removed,
and its ordinary fragment has explicit constructors. Exact creation is now
one of those constructors. A focused transport experiment recovers its
canonical renamed/store-embedded behavior and exposes one missing invariant
in the old generalized fusion spine: the final index must equal the
transported creation index rather than be arbitrary. The unsafe generic
renaming closure has been removed and replaced by a creation-specific
canonical transport edge whose endpoints are proved terminal. Neither
prototype has replaced `QuotientedTermImprecision`. The public statement and
compiler boundary are checked, but no complete theorem inhabitant exists yet.

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
- the smaller candidate has no target-only type-application or `ν` rule.
  Their pre-allocation index and independently opened body index are
  inconsistent; real target-only `inst` allocation is crossed by target
  reduction before the final ordinary relation is required.
- target-only `inst` catch-up retains a `TargetInstantiationCreation`
  residual: matched body imprecision, target cast typing, the index
  composition equation, and store lineage into the right-extended world.
  Up-to-reduction removes transient allocation edges but not this final
  semantic creation case.
- endpoint transport of an exact creation edge produces the canonical renamed
  imprecision index. Any client that asks for another proof-relevant index
  must provide an equality to that canonical index.
- the smaller relation has no generic renaming constructor. Arbitrary
  well-scoped renamings may identify distinct seal names and change which
  reduction rule applies.
- only target-instantiation creation may cross the current canonical transport
  boundary. Both transported endpoints are values, so its source- and
  target-leading simulation cases are impossible.

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

The implemented smaller prototype now has its own ordinary grammar.
`ordinaryᴿ` has been deleted, and neither the smaller definition nor its
neutral quotient support imports the live term-imprecision relation.  The
target-instantiation test constructs both its initial and final rows in this
independent relation.  `TargetInstantiationCreation` is parametric in its
matched body relation, so the same residual can be checked with either
relation without importing one into the other.

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

### Target-only `ν` index audit

The live target-only `ν` constructor records four pieces of evidence:

$$
\begin{aligned}
q &: \Phi \mathbin{;} \Delta_L
  \vdash B \mathrel{\sqsubseteq} \forall C'
  \dashv \Delta_R,\\
r &: \mathord{\uparrow_R}\Phi \mathbin{;} \Delta_L
  \vdash B \mathrel{\sqsubseteq} C'
  \dashv \operatorname{suc}(\Delta_R),\\
r[0 \mapsto {\uparrow A}]^R
  &\doteq \operatorname{lift}^{R}(p),\\
s &: C' \longrightarrow \mathord{\uparrow}B'.
\end{aligned}
$$

Here the last line records only the endpoints of the target reveal
conversion.  The first two lines already imply contradiction.  The strict
[`NuImprecisionTargetBulletIndexCycleLemma.agda`](../../NuCore/Misc/NuImprecisionTargetBulletIndexCycleLemma.agda)
proves the general statement by right-lifting `q`, pairing it with `r`, and
applying the exhaustive common-target-extension obstruction.  Its focused
Agda check passes without postulates, holes, or permissive options.

The example audit found no closed positive construction of the target-only
`ν`, casted-`ν`, or target-only type-application rules.  All apparent uses
either pattern-match an assumed derivation, transport it conditionally, or
implement a semantic root whose `q` and `r` hypotheses are themselves
uninhabited.  The concrete
[`NuImprecisionRightOpenedInstantiationIndexCounterexample.agda`](../../Right/Core/NuImprecisionRightOpenedInstantiationIndexCounterexample.agda)
exhibits the smallest failed opening: a matched target universal cannot be
reopened as an independent target-only binder.

Target-only allocation is nevertheless operationally reachable inside target
`inst` administration.  The positive
[`NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedPostBetaCatchupRegression.agda`](../../WorldCoherent/Right/Target/WidenNarrow/NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedPostBetaCatchupRegression.agda)
uses the target trace

$$
\langle\mathsf{inst}\rangle
\mathbin{;}
\mathsf{bind}\ \star
\mathbin{;}
\beta_{\forall}
$$

and establishes a live-QTI edge only after that trace.  That final edge uses
the fused `Λ⊑instβᵀ` constructor, so the regression does not yet validate the
smaller ordinary relation by itself.

The tighter positive invariant suggested by this example is a
target-instantiation creation square:

$$
\left\lfloor \forall^{\,i}q_{\mathrm{body}} \right\rfloor
\mathbin{;}
\left\lfloor \mathsf{inst}\ B'\ s \right\rfloor
\mathrel{\cong}
\left\lfloor p_{\mathrm{final}} \right\rfloor.
$$

It retains the matched body relation before allocation, the target
conversion, the necessarily source-only final index, and the right-allocation
store lineage.  It contains no independently opened `r`.

The strict
[`NuImprecisionTargetInstantiationCreationExamples.agda`](../../Quotient/NuImprecisionTargetInstantiationCreationExamples.agda)
now completes this test. It checks the initial ordinary top relation and the
complete target trace without using the fused final constructor. It also
proves that factoring the final edge through the ordinary source-only-lambda
and target-cast rules would require

$$
((0 \mathrel{\sqsubseteq} \star)::[])
\mathbin{;} 1
\vdash
(\alpha\to\alpha)
\mathrel{\sqsubseteq}
(\alpha\to\alpha)
\dashv 1,
$$

whose variable premises are impossible. The companion
[`NuImprecisionTargetInstantiationCreationDef.agda`](../../Quotient/NuImprecisionTargetInstantiationCreationDef.agda)
packages exactly the surviving matched-body, cast, composition, and
allocation-lineage evidence. The focused modules type-check without
postulates, holes, or permissive options.

Conclusion: up-to-reduction eliminates the transient target-only `ν` and
runtime-bullet edges, but not the final semantic creation case. Under the
current `WeakOneStepResult` and public DGG conclusions, the large fused
constructor should be replaced by a small exact creation constructor fed by
this residual, with renaming, store embedding, and endpoint transport proved
separately. Eliminating even the exact constructor would require a
creation-saturated final relation, which relocates rather than removes the
same case.

The live relation is not changed at this checkpoint.  Deleting the
uninhabited constructors and their conditional transport cases belongs in the
later relation migration. That migration should first introduce the exact
creation constructor and prove that it supports the generalized live
consumers before deleting `Λ⊑instβᵀ`.

### Live target-instantiation consumer audit

The direct positive consumers of `Λ⊑instβᵀ` now fall into four groups.

- The direct paired-lambda post-beta context uses identity renaming, the exact
  allocated store, and the canonical index `⊑-target-lift-rightᵢ f`. It is
  ready for the first live migration.
- The pure and paired universal-fusion spine contracts formerly retained an
  arbitrary final index. Both now require equality with the canonical
  endpoint-transported creation index, and their strict folds type-check.
- The paired-lambda closing leaf view still extracts an arbitrary final index
  from the old fused constructor. Its view, handler, and reconstruction
  contracts must be strengthened together; the required equality cannot be
  derived from the old constructor.
- The unfinished target widening `β-inst` root cases are indirect consumers.
  Their current contracts retain the outer relation and cast typing but drop
  the cast-shape composition equation and the matched body/allocation
  witnesses needed to construct exact creation.

The permissive catch-up scratch concealed two more old-constructor cases.
`left-catchup-indexed-prefixᵀ` now routes the stored final source value through
ordinary value catch-up. `weak-one-step-indexed-simulationᵀ` now rejects its
leading target step using the stored final target value and `value-no-step`.
The scratch remains permissive because of its twelve previously recorded
holes and other incomplete constructor coverage, not because these two cases
are absent.

The generic `rename-storeᴿ` experiment failed its operational audit.
`TyRenameWf` preserves scope but not injectivity, and `RelStoreEmbeddingⁱ`
does not provide a renaming inverse. A renaming may identify distinct seals
and change `tag-untag-bad` into `tag-untag-ok`, so arbitrary reduction
reflection is false. The constructor has been removed. The replacement
`target-instantiation-transportᴿ` applies only to exact creation, fixes the
canonical index, and carries exact endpoint typings. The strict terminal
experiment proves that both transported endpoints are values and cannot take
a leading step.

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
| [`NuImprecisionQuotientBoundarySupport.agda`](../../Quotient/NuImprecisionQuotientBoundarySupport.agda) | **completed support** | Cast-mode and hereditary widening evidence with no dependency on a term-imprecision relation |
| [`NuImprecisionReductionClosedQuotientDef.agda`](../../Quotient/NuImprecisionReductionClosedQuotientDef.agda) | **completed prototype** | Independent smaller ordinary grammar, exact creation, creation-specific canonical endpoint transport, one paired narrowing boundary, and no generic renaming, quotient application, or fused down/application/up rule |
| [`NuImprecisionReductionClosedQuotientExamples.agda`](../../Quotient/NuImprecisionReductionClosedQuotientExamples.agda) | **completed diagnostic** | Nontrivial two-function-cast relation, identity reduction, arbitrary substitution, and checked active-`inst` allocation boundary |
| [`NuImprecisionSingleNarrowingBoundaryExamples.agda`](../../Quotient/NuImprecisionSingleNarrowingBoundaryExamples.agda) | **completed diagnostic** | Same-polarity three-step reductions, a positive length-two spine, and a checked impossibility result for the single-boundary relation |
| [`NuImprecisionTargetInstantiationCreationDef.agda`](../../Quotient/NuImprecisionTargetInstantiationCreationDef.agda) | **completed prototype** | Relation-parametric matched-body, cast-composition, and right-allocation residual |
| [`NuImprecisionTargetInstantiationCreationExamples.agda`](../../Quotient/NuImprecisionTargetInstantiationCreationExamples.agda) | **completed diagnostic** | Independent smaller initial/final rows, target allocation trace, creation residual, and strict refutation of ordinary final-edge factorization |
| [`NuImprecisionTargetInstantiationTransportExperiment.agda`](../../Quotient/NuImprecisionTargetInstantiationTransportExperiment.agda) | **completed diagnostic** | Canonical renaming/store-embedding transport and endpoint replacement with an explicit final-index coherence equality |
| [`NuImprecisionTargetInstantiationTransportSpineExperiment.agda`](../../Quotient/NuImprecisionTargetInstantiationTransportSpineExperiment.agda) | **completed diagnostic** | Strict recursive fold for arbitrarily nested exact creation and canonical endpoint transport |
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

- Removed `ordinaryᴿ` and changed the smaller relation's worlds, stores, and
  contexts from fixed parameters to indices. Its variable, abstraction,
  application, polymorphic, constant, primitive, one-sided cast, paired
  widening, exact creation, and quotient-boundary cases are now independent
  constructors.
- Split `SpineCastMode` and `QuotientWideningCompatible` into
  `NuImprecisionQuotientBoundarySupport`, which imports no term relation.
- Made `TargetInstantiationCreation` parametric in the matched body relation
  and used it as the sole premise of the smaller exact-creation constructor.
- Proved canonical closed-endpoint renaming/store transport of exact creation.
  Endpoint equations are admissible when the final type-imprecision index is
  explicitly equal to the transported exact index.
- Removed the generic `rename-storeᴿ` constructor after showing that arbitrary
  well-scoped renaming need not preserve or reflect reduction. Replaced it
  with creation-specific canonical transport and proved both transported
  endpoints irreducible by value inversion.
- Audited direct and indirect `Λ⊑instβᵀ` consumers. Added its two missing
  permissive-scratch cases, strengthened the pure and paired fusion-spine
  contracts with canonical-index equality, and identified the paired-lambda
  leaf view and target widening `β-inst` roots as the remaining evidence-loss
  boundaries.
- Strengthened an independent finite target-instantiation spine with that
  equality and exact post-allocation endpoint typings. Its recursive fold into
  the smaller relation is strict, so nested creation itself introduces no
  further constructor requirement.
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
  machinery before the second function beta. The exact creation invariant at
  that boundary is now checked; its integration with quotient closing and the
  second function beta remains open.
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
  design. Its ordinary layer now states the variable, blame, natural-number,
  addition, one-sided cast, paired conversion, and paired widening rules
  explicitly, including every relevant index-composition or
  index-substitution premise.
- The target-instantiation creation test constructs a valid ordinary top row,
  takes the target through allocation and type beta, packages the surviving
  creation evidence, and proves that ordinary source-only-lambda plus
  target-cast rules cannot relate the final values. This establishes that
  up-to-reduction can replace transient allocation edges but cannot eliminate
  the final semantic creation case under the current DGG conclusion.

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

1. Strengthen the paired-lambda `leaf-instβ` view, all of its handlers, and
   its reconstruction boundary so they retain exact creation plus the
   canonical final-index equality. Do not manufacture that equality from the
   old fused constructor.
2. Strengthen the unfinished target widening `β-inst` root contracts with the
   cast-shape composition equation and matched body/allocation witnesses
   needed by exact creation. Cover both the ordinary cast-mode and
   identity-mode roots.
3. Migrate the direct identity post-beta context first, then the strengthened
   paired-lambda leaf and fusion spines. After every positive consumer passes,
   replace `Λ⊑instβᵀ` with exact creation plus canonical transport and remove
   the fused constructor.
4. Replace the interim creation-specific transport constructor with an
   admissible syntax-directed no-bullet world-embedding theorem requiring
   renaming left inverses and cast-mode renamers. Do not reintroduce a generic
   outer renaming constructor.
5. State the allocation-aware quotient `sim-beta-cast` contract directly in
   terms of the existing world-coherent weak result: the inert route supplies
   the source catch-up, while the active `inst` route uses the target tail,
   the creation constructor, and the resulting store extension.
6. Connect that contract to the existing paired-widening target
   pending-allocation machinery. The immediate leaf is the quotient-`inst`
   residual already counted among the four ordinary/generated down/up holes in
   `NuImprecisionCatchupScratch`.
7. Complete the two-function-cast operational square and confirm that its
   related endpoint is the ordinary QTI derivation consumed by
   `two-round-trips-substitutionᵀ`.
8. Discharge the target quotient closing-widening `β-seq` root through the
   existing target-tail sequence-resume midpoint machinery. Do not add a
   narrowing spine for this widening-side obligation.
9. If these succeed, derive the live function-cast simulation without
   `down·up⊑down·upᵀ` or quotient application and begin removing those
   constructors in a separate migration. In the same migration, remove the
   uninhabited target-only type-application, `ν`, and casted-`ν` constructors
   and their vacuous semantic roots. If allocation catch-up instead produces
   an irreducible quotient embedded outside a closing boundary, record that
   strict counterexample and return to the compositional design.
10. Prove source and target typing projections for the smaller ordinary and
   one-boundary quotient judgments. Re-run value, `No•`, and terminal
   inversion using the fact that the quotient judgment has exactly one
   constructor.
11. Continue testing valid ordinary top rows with arbitrary lambda bodies,
   nested reachable function casts, source and target cast sequences, and
   active target `inst`. The basic active-target test is complete; its nested
   quotient-closing instance remains. Every test must exhibit its initial
   ordinary term-imprecision derivation before its reduction endpoints are
   considered.
12. Keep the compositional quotient prototype as the fallback. Reintroduce
   quotient application, finite narrowing spines, or a quotient-to-quotient
   cast square only after a strict counterexample shows a derivable ordinary
   top row whose reductions cannot reach an ordinary-related join.
13. Restore hereditary `PairedWideningCompatible`: replace the broad
   `compatible-source-inert` fallback with the target-active case, preserve
   function and universal compatibility recursively, and retain the
   target-inert bridge. Then restore both function-beta consumers and the
   terminal-forward integration check.
14. Add the missing paired-lambda frame-view
   `down·up⊑down·upᵀ` case and restore its focused strict-spine check.
15. Migrate the other six known-incomplete strict proofs to the current
   uniqueness, binder-transport, compatibility, and `down·up⊑down·upᵀ`
   interfaces.
16. Finish quotient transport normalization and the crossed binary
   runtime-sibling catch-up invariant.
17. Prove the source function-cast `β` and `β-↦` value roots using the
   up-to-reduction `sim-beta-cast` argument rather than a quotient application
   or spine-length-specific term rule.
18. Inhabit the remaining exact active-synchronization root records.
19. Assemble the exhaustive prefix-aware world-coherent backward one-step
   dispatcher and restore a practical green backward strict-spine check.
20. Supply that strict dispatcher to both backward terminal engines.
21. Complete the remaining forward engine contracts, invoke the strict terminal
   integration proof, and construct `GradualDGG`.
22. Promote any still-needed generic scratch clauses through strict
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

On 2026-07-27, `make quotient-design-check` passed after the authorized
standard-library interface refresh. It checks the compositional examples, the
independent reduction-closed examples, the single-boundary diagnostic, the
target-instantiation creation example, and the canonical transport,
terminality, and transport-spine experiments. A subsequent unprivileged
strict check of
`NuImprecisionTargetInstantiationTransportExperiment.agda` passed in 2.6
seconds, confirming that the local stdlib cache was coherent.
The optimized focused check of
`NuImprecisionCatchupScratch.agda` also passed after the two formerly omitted
`Λ⊑instβᵀ` clauses were made explicit. Both strengthened fusion-spine folds
pass strict focused checks.

Do not use `All.agda` as the DGG completion criterion. It includes independent
and historical development surfaces. The final completion check is the strict
public DGG dependency cone plus the focused forward and backward terminal
spines.
