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
checkpoint. The complete smaller up-to-reduction prototype is the selected
migration candidate. Its grammar is definitionally independent of live
QTI: variables, blame, abstractions, applications, polymorphism, constants,
primitive operations, casts, conversions, paired widening, generalization
against a target ground type, allocation prefixes, and target-instantiation
creation are all represented directly. Its quotient judgment has exactly one
paired-narrowing constructor.

The smaller relation now passes all three decisive experiments: migration of
the audited `Λ⊑instβᵀ` consumers, the reachable two-function-cast
reduction/imprecision square, and the target instantiation/allocation/type-beta
square. Its supporting typing, value, terminal, world-embedding, parallel
substitution, and fully indexed single-variable substitution proofs are
strict. The concrete Cambridge26 Example 14 regression also passes: two
successive instantiation/generalization round trips reduce through their two
fresh `★` allocations and the enclosing concrete allocation to the same
constant as the more precise term. Exact target-instantiation creation is
closed under a composable
embedded-creation residual, because a binder renames the allocated target seal
from `0` to `suc 0`; the term grammar nevertheless has only one creation
constructor and no generic renaming constructor or separate transported
creation constructor.

The controlled replacement of `QuotientedTermImprecision` is now underway.
The target-instantiation family has moved to the selected design and the
asymmetric administrative shortcuts have been removed. The quotient boundary
and general source and target function-cast simulations still need to be
connected to the existing world-coherent operational machinery. The public
statement and compiler boundary are checked, but no complete `GradualDGG`
inhabitant exists yet.

## Controlled live migration

**MIGRATION IN PROGRESS — quotient administration and obsolete-cone retirement**

The migration runs on `codex/live-qti-migration`. The authoritative module
lifecycle manifest is
[`proof/Quotient/README.md`](../../Quotient/README.md). Phase 1 deleted the
rejected compositional alternative. Phase 2 replaced fused target
instantiation with exact creation plus a composable embedded residual,
migrated its consumers, and deleted the obsolete helper islands. The manifest
distinguishes the remaining selected migration evidence from retiring live
clients, specifies exactly when check roots leave the regression surface, and
requires deletion rather than compatibility wrappers.

Phase 3 deleted `⊑αᵀ`, `⊑νᵀ`, `⊑νcastᵀ`, `νcast⊑ᵀ`, and
`νcast⊑νcastᵀ`. The three target-only cases are uninhabited by the strict
index-cycle obstruction. The cast-specialized matched and source-only cases,
their helper records, and their allocation, frame, catch-up, scheduling, and
transport consumers were removed instead of being preserved behind wrappers.
The direct-constructor audit was followed by a transitive helper-capability
audit before deletion.

Phase 4 is now active. The two source-widening instantiation paths have
completed their controlled checkpoint: after the framed operand catch-up,
source type beta exposes `ν ★`, fresh-seal allocation takes `bind ★`, and
ordinary imprecision is established only for the allocated bullet plus
instantiation cast. The runtime-sibling path uses the same chosen store lift
for its primary and sibling relations. Both focused leaves pass, and the
former casted-`ν` frame helper has no source references.

The live Phase 4 grammar now contains the paired-narrowing quotient
introduction and compatible closing widening, but no fused
`down·up⊑down·upᵀ` or quotient-application rules. World embedding,
bullet-free left renaming, and source-allocation runtime transport have
migrated to that grammar. Remaining downstream clients still mention the
retired names and must migrate or be deleted. The matched target-allocation
root now states its exact value/no-bullet allocation step, fixed target
reduct, and explicit allocated-type imprecision premise; its focused proof
passes. The old first-draft `NuTermImprecision.agda` judgment has now been
removed. Its retained relational-store, term-context, crossed-store, and
general cast-mode support lives in chartered modules under `proof/Store/`,
`proof/NuCore/Relations/`, and `proof/Core/Properties/`. No compatibility
re-export remains.

The phase order is:

1. isolate the selected smaller design and delete the already rejected
   alternative;
2. replace `Λ⊑instβᵀ` atomically with exact and embedded creation;
3. remove target-only and casted-`ν` administrative shortcuts;
4. replace the live quotient boundary and connect function-cast simulation up
   to reduction;
5. promote retained proofs and regressions and delete every migration-only
   source; and
6. run the final canonical checks and record **MIGRATION FINISHED** before
   opening a pull request.

To limit Agda invalidation, obsolete Agda files are marked in the directory
manifest rather than by comment-only edits to their source. Grammar edits are
batched once per phase, leaf consumers are checked before one integration
gate, Agda processes run serially, and `All.agda` is not a migration gate.
Parallel agents may receive only disjoint consumer batches after the active
grammar is frozen; the grammar itself always has one writer.

Large-file work follows dependency structure rather than a line-count target.
Extract a stable proof island only when it has a coherent charter and lets a
substantial set of exact consumers stop importing a high-fanout monolith.
Rewire those consumers directly, keep the old monolith import non-public only
where it remains necessary, and do not add a compatibility re-export. Check
the focused module, the invalidated source, and a representative consumer.
If a large file belongs to a rejected or retiring design, delete its
zero-consumer cone instead of reorganizing it.

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
- in the smaller candidate, a quotient boundary contains exactly one paired
  narrowing cast. Additional casts must already be related at an ordinary
  intermediate index or be consumed by bilateral reduction.
- the smaller candidate has no target-only type-application or `ν` rule.
- live `target-instantiationᵀ` carries exactly one
  `EmbeddedTargetInstantiationCreation`, exposes a source `Λ`, a target cast,
  and a source type headed by `∀`, and retains the canonical final index
  rather than a compatibility wrapper.
- target-only `inst` catch-up retains a `TargetInstantiationCreation`
  residual: matched body imprecision, target cast typing, the index
  composition equation, and store lineage into the right-extended world.
  Its pre-allocation index and independently opened body index need not match
  directly; target reduction crosses the allocation before the final ordinary
  relation is required. Up-to-reduction removes transient allocation edges
  but not this final semantic creation case.
- exact creation is the base of `EmbeddedTargetInstantiationCreation`.
  Each typed relational-world embedding computes the canonical renamed
  imprecision index; no embedding step may choose an unrelated final index.
- exact creation alone is not stable under an enclosing type binder:
  `store-right 0` becomes `store-right (suc 0)`. The embedded residual records
  precisely this necessary closure and composes it without adding another term
  constructor.
- the smaller relation has no generic renaming constructor. Arbitrary
  well-scoped renamings may identify distinct seal names and change which
  reduction rule applies.
- only target-instantiation creation may cross the embedded-creation boundary.
  Every embedded endpoint remains a value, so its source- and target-leading
  simulation cases are impossible.
- single-variable substitution requires unique imprecision assumptions and
  `No•` evidence for both body endpoints and both substituted endpoints. It
  uses only the smaller relation and its syntax-directed world embeddings.

## Selected up-to-reduction design

The selected live quotient design is:

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
quotient-application constructor. After each down/up round trip, compatible
closing returns the argument to ordinary QTI, so the strict
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

The Phase 2 audit also included permissive and incomplete consumers.
`NuImprecisionOneStepTargetCastRoots` and
`NuImprecisionOneStepTargetConversionRoots` accept a relation premise but
only pass it to focused helpers; their remaining holes do not hide additional
term-imprecision constructor cases. The old permissive catch-up scratch was
deleted in Phase 3 together with its retired helper cone.

The generic `rename-storeᴿ` experiment failed its operational audit.
`TyRenameWf` preserves scope but not injectivity, and `RelStoreEmbeddingⁱ`
does not provide a renaming inverse. A renaming may identify distinct seals
and change `tag-untag-bad` into `tag-untag-ok`, so arbitrary reduction
reflection is false. The constructor has been removed. The replacement is
`EmbeddedTargetInstantiationCreation`: exact creation is its base and each
embedding step fixes the canonical renamed index and carries exact endpoint
typings. The term grammar has only `target-instantiationᴿ`; the interim
transport constructor has been deleted. The strict terminal experiment proves
that every embedded pair of endpoints consists of values and cannot take a
leading step.

### Decisive smaller-relation experiments

The three experiments requested before selecting the relation all succeeded.

1. **SUCCESS — `Λ⊑instβᵀ` consumer migration.** The direct identity
   post-beta context, canonical paired-lambda leaf, unframed and framed fusion
   spines, ordinary target widening root, and identity-mode target widening
   root all reconstruct actual smaller-relation derivations. They retain the
   exact creation evidence and canonical final-index equality; none imports
   live term imprecision.
2. **SUCCESS — reachable two-function-cast square.** Both applications take
   two function-cast beta steps and reach a bottom edge built from ordinary
   application, two individually closed down/up round trips, and the complete
   smaller relation. No quotient application, finite narrowing spine, or
   fused down/application/up constructor is used.
3. **SUCCESS — target instantiation/allocation/type beta.** The target takes
   the leading instantiation step, allocates the fresh seal, and completes type
   beta while the source takes zero steps. The final edge is the canonical
   embedded-creation case, with transported store, types, and imprecision
   index. No target-only type-application, target-only `ν`, or live fused
   constructor is used.

Completing the relation exposed and repaired two additional invariants.
Creation must be valid under an arbitrary final term-imprecision context
because its endpoints are closed; otherwise substitution under a lambda
fails. Exact creation must also be saturated under typed relational-world
embeddings, because paired or source-only type-binder weakening renames its
allocated target seal. The resulting grammar still has one creation
constructor and one quotient constructor.

The selection verdict is **ready for controlled live migration**. This means
that the complete independent relation and the decisive local simulation
slices are coherent. It does not claim that the general source and target
simulations, the terminal engines, or `GradualDGG` are complete.

### Cambridge26 Example 14 regression

The concrete repeated-instantiation example succeeds without extending the
smaller relation. In the paper's less-precise-left notation, its top edge is

$$
\bigl(\nu\alpha:=\iota.\,(\mathit{id}\langle\bar\nu\alpha.\alpha^\sharp\to\alpha^\flat\rangle\langle\nu\alpha.\alpha^!\to\alpha^?\rangle\langle\bar\nu\alpha.\alpha^\sharp\to\alpha^\flat\rangle\langle\nu\alpha.\alpha^!\to\alpha^?\rangle)\,\alpha\langle\alpha^\sharp\to\alpha^\flat\rangle\bigr)\,c\mathrel{\sqsupseteq}\bigl(\nu\alpha:=\iota.\,\mathit{id}\,\alpha\langle\alpha^\sharp\to\alpha^\flat\rangle\bigr)\,c.
$$

The Agda relation reverses the displayed orientation: the more precise term is
the left endpoint of `⊢ᴿ … ⊑ …`. The exact initial derivation alternates the
ordinary right-widening and right-narrowing cast rules twice, then uses matched
`ν`, ordinary application, and the constant rule. It uses neither quotient
imprecision nor creation.

The full bilateral square reduces both programs to the same constant. The
four-cast endpoint allocates two fresh `★` seals before allocating the outer
`\iota` seal; the other endpoint allocates only the outer `\iota` seal. The
final relational store has the concrete entry matched at name `0` and the two
additional `★` entries on the four-cast side at names `1` and `2`. Its type
transport is exactly two target-only lifts followed by one matched lift. The
bottom edge is ordinary constant imprecision.

The strict regression is
[`NuImprecisionCambridge26Example14Experiment.agda`](../../Quotient/NuImprecisionCambridge26Example14Experiment.agda).
It contains the exact top edge, both allocation traces, all five exposed
function-cast beta steps, all five cast-cancellation steps, and the final
allocation-aware `⊢ᴿ↠` square. No quotient constructor, finite narrowing
spine, fused application rule, live-QTI embedding, or example-specific
relation constructor is used.

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
| [`QuotientImprecisionCompatibility.agda`](../../../QuotientImprecisionCompatibility.agda) | **canonical support** | Cast-mode and reduction-closed hereditary widening evidence with no dependency on a term-imprecision relation |
| [`NuImprecisionReductionClosedQuotientDef.agda`](../../Quotient/NuImprecisionReductionClosedQuotientDef.agda) | **completed prototype** | Complete independent ordinary grammar, one embedded-creation case, one paired-narrowing quotient boundary, allocation-aware bilateral closure, and no generic renaming, quotient application, finite spine, or fused down/application/up rule |
| [`NuImprecisionReductionClosedQuotientExamples.agda`](../../Quotient/NuImprecisionReductionClosedQuotientExamples.agda) | **completed diagnostic** | Reachable two-function-cast top row, two beta steps on each side, and an ordinary-related join without quotient application or a fused rule |
| [`NuImprecisionReductionClosedQuotientTypingExperiment.agda`](../../Quotient/NuImprecisionReductionClosedQuotientTypingExperiment.agda) | **completed metatheory** | Exhaustive source and target typing projections for the ordinary and quotient judgments |
| [`NuImprecisionReductionClosedQuotientValueExperiment.agda`](../../Quotient/NuImprecisionReductionClosedQuotientValueExperiment.agda) | **completed metatheory** | Exhaustive source and target value classification, including terminal embedded creation |
| [`NuImprecisionReductionClosedWorldEmbeddingExperiment.agda`](../../Quotient/NuImprecisionReductionClosedWorldEmbeddingExperiment.agda) | **completed metatheory** | QTI-free relational-world embeddings, paired/source-only binder lifting, prefix inversion, and the strict exact-creation lifting obstruction |
| [`NuImprecisionReductionClosedWorldRenameExperiment.agda`](../../Quotient/NuImprecisionReductionClosedWorldRenameExperiment.agda) | **completed metatheory** | Exhaustive syntax-directed world embedding for both judgments and canonical paired/source-only binder weakening |
| [`NuImprecisionReductionClosedQuotientSubstitutionExperiment.agda`](../../Quotient/NuImprecisionReductionClosedQuotientSubstitutionExperiment.agda) | **completed metatheory** | Prefix-aware parallel substitution for every ordinary and quotient constructor |
| [`NuImprecisionReductionClosedQuotientSingleSubstitutionExperiment.agda`](../../Quotient/NuImprecisionReductionClosedQuotientSingleSubstitutionExperiment.agda) | **completed metatheory** | Fully indexed single-variable substitution using only the smaller relation |
| [`NuImprecisionTargetInstantiationCreationDef.agda`](../../Quotient/NuImprecisionTargetInstantiationCreationDef.agda) | **completed prototype** | Relation-parametric exact creation plus its canonical composable embedded residual |
| [`NuImprecisionEmbeddedTargetInstantiationCreationProperties.agda`](../../Quotient/NuImprecisionEmbeddedTargetInstantiationCreationProperties.agda) | **completed metatheory** | Canonical typing, value, and no-bullet projections for embedded creation |
| [`NuImprecisionTargetInstantiationCreationExamples.agda`](../../Quotient/NuImprecisionTargetInstantiationCreationExamples.agda) | **completed diagnostic** | Independent smaller initial/final rows, target allocation trace, creation residual, and strict refutation of ordinary final-edge factorization |
| [`NuImprecisionTargetInstantiationTransportExperiment.agda`](../../Quotient/NuImprecisionTargetInstantiationTransportExperiment.agda) | **completed diagnostic** | Canonical renaming/store-embedding transport and endpoint replacement with an explicit final-index coherence equality |
| [`NuImprecisionTargetInstantiationTransportSpineExperiment.agda`](../../Quotient/NuImprecisionTargetInstantiationTransportSpineExperiment.agda) | **completed diagnostic** | Strict recursive fold for arbitrarily nested exact creation and canonical endpoint transport |
| [`NuImprecisionTargetInstantiationConsumerMigrationExperiment.agda`](../../Quotient/NuImprecisionTargetInstantiationConsumerMigrationExperiment.agda) | **completed diagnostic** | Direct, leaf, and target-widening consumers reconstructed without live QTI |
| [`NuImprecisionTargetInstantiationFramedConsumerMigrationExperiment.agda`](../../Quotient/NuImprecisionTargetInstantiationFramedConsumerMigrationExperiment.agda) | **completed diagnostic** | Framed leaf and fusion-spine consumers reconstructed without live QTI |
| [`NuImprecisionTargetInstantiationSimulationExperiment.agda`](../../Quotient/NuImprecisionTargetInstantiationSimulationExperiment.agda) | **completed diagnostic** | Complete target instantiation, allocation, and type-beta square with a zero-step source side |
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
| [`NuImprecisionOneStepTargetCastRoots.agda`](../../OneStep/NuImprecisionOneStepTargetCastRoots.agda) | Eight generic target-cast root holes |
| [`NuImprecisionOneStepTargetConversionRoots.agda`](../../OneStep/NuImprecisionOneStepTargetConversionRoots.agda) | One generic target-conversion root hole |

These modules are outside all canonical strict cones. New strict work must use
their `Def` contracts or extracted strict leaves, never import them merely to
make a theorem facade appear complete.

One non-permissive, importer-free `Proof` module had been classified as
completed by filenames and source scans but fails a focused strict Agda check.
It is excluded from `NuDGGUnassembledProofsStrictSpine` and recorded by
`KNOWN_INCOMPLETE_PROOF_MODULES` in the import audit:

| Module | Exposed obligation |
|---|---|
| [`NuDGGTerminalForwardIntegrationProof.agda`](../TerminalForward/NuDGGTerminalForwardIntegrationProof.agda) | `compatible-source-inert` is uncovered in paired-widening function beta |

The separate
[`NuImprecisionPairedTargetClosingStrictSpine.agda`](../../PairedLambda/Terminal/NuImprecisionPairedTargetClosingStrictSpine.agda)
is also source-safe but not currently a completed aggregate. Its focused check
reaches an uncovered `down·up⊑down·upᵀ` case in
`NuImprecisionPairedLambdaTargetClosingFrameViewProof`. This proof is not in
the importer-free list because later paired-lambda proofs import it.

## Completed recent work

- Completed Phase 3 of the live migration. Removed the five asymmetric
  administrative constructors from the live grammar, migrated their remaining
  structural consumers, and deleted the obsolete allocation, frame,
  casted-`ν` catch-up, runtime-sibling, target-bullet, and scratch helper
  islands. No compatibility wrapper or replacement constructor was added.
- Pruned the source and right `ν`-frame interfaces to their reachable ordinary
  reveal-`ν` cases, and pruned the right target-allocation root interface to
  its matched reveal-`ν` case. This exposed one pre-existing overbroad
  target-allocation root contract for Phase 4 rather than hiding it behind a
  retired case.
- Focused checks passed for the live relation, substitution, embedding,
  allocation transport, frame, exclusion, dispatcher, and value-transport
  leaves affected by Phase 3. The import/strict-cone audit passes with four
  explicitly known incomplete proof roots and no uninventoried proof module.

- Finished the independent smaller relation rather than testing a partial
  surrogate. The ordinary grammar now covers every rule in the design,
  including `gen` against a target ground type, all cast and conversion
  polarities, matched/source polymorphism, allocation prefixes, and the sole
  target-instantiation creation case. The quotient grammar still has exactly
  one paired narrowing constructor.
- Replaced the separate transported-creation term constructor with
  `EmbeddedTargetInstantiationCreation`. Exact creation is its canonical base;
  typed relational-world embeddings compose inside the residual and compute
  the final index. This is necessary because a type binder renames the
  allocated target seal from `0` to `suc 0`.
- Proved exhaustive source/target typing and value projections, embedded
  creation terminality, term-context shift, paired-widening compatibility
  transport, QTI-free world embedding, paired/source-only binder weakening,
  prefix-aware parallel substitution, and fully indexed single-variable
  substitution for the complete relation.
- Completed the three decisive experiments. Audited `Λ⊑instβᵀ` consumers,
  the reachable two-function-cast square, and the target
  instantiation/allocation/type-beta square all succeed without live QTI,
  quotient application, finite spines, or the fused
  `down·up⊑down·upᵀ` rule.
- Added the strict Cambridge26 Example 14 regression. Its exact top edge and
  complete bilateral reduction square pass with two target-only `★`
  allocations, one matched concrete allocation, and an ordinary constant
  bottom edge.
- Split live-prefix inversion out of
  `NuImprecisionRelStoreEmbeddingAlgebra`, leaving the generic relational-store
  embedding algebra independent of live term imprecision. Existing live
  consumers import the focused prefix proof.
- Removed `ordinaryᴿ` and changed the smaller relation's worlds, stores, and
  contexts from fixed parameters to indices. Its variable, abstraction,
  application, polymorphic, constant, primitive, one-sided cast, paired
  widening, exact creation, and quotient-boundary cases are now independent
  constructors.
- Split `SpineCastMode` and reduction-closed widening compatibility into
  relation-independent support, now canonical in
  `QuotientImprecisionCompatibility`.
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
- The endpoint-MLB fixture now supplies the explicit `NonVar` witness required
  by the strengthened `ν` imprecision constructor; this removes a stale-source
  failure that had been hidden by an older Agda interface.
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
  the completed right/source-`∀` aggregate. Five other importer-free
  candidates failed focused checks and are tracked explicitly as incomplete.
  The audit now fails if a new completed strict `Proof` is left unaggregated or
  if a known-incomplete proof acquires an importer before repair.
- Compacted this ledger. The former 14,000-line chronology remains available
  in Git history rather than on the active proof surface.

## Current proof plan

1. **Completed:** checkpoint the Phase 3 grammar and consumer deletion without
   mixing in the quotient-boundary edit.
2. **Completed:** state and check the allocation-aware up-to-reduction
   contract used by both live source-widening instantiation paths. Their active
   paths take type beta to transient `ν ★`, allocate with `bind ★`, and only
   then construct the next ordinary term-imprecision edge.
3. **In progress:** promote the selected paired-narrowing quotient boundary
   and its metatheory to canonical live modules. The live grammar, typing
   projections, store-prefix evidence, parallel substitution, and term-context
   shift, world embedding, bullet-free left renaming, source-allocation
   runtime transport, quotient-down transport, target seal/tag cancellation,
   and the migrated source-`ν` and right-value leaves pass focused checks.
   The right-allocation source-bullet context mismatch was a shadowing pattern
   variable, not a missing invariant; matching the actual
   `lift-left-ctx-[]` constructor repairs the proof. The strict unassembled
   spine passes, and the remaining terminal-forward consumers are migrating
   now.
4. **In progress:** remove `down·up⊑down·upᵀ`, quotient-indexed application,
   and finite narrowing support. They are gone from the live grammar, but the
   frozen downstream inventory is not yet empty. The current direct counts are
   `2/1/1/12/7/0`. Each remaining client must
   migrate to `paired-downᵀ`/`closeᵀ`, use simulation up to reduction, or be
   deleted rather than wrapped.
5. **Completed:** tighten the matched target-allocation root contract so its
   premise states the allocation root its implementation handles; no catch-all
   for arbitrary frame steps was added.
6. Check only focused Phase 4 leaves, then run the source import/strict-cone
   audit and one public-DGG integration gate. Do not run `All.agda`.
7. **Completed early at the stable source-outcome checkpoint:** split the
   shared store/context infrastructure out of `NuTermImprecision.agda` and
   delete its obsolete first-draft relation. In Phase 5, promote retained
   migration theorems to canonical names, remove all experimental check
   roots, and delete every superseded migration source.
8. In Phase 6, verify that source search and the Makefile contain no obsolete
   constructor, import, wrapper, alias, prototype, or regression root. Run the
   final canonical quotient regressions and strict DGG gates serially.
9. Record the exact marker **MIGRATION FINISHED** in both lifecycle documents
   only after all Phase 6 conditions pass. Create the migration pull request
   only after that marker exists.
10. Resume the DGG proof on the smaller canonical relation: finish quotient
    transport normalization, crossed runtime-sibling catch-up, active
    synchronization, the exhaustive world-coherent dispatcher, both terminal
    engines, and finally construct `GradualDGG`.

## Validation

Routine source audits:

    make qti-migration-check
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
The exact source inventory counts are regenerated by the import audit. Four
proof roots are explicitly known incomplete and no uninventoried proof module
is permitted. Focused Agda checks, not filename or source counts, establish
completion.

On 2026-07-27, the pre-migration design aggregate passed after the authorized
standard-library interface refresh. A subsequent unprivileged strict check of
`NuImprecisionTargetInstantiationTransportExperiment.agda` passed in 2.6
seconds, confirming that the local stdlib cache was coherent.
The optimized focused check of the former catch-up scratch passed after the
two omitted `Λ⊑instβᵀ` clauses were made explicit. Phase 3 subsequently
deleted that permissive scratch and its retired helper cone. Both strengthened
fusion-spine folds pass strict focused checks.

After completing the independent smaller relation on 2026-07-27, the
pre-migration aggregate passed with all fourteen new strict roots:
typing, values, term-context shift, parallel and single substitution, world
embedding and renaming, compatibility renaming, embedded creation properties,
the two constructor audits, the two consumer migrations, and the
target-instantiation simulation. `make dgg-check` also passed after a full
dependency rebuild; this checks the strict unassembled-proof inventory but
does not change the explicitly incomplete terminal-forward status above.
Focused strict rechecks of the world-renaming and term-context-shift
experiments passed after their final formatting edits, and `git diff --check`
passed.

The strict Cambridge26 Example 14 experiment passed on 2026-07-27 and remains
a migration check root. The source file has no lines over 80 columns,
`git diff --check` passes, and the new ledger display uses only the required
`$$` delimiters.

Phase 2 of the live migration completed on 2026-07-27. The old
`Λ⊑instβᵀ` constructor has no Agda references. Live
`target-instantiationᵀ` contains one embedded creation residual and now exposes
the invariant that its source type is headed by `∀`. This made source-atomic
creation cases definitionally impossible and let the paired-lambda leaf,
handler, capability, and continuation interfaces discard their duplicated
renaming equalities, closedness evidence, and endpoint typings.

Focused checks passed for the live relation, residual properties, migrated
typing/value/substitution/world/allocation/catch-up consumers, the target seal
and tag cancellations, the direct target-widening post-beta context and
regression, the paired-lambda view and properties, both handler definitions,
both interpreters, the continuation assembly, and the frame-closing capability
definition. The source audit passed, and the final Phase 2 `make dgg-check`
passed. The permissive catch-up scratch refresh was stopped after several
silent minutes and is not a phase gate. The frame-closing handler assembly is
still blocked by a pre-existing proof-relevant index mismatch in
`NuImprecisionPairedLambdaTargetClosingGenLeafNuClosingProof`, after its
target-instantiation interface was migrated.

Phase 3 completed on 2026-07-27. Focused checks passed for every changed
structural family that is part of the live strict cone, and the import audit
passed after removing the deleted proof roots from its known-incomplete
inventory. The attempted Phase 3 integration gate stopped at two
pre-existing Phase 4 boundaries: the source cast-frame proof lacks a
principled fused `down·up⊑down·upᵀ` case, and the matched target-allocation
root contract admits frame steps that its allocation-root implementation does
not handle. These are recorded as Phase 4 design obligations, not papered over
with new constructors or catch-all clauses.

The first Phase 4 checkpoint completed on 2026-07-27. The ordinary and
runtime-sibling source-widening instantiation leaves now take the complete
type-beta and fresh-`★` allocation tail before constructing their next
ordinary term-imprecision edge. The allocation proof exposes a reusable
chosen-lift form, so the runtime sibling cannot drift into a separately
generated world. Focused checks passed for the allocation helper, the
ordinary source-widening leaf, and the runtime-sibling source-widening leaf.

The second Phase 4 checkpoint completed the live grammar edit on 2026-07-27.
`QuotientedTermImprecision` now has exactly one quotient introduction,
`paired-downᵀ`, and closes it only through compatible `closeᵀ`. Paired reveal,
conceal, and widening are direct ordinary constructors. The fused
cast/application rule, quotient applications, split narrowing constructors,
target-id widening shortcut, and `PairedCast` wrapper are absent from the live
definition. Focused checks passed for the defining module, store-prefix
evidence, parallel substitution, and term-context shift. This is not a phase
gate: the frozen downstream inventory still contains retired source names.

The third Phase 4 checkpoint migrated canonical world and left transport on
2026-07-27. The simulation core transports `closeᵀ` and direct paired
reveal/conceal/widening without compatibility wrappers. The two
`paired-downᵀ` renaming adapters moved behind the strict
`NuImprecisionPairedDownRenameDef/Proof/Lemma` boundary; the core fell from
15,065 to 14,878 lines and no longer imports recursive narrowing-elimination
compatibility. Focused checks passed for both compatibility transports, the
generic Def and Proof, the canonical Lemma, world embedding, bullet-free left
renaming, and source-allocation runtime transport. The latter two proofs
became smaller:
the fused application branches vanished, four quotient application branches
vanished, and the split identity/gradual downcast cases collapsed to one.
The frozen direct source-file counts fell from `14/9/9/46/27/26` to
`8/3/3/39/20/19`; this remains a checkpoint rather than a phase gate.

The next structural check found that the selected prototype support still
defined a nominally distinct copy of the now-canonical compatibility
relations. That duplicate module was deleted, its six clients now import
`QuotientImprecisionCompatibility` directly, and no bridge alias remains.
The live quotient round-trip regression was rewritten with `paired-downᵀ`
and compatible `closeᵀ`; its focused check passes. Store-prefix no-bullet
transport also now has one `paired-downᵀ` branch instead of four split and
application-specific branches.

The redundant `QuotientedTermImprecisionTest` regression was then deleted:
its sole incomparable-intermediate round trip is strictly covered by the
canonical quotient examples with an explicit compatibility witness. The
reviewed standalone-root list was updated in the same checkpoint, and the
source import/strict-cone audit passes. The remaining direct source-file
counts are `8/2/2/37/17/18`; the next foundational task is to replace the two
fixed-mode quotient-down transports with one transport over arbitrary
`SpineCastMode`.

That transport experiment succeeded. The two fixed identity/generated
theorems are now one `quotient-down-transportᵀ`: `id-only↓` remains fixed,
while an arbitrary `gradual↓` mode and its seal evidence are transported
existentially through the source changes and the leading target change plus
target tail. The theorem reconstructs a single `paired-downᵀ`, and its
focused strict check passes. The reusable split now lives once in
`apply-spine-narrows-typing`; the right transport itself is uniform. The
remaining counts are `8/2/2/37/16/17`.

Its enclosing right-frame consumer identifies the next contract question.
The downcast boundary and `QuotientWideningPair` both transport, but `closeᵀ`
also requires its compatibility proof in the final world. The existing weak
one-step coherence interface transports ordinary and quotient indices and
their shapes, but does not yet expose preservation of the recursively
structured widening-compatibility evidence. Do not restore `up⊑upᵀ`; either
derive this preservation from existing world lineage or add the smallest
general coherence field that makes it reusable.

The matched target-allocation checkpoint then completed on 2026-07-27. The
root contract no longer accepts an arbitrary `bind` reduction or a broad
target runtime premise: it requires the target value and no-bullet evidence,
states `((⇑ᵗᵐ V′) •) ⟨ s′ ⟩` as the target reduct, and exposes `pA` as an
ordinary premise. The indexed allocation module now owns a reusable lineage
preservation lemma, so the world-coherent root no longer reconstructs its two
hidden component results with underscores.

Reaching that root also retired an unreferenced paired-all allocation helper
and its four local store-correspondence helpers from
`NuImprecisionSimulation.agda`. Two synchronized allocation cases now use
`paired-revealᵀ` directly, and matched post-allocation `β-gen•` now uses
`paired-downᵀ` with explicit gradual spine modes. Focused checks pass for the
paired-all beta commutation leaf, the tightened target-allocation `Def`, and
the complete target-allocation `Proof`. The direct retired-name counts are
now `8/2/2/37/16/16`.

This checkpoint also exposed a concrete invalidation problem. The final
246-line root check initially took roughly five minutes because its two live
allocation dependencies were in the 2,860-line
`NuImprecisionAllocationSimulation.agda`, whose import cone includes the
15,096-line `NuImprecisionSimulationCore.agda` and the 4,762-line
`NuImprecisionSimulation.agda`.

The first dependency cut succeeded. The complete post-value world-coherent
allocation claim now lives in the 118-line
`NuImprecisionWorldCoherentMatchedNuAllocationAfterValueCatchupDef.agda`
under `WorldCoherent/Right/OneStep/Allocation/`. The 214-line target-allocation
`Proof` depends only on this contract and checks in about six seconds after
invalidation; it does not import `NuImprecisionAllocationSimulation.agda`.
The 91-line canonical `Lemma` supplies the existing indexed-result and
lineage implementations, with the legacy catch-up invariant inversion
confined to that assembly. The `Lemma` also checks strictly.

The implementation split is not finished. The monolithic allocation module
still has three external consumers: this target-allocation `Lemma`,
`NuImprecisionWorldCoherentSourceAllocationStepProof.agda`, and
`NuImprecisionWorldCoherentSourceNuRuntimeSiblingCatchupProof.agda`. Migrate
those consumers to retained chartered allocation modules, remove the
monolithic imports, and delete the obsolete remainder by Phase 5; do not add a
re-exporting wrapper.

The quotient-close checkpoint then migrated the general final-world
compatibility transport, quotient-down frames and roots, atomic target
reindexing, exact narrowing and conversion transport, and target seal/tag
cancellation. The apparent general target-ground quotient elimination lemma
was false: a gradual seal-mode narrowing may end at a target variable. Its
only live caller needs target `★ ⇒ ★`, so the false family was deleted and
replaced by the exact function-ground theorem. The target-tag proof establishes
that endpoint from reduction-closed compatibility before using it.

The allocation-bullet transport pair now dispatches directly over `closeᵀ`,
paired reveal, paired conceal, paired widening, and the generic target
widening rule. Both pending-allocation callers pass. The SourceAll slice now
uses three direct paired residual capabilities instead of the deleted
`PairedCast` carrier and explicitly retains reduction-closed compatibility at
both paired-widening and quotient-closing boundaries. Its separate id-only
target-frame capability became dead after generic mode relaxation and was
deleted with its `Def` and `Proof`.

Focused checks pass for all of those leaves, and
`NuDGGUnassembledProofsStrictSpine.agda` now passes as a whole. The
terminal-forward spine advances to the next retired-carrier consumer in the
source function-cast-beta paired-values family. The current direct retired
source-name counts are `7/2/2/29/12/12`.

The performance audit confirms that dependency cuts should accompany the
migration. Extracting generic narrowing and conversion transport from
`NuImprecisionSimulationCore.agda` reduced one invalidated frame check from
about 58 seconds to about 8 seconds. The next checkpoint candidates are the
QTI typing projections and the store/context infrastructure still bundled
with the obsolete first-draft relation in `NuTermImprecision.agda`; neither
split should be mixed with a live grammar edit.

The QTI typing-projection split is checked. The 627-line live grammar remains
in `QuotientedTermImprecision.agda`; its five mutually recursive typing
projections now live in the focused 395-line
`proof/NuCore/Relations/NuImprecisionQuotientedTyping.agda`. Direct consumers
import the proof-support module themselves, so no compatibility re-export
widens the grammar's dependency cone. Warm focused checks take about three
seconds for the typing module, eight seconds for a representative allocation
consumer, and seven seconds for
`NuDGGUnassembledProofsStrictSpine.agda`. The one-time consumer and aggregate
rebuilds took about one minute and up to three minutes respectively after
removing seven empty grammar imports. The source/import audit passes.

Refreshing the distinct public `NuDGGSpine.agda` then exposed a cached
unmigrated compiler dependency:
`proof/Compilation/CompileTermImprecision.agda` still applies the deleted
`up⊑upᵀ` constructor. This does not invalidate the typing split or the
checked unassembled aggregate.

The natural replacement claim is false, including for canonical `CastPlan`
evidence. Compiling the source cast from `∀ X. X ⇒ X` to `★` produces an
active instantiation followed by a function tag, while the related target
cast from `★ ⇒ ★` to `★` is the inert function tag. Reduction-closed
target-inert compatibility would require `★ ⊑ ★ ⇒ ★`, contradicted by the
existing star/arrow impossibility theorem. Thus compiler monotonicity needs an
up-to-reduction boundary, or closing must change semantically. Adding a plan
field or compatibility wrapper would not prove the missing fact, and
`up⊑upᵀ` must not be restored.

The direct source function-beta paired-values migration now passes its focused
checks. The combined interface has no `PairedCast`: paired reveal and conceal
have direct operational case contracts, paired widening requires
reduction-closed paired-widening compatibility, and quotient closing requires
reduction-closed quotient compatibility. The implementation distributes beta
through direct paired residuals and covers the widening compatibility
constructors exhaustively. The two case contracts, combined
`Def`/`Proof`/`Lemma`, both widening layers, both quotient layers, target
function-cast dispatcher, and `NuDGGUnassembledProofsStrictSpine.agda` all
check. `make audit` passes.

The terminal-forward strict spine now reaches
`NuImprecisionQuotientFunctionPairedNarrowingApplicationProof.agda` and fails
where that proof constructs the deleted quotient-application constructor.
With only `paired-downᵀ`, live quotient syntax cannot directly relate the
application-headed bottom edge. The reduction-closed quotient examples
already show why: repeated function casts may require more beta steps on both
sides before an ordinary live-QTI join exists. This is the decisive boundary
for an up-to-reduction simulation result.

`WorldCoherentSourceOneStepIndexedResult` currently says that the
distinguished source step is the entire source trace. The underlying
`WeakOneStepIndexedResult` already supports arbitrary source catch-up and a
target tail. The next experiment will generalize only the world-coherent
source result so that the distinguished step is a prefix of the source trace,
then test whether it replaces the pure quotient-application family. Until
that operational replacement checks, the old `Def`/`Proof`/`Lemma` chains
remain migration-active and on the regression surface. The remaining direct
retired-name counts are `7/2/2/28/12/12`.

That result-contract experiment succeeded. A completed source step now
exposes the distinguished leading change, an arbitrary administrative source
tail, and a reduction from the immediate reduct to the returned source term.
The public source simulation likewise returns explicit source and target
tails before the final ordinary QTI edge. Exact one-step leaves use an empty
tail; application, primitive, cast, and `ν` frames lift a nonempty tail through
their whole-term contexts. All direct result consumers have migrated, and
source search finds no use of the former exact-change or exact-result fields.

The terminal-forward proof also consumes the generalized result strictly.
It recurses with fuel bounded by the observed source trace length; aligning
the returned source tail against that trace gives the existing strict
residual-length decrease. This is the decisive evidence that the new result
contract composes with the DGG trace induction rather than merely moving the
quotient obstruction into a caller. Focused checks pass for the result and
public simulation definitions, their projection proof, the terminal-forward
proof, all migrated composition and frame clients, and the direct lambda and
primitive schedulers. The terminal-forward strict spine now advances through
this entire checkpoint and stops at the expected obsolete pure
quotient-application proof.

The next step is operational, not grammatical. The paired-quotient
function-beta leaf must terminalize the exposed domain casts after the
distinguished function-beta step. Because either source domain cast may
reduce to blame, that leaf and its scheduler path must return the existing
source-step outcome: either a related result with bilateral tails or source
blame. Once that replacement passes, the pure
quotient-application `Def`/`Proof`/`Lemma` family can leave the regression
surface and be deleted.

That outcome is now propagated through the complete source one-step path.
The direct function-beta case, target-value rank recursion, target
cast/conversion scheduling, application root, and pure-step dispatcher all
preserve source blame instead of forcing an ordinary related result. Exact
branches inject the related alternative. The full
`NuImprecisionWorldCoherentSourceOneStepProof.agda` focused check passes, and
the terminal-forward strict spine again stops exactly at the obsolete pure
quotient-application proof. No outcome-plumbing obligation remains between
the paired-quotient beta leaf and the public source one-step result.

The old target-instantiation consumer audit is also closed: a historical grep
found exactly 26 consumers of `Λ⊑instβᵀ`, and the atomic creation migration
touched all 26. The only permissive QTI-analyzing scratch module contained
both missing creation branches; it migrated and was later deleted. No hidden
incomplete creation consumer remains. Stale references to other deleted
quotient constructors remain separate Phase 4 obligations.

Large-file decomposition is now part of the controlled migration. At this
stable source-outcome checkpoint, the 1,213-line mixed
`NuTermImprecision.agda` was replaced atomically by:

- the 294-line relational-store definition;
- the 163-line term-context definition;
- the 95-line crossed-store construction; and
- three general cast-mode witnesses in the existing cast-properties module.

An import audit found 647 direct clients: 503 store-only, 8 context-only, 127
using both, 8 helper-only, and the aggregate import. None consumed the
first-draft relation or its projections. All clients now import the exact
retained module, `All.agda` no longer imports the obsolete module, and the old
file was deleted rather than retained as a shim. The focused new modules
check in 2–4 seconds; the live QTI join checks; the source one-step proof
checks in about 8 seconds; and `make audit` passes. The terminal-forward
strict spine still reaches the expected obsolete quotient-application proof,
so the infrastructure cut introduced no earlier semantic boundary.

The same hotspot audit found that 35 direct clients imported the 1,276-line
cast-imprecision module solely for `seal★-tag-or-id`. That witness now lives
in the 15-line `SealModeProperties.agda`; every client imports it directly,
and the cast-imprecision module no longer re-exports or defines it. The new
leaf, live QTI join, and source one-step root pass focused checks.

The operational quotient-beta audit has isolated the missing live invariant.
The outer function compatibility decomposes to the final codomain widening,
but it says nothing about the contravariant domain widening exposed by the
next function beta inside the quotient-producing narrowing. The current
`paired-downᵀ` premise therefore cannot terminalize an active paired argument
round trip.

The standalone narrowing-elimination prototype implemented the minimal
recursive repair. At a function narrowing it requires
reduction-closed quotient compatibility for the paired domain widenings and
recurses through the codomain narrowings; when either coercion is not
function-shaped, no elimination evidence is required. The existing
two-function-cast regression constructs the evidence for its genuinely
permuted-`∀` inner narrowing using the already proved route compatibility.

The invariant is now a live premise of `paired-downᵀ`. Its typing,
substitution, store-prefix, world-embedding, source-renaming, allocation, and
target-ground consumers all pass focused checks. The right-leading
quotient-down path transports the recursive evidence across arbitrary weak
steps, including a leading target allocation. The required naturality theorem
for quotient arrow components now lives in the 573-line
`NuImprecisionQuotientWeakTransportProperties.agda`; the former right-value
transport monolith imports that theorem and has shed 429 duplicated lines.

The paired-down renaming adapters also moved out of
`NuImprecisionSimulationCore.agda` into a 109-line `Def`, a 56-line generic
`Proof`, and a 238-line canonical `Lemma`. Widening-compatibility renaming and
narrowing-elimination renaming are separate modules, and the former combined
module was deleted without a shim. The simulation core is now 14,878 lines,
down from 15,065, and future changes to the recursive elimination invariant do
not edit it. `make audit` passes.

This transport checkpoint succeeds. The next decisive test is the operational
paired-quotient function-beta leaf itself: use the recursive domain
compatibility to terminalize the exposed paired argument casts, recurse through
the codomain evidence, return either bilateral tails ending in ordinary QTI or
source blame, and then delete the obsolete pure quotient-application and
paired-quotient-relation families.

That operational test has now found a genuine higher-order counterexample to
the sufficiency of the current invariant. Let the outer closing function
widenings expose domain narrowings `c` and `c′`, and let the inner
quotient-producing function narrowings expose domain widenings `a` and `a′`.
After the outer and inner function-beta steps, the argument relation must have
the live shape

`closeᵀ (paired-downᵀ ... c ... c′ ...) ... a ... a′ ...`.

The inner `function-elimination` premise gives the compatibility needed by the
closing `a`/`a′` pair and recurses through the result narrowings. It does not
give the elimination evidence required by the newly constructed
`paired-downᵀ` for `c`/`c′`. The outer reduction-closed widening compatibility
cannot supply it either: its function case retains only codomain compatibility.
The quotient arrow-component equation recovers the relevant indices and
composition squares, but operational compatibility is additional evidence and
cannot be derived from those equations.

The existing two-function-cast regression did not expose this because its
argument type is not a function, so `non-function-elimination` discharges the
new boundary. At a higher-order argument type both `c` and `c′` are function
coercions and the construction stops. The next invariant revision must
therefore make function elimination mutually recursive across narrowing and
widening: a quotient closing widening must retain elimination evidence for its
contravariant domain narrowing and recurse through its codomain widening. A
strict higher-order regression is the acceptance gate. Only after it passes
will the operational paired-quotient beta leaf resume.

The acceptance experiment succeeded, and its mutual invariant is now live in
`QuotientImprecisionCompatibility.agda`. Function widening retains
contravariant narrowing-elimination evidence and recursive codomain widening
evidence; function narrowing retains contravariant widening evidence and
recursive codomain narrowing evidence. The representative constructor
requires at least one syntactically non-function coercion, so a paired
function cannot bypass the recursive case.

Renaming now lives in the unified
`NuImprecisionQuotientEliminationCompatibilityRename.agda`, with mutual
bilateral and source-only proofs. Weak-step transport carries both relations
mutually, and quotient-down uses that exported transport instead of a private
copy. The superseded standalone definition and both old rename modules were
deleted without compatibility re-exports. Strict checks pass for the live
core and QTI, unified rename, paired-down rename assembly, both weak-step
transport roots, target tag cancellation, the canonical quotient examples,
the higher-order live regression, and the right quotient-down cases.
`make audit` passes.

The next semantic gate is the operational quotient-down value catch-up leaf.
It must use the hereditary evidence to produce bilateral tails ending in
ordinary QTI or propagate a source trace to blame. Only after that gate passes
may the obsolete pure quotient-application and paired-quotient-relation
families be deleted.

The checking-time audit also identified a concrete cleanup that can proceed
without touching the term grammar. The former 2,873-line
`NuImprecisionAllocationSimulation.agda` has only two direct consumers.
Its seven shared source-`ν` lift/replacement properties now live in the
497-line `NuImprecisionSourceNuLiftProperties.agda`; the monolith is 2,444
lines and does not re-export them. The focused property module and the
source-`ν` runtime-sibling consumer pass. The source allocation consumer
reaches its already-known stale `⊑cast⊑idᵀ` migration case after rebuilding,
rather than failing in the extracted properties. The retained source-only
allocation, base matched allocation, and matched
allocation-after-value-catch-up capabilities will then move behind focused
`Def`/`Proof`/`Lemma` boundaries,
after which unused allocation branches and the monolith will be deleted.

The source-only relation boundary has now moved to the strict
`proof/Source/Allocation/NuImprecisionSourceNuAllocationRelationDef/Proof/Lemma`
family. Its two contracts state only the post-allocation QTI edge; the
world-coherent proof reconstructs the immediate source `ν` reduction and
zero-step target tail and takes both relations as higher-order dependencies.
The unused paired-widening-under-binder transport and its private shape
helpers were deleted. All three new modules and the 2,168-line reduced
monolith pass strictly. The world-coherent source allocation proof validates
the new cases and recursive dependency propagation before stopping at the
same retired `⊑cast⊑idᵀ` case.

Matched allocation now has the same focused boundary. The strict
`proof/OneStep/Allocation/NuImprecisionMatchedNuAllocationStepDef/Proof/Lemma`
family returns one indexed result together with its store lineage, exact
source change and result, and one homogeneous equality for the fully packed
final context and store. The after-value-catch-up family exposes the chosen
lifted store and matched head through the same packed equality. Consequently,
the world-coherent proof performs all dependent transport in one place and
reconstructs coherence, source-name exclusivity, and assumption uniqueness
from the exact final store shape.

The target allocation root now assembles the focused world-coherent lemma,
and the source allocation proof takes the base matched step as an explicit
higher-order dependency. The six lower modules, the world proof and lemma,
the target root, and the reduced allocation module all pass focused strict
checks. The source allocation proof elaborates every migrated branch before
stopping at its already-known retired `⊑cast⊑idᵀ` branch. Removing the moved
matched allocation, catch-up, blame, and dispatcher islands reduced
`NuImprecisionAllocationSimulation.agda` from 2,168 to 665 lines and cut its
focused check to 4.70 seconds.

The four zero-consumer residual declarations were then audited against the
unfinished simulation cases. The source-blame allocation wrapper and the
matched and source-only allocation-plus-`β-Λ•` squares are obsolete under the
up-to-reduction architecture and were deleted. The bilateral
post-allocation-`β-gen•` case contained one genuinely reusable piece: the
paired-narrowing quotient edge. That edge now lives, without either reduction
step, in the strict
`proof/OneStep/RuntimeBullet/NuImprecisionMatchedBetaGenNarrowingDef/Proof/Lemma`
family. Its proof takes generic allocation transport as a higher-order
dependency and the lemma supplies the canonical implementation. All three
modules pass focused strict checks. With that kernel preserved,
`NuImprecisionAllocationSimulation.agda` was deleted; no Agda references to
the module or its four former declarations remain.

The operational quotient-beta experiment has now succeeded at the contract
and wrapper level but has not yet produced the semantic inhabitant. The strict
shared post-target-beta contract retains the source's distinguished function
beta, fixes the target after its outer function beta, and returns either
bilateral tails ending in ordinary QTI or a source trace ending in blame. The
source paired-quotient wrapper now takes that contract instead of the
obsolete pure quotient-application theorem, prepends the target beta step,
and passes strict checking.

The first attempted inhabitant exposed an important correction to the design
audit. Inverting the quotient-related function values does make their outer
function casts inert, but it does not make the contravariant component casts
on `W` and `R′` inert. Those casts may be active, so the finite two-beta proof
was rejected. Adding the inner domain widenings around the paired domain
narrowings gives an ordinary `closeᵀ (paired-downᵀ ...)` edge. Existing
quotient-down synchronization proves its first active target step, and
existing left-value catch-up finishes the source once the target is a value.
Iteration between those boundaries requires the canonical
`WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ` dispatcher. Its strict
leaves and frames exist, but its recursive assembly is not yet exported.

The next implementation task is therefore that canonical right one-step
dispatcher, with the post-target paired-quotient worker fitted into its
existing function-cast scheduling SCC. The right-oriented beta leaf must then
receive the outer reduction-closed widening compatibility. Until the shared
worker, both orientations, and terminal-forward integration pass, the two
pure quotient-application theorem families remain migration-active.

An exhaustive assembly audit shows that the dispatcher cannot yet be formed
by merely wiring the existing modules: several value-catch-up, paired-cast,
target-cast, and function-beta proofs still analyze retired QTI constructors.
The ordinary and source-down application families should be deleted rather
than migrated, because live QTIP has only `paired-downᵀ`. The sound order is:

1. migrate left and right value catch-up to the live cast constructors;
2. replace the old `PairedCast` aggregate with explicit paired reveal,
   conceal, and widening cases;
3. remove identity-only target-widening branches;
4. implement matched and source-only runtime-bullet leaves;
5. implement quotient-frame recursion from the existing quotient-down roots;
6. add one compact well-founded SCC containing only the prefix dispatcher,
   quotient-frame recursion, and the post-target quotient-beta worker.

Structural cases recurse on QTI or QTIP derivation height. The genuine
post-target cycle additionally needs a lexicographic administrative measure
using the existing pending-administration and function-cast-spine ranks.
This keeps leaf proofs independently cacheable and confines mutual checking
to the unavoidable control kernel.

The source-allocation proof is now fully migrated to the current QTI and
passes strictly in 22.22 seconds. Its obsolete `⊑cast⊑idᵀ` branch and
identity-only frame dependency were deleted. The stricter check also exposed
three exact-step constructions that predated the generalized source-result
contract; they now state an empty administrative tail and its reflexive
reduction explicitly.

Four more source-side consumers have shed the same retired identity-only
target-widening branch: source-`ν` framing, lambda-beta scheduling, primitive
delta catch-up, and the target-function-cast value scheduler. Their focused
strict checks pass in 9.00, 8.33, 7.87, and 7.60 seconds respectively. The
generic target-widening case now owns this behavior; no compatibility case or
frame remains in those proofs.

The next safe checking-time cut is also complete.
`NuImprecisionSimulation.agda` fell from 4,769 to 4,273 lines. Three live
post-allocation or post-catch-up polymorphic reduction helpers moved to
`NuImprecisionSourcePolymorphicValueBase.agda`; the remaining 400-plus-line
administrative trace and mini-square island had no consumers and was deleted
without re-export. Matched allocation now owns its two private lift/prefix
helpers and imports the canonical store embedding, removing its dependency on
the broad simulation module. The canonical helper module, matched-allocation
Proof and Lemma, one redirected target-allocation consumer, and the reduced
simulation module pass focused strict checks. The two redirected source-widen
consumers currently stop earlier at their independently retired `PairedCast`
imports, which are part of the active value-catch-up migration.

The symmetric right-lift prefix theorem now lives in the focused
`proof/Right/AllocationRuntime/NuImprecisionRightLiftPrefixBodyDef/Proof`
pair and uses the canonical right-store embedding. Its four consumers import
that boundary directly; the former right-lift store embedding, world
embedding, and prefix theorem were deleted from the simulation module without
a shim. The new Def and Proof, both target-allocation clients, both
target-widen allocation clients, and the reduced simulation module pass
strict checks. `NuImprecisionSimulation.agda` is now 4,216 lines, down 553
lines across the three cuts.

The first live value-catch-up prerequisite is complete. The
`WorldCoherentSourceRuntimeCatchupᵀ` contract no longer hides the retired
`PairedCast` aggregate. It exposes separate reveal, conceal, and paired
widening fields, including the live store correspondence, index replacement,
composition, and reduction-closed compatibility evidence. The left
value-catch-up prefix now analyzes `paired-downᵀ`, `closeᵀ`,
`paired-revealᵀ`, `paired-concealᵀ`, and `paired-wideningᵀ` directly.
Its obsolete fused down/up, identity-only target-widening, and undifferentiated
conversion branches are gone. The source-runtime contract, prefix proof, and
canonical left value-catch-up proof all pass focused strict checking.

The symmetric runtime-sibling experiment confirmed the same close-frame
interface. The shared transport now lives in the strict
`proof/Catchup/Core/NuImprecisionCatchupPrefixCloseDef/Proof/Lemma` family,
and both ordinary and runtime-sibling value catch-up use it. The old quotient
catch-up support module had no remaining semantic consumers, so its strict
spine import and the file itself were deleted rather than retained as a
wrapper.

Runtime-sibling catch-up now has one generic quotient-close field instead of
separate identity and generated narrowing fields. Its source-runtime
contract exposes paired reveal, conceal, and widening explicitly, and its
value dispatcher analyzes `closeᵀ`, `paired-downᵀ`, and the three paired cast
constructors directly. The fused down/up, identity-only target-widening, and
generic paired-conversion cases are gone. The close Def/Proof/Lemma, ordinary
value prefix and wrapper, quotient runtime-sibling contract and proof, and
runtime-sibling value consumer all pass focused strict checks. The direct
quotient-final Lemma was then blocked downstream by the retiring
`NuImprecisionQuotientValue.agda` case analysis over removed narrowing
constructors. That unused provider cone has since been deleted rather than
repaired.

There is still no canonical Proof/Lemma inhabitant for the revised
`WorldCoherentSourceRuntimeCatchupᵀ` record. Do not adapt the old
`SourcePairedCastCatchup` aggregate as a compatibility layer.

The right-value no-bullet transport monolith has also received a stable
invalidation cut. Its term/runtime facts, allocation-prefix transport, fixed
narrowing transport, and quotient-index transport now live in three focused
same-subtree modules. Each new module passes a focused strict check in about
five to six seconds. Two unused private helpers were deleted, and the main
proof fell from 3,185 to 2,815 lines. Its focused check still stops upstream at
the known removed-`PairedCast` dependency; the extracted modules introduce no
new blocker and do not hide the constructor-sensitive recursion.

The missing canonical source-runtime provider is not merely an absent record
literal. The current source-widening field is broader than the checked
case proof: its source-inst branch is valid only when the index has the
admissible `ν` shape. The provider must first expose that admissible case view,
then integrate bullet, narrowing, widening, `ν`, and the three explicit paired
cases through the existing well-founded source-administration measure. Do not
tie the prefix proof and source-runtime record into an opaque higher-order
recursive knot. The old `SourcePairedCastCatchup` graph is obsolete; after its
two right-root consumers are classified against the explicit live
constructors, delete it without a shim.

Two further performance cuts are migration-aligned. Split the 1,435-line
source-widening case proof into stable transport support and focused
inert/identity, sequence, and `ν`-indexed inst cases before adding the
admissible dispatcher. Split the 937-line source-conceal monolith into a true
Def/Proof/Lemma family, moving only the neutral atomic reindex and
post-`β-id` support shared by reveal and widening clients. These results are
intended to survive migration; do not similarly split the retiring
2,090-line quotient-value case analysis merely to preserve it.

After the operational quotient interfaces settle, extract the stable generic
transport, weak-composition, and world-transport regions from the 14,878-line
`NuImprecisionSimulationCore.agda`, followed by the reusable cast-frame region
of the 4,762-line `NuImprecisionSimulation.agda`. These must be genuine
dependency cuts, not re-exporting wrappers.

The source-widening split is now implemented. The former 1,435-line case
proof has been replaced by a 336-line common transport core and separate
inert/identity, sequence, and source-only-`ν` instantiation proofs. The
definition exposes only those four exact contracts; the unjustified broad
source-widening leaf assumption is gone. The full source-widening case remains
valid only after the caller analyzes the widening derivation and rules out
inadmissible index/shape combinations. The Def, common core, sequence, and
`ν`-indexed proofs pass focused strict checks. The inert/identity proof also
passes after switching its atomic result reindex to the live relation.

That reindex is now the exhaustive
`proof/OneStep/NuImprecisionAtomicSourceReindex.agda`; it covers `closeᵀ`,
target instantiation, generalization against ground, and the three explicit
paired branches. The obsolete `NuImprecisionPairedCastResultShape.agda` and
the old private reindex were deleted. Source conceal is 202 lines smaller and
passes strictly against the focused theorem.

The four generic source-cast result framers also moved out of
`NuImprecisionSimulation.agda` into the strict 182-line
`NuImprecisionWeakOneStepSourceCastFrame.agda`. Direct clients now import that
module instead of the broad simulation file, and the simulation file is down
to 4,093 lines. This is a real dependency cut: the new module depends only on
the result definition and is not re-exported by a wrapper.

The active and inert right source-root families now take explicit paired
reveal, conceal, and widening evidence. Each family is split into three
focused case proofs and a small aggregate proof; all six leaves and both
aggregate Lemmas pass strict checks in roughly 10–12 seconds. Active-value
synchronization is the direct final-value restriction of the same exact
record and passes strictly. Endpoint cast syntax is not used as a substitute
for constructor evidence.

These migrations removed the last consumers of the old source
`PairedCast` catch-up aggregate, so its Def/Proof pair has been deleted
without a shim. The next right-side blocker is the paired-value root, followed
by the paired outer-cast dispatcher; both still state their contracts using
the removed aggregate.

The live `cast⊑⊑ᵀ` value-catch-up dispatcher also succeeds. It is exhaustive
over all eleven `Widening` constructors: atomic identities use the identity
proof, structural casts use the inert proof, sequences use the sequence proof,
source-only instantiation uses the `ν`-indexed proof, and bare unseal uses
source reveal. The instantiation clause simultaneously matches the inner
index as `ν`, the cast shape as `shape-inst`, and composition as `comp-ν`;
the unseal clause matches `tagˣ`, `id★`, `shape-unseal`, and
`comp-tagˣ-id★`. Agda accepts the structural recursion directly, including
the callbacks passed only to sequence and instantiation, without a postulate,
termination pragma, or auxiliary admissibility alias. The focused prefix
proof passes strictly.

The next paired-root audit found a deletion opportunity rather than another
aggregate to migrate. The standalone paired-value root, mixed paired
outer-cast Def/Proof/Lemma, old paired-cast frame, its transport Lemma, and
the superseded active-value-roots Def had no semantic consumers outside the
inventory spine and were deleted. The separate live ordinary root records,
quotient recursion contract, and active synchronization contract remain for
the future operational SCC. A second strict-only
source-`ν` paired-all target-closing triple was likewise removed from its
inventory spine and deleted.

The obsolete ordinary-down-application and source-down-application families
were also self-contained behind the terminal-backward inventory spine. Live
QTIP has only `paired-downᵀ`, so their ten scheduling, synchronization, frame,
root, and cases modules were deleted rather than adapted. The separate
zero-consumer source-down compatibility helper in `proof/Quotient/` was
deleted with them.

The three live aggregate boundaries now use exact constructors. Right
value-catch-up has reveal, conceal, and widening frame fields; source one-step
framing has the same three fields; and function-cast beta has reveal,
conceal, live widening, and a separate quotient-close field. The
function-beta implementation is split into focused conversion, widening, and
quotient proofs with a 56-line assembly. The focused contracts and case
proofs pass strictly. Their larger dispatchers stop only when they reach
other already-retired constructor clauses.

Terminal-forward integration now accepts the exact right paired-frame record
directly. No canonical provider has been fabricated. Constructor-specific
transport plus neutral paired framing still leaves a real semantic question
when the transported target cast is active: the target cast must be
terminalized inside the operational right-dispatch SCC before the result is a
value.

The correspondence layer also received a stable checking-time cut. The
lineage theorem moved from the misleading left-silent subtree to
`proof/Store/Lineage/NuImprecisionStoreCorrespondsLineageTransportProof.agda`.
Its statement has no silent-result premise, and both it and the exact paired
conversion transport pass focused strict checks in under six seconds.
`NuImprecisionQuotientDownTransportProof.agda` now has a strict
`quotient-down-evidence-transportᵀ` theorem for recursive clients; the
canonical indexed-result theorem is a small corollary.

The right no-bullet migration is complete. Its only quotient-prefix case is
`paired-downᵀ`, and its two active closing cases use `closeᵀ`; reveal, conceal,
and widening remain explicit. The main proof shrank from 2,677 to 1,766 lines
and passes strictly together with its direct Lemma. The now-unreferenced
generic and right-silent paired-cast transport Def/Proof family was deleted.
The right value dispatcher likewise has one exact quotient-down/up frame and
passes strictly.

The two final source-`ν` source-only proofs now pass strictly. Their contracts
carry `AssumptionMembershipUnique Φ` explicitly, and their allocation results
supply all ten source-lift coherence fields. The `ν ★` cast proof does not
assume that every post-allocation widening is a single instantiation:
identity, inert, sequence, and instantiation casts are all possible. It
therefore exposes one recursive `WorldCoherentLeftValueCatchupPrefixᵀ` call
on the complete post-allocation cast relation. The eventual source-runtime
provider must discharge that honest recursive edge with the existing
well-founded source-administration measure. Both completed Proof roots have
left the known-incomplete list and are imported by the unassembled strict
spine. Source narrowing now carries membership uniqueness through all three
framed branches and reconstructs all ten source-lift coherence fields, so it
has also left the list. A cached ordinary source-`ν` consumer was missing the
same explicit uniqueness argument; repairing that call makes it strict.
Only terminal-forward integration remains on the known-incomplete list.

The compiler migration found a real negative result. Canonical cast plans do
not in general satisfy `ReductionClosedQuotientWideningCompatible`: the
strict counterexample
`proof/Compilation/CompileCastWideningCompatibilityCounterexample.agda`
uses the actual plans for `∀ X. X ⇒ X` versus `★ ⇒ ★` and derives the
impossible bridge `★ ⊑ A₁ ⇒ A₂`. At a value boundary the existing
`WorldCoherentQuotientFinalCatchupᵀ` is the sound up-to-reduction replacement,
but finite reduction cannot repair a pending boundary under a lambda or
around an open variable.

The compiler-origin pending-close experiment succeeded on all three decisive
tests before its source was deleted. The actual
polymorphic-identity/dynamic-function cast-plan pair inhabited the boundary; a
reduction-closed compatible widening closed it with live `closeᵀ`; and the
operational value case needed no widening compatibility. Its negative
conclusion remains: one top-level pending node whose inner relation is
ordinary QTI cannot be promoted unchanged. Pending sites can occur under
lambdas, type lambdas, `ν`, and either application child, where a root-level
`ordinary QTI ⊎ pending close` result is not structurally closed and reduction
cannot expose the site.

The required compiler relation must therefore be syntax-directed and
recursive, with an ordinary-QTI embedding and a pending constructor whose
inner premise is the compiler relation itself. That constructor cannot
universally require `QuotientNarrowingEliminationCompatible`. The strict
`CompileCanonicalDownCompatibilityExperiment.agda` refutes that invariant
for every quotient index: canonical function downcasts from
`★ ⇒ ℕ` expose the already-bad polymorphic-identity versus dynamic-function
widenings contravariantly, forcing the impossible indexed relation
`★ ⊑ A₁ ⇒ A₂`. The minimized counterexample checks in 3.12 seconds; importing
the endpoint-completeness theorem had caused two unproductive ten-minute
checks and was unnecessary.

The next compiler experiment must use a weaker direct operational
pending-down boundary, or separate compatible and incompatible pending
constructors, and must test recursive sites under binders and applications.
Do not add this compiler relation to live QTI, restore `up⊑upᵀ`, strengthen
`CastPlan` with either false compatibility invariant, or pass the new
relation directly to `ClosedNuDGG`. Its eventual consumer is a
compiler-specific operational DGG theorem.

Function-cast beta exposes the same operational boundary. The old pure
quotient-application island is still a genuine live consumer, so it cannot be
deleted yet. Its selected replacement is
`WorldCoherentSourceFunctionCastBetaPairedQuotientPostTargetᵀ`; completing it
requires recursive right-step/quotient-frame dispatch after target `β-↦`,
including source-value catch-up and source-blame propagation.

The post-target audit sharpens this obligation. After the two outer
function-cast beta steps, the inner beta redexes are blocked until the exposed
arguments `W ⟨ c ⟩` and `R′ ⟨ e ⟩` become values. The worker must therefore
administer those arguments through the live right dispatcher and use left
value catch-up when the target becomes a value. After both inner beta steps,
the bottom relation is derivable with two nested live
`closeᵀ (paired-downᵀ ...)` edges. The existing mutual compatibility
invariant already supplies exactly the two domain-elimination and two
codomain-widening facts needed by those edges; no new term-imprecision
constructor is required.

The smallest remaining assembly is a ranked dispatcher/post-target SCC:
ordinary QTI recursion decreases structurally, quotient function beta
decreases the function-spine rank, and exposed-argument administration
decreases `pendingAdministrationRank`. Use accessibility or a lexicographic
worker, never `TERMINATING`. The old
`WorldCoherentRightOneStepQuotientFrameRecursionᵀ` and quotient active-value
contracts mention retired `up⊑upᵀ`, omit live closing compatibility, and have
no semantic consumers. Replace them with exact live-close contracts only
where the dispatcher needs them; otherwise delete them. Once source, right,
and terminal-forward orientations pass, delete both the pure quotient
application and pure paired-quotient relation Def/Proof/Lemma families.

The zero-consumer half of that cleanup is complete. The obsolete outer
quotient-frame recursion definition and the four quotient active-value
root/synchronization modules formed a self-contained five-module island.
Their only external importer was the terminal-backward inventory spine, so
all five modules and those inventory imports were deleted: 481 lines left the
migration surface without touching the live `QuotientDownActive*` family.
The focused live quotient-down synchronization check and `make audit` pass.
The broad backward spine now reaches the independent live source-seal
cancellation proof, whose old exhaustive analysis still mentions
`up⊑upᵀ` and other retired constructors; that proof must migrate rather than
being discarded because source reveal/unseal catch-up consumes it.

That live proof has now migrated without changing
`SourceSealCancellationᵀ`. Its exhaustive analysis uses
`closeᵀ (paired-downᵀ ...)` for the quotient case, the direct live paired
reveal, conceal, and widening constructors, and no
`⊑cast⊑idᵀ` compatibility branch. Strict checks pass for the Proof, its
canonical Lemma, and both immediate source unseal/reveal consumers. This
removes the next retired-constructor boundary from the backward dependency
cone while preserving the theorem used by source catch-up.

The attempted nonrecursive implementation of the three live quotient-down
active roots was also rejected. The existing target identity, sequence, and
untag context lemmas begin with ordinary QTI and an already completed
right-value catch-up result. The quotient-down roots instead begin with a
target value inside `paired-downᵀ`; after the target root step the paired
downcast is erased or split. Thus those context lemmas cannot reconstruct the
required bottom quotient edge directly. Compatibility-directed
representative elimination and the ranked target-administration worker must
run first. The exact next contract is therefore a ranked paired-down value
catch-up boundary, carried with the closing widening evidence supplied by
function elimination, rather than three fabricated root adapters.

That entry boundary is now strict in
`NuImprecisionWorldCoherentRightOneStepQuotientDownValueAccDef`. It starts
with source and target values at one exact coherent world, retains the live
paired narrowing and closing widening composition and compatibility evidence,
and exposes accessibility at the two-cast target pending spine. Contract
checking also found that this boundary is not itself a recursively closed
worker. In the target identity case, a valid
`non-function-elimination (target-non-function non-function-id)` erases the
target downcast, leaving only the target widening pending. The original
quotient index and source down/up state remain semantically necessary, but
neither an ordinary QTI edge nor an ordinary `TargetAdministrationSpine` can
be reconstructed from that residual.

The same issue occurs in the sequence and successful-untag cases with target
residual spines of three and one casts respectively. Their
`pendingAdministrationRank` is smaller, so termination is not the obstacle.
The recursive state must instead range over an arbitrary target pending-cast
list while retaining the original source paired-down/close boundary and its
compatibility evidence. Each branch must either expose an ordinary
representative and delegate to the existing target pending-cast worker, or
descend through `compatible-quotient-functionᴿ`. The checked two-cast contract
should remain the entry wrapper for that generic residual SCC, not be mistaken
for its implementation.

That generic state is now strict in
`NuImprecisionWorldCoherentRightOneStepQuotientDownResidualAccDef`. In
addition to the original paired-down/close evidence, it retains a reduction
trace from the original two-cast target to
`applyTargetPendingCasts W cs`. The first trace step is the simulated target
step and every remaining step is `keep`; accessibility is measured at the
current value and pending list. This operational-origin invariant makes the
identity, sequence, and successful-untag residuals direct instances without
inventing an ordinary intermediate imprecision index that
`non-function-elimination` does not provide. The statement checks strictly in
5.17 seconds.

The keep-only residual worker is not meant to absorb allocation or blame.
Those are leaf handoffs because allocation changes the world and blame ends
the branch. The next proof experiment must test whether compatibility
inversion can either close each keep-only residual or reach one of those
leaves. If it needs the ordinary target pending-cast worker before exposing an
ordinary representative, then the missing object is a quotient residual plan
indexed by the original boundary—not another QTI constructor or a fabricated
ordinary index.

The entry-adapter experiment validates the value half of this design.
Identity, sequence, and successful untag each construct the required
one-step keep trace and a strict `pendingAdministrationRank` decrease.
Instantiation and seal/unseal roots are impossible for the target narrowing,
and a blame body contradicts the target value premise. Failed untag is the one
real terminal exception:
`((V′ ⟨ G ! ⟩) ⟨ H ？ ⟩) ⟨ u′ ⟩` steps to
`blame ⟨ u′ ⟩`, which cannot be represented by
`applyTargetPendingCasts W cs` with `Value W`. Closing that branch also
requires a source trace from the retained close boundary to `blame`; no live
lemma currently supplies it. The analogous retiring proof uses the obsolete
relation.

Therefore the generic residual state should remain value-only. Add one
dedicated live quotient-down bad-untag/source-blame leaf, then prove the
two-cast entry adapter from that leaf plus the whole residual worker. Do not
pollute recursive administration with a terminal blame alternative merely to
make one root fit.

That repair is now checked. The strict
`NuImprecisionWorldCoherentRightOneStepQuotientDownBadUntagRootDef` retains
the original quotient boundary and asks only for the reusable source-to-blame
trace. The strict `*QuotientDownValueAccProof` proves the two-cast entry
contract from the whole value-residual worker and this one leaf. It constructs
the identity, sequence, and successful-untag traces and rank decreases,
delegates failed untag to the leaf, and exhaustively eliminates the impossible
roots. The Def and Proof checks take 5.60 and 7.00 seconds. The Proof is
registered in `NuDGGUnassembledProofsStrictSpine`, and `make audit` reports no
uninventoried strict Proof modules. The updated 366-module unassembled spine
also passes strictly after an approximately 209-second interface refresh.
Treat that as a phase-gate cost; continue using the 5–7 second leaf checks
during development.

The remaining semantic work at this boundary is now explicit: implement the
keep-only residual worker and the lower bad-untag source-blame theorem, then
assemble the entry contract. Neither missing inhabitant is evidence for
broadening QTI.

The bad-untag boundary has now been lowered one cast further. The strict
`NuImprecisionWorldCoherentQuotientDownBadUntagSourceBlameDef` asks for the
source downcast itself to reach blame and omits all closing-widening evidence.
The strict
`NuImprecisionWorldCoherentRightOneStepQuotientDownBadUntagRootProof` is a
thin adapter: it lifts that trace through the closing widening and appends
the enclosing blame step. The source `gen` branch is supported by the repaired
`SourceValueGenTargetGroundAgreementᵀ`, whose `Value`, `No•`, and target-value
premises exclude the earlier active-source-untag counterexample. These Proof
modules are inventoried in `NuDGGUnassembledProofsStrictSpine`. Focused strict
checks take about six seconds each.

An exhaustive audit of the lower bad-untag theorem leaves one reusable proof
ingredient: after exposing an ordinary source tagged value, synchronize its
ground tag with the coherent target tag. Source-only variable and seal cases
are impossible in the two live quotient-down modes; base, function,
universal, and `gen` cases close by ground-shape inversion and tag
cancellation. This is a focused coherent-tag theorem, not a reason to add a
QTI constructor.

The first residual datatype separated ordinary bottom, ordinary opening,
rank-decreasing target keep, and source blame. Later checking showed that this
operational trace could not reconstruct the current quotient derivation,
widening pair, composition square, or reduction-closed compatibility. Its
zero-consumer definition has therefore been deleted; function-frame beta
remains at the whole-application root.

A proposed two-way target-instantiation classification—ordinary opening or
the existing bare-`Λ` target-instantiation creation rule—is false. The checked
round-trip regression in
`NuImprecisionReductionClosedQuotientExamples.agda` uses
`∀X. ∀Y. X ⇒ Y` on the source quotient edge and
`∀Y. ∀X. X ⇒ Y` on the target edge. The target closing widening reduces by
instantiation while the source remains behind two inert casts. There is no
ordinary edge from `∀X. X ⇒ ★` to `∀Y. ∀X. X ⇒ Y`, and the source is not a
bare `Λ`, so neither proposed branch applies. The proof therefore requires
a third operational quotient-instantiation residual that preserves the
original paired-down/closing boundary and its genuine `∀` permutation.

An intermediate opaque-trace allocation boundary retained the universal
permutation but still could not produce the logical quartet required after
the framed target step. It also had zero importers once the direct typed path
was stated, so it has been deleted. The active `inst` is not folded into the
ordinary `TargetAdministrationSpine`, because the ordinary
pre-instantiation edge is false in the permutation example.

That direct active-instantiation boundary is now stated by the 164-line
`NuImprecisionWorldCoherentRightTargetQuotientDownPendingNuAllocationPathAccDef`.
It retains the current proof-relevant quotient representative, both normalized
`∀`-permutation paths and their agreement with the raw permutations, the
current quotient widening pair and composition square, reduction-closed
compatibility for the active source widening and target `inst`, and the typed
outer administration spine. Its result is the existing world-coherent indexed
right-value catch-up package, together with the exact right-context action and
right-only store prefix. The strict definition check passes in 3.51 seconds.
This is the semantic target allocation leaf; it is not a new term-imprecision
constructor and does not assert the false ordinary pre-instantiation edge.

The keep-only residual trace cannot derive the four current logical witnesses
retained by that leaf: the exposed quotiented term derivation, current
`QuotientWideningPair`, current quotient composition square, and current
reduction-closed compatibility. The next proof boundary must therefore either
produce those witnesses while processing the residual or deliberately narrow
the caller to the direct active-`inst` state. Do not hide this gap behind a
larger dispatcher or an unproved conversion from the operational trace.

The correct producer boundary is now stated by the 136-line
`NuImprecisionWorldCoherentRightTargetQuotientDownPendingCastsAccDef`.
It starts from the current quotient term derivation, widening pair,
composition square, and active reduction-closed compatibility, keeps the
active target cast separate from the ordinary outer
`TargetAdministrationSpine`, and returns the same contextual catch-up package
as the allocation leaf. Its strict definition check passes in 6.27 seconds.
The `closeᵀ (paired-downᵀ ...)` frame must transport the quartet through inner
catch-up and pass it to this worker. An inert active cast can close the
ordinary term relation before delegating the outer tail; an active `inst`
reduces once and calls the allocation-path leaf. Identity, sequence, unseal,
and tag-cancellation cases must update the quartet structurally rather than
erase it into an opaque target trace.

The older `QuotientDownResidualCorePlan` and opaque-trace allocation residual
were not the semantic worker: their keep-only trace could not reconstruct the
current quartet. Both had zero importers after the typed worker boundary was
introduced, so they have now been deleted. The still-used value residual
adapter remains until the typed worker is assembled into its one-step caller.

The first two worker layers are now strict. The 83-line
`NuImprecisionWorldCoherentRightTargetQuotientDownPendingCastsAccProof`
decides whether the active target cast is inert. In the inert branch it builds
the live `closeᵀ` relation from the current quartet and invokes the canonical
ordinary pending-cast worker on only the outer tail; the proof preserves the
accessibility decrease, context action, and right-only lineage. It delegates
only the non-inert active-cast residual. The focused strict check passes in
6.71 seconds.

The 140-line active-`inst` Def and 111-line Proof form the next exact cell.
The Proof exposes the `quotientᵖ` representative, uses the normalized source
and target paths with reflexive agreement proofs, derives the strictly smaller
post-`β-inst` administration rank, invokes the allocation-path leaf, and
prepends `β-inst` beneath the ordinary outer cast tail. Its focused strict
check passes in 7.95 seconds. This cell is conditional only on the direct
allocation-path contract; it does not use the opaque-trace residual or assert
an ordinary pre-instantiation edge.

The non-inert dispatcher is now tighter and the instantiation cell is wired
into it. `ActiveWideningShape` proves that a non-inert widening has exactly an
identity, sequence, unseal, or instantiation shape. The pending worker invokes
the checked instantiation cell directly; its remaining residual carries
`NonInstantiationActiveWideningShape` and therefore contains only identity,
sequence, and unseal. Untag is impossible at this closing-widening boundary
and remains only in lower narrowing/cancellation paths. Focused strict checks
pass for the classifier and revised pending worker in 3.8 and 7.3 seconds.
The allocation-path leaf remains conditional.

Checking-time cleanup follows one rule during migration: split canonical
support that survives the selected relation, and shrink retiring files by
deletion. Therefore the 2,090-line quotient-value analysis will not be
reorganized, while stable portions of simulation, value transport, source
widening, and reveal/conceal are receiving focused cuts.

A fresh hotspot audit identified three stable cuts. The first is complete:
477 lines of indexed-imprecision renaming/lifting now live in
`proof/Core/Properties/NuImprecisionIndexedRenamingProperties.agda`.
`MaximalLowerBoundsWf.agda` shrank from 20,373 to 19,945 lines, and its direct
fan-out fell from 174 files to 22; 164 direct consumers now depend on the
focused module instead. The new module and reduced MLB file check in about
four and five seconds with warm dependencies. After the one-time 255-second
cold rebuild, `NuDGGUnassembledProofsStrictSpine.agda` passes.

The second stable cut is complete. The 489-line
`proof/Catchup/Simulation/NuImprecisionWeakOneStepResultTransport.agda`
owns weak-result endpoint transport, reindexing, and coherence preservation;
the 29-line
`proof/Core/Equality/HeterogeneousEqualityTransport.agda` removes duplicate
local heterogeneous-transport helpers. `NuImprecisionSimulationCore.agda`
shrinks from 14,880 to 14,418 lines, and its direct fan-out falls from 85 to
71; the focused transport module has 55 direct importers. Fourteen consumers
drop the simulation-core import entirely. The focused modules, reduced core,
representative live consumers, source/import audit, and diff audit pass.
One attempted historical quotient-final consumer reached the obsolete
quotient-value analysis through its stale `down⊑downᵀ` branch. The later
retirement checkpoint deleted that provider cone rather than repairing it.

The third stable cut is complete. The 30-line
`NarrowWidenStoreInvariantDef.agda` defines `StoreUnique` and `StoreDetWf`;
the 133-line `NarrowWidenStoreInvariantProof.agda` constructs and preserves
them. The proof reuses the canonical `NuStoreProperties` membership,
uniqueness, and binding facts, and the obsolete duplicate
`StoreUnique-inst` is gone. `NarrowWidenProperties.agda` shrinks from 4,385 to
4,230 lines. Twelve consumers now import the focused boundary directly.
Strict checks pass for the new modules, reduced monolith, `Compile.agda`,
term narrowing, store correspondence, cast imprecision, and the other live
representatives. `CompileTermImprecision.agda` still stops independently at
its retired `up⊑upᵀ` use.

The fourth stable cut is complete. The 91-line
`proof/Core/Properties/NarrowWidenBinderProperties.agda` is now the canonical
home of narrowing/widening opening and allocation under type binders.
`NarrowWidenProperties.agda` shrinks from 4,230 to 4,156 lines and its direct
importer count falls from eight to four; the four binder consumers import the
focused module directly with no compatibility re-export. Strict checks pass
for the focused module in 2.91 seconds, the invalidated monolith in 49.77
seconds, the matched-`β-gen` consumer in 2.49 seconds, and the source inert
bullet consumer in 67.07 seconds. The two simulation monoliths were not
rechecked merely to exercise an already checked export.

The fifth stable cut removes both misplaced support and dead code from
`ReductionProperties.agda`. The 93-line
`proof/Core/Properties/TypeInjectivityProperties.agda` now owns constructor
and injective-rename facts used by three target-closing consumers. The
zero-consumer store-change/type-renamed reduction API was deleted rather than
wrapped. `ReductionProperties.agda` shrinks from 1,242 to 1,051 lines.
Strict checks pass for the focused module in 4.42 seconds, the reduced
monolith in 5.56 seconds, and the paired-reveal consumer in 7.84 seconds;
`make audit` also passes.

The sixth stable cut begins retiring the 19,945-line
`MaximalLowerBoundsWf.agda` selector development instead of splitting its
obsolete algorithm. The 389-line
`proof/Core/Properties/NuImprecisionTransitivityProperties.agda` now owns
indexed context composition, binder-aware transitivity, and its
occurrence/non-variable support. Five exact external consumers import it
directly, with no compatibility re-export. The endpoint monolith shrinks to
19,606 lines and its direct importer count falls from twenty to eighteen.
Strict checks pass for the focused module in 4.81 seconds, the one-time
invalidated monolith in 47.98 seconds, imprecision composition in 2.95
seconds, endpoint maximality in 6.52 seconds, and endpoint quotienting in
35.96 seconds.

The seventh stable cut extracts the 262-line
`proof/Core/Properties/NuImprecisionWfBridgeProperties.agda`. It owns the
legacy/indexed forgetting and reconstruction bridge, target lifting, and
target-context dropping. Nine clients import it directly; the endpoint
selector imports it non-publicly and does not re-export it. The selector
shrinks from 19,606 to 19,402 lines and its direct importer count falls from
eighteen to thirteen. Strict checks pass for the focused module in 4.29
seconds, the invalidated selector in 50.89 seconds, the cast-compatibility
counterexample in 90.41 seconds, endpoint maximality in 2.33 seconds, and
factorization shape in 24.60 seconds.

The eighth stable cut extracts the 784-line
`proof/Core/Properties/NuImprecisionBinderPermutationProperties.agda`. It
owns indexed context permutation, the corresponding type renamings, and
permutation transport for well-formed indexed imprecision. Four exact
external consumers import it directly; the endpoint selector keeps only a
non-public transition import. The selector shrinks from 19,402 to 18,665
lines. The focused module checks in about five seconds from the invalidated
state and two seconds warm, the selector in about fifty seconds, and the two
small representative consumers in about twenty-two and three seconds. The
14,000-line simulation modules remain deferred to the migration phase gate.

The ninth stable cut extracts the 333-line
`proof/Core/Properties/NuImprecisionBinderDropProperties.agda`. It owns the
298-line source-only and paired binder-drop island, including context
membership transport and unused-opening algebra. Eight exact external
consumers import it directly; the endpoint selector again imports it
non-publicly and does not re-export it. The selector shrinks from 18,665 to
18,367 lines and now has only five direct external importers. Strict checks
pass for the focused module in 2.33 seconds, the invalidated selector in
48.43 seconds, and two small consumers in 2.23 and 1.93 seconds. A warm
recheck takes about two seconds. `make audit` still reports zero unresolved
imports, zero unsafe roots, and zero uninventoried strict Proof modules.

The endpoint-selector retirement is now complete. The only three live clients
needed the genuine `CommonLowerBoundᵢ` concept or a generic occurrence fact.
The former now lives in the 19-line
`proof/EndpointMLB/Core/EndpointLowerBoundDef.agda`; the latter lives in
`TypeProperties.agda`. The selector-independent no-GLB counterexample remains
as a 112-line strict regression and now matches the `NonVar` premise of raw
`ν` directly. The evidence-directed counterexample tail, the 18,367-line
`MaximalLowerBoundsWf.agda`, its 136-line explicitly obsolete postulate
experiment, and its 3,728-line historical work log are deleted. Strict checks
pass for the new Def in 3.61 seconds, `TypeProperties` in 3.46 seconds, the
retained counterexample in 5.26 seconds, completeness in 12.74 seconds,
maximality in 5.58 seconds, and factorization shape in 46.39 seconds.
`make audit` passes.

The tenth stable cut extracts the 375-line
`proof/Core/Properties/NuCastModeRenamerProperties.agda`. It owns the
coercion-mode renamers for left insertion, adjacent name swapping, identity,
and composition, with no term-imprecision or world dependency. Seven
external consumers import it directly; `NuImprecisionSimulationCore.agda`
keeps one non-public import and shrinks from 14,421 to 14,095 lines. Strict
checks pass for the focused module in 27.4 seconds, the invalidated simulation
core in 28.3 seconds, and two small representative allocation/renaming clients
in 27.5 and 24.0 seconds. The broad simulation assembly remains deferred to
the migration phase gate.

The isolated raw-imprecision selector is also retired. Its only Agda client
was the standalone `MlbTypeTest` suite; the live compiler has long used
`EndpointCanonicalMLBSimple` and `MLB-monotoneᵖ` instead. The 4,604-line
`MaximalLowerBounds.agda`, its 253-line test, and the 308-line stale
`CompilePlan.md` are deleted, and the standalone-root inventory no longer
lists the removed test. `make audit` passes with no unresolved import and no
uninventoried strict Proof module.

The eleventh stable cut extracts the 142-line
`proof/Core/Permutation/ForallPermutationPath.agda`. It is the canonical home
of normalized `∀`-permutation paths, their elementary steps, reflexivity,
symmetry, transitivity, arrow and universal lifting, and normalization from
raw `ForallPermutation`. The former world-coherence Def shrinks from 202 to
81 lines, imports only the path operations needed by its theorem, and does not
re-export them. Every exact consumer now imports the focused Core module
directly. Strict checks pass for the path module in 3.34 seconds, the reduced
world Def in 6.05 seconds, the path properties in 6.18 seconds, and a
representative cases proof in 3.64 seconds.

The twelfth stable cut extracts the 614-line
`proof/Catchup/Simulation/NuImprecisionIndexedIdentityTransport.agda`.
It owns identity renaming for indexed imprecision, source/target/paired
replacement transport, target-lift replacement transport, endpoint transport
for arrows, universals, and source-only `ν`, and their shape refinements. All
thirteen exact external consumers import it directly; two drop
`NuImprecisionSimulationCore` entirely. The simulation core keeps a
non-public import for only its five remaining uses and shrinks from 14,095 to
13,584 lines; its direct importer count falls from 71 to 69. Strict checks
pass for the focused module in 4.42 seconds, the invalidated core in 61.71
seconds, and three representative consumers in 7.91, 9.93, and 9.17 seconds.
`git diff --check` and `make audit` pass.

The thirteenth stable cut extracts the 395-line
`proof/Catchup/Simulation/NuImprecisionKeepCastFrameSupport.agda`. It owns
source-`keep` and universal-catch-up composition, the target-cast weak-step
frame with its transport/coherence facts, and indexed source narrow/widen cast
frames. All fifteen exact external consumers import it directly;
`NuImprecisionSimulation.agda` retains one non-public import for later
polymorphic uses, shrinks from 4,134 to 3,804 lines, and falls from eighteen
direct importers to three. Strict checks pass for the focused module in 7.88
seconds, the invalidated monolith in 15.87 seconds, and three representative
consumers in 5.48, 3.86, and 9.13 seconds.

The complete over-2,000-line audit now leaves no further profitable
phase-local split in `NuImprecisionSimulation.agda`. The remaining large
`NarrowWidenProperties`, endpoint permutation/factorization, and compiler
files are cohesive or low-fan-out and should remain intact during this phase.

The 2,090-line quotient-value retirement is complete. A transitive import
audit showed that no public DGG theorem, terminal strict spine, or unassembled
proof spine reached it; only a historical seven-import provider block in
`NuDGGStrictSpine` kept the cone on the regression surface. After removing
that block, the source/import audit showed that no semantic root reached the
cone, so the 21-file quotient-value, old ground-value elimination, source-tag,
InstFunTag, classification, and unused final-provider cone was deleted. The
earlier cached 26-second strict-spine pass was not a valid fresh integration
result: after the dependency refresh, a 241-second check correctly stops in
the independent live `CompileTermImprecision` consumer at its retired
`QTI.up⊑upᵀ` use. The two
`NuImprecisionWorldCoherentQuotientFinal*CatchupDef` capability definitions
remain temporarily because live value-prefix consumers still take them as
parameters; migrate those consumers before deleting the final two contracts.

The separate 37-file quotient-instantiation path/provider experiment is now
deleted. Its normalized path cases, identity specializations, representative
provider, and compiler pending-close root had no semantic consumer: only the
strict inventory spine and one Makefile check kept them on the regression
surface. Source search finds no stale Agda or Makefile import.

Exactly two live consumers still mention the temporary
`NuImprecisionWorldCoherentQuotientFinal*CatchupDef` capabilities: ordinary
value-prefix catch-up and its runtime-sibling variant. Their replacement is
one source-oriented accessibility-ranked quotient-close terminalization
worker over a reconstructed live `closeᵀ (paired-downᵀ ...)` edge. A
caller-supplied continuation distinguishes the ordinary and sibling outcomes.
The target-oriented pending-cast worker is not a substitute for this source
worker.

The target closing-`inst` allocation leaf requires a different abstraction:
a right-oriented typed target-instantiation quotient path view that transports
the quotient derivation, closing pair, composition quartet, compatibility, and
normalized target permutation through `bind`. It also needs a path-aware rank
decrease; the former opaque operational trace could not reconstruct those
witnesses and its two zero-consumer definitions are deleted.

The remaining non-instantiating active target casts are identity, sequence,
and unseal. Their rank decreases and administrative reductions already exist,
but none of the three cases has the needed semantic conclusion. The next
theorem must preserve the original quotient evidence while the target cast
spine normalizes and expose the final ordinary imprecision relation only at
the end. Identity needs quotient-target identity elimination, unseal needs
quotient-specific seal cancellation, and sequence must not require an
intermediate composition-quartet factorization: such an intermediate ordinary
index need not exist.

The immediate migration order is:

1. replace the two temporary final-catch-up consumers with the source-oriented
   ranked quotient-close worker and delete their capability Defs;
2. state and prove the right-oriented target-instantiation path view and its
   path-aware rank decrease;
3. prove non-instantiating target normalization without intermediate quartet
   factorization;
4. assemble the target pending worker and allocation leaf;
5. use that operational SCC in quotient function-cast beta; and
6. resume compiler and remaining consumer migration, deleting each obsolete
   cone as its replacement gate passes.

The migration Makefile's quotient-world list now names the existing
`NuImprecisionQuotientEliminationCompatibilityRename.agda`; the stale,
absent pre-rename filename is gone.

Two independent migration debts remain from earlier invalidation:
`GenSafeMismatchBlameRegression` still pattern-matches the pre-`NonVar` `ν`
shape, while `CompileTermImprecision` still reaches the removed
`up⊑upᵀ`. Classify those clients for migration or deletion; do not restore
obsolete constructors to keep them checking.

Invalidating the other two consumers exposed existing migration debt rather
than import failures. The paired-lambda widening consumer has nine missing
`NarrowWiden` cases in its own dispatcher and belongs to the retiring
paired-lambda surface, so it should be deleted with that surface instead of
repaired. The source paired post-beta consumer reaches the selected-migration
`NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationDef`,
which still imports retired `PairedConversion`; that live source path remains
a migration gate.

Further safe cuts are store-relation structure, endpoint-shape inversions, and
coercion-mode renaming algebra. These are lower priority than the operational
quotient SCC unless they directly reduce a file being invalidated by the
migration. Do not split the retiring quotient-value monolith or migration
experiments. The endpoint selector, `MaximalLowerBoundsJunk.agda`, and their
historical plans are deleted; Git history is the archive.

The source/import audit passes after this checkpoint: all local imports
resolve, all five strict safety roots remain safe, the one known-incomplete
Proof module is explicitly excluded, and no strict-looking Proof module is
left without either a Lemma consumer or the unassembled-proof inventory
spine.

Do not use `All.agda` as the DGG completion criterion. It includes independent
and historical development surfaces. The final completion check is the strict
public DGG dependency cone plus the focused forward and backward terminal
spines.
