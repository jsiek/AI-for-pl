# Canonical world migration plan

## Current checkpoint

The live world is `proof.DGG.World._⊑ᶜ_`, indexed by complete source and
target `Ctx` endpoints.  The live cast-term imprecision relation, its typing
theorem, compilation preservation, `Sim`, `SimBack`, `MultiSim`, and
`MultiSimBack` now state their claims using this world and
`MultiWorldEvolution`.

The endpoint-to-center maps are arbitrary injections, not order-preserving
embeddings.  The change is forced by the checked
`SourceBindLiftLeftTrustedProbe`: a protected source pivot must move past a
fresh source or paired allocation while the other endpoint alignments remain
fixed.  The required endpoint map is injective but not order preserving.
Center changes produced by weakening and runtime allocation remain OPEs.

`SimProof` and `SimBackProof` are goal-free parameterized proofs.  They are
not yet closed theorems because several semantic closing and catch-up
interfaces still need canonical implementations.

`DynamicGradualGuaranteeDef` and `DynamicGradualGuaranteeProof` have been
migrated in place and check strictly.  The proof is parameterized by the two
multi-step simulations and the two direction-specific catch-up theorems.
`MultiSimProof` and `MultiSimBackProof` are complete and reduce those first
two parameters exactly to `Simᵀ` and `SimBackᵀ`.  Work therefore proceeds
top-down through the one-step proof parameters, while independent agents
discharge their semantic proof interfaces.

The first `All.agda` error is the obsolete `ParkedWorldDef` import of the
deleted `proof.DGG.CtxImp`.  This is not a reason to port `ParkedWorld`:
canonical simulation uses `openFramesᶜ γ ≡ []` and
`MultiWorldEvolution` directly.  The parked-world family should be deleted
after its remaining consumers are migrated.

## Milestones

### 1. Canonical CTI transport

Rebuild `TransportTermImprecisionProof.agda` in place as a proof of
`TransportTermImprecisionᵀ`.  Induct over `MultiWorldEvolution` and transport
every CTI constructor without importing `CtxImp`, `ParkedWorld`, or a
compatibility wrapper.

This milestone has two proof-engineering layers:

1. The sequence driver lifts a one-step CTI transport through
   `MultiWorldEvolution`. This layer is complete and checked in
   `TransportTermImprecisionProof`.
2. The one-step theorem transports every CTI constructor through one
   `WorldEvolution`. Its checked outer case split is complete in
   `TransportTermImprecisionStepProof`: `evolution-keep` is immediate, and
   each allocation is delegated to one of four explicit structural
   inductions: source bind, target bind, paired precise bind, and paired
   dynamic bind.

The second layer has genuine pre-induction obligations under term binders,
type binders, and source rebases.  A runtime bind outside a type binder has
store shape `store-bind (store-lift Σ) ...` when naively pushed inward, while
the CTI premise requires `store-lift (store-bind Σ ...)`.  Therefore the
one-step proof must use structural source, target, and paired extension through
world history; it must not pretend that an ordinary root `WorldEvolution`
commutes definitionally with scope.  Keep those structural inductions as
explicit module parameters while they are incomplete, then expose the closed
transport from a `...Lemma` module.

The source-bind induction now traverses every current CTI constructor. The
single `SourceBindScope` graph follows source allocation through term binders,
paired type binders, and source-only type binders while recording the source
thinning and deriving the center, context, store, and type-imprecision
commutation laws. Term abstraction, paired type abstraction, and source-only
type abstraction are therefore direct clauses of one induction. Its root
records `sourceRebaseCountᶜ γ ≡ 0`. Reveal pushes a synchronized direct-rebase
frame through the scope; conceal pops that exact frame, recursively through
protected term and type scopes. `TransportSourceBindProof` is goal-free and is
parameterized only by the genuine forward rebase-push induction.

The target-bind induction also traverses every current CTI constructor. Its
single `TargetBindScope` graph follows target allocation through the same
three scopes and derives the corresponding center, context, store, typing,
occupancy, and type-imprecision actions. In particular, its source-only
conversion clauses treat the newly allocated target variable separately;
they do not assume that every target name lies in the old renaming image.
Only target reveal and target conceal across a source rebase remain as module
parameters. Their exact statements live in `TransportTargetBindDef`, and the
goal-free parameterized proof lives in `TransportTargetBindProof`.

The precise and dynamic paired-bind inductions share one `PairedBindScope`
graph and one proof. Their root changes differ, but their actions through term
and type scope are identical. The proof renames both endpoints together and
traverses every current CTI constructor, including the paired conversion
position and alignment evidence. Its two source-rebase commutations are
stated in `TransportPairedBindDef`; the goal-free parameterized proof lives in
`TransportPairedBindProof`.

All four allocation kinds have complete ordinary structural inductions. The
old six universal source-rebase commutation interfaces are not the target:
they forgot reveal/conceal nesting and asked for false arbitrary pullbacks.
Keep a clause as a named parameter only when it requires a genuine separate
world-history induction; discharge ordinary same-scope clauses directly.

The first rebase-commutation pass exposed two definition-level issues rather
than missing proof ingenuity.  First, an OPE cannot represent the checked
protected-pivot crossing above.  `World` now uses `Injectionᵗ` endpoint maps,
and a direct source rebase stores a `PivotUpdateᵗ`: the new injection, the
selected alignment, and the fact that every other source pivot is fixed.
Second, reveal and conceal form a properly nested scope discipline.  A
universal conceal-pullback theorem is false because it forgets which reveal
introduced the rebase frame.

The source-bind transport is consequently stated as balanced world-history
operations. Its root starts at source-rebase count zero; reveal pushes a
synchronized direct-rebase frame through the bind scope; and conceal pops
that exact frame. Protected term, paired-type, and source-only type scopes
recurse through the stack. The same design must be applied to the target and
paired bind transports. Do not restore the six universal whole-CTI
commutation interfaces: they were stronger than the simulation call sites and
erased the nesting invariant needed for the reverse move.

The one-step and sequence transport APIs now both take the root
`sourceRebaseCountᶜ γ ≡ 0` premise. That premise has been threaded through all
live Sim and SimBack consumers. `TransportTermImprecisionStepProof`,
`TransportTermImprecisionProof`, `SimProof`, and `SimBackProof` all check with
zero goals and metas. Their remaining module parameters are the honest
balanced bind-scope operations, not an implicit claim that arbitrary rebased
histories commute.

### 2. Canonical CTI substitution

CTI preservation is now proved under a typed parallel term-substitution
scope. The full 23-constructor case split and every recursive call are checked.
The scope extends under a term binder and lifts under paired and source-only
type binders. The public `TermImprecisionSubstitutionᵀ` theorem is derived as
the single-environment corollary. `TermImprecisionSubstitutionProof` is
parameterized only by five genuine scope inductions: term extension, paired
type lift, source-only type lift, balanced rebase push, and balanced rebase
pop. Once those operations are closed, expose the instantiated theorem from a
`...Lemma` module.

### 3. Value catch-up

Produce closed canonical implementations of:

- `CatchupToMorePrecise`;
- `CatchupToLessPrecise`.

Migrate or replace the old boundary/parked implementation rather than
adapting it through aliases.  Preserve the direction-specific blame policy:
only catch-up to the less precise side may return source blame.

### 4. Semantic closing lemmas

Discharge the named closing interfaces consumed by `SimProof` and
`SimBackProof`, using CTI transport, substitution, and catch-up as their
pre-induction dependencies.  Add a `...Lemma` module for each closed theorem;
keep a `...Proof` module only when its proof remains parameterized by a genuine
separate induction.

The paired universal closing layer is now checked.  Its statement already
matches every root type-application call in `SimProof`.
`SimPairedAllClosingProof` performs target value catch-up, transports the type
argument and opened result relation, and composes the resulting type-
application trace and world evolutions.  It is parameterized only by the
genuine value-spine induction `SimPairedAllValuesᵀ`; that induction is the next
obligation before this proof can move to a `...Lemma` module.

The source-only universal closing layer is checked by the same architecture.
`SimSourceAllClosingProof` catches up the target, transports the dynamic type
argument and opened result relation, and composes the target trace and world
evolutions.  Its sole remaining parameter is the genuine value-spine induction
`SimSourceAllValuesᵀ`.

The paired ordinary-cast value layer is also checked against the current world.
`SimPairedCastValuesProof` has an exhaustive split over the source cast-root
reductions and no residual or step-classifier surface.  It factors each case
through the genuine source-only cast simulation and the value-level
consistency-square diagonal `RelatedValueCastSquareᵀ`, then reattaches the
unchanged target cast.  The diagonal is the separate value/typing induction
that rules out the empty bottom-type corner of the consistency square.

The source-only ordinary-cast value layer is checked as well.
`SimSourceCastValuesProof` has the exhaustive current-world cast-root split and
no residual or step-classifier surface.  The identity and blame rows close
directly.  Its module parameters are precisely the two left-endpoint ground
witness inductions, source generated-tag inversion, and the beta-instantiation
value-spine induction; it does not depend back on paired-cast simulation.

Source-only reveal cancellation is checked against its sole `SimProof` root
call.  `SimSourceRevealClosingProof` catches the unchanged sealed source value
up to a target value, transports the source-only occupancy evidence across that
target evolution, and applies the genuine source-seal inversion induction.
The identity roots are ruled out by the non-absent generator premise, while
blame and frame roots are impossible for the source value.  There is no reveal
classifier or residual-family surface.

Paired reveal closing is checked by the same top-down architecture.
`SimPairedRevealClosingProof` catches the target reveal body up to a value,
transports the target conversion typing, generator position, pivot alignment,
and representation relation, then invokes the genuine
`SimPairedRevealValuesᵀ` induction.  It composes the lifted target-body trace
with the returned reveal-root trace explicitly.  Its root split covers identity
reveal, conceal/reveal cancellation, blame, and frame propagation directly,
with no classifier or residual-family surface.

Primitive closing is checked in left-to-right evaluation order.
`SimPrimitiveClosingProof` catches up the target left operand, transports the
untouched right relation, catches up the right operand, and transports the first
value before applying the closed `SimPrimitiveValuesLemma`.  The lemma uses
canonical forms to identify the related target constants and takes the matching
delta step.  The closing proof explicitly composes both operand traces with the
delta trace and splits exhaustively over addition and conjunction evidence.

Target reveal-rebase closing now uses its honest term/CTI boundary. The world
is the sole balance carrier: `openFramesᶜ γ` is derived from role-tagged world
history, and each nested CTI node owns the world in which its frame is open.
There is no parallel `SourceRebaseStack` or stack-evolution relation.

`SimTargetRevealRebaseContextDef` defines a CTI-indexed evaluation-context
zipper. Its immediate edges are exactly the source evaluation positions of
the CTI constructors. Each edge stores the related sibling and conversion
evidence needed for reconstruction. `RebuildSource` carries the actual
constructor-form source-result equation, including store-change renaming of
siblings, types, casts, reveals, and conceals. Target-only CTI wrappers record
identity source reconstruction.

`ContextualTargetRevealRebaseClosingᵀ` keeps the public closing boundary fixed
and adds a focused CTI node, a path from the boundary to that node, its source
step, and source reconstruction. Its conclusion is exactly the existing root
closing conclusion. The public `SimTargetRevealRebaseClosingᵀ` is its
`focus-here` adapter, so no caller-facing interface changes.

The recursive proof skeleton is now in
`SimTargetRevealRebaseClosingProof.agda`. Every contextual application,
primitive, type-application, cast, reveal, and conceal case extends the zipper
before making its recursive call. Only the dynamic root families remain as
manifested semantic goals. The obsolete stack Def/Proof, catch-up, and
transport modules have been deleted.

The reason a world-only synchronized evolution cannot replace the stack is
recorded in `GammaDerivedFrameEvolutionAudit.md`. In the trusted
`TargetIdentityReveal` allocation, root worlds evolve from `[]` to `[]`, while
the nested CTI changes from `[X ↔ Y′, X ↔ Z′]` to `[X ↔ Y′]`. The outer
`X ↔ Z′` boundary becomes paired and the inner `X ↔ Y′` boundary survives.
Those nested worlds are not endpoints of one ordinary `MultiWorldEvolution`.
The strict `TargetRevealRebaseContextProbe.agda` pins both the ordinary root
evolution and the final paired-outer/target-rebase-inner CTI shape.

### 5. Closed simulation

Instantiate the parameterized one-step proofs to obtain closed `Simᵀ` and
`SimBackᵀ` theorems.  Then instantiate `MultiSimProof` and
`MultiSimBackProof` to obtain the corresponding multi-step theorems.

Follow the `SimProof` module parameters in declaration order.  Transport and
`CatchupToMorePrecise` are already active proof arcs; the next closing arc is
`SimPairedFunClosingᵀ`, followed by paired and source universal closing.  Reuse
finished value lemmas only when their statements have a clear independent
semantic role; delete the old classifier and residual-family surfaces.

### 6. Dynamic gradual guarantee

This migration is complete.  `DynamicGradualGuaranteeProof.agda` uses:

- `CompilePreservesImprecision.compile-preserves-imprecision`;
- `initialContextWorld` and its no-source-rebase theorem;
- canonical multi-step simulation and backward simulation;
- canonical value catch-up;
- `MultiWorldEvolution` throughout.

It retains none of the old `World`, `CtxImp`, or `ParkedWorld` result shapes.
The remaining task is instantiation after the four canonical dependencies are
closed, not another rewrite of the DGG theorem.

### 7. Closed-world retirement and gates

Delete the obsolete parked-world modules and old boundary/catch-up modules as
their last consumers disappear.  Migrate or retire remaining red example,
probe, inversion, and catch-up files rather than removing them silently from
the aggregate gate.  The migration is complete when `All.agda`, the
postulate check, and the example checkpoint suites are green.

## Validation at every milestone

- Load the changed module and its nearest consumer with Agda 2.8.0.
- Require zero diagnostics, goals, and invisible metavariables for completed
  modules.
- Run `git diff --check` and `make -C GTSFImp postulate-check`.
- Commit and push each milestone separately.
