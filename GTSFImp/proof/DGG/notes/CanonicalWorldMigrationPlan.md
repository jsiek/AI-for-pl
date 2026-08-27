# Canonical world migration plan

## Current checkpoint

The live world is `proof.DGG.World._⊑ᶜ_`, indexed by complete source and
target `Ctx` endpoints.  The live cast-term imprecision relation, its typing
theorem, compilation preservation, `Sim`, `SimBack`, `MultiSim`, and
`MultiSimBack` now state their claims using this world and
`MultiWorldEvolution`.

`SimProof` and `SimBackProof` are goal-free parameterized proofs.  They are
not yet closed theorems because several semantic closing and catch-up
interfaces still need canonical implementations.

The first `All.agda` error is the obsolete `ParkedWorldDef` import of the
deleted `proof.DGG.CtxImp`.  This is not a reason to port `ParkedWorld`:
canonical simulation uses `sourceRebaseCountᶜ γ ≡ 0` and
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
type abstraction are therefore direct clauses of one induction. Only target
reveal and target conceal across a source rebase remain as module parameters;
their exact statements live in `TransportSourceBindDef`, and the goal-free
parameterized proof lives in `TransportSourceBindProof`.

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

All four allocation kinds now have complete ordinary structural inductions.
The remaining work in this milestone is to prove the six source-rebase
commutations isolated by those inductions and instantiate the one-step
transport proof. Keep a clause as a named parameter only when it requires a
genuine separate world-history induction; discharge ordinary same-scope
clauses directly.

The first rebase-commutation pass exposed a definition-level obstruction, not
a missing induction. `CanRebaseSourceᵗ` itself commutes structurally through
both possible center actions: target-only allocation uses
`canRebaseSource-skipᵗ`, while source and paired allocation use
`canRebaseSource-keepᵗ`. However, a bind after a conceal-induced rebase has
world history `rebase ; bind`, whereas the current `⊑conceal-rebase²` rule can
only conclude a world whose last change is rebase, namely `bind ; rebase`.
These histories have the same endpoint contexts and corresponding interpreted
geometry, but they are different inhabitants of `_⊑ᶜ_`. Therefore the six
parameters cannot be discharged by adding proof adapters. Before completing
this milestone, replace the reveal/conceal rules' fixed final-change indices
with one genuine source-rebase graph that is closed under world evolution.
Gate that relation change through the required concrete reduction square and
imprecision ladder; do not add a compatibility equality between world
histories.

### 2. Canonical CTI substitution

Implement `TermImprecisionSubstitutionᵀ` over `bind-termᶜ`.  Keep the
substitution induction separate from the simulation induction and expose the
finished theorem through a `...Lemma` module when no parameters remain.

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

### 5. Closed simulation

Instantiate the parameterized one-step proofs to obtain closed `Simᵀ` and
`SimBackᵀ` theorems.  Then instantiate `MultiSimProof` and
`MultiSimBackProof` to obtain the corresponding multi-step theorems.

### 6. Dynamic gradual guarantee

Rewrite `DynamicGradualGuaranteeProof.agda` using:

- `CompilePreservesImprecision.compile-preserves-imprecision`;
- `initialContextWorld` and its no-source-rebase theorem;
- canonical multi-step simulation and backward simulation;
- canonical value catch-up;
- `MultiWorldEvolution` throughout.

Do not retain the old `World`, `CtxImp`, or `ParkedWorld` result shapes.

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
