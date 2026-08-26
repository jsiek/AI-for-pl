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
