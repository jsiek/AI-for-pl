# Agda MCP resume handoff

## Checkpoint

Resume from the tip of `codex/gtsf-world-invariants-live` and draft PR #184.
The worktree should be clean.  Configure and verify the Agda MCP server before
starting the next proof arc; use its interactive goal/context support for the
remaining dependent transports rather than recreating long batch-only edit
cycles.

The canonical live two-context foundation now consists of:

- `World` and `WorldInvariants`;
- `SourceRebasePlan` and `SourceRebaseRequest`;
- `CenterRenamePlan` and `TargetExtend`;
- `WorldEvolution`, its request producer, and its multi-step sequence;
- trusted preservation over arbitrary term contexts.

The globally indexed relation probe covers variables, functions, universals,
type application, constants, blame, all ordinary cast polarities,
current-mode-unoccupied source conceal, and term-independent paired
reveal/conceal.  Its endpoint typing theorem is exhaustive for this fragment.

## Established design constraints

- Do not add a compatibility bridge from the canonical two-context world to
  the old `CtxImp.World`.
- Do not use `resolveVar` as reveal, conceal, rebase, or alignment evidence.
- One-sided source conceal requires an unoccupied target pivot in the current
  mode.
- Paired reveal/conceal use direct endpoint store membership and do not inspect
  either term.
- Administrative aliases are exact, scoped, one-edge boundaries; they do not
  weaken the stable direct-representation invariant.
- Trusted reductions expose only `keep` or `bind`.  A simulation-layer world
  evolution producer must additionally supply right freshness, direct paired
  type imprecision, and the precise/dynamic mark choice.

## Next proof arc

1. Define the simulation/typing producer that constructs
   `WorldEvolutionRequest` from a pair of related trusted steps and the direct
   relational evidence already present at that boundary.
2. Connect the globally indexed two-context term relation to the live DGG
   theorem surface without introducing a parallel `CtxImp` witness.
3. Produce the live strict-`Λ` child endpoint, relation, and exact provenance;
   its frame, plan, spine-typing, and strict-child bookkeeping already
   assemble.
4. Retire `TargetBindLift` and its invalid split-world path rather than
   repairing `targetStoreAs` with an arbitrary world constructor.

The full safe aggregate currently stops at the known legacy error:

```text
proof/DGG/TargetBindLift.agda:396
Not in scope: CTX.world
```

This is an intentional frontier, not a regression in the two-context modules.

## Validation

Use focused `agda --safe --no-caching -i GTSFImp` checks for the module being
edited and its nearest consumer.  Before the next milestone also run:

```text
make -C GTSFImp postulate-check
git diff --check
agda --safe --no-caching -i GTSFImp GTSFImp/All.agda
```

The first two commands must pass.  Until `TargetBindLift` is retired, the last
command should reach only the error recorded above.
