# Ginger Agda workflow

This is the canonical operational guide for running focused GTSF Agda checks
on `ginger.luddy.indiana.edu`.

## Locations

- Remote checkout: `/home/jsiek/src/AI-for-pl`
- Repository wrapper: `scripts/agda-ginger`
- Repository library configuration: `scripts/agda-ginger-config/`
- Agda executable: `/home/jsiek/.local/opt/Agda-v2.7.0.1/bin/agda`
- Standard library source: `/home/jsiek/.local/opt/agda-stdlib-2.1.1/src`
- Standard library interface cache:
  `/home/jsiek/.local/opt/agda-stdlib-2.1.1/_build`
- Codex executable: `/home/jsiek/.local/bin/codex`
- Codex worker wrapper: `scripts/codex-ginger`

The configuration directory contains:

- `libraries`, the library registry passed explicitly to Agda;
- `defaults`, selecting `standard-library`; and
- `standard-library.agda-lib`, pointing at the installed standard-library
  source and recording its warning policy.

## Normal use

From the root of the checkout or any worker worktree, run:

    scripts/agda-ginger --no-allow-unsolved-metas -v0 proof/<OwnedModule>.agda

The wrapper changes into `GTSF/`, so module paths are relative to that
directory.  Do not invoke the bare `agda` executable for routine ginger work.

For an existing deliberately partial legacy module that explicitly enables
unsolved metas, omit `--no-allow-unsolved-metas`:

    scripts/agda-ginger -v0 proof/<PartialModule>.agda

Do not use that pattern for new skeleton or worker modules.  State unfinished
major dependencies as higher-order contract parameters so the new module can
pass the strict command from its first checked version.

## Starting a remote worker worktree

The following is the standard setup for one isolated proof slice.  Replace
`<slice>` and `<frozen-commit>` with the work-package name and the exact commit
that contains its checked interface.

    ssh ginger.luddy.indiana.edu
    cd /home/jsiek/src/AI-for-pl
    git fetch origin
    git worktree add -b codex/ginger-<slice> \
      /home/jsiek/src/AI-for-pl/.codex-ginger-worktrees/<slice> \
      <frozen-commit>
    cd /home/jsiek/src/AI-for-pl/.codex-ginger-worktrees/<slice>
    scripts/agda-ginger --no-allow-unsolved-metas -v0 proof/<OwnedModule>.agda

Commit and push only the worker's owned files from that worktree.  The local
integrator fetches the worker branch, reviews its exact diff, integrates it,
and runs the nearest focused consumer check.  Do not run `All.agda` in the
worker worktree.

For a completed leaf, remove any local `--allow-unsolved-metas` and
`--allow-incomplete-matches` options before the final check.  Agda's
command-line `--no-allow-unsolved-metas` does not reliably override a source
module that locally enables unsolved metas, so the final audit must also
confirm that the owned file contains no holes or permissive module options.

Launch a worker through the repository wrapper:

    scripts/codex-ginger -m gpt-5.5 \
      -s workspace-write --dangerously-bypass-hook-trust -

Do not replace this with bare `codex exec -s workspace-write`.  Agda stores
standard-library interfaces under the installed library's `_build` directory,
which is outside a worker worktree.  A workspace-only Codex sandbox can read
the library but fails when Agda must replace a stale interface.  The wrapper
adds only that `_build` directory as an extra writable root; it does not make
the standard-library source or the rest of the home directory writable.

After installing or upgrading Agda or the standard library, run one focused
`scripts/agda-ginger` check outside a Codex worker before starting several
workers concurrently.  This warms the shared library cache and avoids having
multiple workers regenerate the same interfaces at once.  The narrow
`--add-dir` permission remains necessary because a later focused check may
still discover one stale library interface.

Use checks in three tiers:

1. Every worker checks only its owned module.
2. The integrator checks the nearest focused consumer after batching worker
   results.
3. `proof/NuDGGStrictSpine.agda` and `All.agda` are milestone checks, not
   per-worker or per-commit checks.

When a focused check is unexpectedly expensive, profile that boundary rather
than starting with `All.agda`:

    scripts/agda-ginger --profile=modules -v0 proof/<FocusedConsumer>.agda
    scripts/agda-ginger --profile=definitions -v0 proof/<OwnedModule>.agda

## Why the wrapper is necessary

The installed Agda executable has a stale compiled-in Cabal data location, and
Agda may otherwise try to refresh standard-library interfaces inside the
read-only installation.  The wrapper:

1. sets `Agda_datadir` to the matching Agda installation's `data` directory;
2. sets `AGDA_DIR` to `scripts/agda-ginger-config` in the current worktree;
3. passes the repository-local `libraries` file explicitly;
4. selects `standard-library`; and
5. adds `GTSF/` as the project include path.

This keeps regenerated application and library interfaces writable in the
worker worktree and makes checks independent of per-user Agda library
registration.

## Installation changes and troubleshooting

If Agda moves but retains the same directory layout, override its prefix:

    GINGER_AGDA_PREFIX=/new/agda/prefix scripts/agda-ginger -v0 proof/<Module>.agda

If the standard library moves, update the `include` entry in
`scripts/agda-ginger-config/standard-library.agda-lib` as part of the same
repository change.

The wrapper fails early with a specific message if the executable, runtime
data, or repository library descriptor is missing.  If a check instead reports
that it cannot write an interface beneath `/home/jsiek/.local/opt`, first
confirm that both repository wrappers were used: `scripts/codex-ginger`
launched the worker and `scripts/agda-ginger` launched Agda.  Also confirm that
the worktree contains all three library-configuration files.  A
`removeLink: permission denied` error under the standard-library `_build`
directory specifically means the worker was launched without the narrow
Codex-cache permission.

Do not repair an Agda problem by changing the shared GitHub CLI authentication
configuration.

## Remote worker contract

Give every GPT 5.5 worker a separate worktree and branch based on a frozen
interface commit.  The assignment must state:

1. the exact theorem and base commit;
2. one owned file or nonoverlapping helper module;
3. allowed imports and forbidden API changes;
4. the exact focused wrapper command;
5. that interface changes must be reported instead of made; and
6. that the completed slice must contain no holes, postulates, or incomplete
   matches.

The local GPT 5.6 integrator owns focused consumer checks, architecture-sensitive
proofs, and milestone aggregate checks.
