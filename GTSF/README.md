
This is a mechanization of a polymorphic gradually typed lambda calculus.

Major metatheory boundaries use the `Def`/`Proof`/`Lemma` organization and
strictness policy documented in [`proof/README.md`](proof/README.md).

## Remote Agda checks on ginger

Use the checked-in [`scripts/agda-ginger`](../scripts/agda-ginger) wrapper for
Agda work on `ginger.luddy.indiana.edu`.  The canonical setup, worktree
workflow, focused-check policy, installed paths, and troubleshooting notes are
in [`scripts/GINGER_AGDA.md`](../scripts/GINGER_AGDA.md).  The wrapper uses the
repository-local configuration in
[`scripts/agda-ginger-config/`](../scripts/agda-ginger-config/) and should be
run from the root of a checkout or worker worktree.

## Local Codex standard-library cache

On the local Mac, Agda stores derived standard-library interfaces under
`/Users/jsiek/agda-stdlib-2.2/_build`. A sandboxed check can read those
interfaces but may report `removeLink: permission denied` when Agda needs to
replace a stale one. This is not a proof failure.

For local Codex checks, authorize writes only to that `_build` directory and
rerun the focused command. Do not grant access to the standard-library source
or the rest of the home directory, and do not weaken the strict Agda flags in
the Makefile. Let an authorized refresh finish: interrupting it can leave a
partly refreshed cache that makes the next check encounter another stale
interface.
