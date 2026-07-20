
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
