# EpistemicLambda Agda development

This directory contains the Milestone 1 observer model layered over the
existing `STLCRef` mechanization.

## Public audited surface

- `GroundInterface.agda` defines ground results, observer states, public
  return/read/write labels, and finite source executions.
- `Bisimulation.agda` defines observer bisimulation and the canonical ground
  relation.
- `GroundBisimulation.agda` states the main matching and distinguishability
  theorems.
- `MilestoneOneExamples.agda` connects concrete `STLCRef` reductions to the
  observer model.
- `CheckEpistemicLambda.agda` checks the complete public surface.

Proof implementations are under `proof/` and are checked with `--safe`.

Run `make check` from this directory. The include path imports the canonical
source language from `../../STLCRef/agda`; no source definitions are copied.

## Milestone 1 boundary

The public interface supports results of type `nat`, `unit`, and `ref nat`.
Concrete location numbers do not occur in public labels. After returning one
`ref nat`, the observer may repeatedly read and write it. Returned functions,
multiple disclosed references, references containing references, and stored
functions belong to later milestones.

The current `KeyCorrespondence` is the one-pair base case of the eventual
partial bijection: it relates the single returned location on each side by
requiring their current contents to agree. The bisimulation proof shows that
this correspondence survives arbitrary matching writes.

Internal source reductions are summarized by `_⇓[_]_` before the boundary
state is exposed. Strong bisimulation on the resulting public return/read/write
system therefore plays the role of weak observer bisimulation: allocation and
evaluation steps never occur in labels.
