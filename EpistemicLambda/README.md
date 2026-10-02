# Epistemic Lambda

This directory investigates whether the state models, program models, update
products, and bisimulations of dynamic epistemic logic can support a fully
abstract semantics for the repository's call-by-value `STLCRef` calculus with
mutable general references, natural numbers, and unit.

The motivating picture is that a reference is a locked box and a location is
its unforgeable key. A context can observe a box only if evaluation has
disclosed a key that reaches it. Local state is therefore hidden information,
not absent state.

The first research question is:

> Can contextual equivalence be characterized as bisimilarity of epistemic
> interaction models whose accessibility records what the surrounding program
> can distinguish?

[`Design.md`](Design.md) gives the initial calculus, works through the hidden
alternating-bit example, extracts the reusable structure from Baltag and
Moss's *Logics for Epistemic Programs*, compares candidate semantic designs,
and proposes the first milestones.

Milestone 1 is now mechanized in [`agda/`](agda/README.md). It imports the
existing [`STLCRef`](../STLCRef/agda/README.md) development as its operational
source language and adds a first-order observer transition system and
bisimulation. The model proves fresh-address irrelevance, private-garbage
irrelevance, matching behavior through one disclosed key, distinguishability
of different natural-number results, and sensitivity to termination versus
abstract divergence.
