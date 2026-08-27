# Audit of a world-only `OpenFrameEvolution`

Status: rejected design. This note records why the source-rebase stack must be
removed without replacing it by an ordinary evolution between nested worlds.
It does not change CTI.

## Trusted transition

The `TargetIdentityReveal` checkpoint-2 to checkpoint-3 source allocation has
these derived frame lists:

```text
checkpoint₁-world          []
checkpoint₁-outer-current  [X ↔ Z′]
checkpoint₁-inner-current  [X ↔ Y′, X ↔ Z′]

checkpoint₃-world          []
checkpoint₃-inner-current  [X ↔ Y′]
```

The root transition is the checked `evolution-bind-left-aligned` from
`checkpoint₁-world` to `checkpoint₃-world`. It allocates the source
representation for the outer boundary and records the paired outer reveal as
an `alignment-onlyᶜ` world change. The final CTI derivation then reconstructs
the inner boundary with `⊑reveal-rebase²` underneath the paired outer
`reveal⊑reveal²` node.

Thus the runtime transition is not an evolution

```text
checkpoint₁-inner-current  →  checkpoint₃-inner-current.
```

Every live `WorldEvolution` constructor preserves the number of open frames:
it may rename their endpoint pivots, but it neither opens nor discharges a
frame. The proposed nested evolution would have to change two frames into one.

## Why one pair of worlds is the wrong index

At the simulation conclusion, the initial and final worlds both have no open
frames. The disappearing outer frame and surviving inner frame occur at
different nested nodes of the CTI derivations. Moreover, the source allocation
is the
`β-Λ` step that exits the source type-binder scope; the nested worlds are not
the endpoints of the root store-change trace.

Consequently, a relation indexed only by one initial world, one final world,
and the root store-change traces has two bad choices:

- indexing the root worlds records only `[]` to `[]` and loses the nested
  reconstruction; or
- indexing the nested worlds falsely assigns the root allocation trace to
  `[X ↔ Y′, X ↔ Z′]` to `[X ↔ Y′]`.

Adding a generic discharge constructor does not repair this abstraction. A
sound discharge needs the paired conversion boundary and the surrounding CTI
node that consumes the old target-only reveal. Those are term-imprecision and
source-step facts, not world-evolution facts.

## Canonical proof locus

The existing `SimTargetRevealRebaseClosingᵀ` statement has the necessary
indices. It retains the enclosing target reveal and its `SourceRebaseᶜ` while
inducting on the inner CTI derivation and source step. Its conclusion exposes
only the ordinary evolution of the enclosing world and the complete final CTI
derivation. Therefore the allocation case may replace the target-only outer
node by a paired outer node while reconstructing the inner frame below it.

The canonical migration is to prove that statement directly. Do not replace
the obsolete `SourceRebaseStack` with a world-only `OpenFrameEvolution`, a
universal inner `MultiWorldEvolution`, or a theorem that promises to preserve
an arbitrary selected `SourceRebaseᶜ` across aligned allocation.

## CTI evaluation-context index

The direct induction needs a term-specific zipper, not a second balance
index. A packaged configuration contains one complete `⊢²` node, including
its world and source and target terms. One descent edge selects a reducing
source child of that node. The reflexive-transitive closure of these edges is
the context from the selected closing boundary to the current recursive call.

The complete primary edge set is:

- application left and right;
- primitive left and right;
- paired and source-only type application;
- paired, source-only, and target-only cast;
- target-only identity reveal and conceal;
- source-only identity reveal and conceal;
- source-only active reveal and conceal;
- paired reveal and conceal; and
- target-only rebase reveal and conceal.

There is no edge beneath a term abstraction or type abstraction because the
reduction relation does not descend beneath either value.

Each edge has a separate reconstruction constructor. Its result index is a
variable, and the constructor carries the actual term equation internally.
For example, application-left reconstruction carries

```text
N = P · applyTerm χ M,
```

where `P` is the reduct of the selected function child and `M` is the saved
source argument. Application-right and the two primitive constructors carry
the corresponding renamed sibling. Type application carries `applyBody` and
`applyTy`; casts carry `applyConsistency`; source reveal and conceal carry
`rename↑` and `rename↓`. A target-only wrapper carries `N = P`, because it
contributes no source syntax. Thus no defined function occurs in an index,
and no vacuous reflexive equation can fabricate a reconstruction.

The generalized theorem keeps the original target-reveal closing boundary
fixed and adds a path to the focused `⊢²` node. A recursive contextual case
extends the path and supplies the matching reconstruction constructor. The
result is still the unchanged public closing conclusion for the whole root
term. The public theorem is the `focus-here` adapter.

For the trusted allocation, the root evolution remains
`checkpoint₁-world []` to `checkpoint₃-world []`. Reconstruction replaces
the outer `X ↔ Z′` target-only boundary by the paired outer boundary, while
the nested CTI result explicitly rebuilds the surviving `X ↔ Y′` boundary.
No context index contains either frame list: both lists continue to be derived
only from the worlds stored at their owning CTI nodes.

## Focused value catch-up boundary

The first nonlocal root obstruction is not another world invariant. When the
focus lies in the right child of an application or primitive, the zipper
records the source left sibling as a value because that is exactly the premise
of the source reduction rule. It cannot record the target left sibling as a
value: obtaining that target value is catch-up work that has not happened yet.

`MorePreciseTargetRevealRebaseContextCatchupᵀ` is the direct semantic boundary
for that work. It catches up a source value at a focused CTI node while keeping
the selected enclosing reveal in the target term. Its result returns:

- the ordinary evolution of the enclosing no-frame world;
- the reconstructed evolved source rebase;
- evolved root and focus CTI derivations connected by an evolved zipper; and
- the target reduction to the evolved root term under the enclosing reveal.

The result also carries `TargetReady` for the evolved zipper. `TargetReady` is
derived evidence, not a stronger zipper constructor: it requires a target
value only at application-right and primitive-right edges and recursively
preserves that evidence through all other edges. A later target-step replay can
therefore use `ξ-·₂` or `ξ-⊕₂` honestly. A keep-only source replay needs no such
evidence because it performs zero target steps and leaves every target sibling
unchanged.
