LG-3 resister: erased `WorldExtendᴿ` is too weak for source-wrapper replay

Status: open as of 2026-08-16.

The supervisor restatement resolves the fun×expand endpoint counterexample,
but rebuilding `ValueCatchupRightAt` against the live fuel interfaces exposes a
separate surface mismatch.

The source-wrapper replay lemmas that already exist for reveal/conceal need a
structural right-world trace:

`StructuralWorldExtendᴿ χs W W′`

For example:

- `structural-reveal-replay` transforms `RebaseAtᴸ W Wᵖ Xᴸ?` through a
  structural target evolution.
- `structural-conceal-replay` additionally rebuilds the
  `SourceConcealPartnerOK` side condition at the endpoint.

The live M6 public/fuel surfaces return only the erased extension:

`ext : WorldExtendᴿ χs W W′`

This is enough to transport the endpoint imprecision and context, but it does
not record the keep/bind insertion history needed to construct the premise
world for source `reveal⊑²` / `conceal⊑²` replay.

Concrete blocking shape:

`ValueCatchupRightAt fuel` recurses under a source wrapper such as

`reveal⊑² mono rb sameγ c⊢ prem q`

The recursive normalization of `prem` may allocate on the target side, for
example when the target subtree later reaches an `inst` cast.  Its public result
has:

`Wᵖ′`, `χs`, `extᵖ : WorldExtendᴿ χs Wᵖ Wᵖ′`

To replay the outer `reveal⊑²`, the proof needs a corresponding outer endpoint
world `W′`, a structural plan from `W` to `W′`, and a transported rebase:

`RebaseAtᴸ W′ Wᵖ′ Xᴸ?`

That data is exactly what `structural-rebase-atᴸ` computes from a
`StructuralWorldExtendᴿ` plan.  It is not recoverable from the erased
`WorldExtendᴿ` record alone: the erased record stores source-store equality,
target-store following, and imprecision transport, but no target insertion
history or premise-world alignment.

This blocks the source-wrapper rows of the multi-step inversion and therefore
the `ValueCatchupRightAt`/`ExtraCastRightAt` factory assembly at the current
surface.

Likely repair:

Strengthen the internal multi-step/value-catch-up package to carry
`StructuralWorldExtendᴿ` and erase it only at the public boundary, or add
source-wrapper replay lemmas whose hypotheses explicitly include enough
right-world history to reconstruct `RebaseAtᴸ`, `TagRebaseAtᴸ`, and endpoint
partner evidence.  The CTI relation and reduction relation do not need to
change.
