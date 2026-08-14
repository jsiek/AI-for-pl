NS-4 stage 1m target-only builder resister
==========================================

Date: 2026-08-14

Status
------

Stage 1m closed the relation-transport gap for target reveal/conceal frame
absorption.  The live chain entries now carry a supplied transport from the
conclusion world to the premise world required by `⊑reveal²` and
`⊑conceal²`.

The remaining requested builder surface is not currently implementable from
the stated inputs:

`structural-target-normalize : target value + AllValueView + pending spine`

where the pending spine is the raw `InstantiationSpine`.


Resister 1: raw spines do not carry target conversion typing
-----------------------------------------------------------

`StructuralFrameOutcome` is the checked target-only classifier for
conversion frames.  Its reveal branch needs:

`targetStoreʷ W ⊢↑ c`

and a target typing derivation for the value:

`⟨ Δ , targetStoreʷ W , [] ⟩ ⊢ V ⦂ A`

Its conceal branch needs:

`targetStoreʷ W ⊢↓ c`

The raw spine constructors only store the conversion syntax:

`reveal-frame c`

`conceal-frame c`

They do not store `targetStoreʷ W ⊢↑ c` or `targetStoreʷ W ⊢↓ c`.
The existing generated-frame geometry records do carry indexed conversion
typing for generated strict children, and caller-supplied chain entries carry
indexed relation-rule conversion typing, but neither is an input to a
target-only normalizer over an arbitrary raw `InstantiationSpine`.

Consequently, the reveal/conceal frame cases cannot call
`structural-reveal-frame-outcome` or `structural-conceal-frame-outcome` from
the proposed builder inputs alone.


Resister 2: the current name worker surface lacks the chain argument
-------------------------------------------------------------------

The requested general spine worker cases for `cast-frame`, `reveal-frame`, and
`conceal-frame` require:

`TargetFrameAbsorptionChain W γ A spine q`

The current checked accessibility surfaces in
`StructuralNameInstantiationProof.agda` are:

`StructuralValueSpineInstantiationAccᵀ`

`StructuralNameInstantiationAccᵀ`

and the public internal surface in `StructuralInstantiationDescentDef.agda` is:

`StructuralNameInstantiationᵀ`

These surfaces take the post-plan, relation, values, spine, and target
package, but not the target-frame absorption chain.  Adding the chain directly
is not a local edit: the source-wrapper equal cases then need child chains at
the source-premise type, so the hereditary source post-plan and target-frame
post-plan have to be threaded together rather than only adding an argument to
the top-level worker.


Concrete blocked builder case
-----------------------------

For a target value `V` and a pending frame

`reveal-frame c ▻ⁱ spine`

the target-only builder must decide whether `V ↑ c` is already a value or
takes one keep step to a value.  The checked classifier requires target
conversion typing:

    V        : A
    |
    | reveal-frame c, with targetStoreʷ W ⊢↑ c
    v
    V ↑ c    value or one keep step

The proposed raw builder inputs provide `V`, `AllValueView V`, and `c`, but
not `targetStoreʷ W ⊢↑ c`.  This is a target-only evidence gap, not a
source-relation gap.


Consequence
-----------

Stop on the fuel-free target-only builder surface as currently stated.  A live
builder needs an explicit typed-spine surface, or a narrower generated/root
spine surface that packages the target conversion typing owned by the strict
view geometry and by root callers.

No live Agda proof module was weakened for this resister.


PARTIAL RESOLUTION postscript, 2026-08-14
-----------------------------------------

Resister 1 is closed in live Agda by:

`GTSFImp/proof/DGG/Catchup/StructuralSpineTypingDef.agda`

The new checked surface is `SpineTyped Σ spine`, with world abbreviation
`SpineTypedʷ W spine`.  It carries target conversion typing for reveal and
conceal frames, provides transports for `mapInstantiationSpine keep`,
`mapInstantiationSpine (bind R)`, left rebase/tag-rebase/lift, and constructs
the generated/root typed spines.

Resister 2 is only partially advanced.  `StructuralNameInstantiationᵀ`,
`structural-name-package`, `erase-structural-name-root`, and the strict view
surface skeleton now thread the target chain and typed spine as sibling data.
The Acc/Equal worker skeleton still needs hereditary child-chain evidence for
source-wrapper equal premises.  That remaining statement-plumbing obstruction
is tracked in:

`GTSFImp/proof/DGG/notes/ns4-stage-1n-chain-threading-resister.red`
