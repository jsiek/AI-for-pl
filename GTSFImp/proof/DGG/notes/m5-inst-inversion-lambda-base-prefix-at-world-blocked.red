M5 instantiation inversion blocker: `Λ⊑Λ²` base prefix at a parameter post world

Date: 2026-08-12

Context:

  The smart source-prefix world mismatch from
  `m5-inst-inversion-smart-source-prefix-world-blocked.red` is resolved.
  The live proof now has a parameterized post-prefix package:

    `ΛPostPrefixPackageAtBase rel ext₂ c′ B′≢★`

  where the two-allocation post world is an explicit parameter `W₂`, not
  hard-coded to:

    `rightOnlyWorld (rightOnlyWorld W ★) (＇ zero)`.

  The checked rewrap:

    `Λ⊑²-smart-recursive-prefix-at-base`

  can rebuild an outer `Λ⊑²-smart-comma` from a recursive prefix package in
  the target-inserted smart premise world.

New resister:

  The recursive worker still has to produce that premise prefix package.
  If the smart premise derivation reaches the ordinary `Λ⊑Λ²` base case, the
  available live base transport is:

    `Λ⊑Λ²-post-body-transport : Λ⊑Λ²PostBodyTransportᵀ`

  and the prefix wrapper around it is:

    `Λ⊑Λ²-base-prefix-at`.

  Both are fixed to the concrete right-only post world:

    `rightOnlyWorld (rightOnlyWorld Wᵐ ★) (＇ zero)`.

  But the smart premise recursion needs the same `Λ⊑Λ²` post-body transport
  at the pushout-indexed smart premise post world produced by the M-2 target
  insertion stack:

    `Wᵐ₂ = smartAliasInsertWorld ...`

  or

    `Wᵐ₂ = smartFreshInsertWorld ...`.

Why the existing target insertion proof is not enough:

  `TargetExtend.⊢²-target-insert` transports an already-built derivation
  forward along a `TargetInsert`.  The concrete right-only post world and the
  pushout-indexed smart post world have the same target-store shape, but not
  the same center context or embeddings.  Transporting from the concrete
  prefix package to the pushout package would require a same-dimension
  center-world bridge plus context and obligation transport, which is exactly
  the heavier bridge option that the previous blocker avoided.

  The smaller next surface is therefore to prove the base transport directly
  at the supplied post world, i.e. the design-scratch shape:

    `Λ⊑Λ²PostBodyTransportAtᵀ`

  or a narrower smart-target-inserted instance of it.  Once that base
  transport exists, `Λ⊑Λ²-base-prefix-at` can gain a parameterized companion
  and the recursive smart source case can call
  `Λ⊑²-smart-recursive-prefix-at-base` end-to-end.

Checked state:

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp \
    -i GTSFImp/proof/DGG/notes -v0 \
    GTSFImp/proof/DGG/Catchup/InstInversionProof.agda

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp \
    -i GTSFImp/proof/DGG/notes -v0 \
    GTSFImp/proof/DGG/notes/M5InstInversionDesignScratch.agda

No live relation was changed, and no postulate, hole, or catch-all was
added.

M-4 continuation, base-transport pass:

  The prefix-package side of the approved base-parameterization now checks.
  The live proof has a parameterized consumer:

    `Λ⊑Λ²PostBodyTransportAtᵀ`

  and the wrapper around it:

    `Λ⊑Λ²-base-prefix-at-base`

  The design scratch validates both call sites that matter:

    `Λ⊑Λ²-base-prefix-at-base-preflight`
    `Λ⊑Λ²-smart-premise-base-preflight`

  The exact remaining concrete ingredient is the reveal-window part of
  `Λ⊑Λ²-post-body-transport`, not the prefix package.  Its composition is
  still hard-coded through:

    `ΛPostMidWorld W`

  and the final post world:

    `liftWorldLeft X⊑★
       (rightOnlyWorld (rightOnlyWorld W ★) (＇ zero))`

  The concrete dependencies are:

    `Λ-route1-out-ctx`
    `Λ-route1-out-liftCtxᴸ`
    `Λ-mid-to-out-shifted-⊑ᵂ`
    `Λ-out-mid-mono`
    `Λ-outer-rebaseᴿ`
    `Λ-final-body-⊑ᵂ`

  plus the final target typing extraction through `liftCtxᴸ-target`.

  These helpers need the two generated target centers and the two intermediate
  reveal rebases to be definitionally the concrete right-only window.  A plain
  `WorldExtendᴿ` at the pushout-indexed smart premise world only carries store
  and obligation transport; it does not expose the target OPE/image facts,
  intermediate worlds, context equality, `ImpEnvMono`, or `RebaseAtᴿ` witnesses
  needed to rebuild the two generated reveals.

  `TargetExtend.⊢²-target-insert` is also insufficient as-is: it transports an
  already-built derivation forward from the pre-insertion world.  The
  `Λ⊑Λ²` post-body transport must first construct the reveal-wrapped target
  term and its two reveal premises at the post world.  Transporting the
  concrete right-only result afterward would require a same-dimension bridge
  from:

    `rightOnlyWorld (rightOnlyWorld Wᵐ ★) (＇ zero)`

  to:

    `smartAliasInsertWorld ... Wᵐ`

  or:

    `smartFreshInsertWorld ... guard`

  including context, obligation, typing, and rebase transport for the
  already reveal-wrapped term.  That bridge is not part of the current
  `TargetInsert`/`CenterRename` surface.

  Smallest next surface:

    add a post-window geometry package for the two generated target binds,
    carrying the target insertion evidence and the concrete middle/out reveal
    witnesses (`ImpEnvMono`, `RebaseAtᴿ`, context transport, final obligation
    transport, and typing context equality) for the supplied `W₂`; then
    implement `Λ⊑Λ²PostBodyTransportAtᵀ` from that package.  The existing
    concrete right-only instance should remain as the proven consumer for the
    depth-0/base path.
