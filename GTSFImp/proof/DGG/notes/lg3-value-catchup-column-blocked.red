LG-3 column blocker: SUPERSEDED-BY-REDESIGN on 2026-08-16

The old blocked surface was `ValueCatchupRightAt` / M6 fuel knot with a
syntactic target `CastColumn`.

That plan is no longer live.  `CastColumn`, `applyColumn`, `columnSize`,
`mapColumn`, and `ColumnSupportProof` have been removed from the checked
surface.  The live value-catch-up surface now consumes a whole CTI derivation:

`Value M`, `rel : W ∣ γ ⊢² M ⊑ M″ ∶ q`, and
`TargetCastBound fuel rel`.

`TargetCastBound` is a structurally recursive predicate over the CTI
derivation.  For `⊑cast² c′ rel q` and `cast⊑cast² c c′ rel q` it evaluates
to `castSize c′ < fuel × TargetCastBound fuel rel`; structural CTI heads
replay the premise bound; constants and source blame contribute `⊤`.

The old column peel theorem is therefore obsolete.  The remaining M6 resister
is not a column issue: it is the structural multi-step target-cast worker
recorded in `lg3-target-cast-multistep-worker-resister.red`.
