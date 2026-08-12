M5 instantiation inversion blocker: lifted target pivot center

Date: 2026-08-12

Refined by:

  `m5-inst-inversion-lambda-under-lift-premise-blocked.red`.  The newer
  note records the k=1 consumer preflight that now checks, and isolates
  the remaining false premise conversion before the under-left-lift
  helper stack can run.

Blocked target:

  implementation of the successor case of the tower-indexed
  `Λ⊑Λ²PostBodyTransportᴸᵀ`.

Checked before this blocker:

  The live definition now has the depth-indexed surface:

    Λ⊑Λ²LeftTower W W₂ ext₂
    Λ⊑Λ²PostBodyTransportᴸᵀ

  and the scratch checks that a transport at a caller-supplied tower
  rewraps mechanically through `Λ⊑²`:

    Λ⊑Λ²-base-rewrap-preflightᴸ

  The one-bind lifted extension still checks, and the two-bind lifted
  extension is the composition:

    right-bind-under-left-lift {B = ★}
    then
    right-bind-under-left-lift {B = ＇ zero}

New resister:

  At positive left-lift depth, the existing Route 1 prefix leaves the
  abstract target pivot introduced by `liftWorldBoth` before the
  existing source-only binders, while the caller-supplied lifted
  two-bind tower places the generated target names after those source
  binders.

  For one existing source-only lift over `W`, the direct prefix route is:

    liftWorldBoth X⊑★
      (liftWorldLeft X⊑★ (rightOnlyWorld W ★))

  followed by the same `CenterRename wk↪ᵗ` used at depth 0.  In that
  renamed world, the abstract target pivot `zero` embeds at center
  `suc zero`.

  The recursive caller, however, needs the post body relation in:

    liftWorldLeft X⊑★
      (liftWorldLeft X⊑★
        (rightOnlyWorld (rightOnlyWorld W ★) (＇ zero)))

  In this tower, the generated target pivot `zero` embeds at center
  `suc (suc zero)`: the inner source binder is at center `zero`, the
  existing outer source-only binder is at center `suc zero`, and the
  generated target names follow them.

Why existing machinery does not cover it:

  * `TargetInsert.liftLeftTargetInsert` and
    `right-bind-under-left-lift` correctly place the runtime right binds
    under the existing source-left tower.
  * `TermImpDecay.liftBothBinderDecay` still applies after that first
    insertion.
  * `TargetBindLift.TargetStoreMove` can change only target-store
    bookkeeping; its `ηᴿ-same` field prevents moving the abstract target
    pivot from center `suc zero` to center `suc (suc zero)`.
  * `CenterRename` is order-preserving.  It can insert fresh centers, but
    it cannot insert a center after the existing source-only binders while
    keeping the inner `liftWorldBoth` target pivot after them; doing so
    would swap the inner target binder past source-only binders.
  * The generated target reveal constructors use `RebaseAtᴿ`, whose
    `ηᴿ-frozen` field freezes every target variable across the reveal
    premise.  So the target pivot center must already agree before the
    reveal rebuild starts.

This is not the previous concrete-tower specialization mismatch.  That
one was solved by indexing the transport by the left-lift tower.  The
new issue is inside the successor proof: the current prefix route can
construct the right target store, but not the needed target-center
placement for the abstract binder at positive source-left depth.

Likely missing shape:

  a relation-level transport or alternative prefix route that re-points
  the `liftWorldBoth` target binder after an existing source-left tower
  without requiring a non-order-preserving center substitution.  If that
  transport is necessarily substitution-shaped, it is a design decision
  rather than a local proof-engineering step.

No live relation was changed, and no postulate, hole, or catch-all was
added.
