M5 instantiation inversion blocker: Λ recursive extension tower

Date: 2026-08-12

Blocked target:

  the recursive assembly of `InstInversionPackage.Λ-package`,
  specifically the `Λ⊑²` branch of the derivation-recursive worker.

Resolved before this blocker:

  Route 1 for the `Λ⊑Λ²` base transport checks.  The base package now
  produces an indexed `InstPostCatalogPackageAt` at the concrete tower:

    W₂ = rightOnlyWorld (rightOnlyWorld W ★) (＇ zero)
    χs₂ = bind ★ ∷ bind (＇ zero) ∷ []

  with the post term:

    Λ⊑Λ²PostTerm V′ B

New resister:

  In the one-sided source-polymorphic case,

    CTI2.Λ⊑² Anv zero∈A liftγ vV target⊢ bodyRel p

  the recursive body call must return its post-catalog relation at the
  caller-supplied lifted extension:

    liftWorldLeft X⊑★
      (rightOnlyWorld (rightOnlyWorld W ★) (＇ zero))

  so that `Λ⊑²AtRewrapᵀ` can rebuild the parent relation.

  But the specialized `Λ⊑Λ²PostBodyTransportᵀ` base case for a recursive
  call whose input world is `liftWorldLeft X⊑★ W` lands in the concrete
  two-bind tower of that input world:

    rightOnlyWorld
      (rightOnlyWorld (liftWorldLeft X⊑★ W) ★)
      (＇ zero)

  These worlds differ by the order of the existing source left lift and
  the two generated right binds.  The currently proven
  `right-bind-under-left-lift` handles one bind for CPS rewrap, but there
  is no transport that converts an arbitrary recursive indexed package
  between the full two-bind towers, nor a base transport surface that
  targets the caller-supplied left-lifted tower.

Why this blocks the recursive theorem:

  A generic `derivation-recursive-Λ-at` must honor the caller-supplied
  `χs₂`, `W₂`, and `ext₂`.  The `Λ⊑Λ²` base implementation currently
  knows only the definitionally concrete tower above.  A root-only worker
  can close the visible `Λ⊑Λ²` base, but the `Λ⊑²` recursive case needs
  the body result specifically at the lifted parent tower.

Smallest unblocking work:

  either generalize/supplement the base post-body transport so it can
  target the two generated right binds under an existing source left lift,
  or prove a package-level world/order transport between:

    rightOnlyWorld
      (rightOnlyWorld (liftWorldLeft X⊑★ W) ★)
      (＇ zero)

  and

    liftWorldLeft X⊑★
      (rightOnlyWorld (rightOnlyWorld W ★) (＇ zero))

  including context transport, residual cast/provenance transport, spine
  descent, and finish composition.

  The source-strip branches (`cast⊑²`, `reveal⊑²`, `conceal⊑²`) also need
  the recursive package to expose premise-side residual obligations or a
  relation-only helper before rebuilding the source wrapper, but the first
  hard mismatch is the `Λ⊑²` lifted-tower requirement above.

No live statement was weakened, and no postulate, hole, or catch-all was
added.

REFINED (2026-08-12): the live surface is now tower-indexed by
`Λ⊑Λ²LeftTower`, and the scratch validates the recursive rewrap consumer
shape.  The remaining obstruction is inside the successor transport
implementation: the abstract target pivot introduced by `liftWorldBoth`
still sits before an existing source-only binder, while the lifted
two-bind post tower needs the generated target names after it.  See
`m5-inst-inversion-lambda-lifted-target-pivot-blocked.red`.
