M5 instantiation inversion blocker: cross-side term exchange

Date: 2026-08-12

Blocked target:

  the successor-depth `Λ⊑Λ²PostBodyTransportᴸᵀ` route that applies the
  closed depth-0 theorem at the lifted base and then moves only
  source-left binders across generated right binds.

Checked before this blocker:

  The immediate lifted-base use of the closed depth-0 theorem checks in
  the scratch:

    Λ⊑Λ²-one-lift-born-rewrap-preflight

  This instantiates `Λ⊑Λ²-post-body-transport` at:

    W := liftWorldLeft X⊑★ W₀

  so the premise is exactly the born shape:

    liftWorldBoth X⊑X (liftWorldLeft X⊑★ W₀)

  No same-side world conversion is used.

  The live proof also now has the one-bind cross-side type exchange:

    right-left-exchange-⊑ᵂ

  It transports type imprecision from:

    rightOnlyWorld (liftWorldLeft X⊑★ W) B

  to:

    liftWorldLeft X⊑★ (rightOnlyWorld W B)

  The proof is a raw `rename-⊑` by the center swap `swap01`.  This is
  sound because the swapped source-only and target-only centers are both
  marked `X⊑★`.

New resister:

  The recursive `Λ⊑²` rewrap cannot consume the born-order post relation
  produced by the depth-0 theorem at the lifted base.

  Born body world:

    liftWorldLeft X⊑★
      (rightOnlyWorld
        (rightOnlyWorld (liftWorldLeft X⊑★ W₀) ★)
        (＇ zero))

  World required by the existing tower-oriented `Λ⊑²` rewrap:

    liftWorldLeft X⊑★
      (liftWorldLeft X⊑★
        (rightOnlyWorld (rightOnlyWorld W₀ ★) (＇ zero)))

  Equivalently, the born relation has center order:

    current source, generated target, generated target, outer source

  while the `Λ⊑²` constructor needs:

    current source, outer source, generated target, generated target

  The type-level exchange proves that obligations can cross this
  boundary, but the term relation also needs a derivation transport.
  Existing `WorldExtendᴿ` transports only type obligations and contexts,
  and `TargetExtend.⊢²-target-insert` inserts fresh right binds from a
  pre-bind derivation; neither exchanges an already-built derivation
  across a zero-change cross-side center permutation.

Born-order restatement result:

  Restating the immediate `Λ⊑Λ²` base consumer at born order succeeds.
  Restating the recursive `Λ⊑²` package consumer at born order does not
  give a usable rewrap: the body package world has the extra source
  binder in its own source context, but `CTI2.Λ⊑²` requires the body
  derivation to live under `liftWorldLeft W₂` for a top world `W₂` whose
  source context is the conclusion source context.  The born package
  world is not such a `liftWorldLeft W₂`.

Consequence:

  To continue, the development needs a term-level cross-side exchange
  theorem for the generated relation, or a redesigned recursive tower
  orientation whose package-level rewrap still matches `CTI2.Λ⊑²`.
  This is a design decision rather than a local assembly step.

No live relation was changed, and no postulate, hole, or catch-all was
added.
