M5 instantiation inversion blocker: under-left-lift premise order

Date: 2026-08-12

Blocked target:

  implementation of the successor-depth case of the tower-indexed
  `Λ⊑Λ²PostBodyTransportᴸᵀ`.

Checked before this blocker:

  The scratch now validates the k=1 consumer surface:

    Λ⊑Λ²-one-lift-rewrap-preflight

  If a transport is available at a one-left-lift extension of any existing
  `Λ⊑Λ²LeftTower W W₂ ext₂`, the recursive `Λ⊑²` base rewrap accepts the
  caller-supplied lifted tower:

    liftWorldLeft X⊑★ W₂

  The proof is only a statement-level consumer check.  It does not prove
  the transport.

Under-lift forms checked/reused:

  * `TargetExtend.liftLeftTargetInsert` threads target insertion through
    a source-left lift.
  * `right-bind-right-bind-under-left-lift` builds the expected lifted
    two-bind extension:

      liftWorldLeft X⊑★ W
        ↣ liftWorldLeft X⊑★
            (rightOnlyWorld (rightOnlyWorld W ★) (＇ zero))

  * `TermImpDecay.liftDecayLeft` and `liftBothBinderDecay` are sufficient
    once the premise is already in the intended under-left world order.
  * `TargetBindLift.liftTargetBindMoveLeft` threads a target store move
    through a source-left lift when the source and target embeddings agree.

New resister:

  The actual recursive `Λ⊑²` premise is not born in the under-left world
  order needed by those helpers.  At k=1 the premise has shape:

    liftWorldBoth X⊑X (liftWorldLeft X⊑★ W)

  After decay, its target embedding is still:

    keep (skip ηᴿ)

  so target variable zero embeds at the fresh center zero.

  The desired under-left route would need to run the internal prefix in:

    liftWorldLeft X⊑★ (liftWorldBoth X⊑★ W)

  whose target embedding is:

    skip (keep ηᴿ)

  so target variable zero embeds at `suc zero`, after the existing
  source-left binder.

Why this is not a local transport:

  A relation-level conversion from

    liftWorldBoth X⊑★ (liftWorldLeft X⊑★ W)

  to

    liftWorldLeft X⊑★ (liftWorldBoth X⊑★ W)

  is false for the variable case.  Take the constructor with
  `A = ＇ zero`, `B = ＇ zero`, and the local imprecision proof
  `I.X⊑X`.  In the input world, the two variables embed to the same
  center.  In the desired under-left world, the source variable still
  embeds to `＇ zero`, but the target variable embeds to `＇ (suc zero)`.
  There is no imprecision constructor proving:

    ＇ zero ⊑ ＇ (suc zero)

  Decay from `X⊑X` to `X⊑★` does not change this constructor, because
  the existing `X⊑X` proof is syntactic equality of the embedded
  variables, not mark evidence parked on a generated target binder.

Consequence:

  The depth-0 script does not replay at k=1 by merely substituting the
  under-left forms.  The route would need an additional design principle
  that permutes the `liftWorldBoth` target binder past an existing
  source-left binder, or a substitution-shaped reconstruction of the
  premise.  That is outside the allowed local assembly step.

No live relation was changed, and no postulate, hole, or catch-all was
added.
