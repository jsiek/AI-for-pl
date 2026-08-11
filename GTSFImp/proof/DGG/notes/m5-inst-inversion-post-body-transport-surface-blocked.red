M5 instantiation inversion blocker: post-body transport surface is too general

Date: 2026-08-11

Blocked target:

  implementation of `Λ⊑Λ²PostBodyTransportᵀ` in
  `proof/DGG/Catchup/InstInversionProof.agda`.

The task-proposed construction is the concrete two-bind route:

  1. target-insert the `Λ⊑Λ²` body premise under
     `liftWorldBoth X⊑X W` using
     `TargetExtend.⊢²-target-insert` with
     `keepRightBindTargetInsert` for `bind ★`;
  2. target-insert once more with `keepRightBindTargetInsert` for
     `bind (＇ zero)`;
  3. decay the resulting body relation from the `X⊑X` mark introduced by
     `liftWorldBoth` to the `X⊑★` mark needed by `liftWorldLeft`;
  4. rebuild the generated target reveals via `RebaseAtᴿ` premise worlds;
  5. take the target typing from
     `CastTermImprecision2Typing.target-typing²`.

That route lands in the concrete post-catalog world:

  W₂ = rightOnlyWorld (rightOnlyWorld W ★) (＇ zero)
  χs₂ = bind ★ ∷ bind (＇ zero) ∷ []

But the live statement is indexed over an arbitrary caller-supplied
right extension:

  Λ⊑Λ²PostBodyTransportᵀ =
    ∀ {Δᴸ Δᴿ Δ Δᴿ₂ Δ₂}
      {W : World Δᴸ Δᴿ Δ} {W₂ : World Δᴸ Δᴿ₂ Δ₂}
      ...
      {χs₂ : StoreChanges Δᴿ Δᴿ₂}
      {ext₂ : WorldExtendᴿ χs₂ W W₂}
      ...

There is no `TargetInsert` or equality tying `χs₂`, `Δᴿ₂`, `Δ₂`, and
`W₂` to the two generated binds. A scratch clause specialized to the
intended world failed before proof construction:

  post-transport-scratch {Δᴿ₂ = .(suc (suc _))}
      {Δ₂ = .(suc (suc _))}
      {W = W}
      {W₂ = .(rightOnlyWorld (rightOnlyWorld W ★) (＇ zero))}
      {χs₂ = .(bind ★ ∷ bind (＇ zero) ∷ [])}
      ...

Agda rejects the clause because the statement still permits arbitrary
`Δᴿ₂`:

  suc (suc _n_1) != Δᴿ₂ of type ℕ
  when checking that the given dot pattern suc (suc _) matches the
  inferred value Δᴿ₂

This is not just a coverage nuisance. The ingredients named for the
construction operate on the concrete `TargetInsert` tower. The exported
`WorldExtendᴿ` record only transports obligations and stores; it does not
carry the target OPE/term-renaming/rebase-commutation evidence needed to
transport arbitrary `_∣_⊢²_⊑_∶_` derivations through arbitrary `χs₂`.

Smallest unblocking statement change:

  replace or supplement `Λ⊑Λ²PostBodyTransportᵀ` with a two-bind-indexed
  surface whose post world is definitionally
  `rightOnlyWorld (rightOnlyWorld W ★) (＇ zero)` and whose extension is
  the composed `bind ★ ∷ bind (＇ zero) ∷ []` right extension, or add
  explicit equality/`TargetInsert` evidence tying the caller-supplied
  `ext₂` to that tower.

No live statement was weakened, and no postulate, hole, or catch-all was
added.

RESOLVED (2026-08-11):

  `Λ⊑Λ²PostBodyTransportᵀ` is now specialized to the concrete two-bind
  tower:

    W₂ = rightOnlyWorld (rightOnlyWorld W ★) (＇ zero)
    χs₂ = bind ★ ∷ bind (＇ zero) ∷ []

  The live statement takes the corresponding `WorldExtendᴿ χs₂ W W₂`
  explicitly, and `M5InstInversionDesignScratch.agda` checks the updated
  `Λ⊑Λ²-base-rewrap-preflight`.  The Λ base call site accepts the tower;
  the remaining blocker is now inside the post-body transport proof, not
  its exported surface.
