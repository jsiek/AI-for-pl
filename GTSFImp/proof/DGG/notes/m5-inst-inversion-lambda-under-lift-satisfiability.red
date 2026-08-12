M5 instantiation inversion verdict: depth-1 under-lift reveal satisfiability

Date: 2026-08-12

Question tested:

  Before escalating the depth-k generated reveal problem to a possible
  `InstCatchupRight²` statement issue, check the one remaining concrete
  route: generate the first under-lift target reveal with a non-moving
  same-world rebase rather than the depth-0 pivot-moving `RebaseAtᴿ`.

Checked scratch:

  `M5UnderLiftRevealScratch.agda`

  Command:

    AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
      M5UnderLiftRevealScratch.agda

What the target reveal rule demands:

  The target-only reveal rule is:

    `⊑reveal² mono rb sc c′⊢ premise q`

  where:

    `rb : RebaseAtᴿ W W′ Xᴿ?`
    `c′⊢ : targetStoreʷ W ⊢↑[ Xᴿ? ] c′`
    `premise : W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p`
    `q : A ⊑ᵂ⟨ W ⟩ B′`

  Thus a non-moving route is accepted exactly when `W ≡ W′` and
  `RebaseAtᴿ` is `rebase-varᴿ (sameWorldRebaseAt aligned reps)`.
  For the depth-1 final fresh world

    `ΛLiftToBindFreshWorldᴸ X⊑★ W`

  the same-world alias route checks:

    `depth1-inner-sameWorld-rebaseᴿ`

  with target pivot `zero`, using the existing alignment of source
  `zero` and target alias `zero` at center `suc zero`, and

    `depth1-inner-sameWorld-reveal-⊢↑`

  with the generated conversion

    `〖 zero , ⇑ᵗ (＇ zero) ↑ applyBody (bind ★) (＇ zero ⇒ ★) 〗`.

Route-1 result:

  The non-moving rebase evidence and conversion typing both exist.  The
  route still fails because the reveal rule also requires the post type
  relation `q` in the same world.  For the finite non-variable source
  body

    `A = ＇ zero ⇒ ★`
    `B = ＇ zero ⇒ ★`

  that obligation is empty:

    `depth1-inner-sameWorld-q-empty`

  It reduces to the atom

    `＇ (suc zero) ⊑ ＇ (suc (suc (suc zero)))`

  after embedding source `zero` and the generated target representative
  in `ΛLiftToBindFreshWorldᴸ X⊑★ W`.  The scratch proves:

    `no-var1⊑var3`

  by constructor inversion on type imprecision.

Satisfiability hunt:

  The moving route remains blocked by source OPE order.  The scratch
  proves the finite source-embedding obstruction:

    `no-ope-0↦3-1↦2`

  No `_↪ᵗ_` can map source `zero` to center 3 while mapping source
  `suc zero` to center 2.  This is exactly the shape needed to align the
  current source binder with the generated target representative while
  preserving the older source-only binder demanded by
  `RebaseAt.ηᴸ-off-pivot`.

Verdict:

  The non-moving route avoids constructing an impossible premise world,
  but it cannot type the generated reveal's post relation.  The moving
  route can target the post relation only by requiring the impossible
  same-side source reversal.  For the finite depth-1 body
  `＇ zero ⇒ ★`, every checked route to the first generated target reveal
  dies before the second wrapper.

  This is a satisfiability-class blocker for nested source-only-Λ inputs.
  The scratch does not claim global emptiness for every term and type in
  the relation; it proves the sharp finite obstruction currently needed
  for escalation of the package/tower orientation or the
  `InstCatchupRight²` statement.

No live relation was changed, and no postulate, hole, catch-all, or live
statement weakening was added.
