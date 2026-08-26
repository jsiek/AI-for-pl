M5 instantiation inversion blocker: side-stable cycle has no exchanged rebase

Date: 2026-08-12

New checked artifact:

  `SideStableCycleCounterScratch.agda`

Checked command:

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp \
    -i GTSFImp/proof/DGG/notes -v0 \
    GTSFImp/proof/DGG/notes/SideStableCycleCounterScratch.agda

What it checks:

  The scratch isolates the small finite geometry behind the remaining
  `CenterMapSupport.rebaseAtForward` field.

  Before exchange, this source re-park is valid:

    source embedding before: `keep (skip (keep empty))`
      source variables at centers 0 and 2

    target embedding before: `skip (keep empty)`
      target variable at center 1

    source embedding after: `keep (keep empty)`
      source variables at centers 0 and 1

    pivot: source variable 1 re-parks from center 2 to the frozen target
      center 1; source variable 0 stays at center 0.

  This is exactly a legal `RebaseAt`: no source variable is crossed on the
  input side.

  After the right/left exchange, the parent output has:

    source embedding: `skip (keep (keep empty))`
      source variables at centers 1 and 2

    target embedding: `keep (skip empty)`
      target variable at center 0

  If the support field existed, it would need some output world `W′` with:

    `RebaseAt scratch-world-exchanged W′ (suc zero) zero`

  But the rebase fields force:

    source variable 0 stays at center 1
    source variable 1 aligns with frozen target center 0

  No order-preserving source embedding `2 ↪ᵗ 3` can map the earlier source
  variable to 1 and the later source variable to 0.  The scratch proves:

    `scratch-rebase-after-impossible :
       ∀ {W′ : World 2 1 3} →
       RebaseAt scratch-world-exchanged W′ (suc zero) zero → ⊥`

Consequence:

  The requested cycle correction cannot merely adjust the premise map
  `ρᵖ`.  The wrapper constructor also requires the rebuilt evidence
  `RebaseAt Wˣ Wᵖˣ Xᴸ Xᴿ`, and in this legal source-repark geometry there
  is no candidate `Wᵖˣ` at all.  This is independent of the mark
  environment: the obstruction is the source OPE order forced by
  `ηᴸ-off-pivot`, `ηᴿ-frozen`, and `pivotAligned`.

  Therefore the general arbitrary-derivation `CenterMapSupport` closure
  for source re-parks remains false for the current `RebaseAt` semantics.
  Continuing requires a design decision: restrict the derivations/support
  invariant so this source-repark shape is absent at the generated
  exchange site, change the exchange target surface so it does not require
  this rebuilt `RebaseAt`, or revise the rebase/world semantics.  No live
  relation was changed in this run.

No postulate, hole, catch-all, or live-statement weakening was added.
