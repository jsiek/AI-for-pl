M5 smart comma M-2 continuation 2 blocked at M3 center-map support.

Status: BLOCKED, 2026-08-12.

Resolved before this block:

* `proof.DGG.CastTermImprecision2` now records target-mark locality on the
  smart lift guards:

      SmartFreshBehindGuard.target-mark-mono :
        ∀ Xᴿ
        → impEnvʷ W (toRenameᵗ (ηᴿʷ W) Xᴿ) ≡ X⊑★
        → impEnvʷ Wᵐ (toRenameᵗ (ηᴿʷ Wᵐ) Xᴿ) ≡ X⊑★

      SmartAliasMergeGuard.target-mark-off-footprint :
        ∀ Xᴿ
        → Xᴿ ≢ β
        → Xᴿ ≢ α
        → impEnvʷ W (toRenameᵗ (ηᴿʷ W) Xᴿ) ≡ X⊑★
        → impEnvʷ Wᵐ (toRenameᵗ (ηᴿʷ Wᵐ) Xᴿ) ≡ X⊑★

  The on-footprint facts remain the existing guard fields:

      alias-mark-dynamic :
        impEnvʷ Wᵐ (toRenameᵗ (ηᴿʷ W) β) ≡ X⊑★

      name-mark-dynamic :
        impEnvʷ Wᵐ (toRenameᵗ (ηᴿʷ W) α) ≡ X⊑★

      fresh-mark-dynamic :
        impEnvʷ Wᵐ (toRenameᵗ (ηᴸʷ Wᵐ) zero) ≡ X⊑★

* `proof.DGG.TargetBindLift` derives the pivot mark needed by the moved
  smart premise:

      target-pivot-star-source :
        TargetBindLiftMove W Wᵗ Y
        → impEnvʷ W (toRenameᵗ (ηᴿʷ W) Y) ≡ X⊑★

      smartAliasPivotStar :
        TargetBindLiftMove W Wᵗ Y
        → SmartAliasMergeGuard W Wᵐ β α
        → impEnvʷ Wᵐ (toRenameᵗ (ηᴿʷ Wᵐ) Y) ≡ X⊑★

      smartFreshPivotStar :
        TargetBindLiftMove W Wᵗ Y
        → SmartFreshBehindGuard W Wᵐ
        → impEnvʷ Wᵐ (toRenameᵗ (ηᴿʷ Wᵐ) Y) ≡ X⊑★

  These close the `Λ⊑²-smart-comma` cases of
  `⊢²-target-bind-lift-move`; `TargetBindLift.agda` checks.

* `proof.DGG.TargetExtend`, `proof.DGG.TermImpDecay`, and
  `proof.DGG.CenterRename` were adjusted for the locality fields and check.

* In `proof.DGG.Catchup.InstInversionProof`, the mechanical
  `WindowFresh²` and `⊢²-target-insert-window-fresh` smart cases are added.

The next full-tree gate stops in `proof.DGG.Catchup.InstInversionProof`:

    ⊢²-center-map
    ⊢²-center-map-window

both missing `Λ⊑²-smart-comma`.

This is not just a missing one-line recursive case.  The plain `Λ⊑²` case
uses:

    center-map-lift-left : CenterMapWorld ρ W Wˣ
                         → CenterMapWorld ρ
                             (liftWorldLeft X⊑★ W)
                             (liftWorldLeft X⊑★ Wˣ)

and `CenterMapSupport` carries exactly `liftLeftSupport` for that generated
premise world.

For `Λ⊑²-smart-comma`, the premise world is an arbitrary guarded smart world:

    liftW : SmartCommaLiftᴸ W Wᵐ
    prem  : Wᵐ ∣ γᵐ ⊢² V ⊑ N ∶ p

To recurse under a center map, the proof needs a mapped smart premise package:

    Σ[ Wᵐˣ ]
    Σ[ ρᵐ ]
    Σ[ mpᵐ ∈ CenterMapWorld ρᵐ Wᵐ Wᵐˣ ]
      SmartCommaLiftᴸ Wˣ Wᵐˣ
      × SmartLiftCtxᴸ (center-map-ctx mp γ)
          (center-map-ctx mpᵐ γᵐ)
      × CenterMapSupport mpᵐ

No such field exists in `CenterMapSupport` or `CenterMapWindowSupport`.
The existing support surface only knows how to map the fixed generated
`liftWorldBoth` and `liftWorldLeft` premise worlds.  A smart premise world
can merge a source binder into an existing target alias center or place a
fresh source center behind a target window; mapping that world through the
M3 adjacent swaps needs explicit support evidence for the smart guard,
embeddings, marks, and recursive support.

Plausible next step:

* extend `CenterMapSupport` and `CenterMapWindowSupport` with a smart-premise
  mapping field returning the package above, then implement it for the concrete
  adjacent-swap supports used by the M3 stack.
