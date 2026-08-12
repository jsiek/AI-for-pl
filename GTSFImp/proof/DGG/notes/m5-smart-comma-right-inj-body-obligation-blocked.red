M5 smart comma M-2 continuation 3 blocked at right-injection inversion.

Status: BLOCKED, 2026-08-12.

Resolved before this block:

* The pre-A3 exchange layer in `Catchup/InstInversionProof.agda` was checked
  for external consumers and pruned.  No live Agda source outside the cluster
  referenced:

      swap01 / swap12 exchange OPE scaffolding
      CenterMapWorld
      WindowFresh²
      ⊢²-target-insert-window-fresh
      CenterMapSupport
      ⊢²-center-map
      CenterMapWindowSupport
      ⊢²-center-map-window
      right-left-center-map and right-left-under-right-center-map
      right-left exchange/rebase helpers

  The retained direct depth-0 route still checks:

      Λ⊑Λ²-post-body-transport
      right-bind-under-left-lift
      right-bind-right-bind-under-left-lift

* `TargetWalkSupport.agda` now handles the smart pending-Λ constructor in
  `tagged-target-nonvar-nonstar-spine-⊥`.

* `TargetStripProof.agda` now handles the smart pending-Λ constructor in
  `seal-descent-at-var-＇` and `tag-dispatch-at★`.

The next full-tree gate stops in `RightInjInversion2Proof.agda`:

    right-inj-inversion²

missing the top-level `Λ⊑²-smart-comma` case, and the generated nested
with-function also reports the source-seal branch whose premise is
`Λ⊑²-smart-comma`.

The top-level case is not mechanical.  In the plain `Λ⊑²` branches,
right-injection peeling has:

    q : `∀ A ⊑ᵂ⟨ W ⟩ H

and, when `q` is a `∀⊑` view, it uses:

    liftWorldLeft-⊑ᵂ :
      instᵐ (impEnvʷ W) ⊢
        renameᵗ (extᵗ (toRenameᵗ (ηᴸʷ W))) A
          ⊑ ⇑ᵗ (embedᴿ W H)
      → A ⊑ᵂ⟨ liftWorldLeft X⊑★ W ⟩ H

to feed the recursive right-injection call on the plain premise.

For the smart constructor the premise is:

    liftW : SmartCommaLiftᴸ W Wᵐ
    prem  : Wᵐ ∣ γᵐ ⊢² V ⊑ N ⟨ H ! ⟩ ∶ pᵐ

To rebuild the smart constructor after peeling the target injection, the proof
needs an arbitrary-smart-world analogue:

    smartCommaLift-∀body-⊑ᵂ :
      SmartCommaLiftᴸ W Wᵐ
      → instᵐ (impEnvʷ W) ⊢
          renameᵗ (extᵗ (toRenameᵗ (ηᴸʷ W))) A
            ⊑ ⇑ᵗ (embedᴿ W H)
      → A ⊑ᵂ⟨ Wᵐ ⟩ H

No such lemma follows from the approved M-1 guard surface.  The smart-alias
case is intentionally non-injective: the fresh source binder is merged into an
existing target alias center, so this is not a `rename-⊑` transport of the
plain `instᵐ` body.  The current guard fields expose the calibrated alias/name
dynamic marks and target mark locality needed by target transports, but not a
general proof that every conclusion `∀⊑` body transports into the arbitrary
smart premise world.

Plausible next decisions:

* add a smart-body obligation transport field/side condition to the smart
  guard surface, if right-injection inversion must peel through arbitrary
  smart pending-Λ derivations;
* or route right-injection inversion around smart pending-Λ cases with a
  narrower reachable-case lemma showing the top-level smart case cannot arise
  on the live M5/M6 path.
