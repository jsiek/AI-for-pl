T10 calibration probe verdicts
==============================

Status: CHECKED as of 2026-08-17.

No live DGG proof or relation file was changed.  The checked scratch modules
live under `proof/DGG/notes/probes/` and are not imported by `All.agda`.


Probe 1: D6 parked-world preservation
-------------------------------------

Verdict: REFUTED for all four proposed claims.

Checked file:

`proof/DGG/notes/probes/T10Probe1ParkedWorldPreservation.agda`

The counterexample uses a parked world `W` made from one paired bind followed
by one target-only bind.  The rebased world `Wᵖ` keeps the stores and target
embedding but moves the single source pivot onto the target-only center.  That
center still has the dynamic mark `X⊑★`, so `Wᵖ` is not a parked world.

Checked facts:

- `parked-W : ParkedWorld W`
- `forward-rebase : RebaseAt W Wᵖ X Y-fresh`
- `reversed-rebase : RebaseAt Wᵖ W X Y-old`
- `not-parked-Wᵖ : ParkedWorld Wᵖ -> ⊥`
- `claim-a-refuted`
- `claim-b-refuted`
- `claim-c-refuted`
- `claim-d-refuted`

The reversed source-conceal direction is refuted by
`claim-d-refuted`, using `TagRebaseAtᴸ Wᵖ W (just X) (just Y-old)`.


Probe 2: D2b source reveal against still-sealed target
------------------------------------------------------

Verdict: INEXPRESSIBLE for the representative partnered `ℕ` seal.

Checked file:

`proof/DGG/notes/probes/T10Probe2SourceRevealStillSealed.agda`

The partnered sealed shape exists before the source peel:

`sealed-before-peel : ＇X ⊑ᵂ⟨ W ⟩ ＇Y`

The source `conceal-reveal` step is checked:

`source-conceal-reveal-step :
  ((V ↓ seal X ℕ) ↑ unseal X ℕ) —→ V`

But the one-sided post-source endpoint cannot be expressed:

`post-source-reveal-still-sealed-empty :
  ℕ ⊑ᵂ⟨ W ⟩ ＇Y -> ⊥`

This supports the two-sided peel route for the concrete non-variable
representation case.


Probe 3: D7 target keep-step same-`q`
------------------------------------

Verdict: REFUTED for a target-only keep step in the paired
conceal-reveal case.

Checked file:

`proof/DGG/notes/probes/T10Probe3TargetKeepSameQ.agda`

The pre-step relation is inhabited at the exact endpoint witness:

`q : ℕ ⊑ᵂ⟨ W ⟩ ℕ`

`before-target-keep :
  W ∣ [] ⊢² source-revealed ⊑ target-revealed ∶ q`

The target takes one keep step to a value:

`target-keep-step : target-revealed —→[ keep ] target-value`

`target-keep-value : Value target-value`

After only the target step, the same-`q` relation is underivable:

`same-q-after-target-only-empty :
  W ∣ [] ⊢² source-revealed ⊑ target-value ∶ q -> ⊥`

The same `q` is recovered after peeling both sides:

`after-both-peel-same-q :
  W ∣ [] ⊢² source-value ⊑ target-value ∶ q`
