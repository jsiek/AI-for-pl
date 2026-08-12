M5 smart comma M-2 blocked at TargetExtend smart-fresh-behind.

Status: RESOLVED in the M-2 continuation, 2026-08-12.

Continuation: `proof.DGG.TargetExtend` now carries the off-image
disjointness lemmas and closes both smart constructor branches of
`⊢²-target-insert`.  The next blocker is recorded in
`m5-smart-comma-target-bind-lift-pivot-blocked.red`.

Checked before the block:

* `proof.DGG.CastTermImprecision2` has the live
  `Λ⊑²-smart-comma` constructor and the M-1 guard predicates.
* `proof.DGG.CastTermImprecision2Typing` checks the source and target
  typing cases.
* `proof.DGG.CenterRename` checks both smart transports.  The
  `smart-fresh-behind` branch uses an explicit pushout of center
  embeddings.
* `proof.DGG.TermImpDecay` checks the smart decay case.  The smart
  guard is stable because the decayed conclusion world's imprecision
  environment is not part of the guard fields.

The first non-mechanical M-2 failure is the generic target-insertion
transport:

    ⊢²-target-insert ins
      (Λ⊑²-smart-comma Anv z∈A (smart-fresh-behind guard)
        liftγ vV target⊢ prem q)

To rebuild the inserted derivation, the natural premise world is:

    old    = SmartFreshBehindGuard.oldCenters guard
    po     = pushout π old
    πᵐ     = EmbeddingPushout.premise po
    old′   = EmbeddingPushout.old′ po

    Wᵐ⁺ = world
      (πᵐ ∘ ηᴸʷ Wᵐ)
      (old′ ∘ ηᴿʷ W⁺)
      (renameEnv πᵐ (impEnvʷ Wᵐ))
      (sourceStoreʷ Wᵐ)
      (targetStoreʷ W⁺)

Most fields have direct transports:

* `sourceStore-lifted` follows from `guard.sourceStore-lifted` and
  `TargetInsert.sourceStore-kept ins`;
* `targetStore-same` is definitional if `Wᵐ⁺` uses `targetStoreʷ W⁺`;
* `target-frozen` follows by definition of `ηᴿʷ Wᵐ⁺`;
* `old-source-frozen` follows from `guard.old-source-frozen`, the
  pushout commute, and `TargetInsert.source-insert ins`;
* `fresh-mark-dynamic` follows from `renameEnv-image` at `πᵐ`.

The missing obligation is exactly:

    ∀ Y′ →
      toRenameᵗ (old′ ∘ ηᴿʷ W⁺) Y′
        ≢ toRenameᵗ (πᵐ ∘ ηᴸʷ Wᵐ) zero

The M-1 guard only provides:

    ∀ Y →
      toRenameᵗ (ηᴿʷ Wᵐ) Y
        ≢ toRenameᵗ (ηᴸʷ Wᵐ) zero

That discharges the old-target-image subcase `Y′ = toRenameᵗ ρ Y`.
It says nothing about a freshly inserted target variable
`Y′` with `preimage? ρ Y′ = nothing`.  `TargetInsert` can reflect target
centers that land in the old center image `π`, but the needed equality is
against the transported smart fresh source center `πᵐ(ηᴸʷ Wᵐ zero)`.
There is no side condition tying newly inserted target centers to that
fresh source center, so the required contradiction is not derivable from
the approved M-1 signature.

This is not an Agda bookkeeping gap.  The live rule statement needs one
more invariant before generic `TargetExtend` can transport the fresh-behind
smart case.  Plausible fixes:

* strengthen `SmartFreshBehindGuard` with a fresh-center disjointness
  invariant strong enough to survive pushouts and target insertions;
* strengthen the pushout/target-insert transport surface with an
  off-image disjointness lemma for newly inserted target centers against
  the transported smart fresh source center;
* restrict `smart-fresh-behind` target transport to the concrete right-bind
  layout used by the generated reveal window, with that disjointness carried
  as an explicit witness.

The `smart-merge-alias` branch does not expose this particular gap: the
alias and name slots are target-image variables `toRenameᵗ ρ β` and
`toRenameᵗ ρ α`, and the old `no-old-source-at-alias` proof can be
transported through `TargetInsert.source-insert`, `TargetInsert.target-insert`,
and injectivity of the center insertion `π`.
