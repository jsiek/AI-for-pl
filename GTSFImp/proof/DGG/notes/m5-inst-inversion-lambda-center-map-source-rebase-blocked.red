M5 instantiation inversion blocker: source rebase breaks side-stable support

Date: 2026-08-12

Completed before this blocker:

  The general support package and derivation exchange theorem are stated
  and checked:

    `CenterMapSupport`
    `⊢²-center-map`

  The induction covers every `CastTermImprecision2` constructor.  Wrapper
  cases consume the relevant Σ-producing support field, rebuild the
  wrapper evidence, and recurse with the returned premise support.

Checked command:

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
    GTSFImp/proof/DGG/Catchup/InstInversionProof.agda

Exact support field that blocks:

  The concrete support constructor for the adjacent exchanges blocks at
  the recursive `rebaseAtForward` field of a premise support returned by
  an earlier successful target-reveal commute.

  The first generated target-reveal commute is fine:

    `right-left-rebase-atᴿ`
    `right-left-under-right-rebase-atᴿ`

  But if that commute rebases the first source variable to the generated
  target center, the returned premise map can have source embedding:

    `keep (skip ηᴸ)`

  and target embedding:

    `skip (keep ηᴿ)`

  This map is still side-stable: each side's image is order-preserving
  for the adjacent swap.

  A later source rebase in an arbitrary derivation can then pivot a later
  source variable (`suc X`) onto the adjacent target center at position
  `Fin.suc Fin.zero`, while the earlier source variable remains at
  position `Fin.zero`.  The premise source embedding becomes:

    `keep (keep η)`

  This is exactly the rejected same-side case.  There is no constructor:

    `Swap01OPE (keep (keep η)) ηˣ`

  and this is correct: swapping positions 0 and 1 would reverse the
  order of two source variables, so the result is not representable as a
  `_↪ᵗ_` source embedding.

  Therefore the recursive support field:

    `rebaseAtForward :
       RebaseAt W Wᵖ Xᴸ Xᴿ →
       Σ Wᵖˣ. Σ mpᵖ. CenterMapSupport mpᵖ × RebaseAt Wˣ Wᵖˣ Xᴸ Xᴿ`

  cannot be filled for the general adjacent exchange support after this
  reachable premise-map shape.

Consequence:

  The parametric theorem is valid: if a caller supplies recursive
  `CenterMapSupport`, `⊢²-center-map` transports an arbitrary derivation
  across the side-stable center map.  But the requested concrete support
  for arbitrary derivations is stronger than the checked OPE
  reification supports.  General derivations may contain source rebases
  that turn a side-stable adjacent exchange into a same-side source swap.

  The `Λ⊑Λ²` generated target-reveal path may still admit a narrower
  support invariant, but the supervisor-requested general support
  constructor for arbitrary derivations does not close with the current
  `World` representation.

No live relation was changed, and no postulate, hole, or catch-all was added.
