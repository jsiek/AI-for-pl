# D16 stage 1: smart-alias input invariant blocker

Date: 2026-08-19

## Status

The chain-permissive fallback repairs the live target-only
`★`-then-`＇ zero` world.  It does not make a
`SmartAliasMergeGuard W Wᵐ β α` compatible with `WorldInvariants Wᵐ`.
Consequently `smartAliasInsertWorld-invariants` is a checked preservation
theorem, but its `WorldInvariants Wᵐ` premise makes the smart-alias branch
uninhabited.  This is a stage-2 caller-supply blocker, not authorization to
change the selected invariant or the smart-alias semantics during stage 1.

## Contradiction

The guard supplies

`sourceStoreʷ Wᵐ ≡ store-lift (sourceStoreʷ W)`,

`targetStoreʷ Wᵐ ≡ targetStoreʷ W`,

`targetStoreʷ W ∋ β ⦂ ＇ α`,

and the fresh source center is aligned with target `β`.  Direct lookup
therefore gives

$$
\mathsf{lookupStore}\;\Sigma^L_{W^m}\;0 = \mathord{\＇}0
\qquad\text{and}\qquad
\mathsf{lookupStore}\;\Sigma^R_{W^m}\;\beta = \mathord{\＇}\alpha.
$$

`representationsImprecise` at that aligned pair forces the two variable heads
to be center-aligned.  Since the source head is already the center of `β`,
injectivity of `ηᴿʷ Wᵐ` yields `β ≡ α`.  But the same guard also
supplies

`targetStoreʷ W ∋ α ⦂ ★`,

so direct lookup would give `＇ α ≡ ★`, a constructor contradiction.

The contradiction is checked locally inside
`smartAliasTargetInsert-direct`; no postulate, hole, or termination pragma is
used.

## Proposal boundary

A future stage must choose one of these design changes before requiring the
companion at smart-alias consumers:

1. change the smart-alias source representation so its fresh direct entry is
   aligned with the direct representation at `β`;
2. weaken or redesign `representationsImprecise`; or
3. remove the smart-alias branch in favor of the fresh-behind construction.

No such change is part of D16 stage 1.
