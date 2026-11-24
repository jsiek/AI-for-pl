# CTI transport consumer audit

This note records the direct consumers of `transport-CTI` before the
contextual-simulation cutover.  The audit distinguishes target-only evolution
from evolution that may allocate and align a source runtime variable.

The broad interface is not sound for arbitrary multi-world evolution.  The
strict probe
`proof.DGG.notes.probes.TransportAlignedRebaseSoundnessProbe` proves both

- `TransportSourceBindTargetRevealRebaseᵀ → ⊥`, and
- `TransportAlignedSourceBindᵀ → ⊥`.

The second theorem uses a root-aligned allocation with no open world frame.
It therefore rejects all three world-only repairs considered during the
transport migration: restricting the theorem to a root source scope,
requiring `openFramesᶜ γ ≡ []`, or combining both restrictions.

## Target-only consumers

The following nine calls receive `MultiWorldEvolution [] χsᴿ` from
`CatchupToMorePrecise`.  An `evolution-bind-left-aligned` edge cannot inhabit
an evolution with an empty source trace.  These calls use the canonical
`TransportTargetTermImprecisionᵀ` interface.

| Consumer | Calls | Evolution provenance |
| --- | --- | --- |
| `SimProof.agda` | 332, 1272 | Function/left-operand `CatchupToMorePrecise` before simulating the right child |
| `SimPairedFunClosingProof.agda` | 81, 97 | Successive function and argument `CatchupToMorePrecise` calls |
| `SimPrimitiveClosingProof.agda` | 63, 77 | Successive left and right operand `CatchupToMorePrecise` calls |
| `SimPairedFunValuesProof.agda` | 366, 500, 637 | Argument `CatchupToMorePrecise` in three target-wrapper cases |

## Aligned-source-sensitive consumers

The remaining nineteen calls stay on the broad interface temporarily.  They
must move to contextual simulation or contextual catch-up; they cannot be
proved by a narrower world-only transport theorem.

### Recursive forward simulation

| Consumer | Calls | Sibling transported after recursion |
| --- | --- | --- |
| `SimProof.agda` | 318, 357 | Application argument; caught-up function |
| `SimProof.agda` | 1208, 1295 | Primitive right operand; caught-up left operand |

The recursive `sim` call may reach the `CTI.⊑reveal-rebase²` branch and
delegate to `SimTargetRevealRebaseClosingᵀ`.  A source `β-inst` step can
return a multi-world evolution beginning with
`evolution-bind-left-aligned`.  The binary parent then tries to transport an
outer sibling that the reveal/rebase closing proof did not receive.

### Backward simulation and source catch-up

| Consumer | Calls | Evolution provenance |
| --- | --- | --- |
| `SimBackProof.agda` | 122, 210, 1184, 1315 | `CatchupToLessPrecise` on the function or left operand |
| `SimBackProof.agda` | 181, 240, 1248, 1343 | Recursive `sim-back` on an application or primitive child |
| `SimBackPairedFunClosingProof.agda` | 97, 135 | Successive `CatchupToLessPrecise` calls |
| `SimBackPairedFunValuesProof.agda` | 459, 627, 810, 999, 1182 | Argument `CatchupToLessPrecise` before reusing the function body relation |

`CatchupToLessPrecise` evolves the source.  Its target-reveal/rebase case is
the clause in `LeftValueCatchupProof.agda` that delegates to
`LeftTargetRevealRebaseCatchupAt`; that interface returns
`MultiWorldEvolution χsᴸ []` and may include aligned source allocation.
The same issue is visible in the source-evolving results of the backward
target-reveal/rebase closing and frame interfaces.

## Why the existing zipper does not cover these siblings

`SimTargetRevealRebaseContextDef` defines edges for applications and
primitives, and those edges retain the sibling CTI derivation.  However,
`contextual-closing-adapter` invokes the contextual proof with
`root-related = focus-related` and `focus-here`.  That relation is the premise
beneath the selected target reveal, in world `γᵖ`.  An enclosing application
or primitive is in the reveal's conclusion world `γ`, so its sibling is not
part of the supplied path.

The next cutover must make `Sim` and `SimBack` contextual over the whole CTI
evaluation context.  Application and primitive recursion should extend that
path and return a relation for the rebuilt whole term, rather than transporting
an arbitrary sibling after recursion.  Forward target catch-up can remain
target-only.  Backward source catch-up also needs a contextual worker because
`CatchupToLessPrecise` itself may return aligned source evolution.

Merely passing the outer zipper is not enough if the proof then replays the
sibling unchanged.  The root counterexample shows that the contextual proof
must either synchronize operational catch-up of the affected sibling or use a
genuine term-level reachability/footprint fact that excludes the target
generator from that sibling.
