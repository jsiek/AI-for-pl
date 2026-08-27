# Role-tagged world-history probe

Status: strict notes-only probe.  This does not change `World.agda` or
`CastTermImprecision.agda`.

The checked implementation is `CTIBalanceRoleTaggedWorldProbe.agda`.  It
models the proposed extra argument to `rebase-source-changeᶜ` as:

```agda
data RebaseRole : Set where
  alignment-only open-frame : RebaseRole
```

`TaggedHistory γ` contains exactly one role for each source-rebase change in
the history of the one current world `γ`.  `deriveOpenFrames γ roles` folds
that history from oldest to newest:

- `alignment-only` keeps the current frame list;
- `open-frame` pushes the rebase's endpoint pair;
- a paired lift or allocation renames every pair by `(suc , suc)`;
- a source-only lift or allocation renames every pair by `(suc , id)`;
- a target-only allocation renames every pair by `(id , suc)`;
- a term binder, center extension, and all other endpoint-preserving changes
  keep the pairs unchanged.

These equations are pinned generically by `refl` in the probe.  Therefore the
frame list is derived from one current world, not stored as a second index on
CTI and not reconstructed from a second predecessor world.

## Trusted geometry pins

All pairs below are endpoint pivots.  The list head is the currently innermost
open frame.

| Geometry | Derived open frames |
| --- | --- |
| Example 12 C1, outside both target reveals | `[]` |
| Example 12 C1, inside the outer reveal | `[X ↔ Y′]` |
| Example 12 C1, inside both reveals | `[X ↔ X′, X ↔ Y′]` |
| Example 12 C12, outside both target reveals | `[]` |
| Example 12 C12, inside the outer reveal | `[X ↔ Z′]` |
| Example 12 C12, inside both reveals | `[X ↔ Y′, X ↔ Z′]` |
| TargetIdentityReveal C1, inside both reveals | `[X ↔ X′, X ↔ Y′]` |
| TargetIdentityReveal after source allocation, before rebases | `[]` |
| TargetIdentityReveal after the alpha alignment rebase | `[]` |
| TargetIdentityReveal C8, inside the live beta frame | `[X ↔ X′]` |

The Example 12 C12 target pivots show the required runtime-allocation
renaming.  The inner and outer target pivots have shifted from `X′, Y′` to
`Y′, Z′`.

## Non-top allocation discharge

Before the source allocation in TargetIdentityReveal, the alpha frame is
below the live beta frame:

`[X ↔ X′, X ↔ Y′]`.

The allocation does not perform an illegal LIFO pop of the lower alpha frame.
The next current world is rebuilt from `checkpoint₁-world`, before either
old rebase, and then records:

1. the alpha rebase as `alignment-only`;
2. the beta rebase as `open-frame`.

The derived C8 list is consequently `[X ↔ X′]`.  The alpha embedding
change remains in the world, while alpha no longer contributes an open CTI
frame.  This is the critical reason that an alignment/open role is useful:
the rebase operation and the dynamic nesting obligation are not the same
fact.

The mechanized migration will still need its world-evolution proof to assign
these roles when it constructs the post-allocation world.  No extra data is
needed in an individual rebase change beyond the role and its existing
endpoint pivots; the non-top discharge is a checked change of current world,
not an in-place list operation.

## Persistent branch sharing

The probe applies frame recovery directly to the two actual C10 subproofs:

- `TargetIdentityConceal.checkpoint₆-beta-concealed-argument-imprecision`;
- `TargetIdentityReveal.checkpoint₈-beta-conceal-imprecision`.

Both recover `[X ↔ X′]` from the same current world.  Each branch may
independently traverse the matching conceal.  Thus frames are persistent
pathwise information, not a linear resource consumed by the first sibling.

The primitive probe's checked CTI checkpoint also recovers `[X ↔ X′]`.
Both primitive operands inherit that same ambient list; only the left operand
contains the conceal.  Shared application and primitive premises therefore
remain adequate.

## Result

A role tag on `rebase-source-changeᶜ` is sufficient for every trusted
geometry checked here.  Together with the existing `Xᴸ` and `Xᴿ` fields, it
derives the open-frame stack, its binder/runtime renamings, LIFO reveal/conceal
behavior, branch sharing, and the non-top allocation discharge.  The tag does
not eliminate the need to prove role preservation or reassignment across
world evolution; it makes that obligation explicit without duplicating the
frame stack in CTI.

The mechanical live migration implied by the probe is:

1. add `RebaseRole` to `rebase-source-changeᶜ`;
2. index `SourceRebaseᶜ` by that role, preserve it through bind/lift closure,
   and require `open-frame` in the two CTI rebase rules;
3. define `openFramesᶜ γ` by the checked history fold, so CTI consumers ask
   only for their current `γ`;
4. make world-evolution constructors state whether a newly constructed
   rebase is alignment-only or open, with the TargetIdentityReveal allocation
   transition proving the one non-top discharge;
5. keep application and primitive closure persistent: every sibling receives
   the same derived `openFramesᶜ γ`.
