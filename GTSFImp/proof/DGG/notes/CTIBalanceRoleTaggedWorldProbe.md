# Role-tagged world-history probe

Status: strict stage-one probe of the live role-aware `World.agda`.  This stage
does not change `CastTermImprecision.agda` or `WorldEvolution.agda`.

The checked implementation is `CTIBalanceRoleTaggedWorldProbe.agda`.
`World.agda` now gives `rebase-source-changeᶜ` a role from the dependent
type:

```agda
data SourceRebaseRoleᶜ γ Xᴸ Xᴿ update : Set where
  open-frameᶜ : SourceRebaseRoleᶜ γ Xᴸ Xᴿ update
  alignment-onlyᶜ : AlignmentBoundaryᶜ γ Xᴸ Xᴿ update
    → SourceRebaseRoleᶜ γ Xᴸ Xᴿ update
```

`openFramesᶜ γ` folds the history of the one current world `γ` from oldest
to newest:

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
| TargetIdentityReveal after the alpha rebase, stage one | `[X ↔ Y′]` |
| TargetIdentityReveal C8, stage one | `[X ↔ X′, X ↔ Y′]` |

The Example 12 C12 target pivots show the required runtime-allocation
renaming.  The inner and outer target pivots have shifted from `X′, Y′` to
`Y′, Z′`.

## Non-top allocation discharge

The separate strict `AlignmentOnlyRebaseInvariantProbe.agda` shows how stage
two can discharge the non-top allocation frame.  Before the source allocation
in TargetIdentityReveal, the alpha frame is
below the live beta frame:

`[X ↔ X′, X ↔ Y′]`.

The allocation does not perform an illegal LIFO pop of the lower alpha frame.
The next current world is rebuilt from `checkpoint₁-world`, before either
old rebase, and then records:

1. the alpha rebase as `alignment-only`;
2. the beta rebase as `open-frame`.

Once that checked role is installed by the evolution migration, the derived C8
list will consequently be `[X ↔ X′]`.  In stage one every production rebase is
deliberately `open-frameᶜ`, so the live C8 pin remains
`[X ↔ X′, X ↔ Y′]`.  The alpha embedding change remains in the world in both
stages; only its dynamic nesting role changes.

The next migration stage must make the world-evolution proof assign the
alignment-only role when it constructs the post-allocation world.  No extra
data is needed in an individual rebase change beyond the role and its existing
endpoint pivots; the non-top discharge is a checked change of current world.

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
geometry checked here.  Stage one derives the open-frame stack and its
binder/runtime renamings directly from the live world while preserving the old
behavior by tagging every production rebase `open-frameᶜ`.  The separate
alignment probe checks the evidence needed for the stage-two non-top discharge.

The mechanical live migration implied by the probe is:

1. completed: add `SourceRebaseRoleᶜ` to `rebase-source-changeᶜ`;
2. completed: make `SourceRebaseᶜ.source-rebase-now` construct only
   `open-frameᶜ` changes and prove its frame equation through all scopes;
3. completed: define `openFramesᶜ γ` by the checked history fold;
4. make world-evolution constructors state whether a newly constructed
   rebase is alignment-only or open, with the TargetIdentityReveal allocation
   transition proving the one non-top discharge;
5. keep application and primitive closure persistent: every sibling receives
   the same derived `openFramesᶜ γ`.
