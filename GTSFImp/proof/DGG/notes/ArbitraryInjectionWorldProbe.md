# Arbitrary endpoint-injection world probe

The checked companion is
`proof.DGG.notes.ArbitraryInjectionWorldProbe`. It imports and exercises the
live endpoint-injection and pivot-update API from `proof.DGG.World`; its small
world record is only a focused test harness. It does not duplicate the live
injection definitions or edit the term-imprecision relation.

## Result

The critical geometry in `SourceBindLiftLeftTrustedProbe` is reachable from
well-typed source programs and ordinary reduction. Therefore it should not be
excluded by a new reachability invariant. The old order-preservation
requirement on the world's endpoint-to-center embeddings is the invariant that
needs revision.

Arbitrary injective endpoint renamings are sufficient for both checked
critical crossings. In each crossing the source embedding before rebase is

    X ↦ X, Y ↦ Y

and the protected `X` must rebase to the target `X₁′` at center `X₁` while the
fresh allocation `Y` remains at center `Y`:

    X ↦ X₁, Y ↦ Y

This function is injective but not order preserving.

For the source-only allocation, the target embedding is

    Z′ ↦ Z, X₁′ ↦ X₁

For the paired allocation, it is

    Y′ ↦ Y, Z′ ↦ Z, X₁′ ↦ X₁

The paired rebase therefore preserves the new alignment `Y ≈ Y′` at center Y.
The probe constructs both pivot updates and checks the central comparisons
`X ⊑ ★` and `ℕ ⊑ ★` after rebasing.

## What requires order today

The following live machinery remains genuinely order-specific:

- `_↪ᵗ_` itself and its `keep`/`skip` constructors;
- OPE-specific helper APIs such as `renameᵐᶜ`, `renameGroundᵐ`, and the
  embedding-pushout code.

These remain appropriate for actual syntax weakening and structural world
evolution. The old source-rebase representation was the inappropriate use of
order: it needed only a renaming function, injectivity, and fixed off-pivot
images.

## What uses only injectivity and equality

The four fields of `DirectWorldInvariantsᶜ` do not mention order:

- `preciseMarksAlignedᶜ` uses equality of the two endpoint images;
- `representationsImpreciseᶜ` uses image equality and central type
  imprecision;
- `unmatchedTargetsDynamicᶜ` uses absence from the source image;
- `dynamicStarSourcesUnoccupiedᶜ` uses absence from the target image.

Likewise, `RightBindFreshᶜ`, CTI's occupancy premises, central type
imprecision, `Occupancy`, `ImpLadder`, and `WorldSnapshot` inspect only endpoint
images, marks, or image equality. The constructor proofs in
`WorldInvariants` use the `keep`/`skip` equations and cancellation of
`Fin.suc`; arbitrary injections provide the same facts.

Type-imprecision renaming needs an injective renaming, not an
order-preserving one: the existing general `rename-⊑` theorem already exposes
exactly that semantic requirement. The same is true conceptually of
occurrence preservation and conversion renaming, although some current helper
signatures package their injective renaming as an OPE.

The order-preserving renamings that represent actual syntax weakening,
endpoint allocation, target extension, or center extension may remain OPEs.
Only the two embeddings stored in a world need to become arbitrary
injections. Composing such an endpoint injection with one of those structural
OPEs produces another arbitrary injection.

## Minimal live surface

The live arbitrary-injection record contains a renaming function and its
injectivity proof. Its core operations are empty, keep, and skip. A live source
rebase carries a pivot update consisting of:

- evidence that the selected pivot actually changes center position;
- the new source injection;
- equality aligning the selected source pivot with the selected target image;
- pointwise equality saying every other source variable keeps its old image.

The world retains its target injection and marks across this change. This is a
genuine replacement for `CanRebaseSourceᵗ`, not a compatibility wrapper.

The direct migration is proceeding in place:

1. `World` now defines injections, `repointⁱ`, and pivot updates.
2. `ηᴸᶜ` and `ηᴿᶜ` now return injections, while structural evolution and
   center-renaming plans remain OPEs.
3. `CanRebaseSourceᵗ` has been deleted and replaced by `PivotUpdateᵗ`.
4. World invariants, occupancy, evolution, rebasing, snapshots, and grounding
   have been migrated and checked.
5. Remaining consumers are being migrated honestly at their import/typecheck
   frontier; no OPE compatibility projection is retained.

This is not a tiny textual migration: 32 live DGG Agda modules mention the
current endpoint projections, and 31 use them through OPE-specific operations.
Most changes are projection and keep/skip algebra. The substantive proof work
is concentrated in `World`, `WorldInvariants`, `WorldEvolution`, the bind
transport families, center/target extension, compilation geometry, and the
right-injection inversion helpers.

This change resolves the concrete crossing geometry. It does not by itself
state or prove the separate reveal/conceal balancing and nesting invariant.
