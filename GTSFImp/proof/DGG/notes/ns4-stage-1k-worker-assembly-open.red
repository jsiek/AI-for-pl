NS-4 stage 1k worker assembly open surface
==========================================

Date: 2026-08-14

Status
------

The view-dispatched strict target-head contracts landed and check in live
Agda:

`GTSFImp/proof/DGG/Catchup/StructuralStrictViewSurfaceDef.agda`

This supersedes the generic opened-target-endpoint route from stages 1i/1j.
It does not yet assemble the general structural-spine worker.


What landed
-----------

The checked child-continuation surface is `StructuralStrictChild`.  It packages
exactly the data a recursive worker call needs:

- `child-endpoint`
- `child-plan`
- `child-relation`
- `child-chain`

The checked strict target-head surfaces are:

- `StructuralΛStrictSurfaceᵀ`
- `StructuralAllCastStrictSurfaceᵀ`
- `StructuralGenStrictSurfaceᵀ`
- `StructuralRevealStrictSurfaceᵀ`
- `StructuralConcealStrictSurfaceᵀ`

Each surface receives:

- the caller's `StructuralNamePostPlan`;
- the source/target relation core for the selected target value head;
- source and target value evidence;
- the tail spine;
- the caller's `TargetFrameAbsorptionChain`;
- the peeled child `StructuralTargetInstantiationPackage`.

Each surface returns the child continuation data in the exact child world
required by the peel.


Remaining assembly blocker
--------------------------

The general spine worker also has to consume non-name frames:

- `type-transport-frame`
- `cast-frame`
- `reveal-frame`
- `conceal-frame`

The live target package constructors are forward builders:

- `structural-target-frame`
- `structural-target-frame-keep-step`
- `structural-target-frame-outcome`

They compose a child target package into a parent package.  The worker is given
the parent package.  To recurse through a non-name frame while preserving the
caller's final target, world-extension trace, and endpoint relation, it needs
the inverse child package for the already-completed parent trace.

The missing inverse surface is especially visible for conversion frames:

Diagram:

    M  ⊑  V
    |      |
    | 0    | reveal/conceal frame
    v      v
    M  ⊑  V frame
           |
           | one keep step may fire
           v
          V₁

`StructuralFrameOutcome` classifies `V frame` as either a value or a one-step
keep reduct, and `TargetFrameAbsorptionChain` supplies the relation-side
endpoint/rebase data.  What remains missing is a checked decomposition of the
caller-supplied `StructuralTargetInstantiationPackage W V
(frame ▻ⁱ spine)` into the corresponding child package for either
`V frame` with `spine` or the keep reduct with `mapInstantiationSpine keep
spine`.

Without that inverse package, any recursive call would normalize an
independently constructed child trace rather than the caller's trace, which
would lose the required final relation endpoint.


Consequence
-----------

Do not mark stages 1g or 1h resolved yet.  The view-dispatched surfaces close
the generic endpoint obstruction, but worker assembly still needs target-frame
package decomposition for the non-name frame cases before
`StructuralNameInstantiationᵀ` and `StructuralValueInstantiationᵀ` can be
inhabited without adding a circular whole-worker argument.
