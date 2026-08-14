NS-4 stage 1b implementation boundary, 2026-08-14:

  Surface:

    `StructuralNameInstantiationᵀ` now has the calibrated R1 shape:
    it consumes a hereditary `StructuralNamePostPlan W A E q` and a
    caller-supplied `StructuralTargetInstantiationPackage W V spine`, then
    proves the final relation at that exact target package and the caller's
    endpoint witness `q`.

  What checks:

    The statement-level calibration cells for the source equal-mass wrappers
    type-check in

      `GTSFImp/proof/DGG/notes/M5StructuralNamePostPlanScratch.agda`

    and the live skeleton in

      `GTSFImp/proof/DGG/Catchup/StructuralNameInstantiationProof.agda`

    now elaborates against the revised worker type.

  New implementation resister:

    The strict target cases cannot yet be implemented against an arbitrary
    caller-supplied `StructuralTargetInstantiationPackage`.

    For a strict target view such as

      `V = Λ V₀`

    the worker must use the first target step

      `(Λ V₀) ⦂∀ B [ ＇ X ]`
      `—→[ bind (＇ X) ]`
      `(V₀ ↑ 〖 zero , ⇑ᵗ (＇ X) ↑ B 〗) ...`

    and then restart recursively at the strictly smaller child spine.  The
    existing strict builders compose child target packages forward:

      `structural-target-Λ-step`
      `structural-target-all-step`
      `structural-target-gen-step`
      `structural-target-reveal-step`
      `structural-target-conceal-step`

    But the revised worker is given the parent package.  There is currently no
    checked inversion/decomposition lemma for

      `StructuralTargetInstantiationPackage W V
        (name-type-app-frame B X refl refl ▻ⁱ spine)`

    that extracts the child package after the first strict target step while
    preserving the caller's final term, structural world-extension trace, and
    final relation endpoint.

  Why this is not the old source-premise blocker:

    The source-premise `q` gap is resolved by `StructuralNamePostPlan`: every
    equal-mass source wrapper has a statement-level child obligation.  The
    remaining obstruction is target-trace decomposition/finalizer support for
    strict target steps.

  Required next support:

    Add one of the following before implementing the total strict worker:

    1. first-step inversion/decomposition lemmas for
       `StructuralTargetInstantiationPackage` at the five `AllValueView`
       strict target heads, or
    2. a revised internal target-plan/finalizer surface that exposes the
       canonical strict child package while still letting equal source wrappers
       transform the caller's target trace into premise worlds.

    The public `InstSpineDescentPackage` and the live relation need not change.
