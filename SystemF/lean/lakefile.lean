import Lake
open Lake DSL

package «systemf» where
  -- Local build for the System F Lean development.
  moreLeanArgs := #[
    "-Dlinter.unnecessarySimpa=false",
    "-Dlinter.unusedVariables=false"
  ]

@[default_target]
lean_lib «SystemF» where
  roots := #[
    `SystemF,
    `extrinsic.Types,
    `extrinsic.TypeSubst,
    `extrinsic.Terms,
    `extrinsic.Reduction,
    `extrinsic.Progress,
    `extrinsic.Preservation,
    `extrinsic.TypeSafety,
    `extrinsic.Eval,
    `extrinsic.LogicalRelation,
    `extrinsic.Parametricity,
    `extrinsic.FreeTheorems,
    `extrinsic.Examples,
    `intrinsic.Types,
    `intrinsic.Ctx,
    `intrinsic.Terms,
    `intrinsic.Reduction,
    `intrinsic.Eval,
    `intrinsic.Examples,
  ]

-- Intrinsic-only build target (no extrinsic modules).
lean_lib «intrinsic» where
  roots := #[
    `intrinsic.Intrinsic
  ]

-- Extrinsic-only build target (no intrinsic modules).
lean_lib «extrinsic» where
  roots := #[
    `extrinsic.Types,
    `extrinsic.TypeSubst,
    `extrinsic.Terms,
    `extrinsic.Reduction,
    `extrinsic.Progress,
    `extrinsic.Preservation,
    `extrinsic.TypeSafety,
    `extrinsic.Eval,
    `extrinsic.LogicalRelation,
    `extrinsic.Parametricity,
    `extrinsic.FreeTheorems,
    `extrinsic.Examples
  ]
