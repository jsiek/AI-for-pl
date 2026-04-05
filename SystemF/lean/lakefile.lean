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
    `extrinsic.Examples
  ]
