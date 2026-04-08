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
    `curry.Types,
    `curry.TypeSubst,
    `curry.Terms,
    `curry.Reduction,
    `curry.Progress,
    `curry.Preservation,
    `curry.TypeSafety,
    `curry.Eval,
    `curry.LogicalRelation,
    `curry.Parametricity,
    `curry.FreeTheorems,
    `curry.Examples,
    `intrinsic.Types,
    `intrinsic.Ctx,
    `intrinsic.Terms,
    `intrinsic.Reduction,
    `intrinsic.Eval,
    `intrinsic.Examples,
    `extrinsic.Types,
    `extrinsic.TypeSubst,
    `extrinsic.Terms,
    `extrinsic.TypeTermSubst,
    `extrinsic.TermSubst,
    `extrinsic.Reduction,
    `extrinsic.Progress,
    `extrinsic.Preservation,
    `extrinsic.TypeSafety,
    `extrinsic.Eval,
    `extrinsic.Examples,
    `extrinsic.LogicalRelation,
    `extrinsic.Parametricity,
    `extrinsic.FreeTheorems,
    `extrinsic.SystemF,
    `extrinsic.All,
  ]

-- Intrinsic-only build target (no curry modules).
lean_lib «intrinsic» where
  roots := #[
    `intrinsic.Intrinsic
  ]

-- Curry-only build target (no intrinsic modules).
lean_lib «curry» where
  roots := #[
    `curry.Types,
    `curry.TypeSubst,
    `curry.Terms,
    `curry.Reduction,
    `curry.Progress,
    `curry.Preservation,
    `curry.TypeSafety,
    `curry.Eval,
    `curry.LogicalRelation,
    `curry.Parametricity,
    `curry.FreeTheorems,
    `curry.Examples
  ]

-- Extrinsic-only build target.
lean_lib «extrinsic» where
  roots := #[
    `extrinsic.Types,
    `extrinsic.TypeSubst,
    `extrinsic.Terms,
    `extrinsic.TypeTermSubst,
    `extrinsic.TermSubst,
    `extrinsic.Reduction,
    `extrinsic.Progress,
    `extrinsic.Preservation,
    `extrinsic.TypeSafety,
    `extrinsic.Eval,
    `extrinsic.Examples,
    `extrinsic.LogicalRelation,
    `extrinsic.Parametricity,
    `extrinsic.FreeTheorems,
    `extrinsic.SystemF,
    `extrinsic.All
  ]
