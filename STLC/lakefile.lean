import Lake
open Lake DSL

package «stlc» where
  -- Keep defaults; this project is just a local theorem check.

@[default_target]
lean_lib «Stlc» where
  roots := #[`STLC, `Subst, `TypeSafety, `Termination]
