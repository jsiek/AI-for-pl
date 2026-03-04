import Lake
open Lake DSL

package «lambda» where
  -- Local project for untyped lambda calculus metatheory.

@[default_target]
lean_lib «Lambda» where
  roots := #[`Lambda, `FullBetaReduction, `CBNReduction, `Subst, `CBNBigStep]
