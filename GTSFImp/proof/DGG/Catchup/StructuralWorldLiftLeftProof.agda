module proof.DGG.Catchup.StructuralWorldLiftLeftProof where

-- File Charter:
--   * Lifts a structural target-extension trace under a source binder.
--   * Uses the canonical lifted target insertion at every bind.

import Data.Nat as Nat
import proof.DGG.CtxImp as CTI2
import proof.DGG.TargetExtend as TE
open import Imprecision using (VarImp)
open import Reduction using (StoreChanges)
open import proof.DGG.Catchup.StructuralWorldExtendDef


structural-lift-left : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (v : VarImp)
  → StructuralWorldExtendᴿ χs (CTI2.liftWorldLeft v W)
      (CTI2.liftWorldLeft v W′)
structural-lift-left structural-[] v = structural-[]
structural-lift-left (structural-keep plan) v =
  structural-keep (structural-lift-left plan v)
structural-lift-left (structural-bind ins follows plan) v =
  structural-bind (TE.liftLeftTargetInsert {v = v} ins) follows
    (structural-lift-left plan v)


structural-lift-left-frozen : ∀ {k Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {plan : StructuralWorldExtendᴿ χs W W′}
  → FrozenStructuralTraceᴿ k plan
  → {v : VarImp}
  → FrozenStructuralTraceᴿ (Nat.suc k)
      (structural-lift-left plan v)
structural-lift-left-frozen frozen-trace-[] = frozen-trace-[]
structural-lift-left-frozen (frozen-trace-keep frozen) =
  frozen-trace-keep (structural-lift-left-frozen frozen)
structural-lift-left-frozen
    (frozen-trace-bind frozen-ins frozen) =
  frozen-trace-bind (frozen-embedding-keep frozen-ins)
    (structural-lift-left-frozen frozen)
