T9 proposal: DGG adapter for left catch-up

Date: 2026-08-17

Reason
------

The top-level DGG statement and the fixed `CatchupToLessPrecise` Def should
not change.  The new work should live behind an adapter that exports exactly
the existing surface consumed by `DynamicGradualGuaranteeProof`.

Before context
--------------

`DynamicGradualGuaranteeProof` currently abstracts over:

```agda
dynamic-gradual-guarantee :
    Sim*ᵀ
  → SimBack*ᵀ
  → CatchupToLessPrecise
  → CatchupToMorePrecise
  → TargetBlameCatchupᵀ
  → GradualDGG
```

The `target-value` branch calls:

```agda
catchup
  (parked-world-closed initial-parked evol₁) N⊑N₂′ vV′
```

and handles:

```agda
inj₁ (... N↠V ... evol₂ ... V⊑V′)
inj₂ (... N↠blame ... evol₂)
```

No caller needs to know whether the implementation uses boundary recursion,
source-cast fuel, source wrapper packages, or a left fuel knot.

After context
-------------

Add a proof adapter after the proposed left stack exists.  It can live in a
new module such as:

  `proof/DGG/CatchupToLessPreciseProof.agda`

Proposed statement:

```agda
module proof.DGG.CatchupToLessPreciseProof where

open import Data.Maybe using (nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import proof.DGG.CatchupToLessPreciseDef
  using (CatchupToLessPrecise)
open import proof.DGG.CatchupToMorePreciseDef
  using (boundary-refl)
open import proof.DGG.Catchup.LeftBoundaryCatchupDef
  using (CatchupToLessPreciseBoundary; LeftCatchupResult)

left-boundary-catchup→catchup-to-less-precise :
  CatchupToLessPreciseBoundary → CatchupToLessPrecise
```

Adapter behavior:

  1. Instantiate the boundary worker at:

       `kind = same-boundary`
       `Xᴸ? = nothing`
       `Xᴿ? = nothing`
       `Wᵖ = W`
       `boundary = boundary-refl`

  2. In the value branch, erase `Wᵖ′`, `boundary′`, and the pivot equality.
     The remaining fields match the fixed value branch:

       Δᴸ′, χsᴸ, V, Δ′, W′, q,
       source trace, source value, `ParkedEvolve χsᴸ [] W W′`,
       final CTI2 relation.

  3. In the blame branch, erase the same boundary-only fields and return:

       Δᴸ′, χsᴸ, Δ′, W′,
       source blame trace,
       `ParkedEvolve χsᴸ [] W W′`.

No GradualDGG shape change
--------------------------

`DynamicGradualGuaranteeDef.agda` should remain unchanged.  Its Part 3 already
allows the exact source-blame alternative needed by left catch-up:

```agda
(source reaches a related value) ⊎ (source reaches blame)
```

`DynamicGradualGuaranteeProof.agda` also should not need a shape change.  The
current catchup call is already at the correct point: after backward
simulation has reduced the target residual to the same value by
`value-irreducible*`.

Implementation order after proposals
------------------------------------

1. Land Def-only left boundary and left fuel surfaces.
2. Prove routine closed zero/refutation rows in a left proof module.
3. Land source operation packages one family at a time.
4. Build the left fuel knot.
5. Add the adapter above.
6. Pass the adapter result into `dynamic-gradual-guarantee` without editing
   the DGG statement.
