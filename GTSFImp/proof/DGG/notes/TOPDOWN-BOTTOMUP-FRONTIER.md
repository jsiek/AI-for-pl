# Top-down / bottom-up frontier reconciliation (supervisor-maintained)

Purpose: PRs #145-#147 landed the TOP-DOWN DGG proof
(`DynamicGradualGuaranteeProof.dynamic-gradual-guarantee`), higher-order
over seven assumed surfaces. The BOTTOM-UP work (the CTI repair gates
LG-1..LG-3, then the M4-M6 Catchup stack, then M7) must eventually
inhabit them — "meet in the middle." This memo tracks the interface fit
and the closing lemmas each meeting point needs. Updated by the
supervisor whenever either frontier moves.

## The top-down assumed surfaces (the unproven lemmas)

    dynamic-gradual-guarantee :
        Sim*ᵀ → SimBack*ᵀ
      → CatchupToLessPrecise → CatchupToMorePrecise
      → TargetBlameCatchupᵀ
      → ValueIrreducible*ᵀ → BlameIrreducible*ᵀ
      → GradualDGG

Sim*ᵀ/SimBack*ᵀ are proven (MultiSim{,Back}Proof) from the ONE-STEP
`Simᵀ` (SimDef) and `SimBackᵀ` (SimBackDef), so the real frontier is:
Simᵀ, SimBackᵀ, CatchupToLessPrecise, CatchupToMorePrecise,
TargetBlameCatchupᵀ (ValueIrreducible*/BlameIrreducible* are
reduction-theory obligations, likely easy).

## Fit assessment, per surface

1. `CatchupToMorePrecise` ↔ bottom-up `ValueCatchupRightAt` (LG-3
   columnless form). SHAPES ALIGN after the columnless redesign
   (arbitrary target term, whole ⊢² derivation, value conclusion, no
   blame disjunct — matches the M4 original-value-conclusion design).
   The old CastColumn form would NOT have aligned. Closing lemmas
   needed at the meeting point:
   a. FUEL DISCHARGE: `∃ fuel. TargetCastBound fuel rel` computed from
      the derivation (finite cast sizes), so the closed form is
      fuel-free like the top-down surface.
   b. EVOLUTION CONVERSION: bottom-up returns `WorldExtendᴿ χs W W′`;
      top-down wants `ParkedEvolve [] χsᴿ W W′` under a `ParkedWorld W`
      premise. Need the embedding lemma (right-only extensions are
      parked: `evolve-right-bind` family). RISK FLAG: the parked
      discipline enters fresh target pivots at Fin.zero (M2 frozen
      rule); if any bottom-up `TargetInsert` used at the catch-up
      surface inserts at a non-zero position, the embedding needs
      either a discipline argument or a parked-family extension —
      check when closing.
   c. Bottom-up theorems are UNCONDITIONAL in ParkedWorld, so the
      premise costs nothing; instantiate at γ = [].
2. `Simᵀ` / `SimBackᵀ` — M7 (one-step simulation over M4-M6). Not
   started; the bottom-up plan already points here.
3. `CatchupToLessPrecise` — LEFT catch-up (target value, source runs,
   with a source-blame disjunct). NO bottom-up machinery exists yet:
   the entire Catchup stack is right-side. NEW OBLIGATION to schedule
   after LG-3 (likely easier: the source is more precise, so its casts
   are no less defined, but the blame disjunct and ParkedEvolve-left
   need their own treatment).
4. `TargetBlameCatchupᵀ` — `M ⊑ blame` implies the source reaches
   blame. NEW OBLIGATION; relates to the tag-discipline blame analysis.
   Note the CTI blame rule (`blame⊑²`) shapes what inversion gives.
5. MERGE FRICTION (mechanical): DynamicGradualGuaranteeProof imports
   `ColumnSupportProof (applyTys-++; composeReduction)` — LG-3 renamed
   that module to FuelSupportProof (contents survive: `_++χ_` still in
   ValueCatchupRightDef; composeReduction/applyTys-++ in
   FuelSupportProof). The LG-3 branch must fix these imports on
   rebase/merge.

## Standing watch instructions

- After each bottom-up gate lands, re-diff origin/main's
  proof/DGG/{SimDef,SimBackDef,Catchup*Def,TargetBlameCatchupDef,
  DynamicGradualGuarantee*}.agda against this memo; update the fit
  table.
- If the top-down side changes an assumed surface's SHAPE, flag to the
  user before the bottom-up work targets the old shape (and vice
  versa: bottom-up statement reshapes — like the columnless redesign —
  should be checked against this list before landing).

## Update 2026-08-16 (PRs #148-#150): the frontier moved substantially

1. FIT TABLE STALE — CatchupToMorePrecise was RESHAPED (+128 lines):
   it is now boundary-kind-indexed (`CatchupBoundaryKind`:
   same/source-reveal/source-conceal/target-reveal/target-conceal
   boundaries) and, notably, imports the NS-4 STRUCTURAL vocabulary
   (`StructuralWorldExtendᴿ`, `mapPivotChanges`, targetPivot maps of
   rebases). The top-down side is converging toward the bottom-up
   structural forms — the meeting point is now much closer to
   StructuralCatchupRightAt than the old fit assessment assumed.
   RE-MAP after LG-3 lands.
2. NEW ASSUMED SURFACES — SimProof (the one-step Simᵀ skeleton, 743
   lines, PR #149-150) is parameterized over EIGHT closing interfaces:
   SimPairedFunClosingᵀ, SimPairedAllClosingᵀ, SimSourceAllClosingᵀ,
   TransportTermImprecisionᴾᵀ, SimSourceRevealᵀ, SimTargetRevealᵀ,
   SimSourceConcealᵀ, SimTargetConcealᵀ — each a separate Def file,
   each an independent bottom-up work item (strong parallelism
   candidates; several look like thin wrappers over the LG-1/NS-4
   strip/replay machinery).
3. SimProof still carries 22 OPEN HOLES (committed to main; the file
   is deliberately partial, not in All.agda) — the remaining sim
   square cases; PR #150 closed the first six.
4. PROCESS FLAG: main's `make postulate-check` is RED — the holes in
   SimProof.agda fail the {! grep. The top-down PRs did not run the
   gate. Needs a user decision: sanction a declared-WIP location the
   hygiene check excludes, or require the gate on top-down PRs.

## Re-map 2026-08-17 (post-#144 merge; supervisor)

The top-down SimProof has ZERO holes; its 13 assumed interfaces are
the entire frontier. Fit classification:
1. CatchupToMorePrecise (boundary-kind-indexed, built on the NS-4
   structural vocabulary) = our ValueCatchupRightAt closed form +
   three linking lemmas (fuel discharge, WorldExtendᴿ→ParkedEvolve,
   boundary adapters). Staged behind the assembly residual (T1/T4).
2. Left-side step family (SimSource/Paired{Cast,Reveal,Conceal}Values,
   SimConversionFrames; SimPrimitiveValues landing separately by the
   user) = the right-side rows mirrored; independent (T2).
3. β-closings (SimPairedFun/AllClosing, SimSourceAllClosing) — the ∀
   ones touch the M5 Λ machinery; queued.
4. TransportTermImprecisionᴾ — transport repackaging; queued.
5. SimBackᵀ, CatchupToLessPrecise, TargetBlameCatchupᵀ — unchanged;
   queued.
Confirmed meet-events: the top-down imports StructuralWorldExtendᴿ /
mapPivotChanges; reveal-↠/conceal-↠ (main, #152/#153) is the likely
discharge of assembly-residual item 1 (T1 confirms first).
Parallel tracks live (2026-08-17): T1 assembly follow-on
(agent/gtsf-lg3-assembly), T2 left-side family
(agent/gtsf-sim-left-values), T3 legacy NON_COVERING repair
(agent/gtsf-legacy-noncovering). T4 = meet-point closure, staged
behind T1.
