# Two-`Ctx` closed-world migration audit

## Scope and verdict

This is a read-only audit of the old world surface in
`proof/DGG/CtxImp.agda` against the live `TwoCtxWorld`,
`TwoCtxWorldInvariants`, and checked `TwoCtxSourceRebasePlanProbe`,
`TwoCtxTargetExtendPlanProbe`, `TwoCtxTargetStripReconstructionProbe`, and the
edge-indexed alias-mode probes.  The typed boundary and scoped-term probes
additionally check the type and term-indexed surface.  The counts below are
exact textual references in live `.agda` files
outside `CtxImp.agda` and `proof/DGG/notes/`, measured on 2026-08-21.  A
breadth such as `4 / 19` means four consumer modules and nineteen exact
references.

The core result is simple: the checked two-`Ctx` relation already represents
every legitimate inductive history head.  No additional core world
constructor is justified by the live surface.  The remaining work is to prove
structural producers that replace four escape/splice constructors and to
integrate the checked rebase and boundary-focus plans.

## Live `World` constructors

| Live constructor | Checked two-`Ctx` form | Live breadth | Disposition |
|---|---|---:|---|
| `emptyʷ` | `emptyᶜ₀` | 9 / 31 | Direct. |
| `skip-centerʷ` | `skip-centerᶜ₀` | 4 / 19 | Direct. |
| `lift-bothʷ` | `lift-both-rawᶜ₀` | 2 / 14 | Direct; raw `Γ` equalities preserve constructor-form indices. |
| `lift-leftʷ` | `lift-left-rawᶜ₀` | 1 / 11 | Direct. |
| `bind-leftʷ` | `bind-left-rawᶜ₀` | 4 / 23 | Direct. |
| `bind-rightʷ` | `bind-right-rawᶜ₀` | 4 / 21 | Direct, with `RightBindFreshᶜ₀`. |
| `bind-bothʷ` | `bind-both-rawᶜ₀` | 3 / 18 | Direct, with an explicit type-imprecision premise. |
| `bind-both-starʷ` | `bind-both-star-rawᶜ₀` | 7 / 30 | Direct, including `⇑ᵗ A ≢ ★`. |
| `honestifyʷ` | no constructor | 2 / 15 | Delete outright; raw worlds are already honest. |
| `lower-leftʷ` | no constructor | 2 / 15 | Delete; it accepts a separately assembled world and invariants. |
| `mix-targetʷ` | no constructor | 2 / 15 | Delete; replace by a structural target-extension producer. |
| `mix-renamed-targetʷ` | no constructor | 3 / 25 | Delete; checked `CenterRenamePlanᶜ₀` reconstructs structural history. |

The checked relation also has `bind-termᶜ₀`, which absorbs the term-context
step that the live design stores separately in `CtxImp`.  This is a genuine
constructor because both complete endpoint `Ctx` indices determine the term
contexts; it is not another world escape.

The direct constructors occur in the following modules.  These are exact
module sets; `CenterRename.agda` accounts for most constructor-pattern
references.

| Constructor | Consumer modules |
|---|---|
| `emptyʷ` | `CenterRename`, `ChainRideProbe`, `Example12Worlds`, `Examples2`, `MovedLinkProbe`, `SmartCommaWitness`, `StarRepChainProbe`, `TagBoundaryProbe`, `TerminusRebuildProbe` |
| `skip-centerʷ` | `CenterRename`, `ChainRideProbe`, `MovedLinkProbe`, `StarRepChainProbe` |
| `lift-bothʷ` | `CenterRename`, `Examples2` |
| `lift-leftʷ` | `CenterRename` |
| `bind-leftʷ` | `CenterRename`, `Example12Worlds`, `Examples2`, `StarRepChainProbe` |
| `bind-rightʷ` | `CenterRename`, `Example12Worlds`, `MovedLinkProbe`, `TagBoundaryProbe` |
| `bind-bothʷ` | `CenterRename`, `Example12Worlds`, `Examples2` |
| `bind-both-starʷ` | `CenterRename`, `Example12Worlds`, `Examples2`, `MovedLinkProbe`, `StarRepChainProbe`, `TagBoundaryProbe`, `TerminusRebuildProbe` |

## Smart constructors and projections

| Live operation | Checked replacement | Live breadth | Status |
|---|---|---:|---|
| `initialWorld` | `initialWorldᶜ₀` recursion through `liftBothᶜ₀` | 7 / 38 | Checked with constructor-form endpoints, center, embedding-alignment, and mark laws. |
| `emptyCenterWorld` | `emptyCenterWorldᶜ₀` recursion through `skip-centerᶜ₀` | 1 / 4 | Checked with center, embedding-alignment, and dynamic-mark laws. |
| `liftWorldBoth` | `liftBothᶜ₀` | 14 / 345 | Checked. |
| `liftWorldLeft` | `liftLeftᶜ₀` | 26 / 433 | Checked. |
| `leftOnlyWorld` | `bindLeftᶜ₀` | 8 / 19 | Checked. |
| `rightOnlyWorld` | `bindRightᶜ₀` | 20 / 287 | Checked. |
| `bothBindWorld` | `bindBothᶜ₀` | 8 / 26 | Checked. |
| direct `bind-both-starʷ` use | `bindBothStarᶜ₀` | included above | Checked smart function; the live layer has no corresponding smart wrapper. |

The exact smart-constructor module sets are:

- `initialWorld`: `CompilePreservesImprecision2`,
  `DynamicGradualGuaranteeProof`, `GroundingMint`, `Occupancy`,
  `Parked/ParkedWorldDef`, `Phase3DeepDives`, and `SmartCommaWitness`;
- `emptyCenterWorld`: `CenterRename`;
- `liftWorldBoth`: `CastTermImprecision`, `CastTermImprecision2Typing`,
  `Catchup/InstInversionDef`, `Catchup/InstInversionLambdaProof`,
  `CenterRename`, `CompilePreservesImprecision2`, `Examples2`,
  `GroundingMint`, `ImpLadder`, `Occupancy`, `ReachabilityScreen`,
  `TargetBindLift`, `TargetExtend`, and `TermImpDecay`;
- `liftWorldLeft`: `CastTermImprecision`, `CastTermImprecision2Typing`,
  `Catchup/InstInversionDef`, `Catchup/InstInversionLambdaProof`,
  `Catchup/InstInversionProof`, `Catchup/StructuralCatchupRightDef`,
  `Catchup/StructuralInstantiationDescentDef`,
  `Catchup/StructuralSourceLambdaReplayProof`,
  `Catchup/StructuralSpineTypingDef`,
  `Catchup/StructuralTargetSourceTransportProof`,
  `Catchup/StructuralTermProvenanceProof`,
  `Catchup/StructuralWorldEvidenceProof`,
  `Catchup/StructuralWorldLiftLeftProof`, `CenterRename`,
  `CompilePreservesImprecision2`, `GroundingMint`,
  `Inversion/TargetStripDef`, `Inversion/TargetStripProof`,
  `Inversion/TargetWalkSupport`, `LambdaImpProbe`, `Occupancy`,
  `SmartCommaWitness`, `TargetBindLift`, `TargetExtend`, `TermImpDecay`, and
  `TerminusRebuildProbe`;
- `leftOnlyWorld`: `ChainRideProbe`, `LambdaImpProbe`, `Occupancy`,
  `Parked/ParkedBindImprecisionProof`, `Parked/ParkedWorldDef`,
  `Parked/ParkedWorldProof`, `TransportTermImprecisionDef`, and
  `TransportTermImprecisionProof`;
- `rightOnlyWorld`: `Catchup/InstCatchupRightDef`,
  `Catchup/InstInversionDef`, `Catchup/InstInversionLambdaProof`,
  `Catchup/InstInversionProof`, `Catchup/StructuralGenDescentProof`,
  `Catchup/StructuralSpineTypingDef`,
  `Catchup/StructuralTargetConversionStepProof`,
  `Catchup/StructuralTargetGenStepProof`,
  `Catchup/StructuralTargetInstStepProof`,
  `Catchup/StructuralTargetLambdaStepProof`, `GroundingPreserve`, `Occupancy`,
  `Parked/ParkedBindImprecisionProof`, `Parked/ParkedWorldDef`,
  `Parked/ParkedWorldProof`, `Phase3DeepDives`, `SmartCommaWitness`,
  `TargetBindLift`, `TargetExtend`, and `TransportTermImprecisionProof`;
- `bothBindWorld`: `ChainRideProbe`, `Occupancy`,
  `Parked/ParkedBindImprecisionProof`, `Parked/ParkedWorldDef`,
  `Parked/ParkedWorldProof`, `Phase3DeepDives`,
  `TransportTermImprecisionDef`, and `TransportTermImprecisionProof`.

The projection migration is lossless:

| Live projection | Two-`Ctx` expression | Live breadth |
|---|---|---:|
| center index `Δ` | `centerᶜ₀ W` | indexed live, so no textual projection count |
| `ηᴸʷ` | `ηᴸᶜ₀` | 33 / 477 |
| `ηᴿʷ` | `ηᴿᶜ₀` | 30 / 510 |
| `impEnvʷ` | `marksᶜ₀` | 24 / 384 |
| `sourceStoreʷ` | `Σᵉ Cᴸ` | 39 / 224 |
| `targetStoreʷ` | `Σᵉ Cᴿ` | 57 / 494 |
| `srcCtxʷ` | `Γᵉ Cᴸ` | 2 / 17 |
| `tgtCtxʷ` | `Γᵉ Cᴿ` | 16 / 83 |

`sourceStoreʷ`, `targetStoreʷ`, `srcCtxʷ`, and `tgtCtxʷ` should disappear,
not be reintroduced as aliases.  The endpoint projections are the canonical
closed-world surface.

The associated context scaffolding has substantial migration breadth:
`CtxImpEntry` is 1 / 4, `CtxImp` is 146 / 867, `SameCtx` is 26 / 147,
`LiftCtx` is 11 / 88, `LiftCtxᴸ` is 18 / 137, and `SmartLiftCtxᴸ` is
13 / 45.  `bind-termᶜ₀` replaces the data representation; syntax-directed
lookup and lifting theorems still have to be rebuilt over endpoint `Γᵉ`.

## Escape and splice deletion order

The four nonstructural `World` constructors have very narrow real producer
sets despite the recursive pattern burden in `CenterRename`:

| Constructor | Exact live modules and reference counts | Actual non-rename producer |
|---|---|---|
| `honestifyʷ` | `CenterRename` 14; `WorldDecay` 1 | `WorldDecay.honestify` |
| `lower-leftʷ` | `CenterRename` 14; `Inversion/TargetStripProof` 1 | target-strip reconstruction |
| `mix-targetʷ` | `CenterRename` 14; `TargetExtend` 1 | target extension |
| `mix-renamed-targetʷ` | `CenterRename` 22; `SmartCommaWitness` 2; `TargetExtend` 1 | smart-comma witnesses and target extension |

These constructors should not survive as invariant-accepting compatibility
paths.  The structural center-renaming interpreter now checks through every
raw history head; its operational callers still need to produce explicit
plans with rebuilt freshness and type-imprecision premises.  Honestification
needs no producer: direct induction proves that raw worlds already mark every
target-unaligned center `X⊑★`.  Deletion of the remaining escapes then requires
target extension and target-strip reconstruction.  Once those producers
exist, the many
`CenterRename` clauses for the four constructors disappear rather than being
translated.

The live smart-comma surface is the same kind of splice at the relation level:

- `SmartFreshBehindGuard`: 12 modules / 134 references;
- `SmartAliasMergeGuard`: 11 modules / 97 references;
- `SmartCommaLiftᴸ`: 14 modules / 31 references.

The exact consumers are:

- `SmartFreshBehindGuard`: `CastTermImprecision2Typing`,
  `Catchup/InstInversionLambdaProof`, `Catchup/InstInversionProof`,
  `Catchup/StructuralWorldEvidenceProof`,
  `Catchup/StructuralWorldSmartLiftProof`, `CenterRename`, `ImpLadder`,
  `Occupancy`, `SmartCommaWitness`, `TargetBindLift`, `TargetExtend`, and
  `TermImpDecay`;
- `SmartAliasMergeGuard`: `CastTermImprecision2Typing`,
  `Catchup/InstInversionLambdaProof`, `Catchup/InstInversionProof`,
  `Catchup/StructuralWorldEvidenceProof`,
  `Catchup/StructuralWorldSmartLiftProof`, `CenterRename`, `Occupancy`,
  `SmartCommaWitness`, `TargetBindLift`, `TargetExtend`, and `TermImpDecay`;
- `SmartCommaLiftᴸ`: `CastTermImprecision`,
  `CastTermImprecision2Typing`, `Catchup/InstInversionLambdaProof`,
  `Catchup/StructuralCatchupRightDef`,
  `Catchup/StructuralInstantiationDescentDef`,
  `Catchup/StructuralSourceLambdaReplayProof`,
  `Catchup/StructuralTargetSourceTransportProof`,
  `Catchup/StructuralTermProvenanceProof`,
  `Catchup/StructuralWorldEvidenceProof`,
  `Catchup/StructuralWorldSmartLiftDef`,
  `Catchup/StructuralWorldSmartLiftProof`, `Occupancy`, `TargetBindLift`, and
  `TermImpDecay`.

The fresh-behind case should become a structural plan produced from raw
history.  The alias-merge case should become a boundary-local
`TargetNameFocus` plus exact `TargetAliasBoundary`, leaving the stable world
unchanged.  Neither case warrants a splice constructor or a record that accepts
an arbitrary post-world and a bundle of global facts.

## Rebase and direct representation

`TwoCtxSourceRebasePlanProbe` now commutes source rebasing through every raw
history head.  It explicitly asks for rebuilt `RightBindFreshᶜ₀` or
type-imprecision evidence exactly where reconstruction needs it.  Its result
preserves both endpoint `Ctx` indices, the hidden center, off-pivot source
embeddings, all target embeddings, pivot alignment, and the direct invariants.

The missing fact is a producer theorem, not another plan constructor.  Its
statement must use the exact direct-store equalities, conversion typing, pivot
alignment or disalignment, and rebuilt allocation premises available at each
operational reveal/conceal caller.  Those caller premises have not yet been
normalized into one checked statement, so this audit does not hide them behind
an informal proposition.  The producer must not authorize transitive store
lookup, and its family must cover live left, right, and tagged wrapper
consumers.

This replacement removes `SameRuntime` because endpoint indices fix both
stores and term contexts.  It also replaces the resolved-representation
surface:

| Live surface | Live breadth | Replacement |
|---|---:|---|
| `SameRuntime` | 8 / 49 | definitional equality of endpoint `Ctx` indices |
| `RebaseAt` | 34 / 366 | checked `RebaseSourceᶜ₀` graph plus a produced plan |
| `RebaseAtᴸ` | 32 / 185 | optional boundary plan |
| `RebaseAtᴿ` | 18 / 81 | target wrapper view of the same produced alignment |
| `TagRebaseAtᴸ` | 25 / 105 | explicit paired or source-only boundary plan |
| `resolveVar` | 12 / 164 | direct `lookupStore` evidence only |
| `resolveRep` | 1 / 2 | delete |
| `StoreRepImp` | 18 / 63 | direct endpoint-entry imprecision |

The twelve live `resolveVar` consumers are `CastTermImprecision`,
`Catchup/InstInversionLambdaProof`, `CenterRename`, `Example12Worlds`,
`Inversion/TargetStripProof`, `Inversion/TargetWalkSupport`,
`SealPeelToolkit`, `StarRepChainProbe`, `TargetBindLift`, `TargetExtend`,
`TermImpDecay`, and `WorldSupport`.  These must be discharged from direct
boundary facts, not by moving the traversal behind a new name.

## Genuinely missing producers

No core `_⊑ᶜ_` constructor is missing.  The initial and empty-center recursors
and their pointwise endpoint laws now check.  The old homogeneous equations
against `id↪ᵗ` are deliberately not restored: the hidden center is only
propositionally equal to the endpoint type context, so those equations would
require transport.  The checked surface still lacks these operational
producers or integrations:

1. Operational producers for the checked `CenterRenamePlanᶜ₀` graph.  The
   interpreter covers every raw constructor, fixes endpoint `Ctx` indices,
   proves both embedding and mark laws, and derives direct invariants from the
   rebuilt history.  Callers must supply rebuilt `RightBindFreshᶜ₀` and
   type-imprecision exactly where their history constructor requires them.
2. Structural target extension/insertion and target-strip reconstruction.
   These replace `mix-targetʷ`, `mix-renamed-targetʷ`, and `lower-leftʷ` at the
   three actual non-rename producer sites listed above.  The checked target
   extension plan now handles fresh `★`, exact alias, skip, both lift heads,
   left bind, right bind, both paired heads, and term binding.  The checked
   type-imprecision transport uses embedding/mark laws and structural renaming,
   not invariants or resolution.  Target-strip reconstruction is checked by
   lowering the retained `SourceRebasePlanᶜ₀` through `lift-left`; arbitrary
   extensional world inversion is deliberately not used.
3. Delete honestification.  The checked elimination theorem reuses the same
   raw world and its direct invariants; no decay rewrite remains.
4. The operational producer for `SourceRebasePlanᶜ₀`, supplying rebuilt
   freshness and type-imprecision premises from direct caller facts.  The
   checked request now classifies no-pivot, unmatched-source, and paired-plan
   cases.  The live rebase boundary must replace resolved representation
   evidence with direct lookup-entry imprecision and retain the plan.
5. A live boundary-focus layer.  The probes now check exact alias allocation,
   stacked `TargetMode` validity, a generic stable/boundary world parameter,
   arbitrary repeated scoped term binding, exact endpoint lookup at depth, and
   a real variable leaf.  The exact edge is closed under binder prefixes and
   the lifted edge-indexed mode retains scoped entries and a variable leaf.
   A scoped CTI fragment checks exact target reveal/conceal, current-mode-open
   source conceal, term-independent paired reveal/conceal, constants, blame,
   ordinary casts, and structural function conversions.  Universal recursion
   now checks in a globally indexed liftable family, including type application
   with an explicit substituted-result relation.  Its structural prefix plan
   now transports runtime state, modes, central imprecision, recursively nested
   scoped types, heterogeneous term worlds, and deep entries at arbitrary
   binder depth.  Endpoint typing is checked directly for the current global
   relation fragment.  Connection to the live DGG remains a migration step,
   not a missing prefix operation.
6. A structural fresh-behind plan for the smart-comma source binder.  Alias
   merge uses item 5 instead; it must not mutate the stable world.  The checked
   plan handles a source lift followed by any target-star prefix and derives
   all geometry, imprecision, freshness, and invariants.  Raw alias heads are
   intentionally excluded because they require new noncollision provenance.
7. Endpoint-indexed world evolution for store-changing reduction.  Raw bind
   constructors express the resulting contexts.  The checked one-step relation
   covers keep and every permitted left/right allocation combination without
   defined functions in indices; the remaining simulation obligation is to
   produce those cases from paired trusted reduction steps.  The checked
   producer request records right-only freshness, paired type imprecision, and
   precise/dynamic allocation classification explicitly.  Its checked
   multi-step closure permits unequal source/target trace lengths by composing
   unilateral and paired steps directly, never by inventing `keep` steps.
   The checked final simulation package indexes its relation by the evolved
   endpoint contexts and derives both final typings plus store/context/term
   projections without `SameRuntime` or `SameCtx`; the full outcome adds the
   existing source-blame alternative.  Trusted one-step and multi-step
   preservation now support arbitrary term contexts, so the same endpoint
   result covers open simulation states.

These are theorem and operational-interface gaps.  Treating any of them as an
arbitrary invariant-accepting constructor would recreate the live escape
problem.

## Count evidence

The tables were generated from the repository root with `rg`, excluding the
definition file and notes.  This command prints the exact per-module counts
used above:

```sh
cd GTSFImp
for symbol in emptyʷ skip-centerʷ honestifyʷ lift-bothʷ lift-leftʷ \
  bind-leftʷ bind-rightʷ bind-bothʷ bind-both-starʷ lower-leftʷ \
  mix-targetʷ mix-renamed-targetʷ initialWorld emptyCenterWorld \
  liftWorldBoth liftWorldLeft leftOnlyWorld rightOnlyWorld bothBindWorld \
  ηᴸʷ ηᴿʷ impEnvʷ sourceStoreʷ targetStoreʷ \
  SmartFreshBehindGuard SmartAliasMergeGuard SmartCommaLiftᴸ \
  SameRuntime RebaseAt RebaseAtᴸ RebaseAtᴿ TagRebaseAtᴸ \
  resolveVar resolveRep StoreRepImp
do
  rg --pcre2 --count-matches \
    "${symbol}(?![-\\p{L}\\p{N}])" proof/DGG ./*.agda \
    --glob '*.agda' --glob '!proof/DGG/CtxImp.agda' \
    --glob '!proof/DGG/notes/**'
done
```

The important migration boundary is therefore not whether the new relation
can represent current worlds; it can represent every structural world.  The
boundary is whether the remaining operational callers can produce structural
plans from direct evidence without the live splice and representation-chain
escapes.
