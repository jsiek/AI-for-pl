D18 Stage 1/2 origin-schedule pre-flight
==========================================

Date: 2026-08-19

Status: NOTES-LEVEL PRE-FLIGHT ONLY.  D18 is signed off in the functional-
origin direction.  This record and
`probes/D18OriginSchedulePreflight.agda` do not change `CtxImp.World`, the
live `CtxImp.RebaseAt`, or the live term-imprecision relation.  Nothing live
was deleted.  In particular, `example12-rebase-X-to-Y` remains present until
the live migration after D16 (#177).


1. Stage 1 construction schedule
--------------------------------

The schedule is construction provenance, not a caller-supplied
`OriginPolicy`.  A scheduled world contains its raw live `World` and an
inductive `OriginSchedule` produced alongside that world.  `stationary` is
the default fixed point.  `edge builder rb rest` records the predecessor of a
moving paired pivot at the point where a real world builder creates that
edge.  Lookup is deterministic: the first construction entry for the queried
pivot pair wins, and an absent key falls through to the stationary world.
Consequently, evidence composed later by strip or chain code cannot become a
rule-facing edge merely by satisfying the old geometric fields.

The sandbox deliberately has no free schedule function and no alias for the
old broad relation.  Its only edge payload is the existing live geometric
record, used as construction evidence so the pre-flight tests the actual
`SameRuntime`, source/target embedding, alignment, and representation fields.
The live version must hide schedule extension behind the D16-valid world
builders; the public relation must only inspect the schedule.

The `originAt` definition is verbatim from the checked probe (including its
recursive lookup helper):

```agda
originAtSchedule : ∀ {Δᴸ Δᴿ Δ} {W′ : CTX.World Δᴸ Δᴿ Δ}
  → OriginSchedule W′
  → TyVar Δᴸ
  → TyVar Δᴿ
  → CTX.World Δᴸ Δᴿ Δ
originAtSchedule {W′ = W′} stationary Xᴸ Xᴿ = W′
originAtSchedule (edge {W = W} {Xᴸ = X₀ᴸ} {Xᴿ = X₀ᴿ}
    builder rb rest) Xᴸ Xᴿ
    with Fin._≟_ Xᴸ X₀ᴸ | Fin._≟_ Xᴿ X₀ᴿ
originAtSchedule (edge {W = W} builder rb rest) ._ ._
    | yes refl | yes refl = W
originAtSchedule (edge builder rb rest) Xᴸ Xᴿ
    | yes Xᴸ≡X₀ᴸ | no Xᴿ≢X₀ᴿ = originAtSchedule rest Xᴸ Xᴿ
originAtSchedule (edge builder rb rest) Xᴸ Xᴿ
    | no Xᴸ≢X₀ᴸ | yes Xᴿ≡X₀ᴿ = originAtSchedule rest Xᴸ Xᴿ
originAtSchedule (edge builder rb rest) Xᴸ Xᴿ
    | no Xᴸ≢X₀ᴸ | no Xᴿ≢X₀ᴿ = originAtSchedule rest Xᴸ Xᴿ

originAt : ∀ {Δᴸ Δᴿ Δ}
  → ScheduledWorld Δᴸ Δᴿ Δ
  → TyVar Δᴸ
  → TyVar Δᴿ
  → CTX.World Δᴸ Δᴿ Δ
originAt (scheduled W provenance) Xᴸ Xᴿ =
  originAtSchedule provenance Xᴸ Xᴿ
```

The fixed-point rule is checked by `originAt-stationary` and consumed by
`stationaryRebaseAt`:

```agda
originAt (stationaryWorld W) Xᴸ Xᴿ ≡ W
```

The head-edge equation is checked once for every construction tag by
`originAt-edge` and `edgeRebaseAt`:

```agda
originAt (scheduled W′ (edge builder rb rest)) Xᴸ Xᴿ ≡ W
```

### Complete `CtxImp.agda` world-builder inventory

The inventory is exhaustive for declarations in `CtxImp.agda` that return a
`World`.  `SmartCommaLiftᴸ` is evidence relating caller-supplied worlds, not
another `World`-valued builder.

| Live construction | Schedule tag | Checked edge rule |
|---|---|---|
| raw `world` constructor | `world-builder` | `world-edge` |
| `liftWorldBoth` | `liftWorldBoth-builder` | `liftWorldBoth-edge` |
| `liftWorldLeft` | `liftWorldLeft-builder` | `liftWorldLeft-edge` |
| `leftOnlyWorld` | `leftOnlyWorld-builder` | `leftOnlyWorld-edge` |
| `rightOnlyWorld` | `rightOnlyWorld-builder` | `rightOnlyWorld-edge` |
| `bothBindWorld` | `bothBindWorld-builder` | `bothBindWorld-edge` |

These are construction-edge rules, not the Stage 3 naturality theorems.
Center rename, decay, target insertion/pullback, bind lift, structural
extension, and smart-comma transport must later prove that their output
construction carries the corresponding tag and predecessor.  They may not
create an arbitrary schedule after the fact.

### Selected-origin properties

The sandbox relation retains the exact D18 field
`origin-determined : W ≡ originAt W′ Xᴸ Xᴿ`.  `edgeRebaseAt` constructs
all six builder cases from `originAt-edge` and the real live record.  The
following checked theorems then state the requested properties of the
selected origin, rather than only of an independently supplied `W`:

| Property | Checked theorem |
|---|---|
| source/target runtime stores agree | `selected-origin-sameRuntime` |
| every non-pivot source center is frozen | `selected-origin-off-pivot` |
| every target center is frozen | `selected-origin-target-frozen` |
| destination pivots are aligned | `selected-origin-pivot-aligned` |
| destination canonical representations are related | `selected-origin-representations` |


2. Stage 2 finite instantiations
--------------------------------

The probe imports the live Example12 worlds rather than replacing them with
abstract fixtures.  The scheduled finite path is

$$

  W_X \xrightarrow{(X,Z)} W_Z \xrightarrow{(X,Y)} W_Y.

$$

The corresponding checked tightened edges and origin equations are:

```agda
example12-rebase-X-to-Zᵀ
example12-X-to-Z-origin-determined

example12-rebase-Z-to-Yᵀ
example12-Z-to-Y-origin-determined
```

The independent representation-to-`ℕ` example is also instantiated:

```agda
example12-nat-rebase-X-to-Yᵀ
example12-nat-X-to-Y-origin-determined
```

The `W_Y, X, Y` key selects `W_Z`.  Therefore the unused live shortcut from
`W_X` to `W_Y` is not merely omitted: the probe proves
`example12-X-to-Y-not-origin-determined`.  No compatibility constructor or
old-relation alias restores it.

The two SmartComma raw target-wrapper mints are instantiated through the
construction-only `target-producer-preflight` adapter.  The checked equations
are `smart-comma-outer-origin-determined` and
`smart-comma-inner-origin-determined`.


3. Per-producer Stage 2 status
------------------------------

`PROVEN-IN-SANDBOX` means the producer's explicit predecessor is either the
stationary fixed point or a construction edge and hence obtains
`origin-determined` by `stationaryRebaseAt`, `edgeRebaseAt`, or
`target-producer-preflight`.  This status is about D18 origin selection; it
does not pre-approve a fixture under the not-yet-joined D16 `World` record.

`FLAG:chain` means the output is composed after construction or otherwise
lacks schedule coherence.  It must become a proof-local chain/link that no
`⊢²` constructor accepts, unless a later D16 proof makes the branch
unreachable.  `FLAG:D16-blocked` cites a concrete violation of D16 invariant
(5): a runtime source name marked `X⊑★`, with direct representation `★`,
has a center-aligned target occupant.

### Direct `rebase-at` producers

| Raw producer | Status | Sandbox evidence or verdict |
|---|---|---|
| `CtxImp.sameWorldRebaseAt:415` | PROVEN-IN-SANDBOX | `originAt-stationary`, `stationaryRebaseAt`. |
| `Example12Worlds:122` (`X→Z`) | PROVEN-IN-SANDBOX | `example12-X-to-Z-origin-determined`. |
| `Example12Worlds:129` (`X→Y`) | FLAG:chain | `example12-X-to-Y-not-origin-determined`; the scheduled origin of `(W_Y,X,Y)` is `W_Z`.  Delete this unused shortcut during the live migration. |
| `Example12Worlds:257` (nat `X→Y`) | PROVEN-IN-SANDBOX | `example12-nat-X-to-Y-origin-determined`. |
| `Examples2:234` (`Z→Y`) | PROVEN-IN-SANDBOX | `example12-Z-to-Y-origin-determined`. |
| `CenterCrossingProbe:190` | FLAG:D16-blocked | In the destination, dynamic direct-`★` source `X₁` is aligned with target occupant `Y₀`; D16 invariant (5). |
| `MovedLinkProbe:185` | FLAG:D16-blocked | Dynamic direct-`★` source `X` is aligned with a target occupant at each endpoint; D16 invariant (5). |
| `TagBoundaryProbe:171,181` | FLAG:D16-blocked | Dynamic direct-`★` source `X` is aligned with `Y`/`Y′`; D16 invariant (5). |
| `TerminusRebuildProbe:312` | FLAG:D16-blocked | `rb-chain`; both Instance-B endpoints violate D16 invariant (5).  `terminus-chain-not-origin-determined` independently checks the schedule conflict. |
| `SmartCommaWitness:176,192` | PROVEN-IN-SANDBOX | `smart-comma-{outer,inner}-origin-determined`; the source cells are `store-lift` names, not direct-`★` source cells. |
| `InstInversionLambdaProof:784,805,2572,2699` | PROVEN-IN-SANDBOX | Each `RebaseAtᴿ (just Y)` output feeds `target-producer-preflight`; route facts already determine both endpoint worlds.  Live target-insert naturality remains Stage 3. |
| `CenterRename:593` | PROVEN-IN-SANDBOX | The renamed output is a construction edge and receives `origin-determined` via `edgeRebaseAt`; live `originAt`/`renameWorld` commutation remains Stage 3. |
| `TermImpDecay:349`, coherent endpoints | PROVEN-IN-SANDBOX | The output construction records the coherently decayed predecessor and `edgeRebaseAt` applies. |
| `TermImpDecay:349`, independently chosen endpoints | FLAG:chain | The current API does not prove that the decayed origin is the scheduled origin.  Restrict it to coherent decay or return a proof-local link. |
| `TargetBindLift:813,836,968,992` | PROVEN-IN-SANDBOX | Explicit output endpoint pairs use the applicable builder edge.  Live forward/backward bind-lift naturality remains Stage 3. |
| `TargetExtend:2083,2140,2298,2458,3158` | PROVEN-IN-SANDBOX | Explicit inserted/pulled-back endpoint pairs use the applicable builder edge.  Live insertion/reflection naturality remains Stage 3. |
| `SourceStripWorkerProof:118` | FLAG:chain | Composed/shortcut producer; no construction edge. |
| `TargetDescentProof:99` | FLAG:chain | Composed/shortcut producer; no construction edge. |
| `TargetStripProof:125,213,357` | FLAG:chain | Composed/lifted shortcuts; retain a proof-local chain/link unless D16 proves a branch unreachable. |
| `TargetWalkSupport:148,684,745,778` | FLAG:chain | Lift/composition shortcuts; no construction-origin proof. |
| `SealTransferCore:64` | FLAG:chain | `composeSourceRebase` chooses an accumulator/earliest origin after construction. |

The input-pattern occurrences called out in the D18 design remain
eliminations, not mints.

### `sameWorldRebaseAt` producers

| Raw producer group | Status | Sandbox evidence or verdict |
|---|---|---|
| finite `Examples2` calls at `437,971,1431,1497,1503,1784,1790,1804,1810,2076,2404,2410,2416` | PROVEN-IN-SANDBOX | Mint a stationary construction key and use `stationaryRebaseAt`; D16 fixture validation still waits for Stage 0. |
| `ChainRideProbe:173,176`; `Parked/ParkedD4CheckpointProof:54`; `Phase3DeepDives:127,469` | PROVEN-IN-SANDBOX | Finite stationary keys; `stationaryRebaseAt`.  D16 fixture validation still waits for Stage 0. |
| `CenterCrossingProbe:199`; `MovedLinkProbe:198`; `TagBoundaryProbe:191,195` | FLAG:D16-blocked | Each aligned stationary world has a dynamic direct-`★` source and target occupant; D16 invariant (5). |
| `SourceStarProbe:110,113`; `StarRepChainProbe:166`; `SealPeelProbe:216` | FLAG:D16-blocked | The paired stationary edge aligns a dynamic direct-`★` source with a target occupant; D16 invariant (5).  Source-only unmatched constructors are unaffected. |
| `TerminusRebuildProbe:305,308` | FLAG:D16-blocked | Instance-B `W` and `Wᵖ`; D16 invariant (5). |
| `Inversion/SourceStripProof:98`; `Inversion/SourceStripWorkerProof:208,244` | FLAG:chain | Generic alignment does not establish a scheduled stationary key. |
| `Inversion/TargetChainProof:436,447,459,474,528,539,554,675,692,720` | FLAG:chain | Generic chain shortcut; requires the proof-local chain relation. |
| `Inversion/TargetStripProof:1527,1536`; `SealTransferCore:259,430` | FLAG:chain | Generic strip/composition shortcut; requires the proof-local chain relation. |

The remaining finite calls `MovedLinkProbe:198`, `TagBoundaryProbe:191,195`,
and the other named calibration rows are not assigned both statuses: the
concrete D16-blocked verdict takes precedence over their structurally valid
stationary equation.

### Identity, unmatched, and wrappers

| Producer | Status | Reason |
|---|---|---|
| `rebase-idᴸ`, `rebase-idᴿ`, `tag-rebase-idᴸ` | PROVEN-IN-SANDBOX | Indices force one stationary world; there is no paired key. |
| `rebase-onlyᴸ`, `tag-rebase-onlyᴸ` | PROVEN-IN-SANDBOX | Indices force one world and no aligned target occupant; `originAt` is not used. |
| `rebase-varᴸ`, `rebase-varᴿ`, `tag-rebase-varᴸ` and inversion/rewrap helpers | same as wrapped base producer | They add no origin choice. |


4. FLAG ledger
--------------

Every Stage 2 stop is recorded here; none was bypassed with an old-relation
alias.

1. `FLAG:chain` -- `Example12Worlds.example12-rebase-X-to-Y`.  The finite
   schedule selects `W_Z`, and the probe refutes the required equation for
   `W_X`.  It is unused and is to be deleted only in the live migration.
2. `FLAG:chain` -- incoherent `TermImpDecay.decayRebaseAt`.  Independently
   chosen endpoint decays do not determine the scheduled predecessor.
3. `FLAG:chain` -- the ten direct strip/descent/walk/seal-transfer producer
   schemata listed above.  No D16 invariant currently proves these generic
   branches unreachable; use a proof-local `RebaseChainAt`/link relation with
   no conversion to rule-facing `RebaseAt`.
4. `FLAG:chain` -- the generic same-world producers in source strip, target
   chain, target strip, and seal transfer.  Alignment plus representation is
   not a stationary schedule proof.
5. `FLAG:D16-blocked` -- `TerminusRebuildProbe.InstanceB.rb-chain`, its two
   stationary edges, and both endpoint worlds.  D16 invariant (5) kills them:
   dynamic direct-`★` source `X` has aligned target occupant `Y` or `Y₂`.
6. `FLAG:D16-blocked` -- the CenterCrossing, MovedLink, and TagBoundary
   calibration mints.  Their explicit direct-`★`, `X⊑★`, aligned-target
   placements violate D16 invariant (5); keep them only as negative fixtures.
7. `FLAG:D16-blocked` -- paired stationary direct-`★` fixtures in
   SourceStar, StarRepChain, and SealPeel.  D16 invariant (5) kills the paired
   edge; their unmatched/no-target cases are not implicated.


5. Exact Stage 0 wait list
--------------------------

The following items intentionally remain unimplemented until D16 (#177)
lands.  This is the complete Stage 0 dependency list for this pre-flight.

1. Put schedule provenance and the computed `originAt` behind the live
   D16-valid `World` construction surface.  The notes constructor must not
   become a public caller-supplied policy or schedule-extension escape hatch.
2. Re-express the six builder tags against the actual D16 constructors and
   prove each constructor preserves all joined world invariants: embedded
   `WFWorld`, aligned representation imprecision, unmatched-target `★`
   representation, and invariant (5) occupancy.
3. Re-run the D16 record constructors on T10 `W`/`Wᵖ`, Terminus Instance-B
   `W`/`Wᵖ`, CenterCrossing, MovedLink, TagBoundary, SourceStar,
   StarRepChain, and SealPeel.  Move or retain rejected worlds only as
   negative fixtures.
4. Decide D16 reachability for each generic strip/chain branch.  Until a
   branch is proved unreachable, introduce the proof-local chain/link
   relation; do not admit its shortcut as a scheduled functional edge.
5. Delete live `Example12Worlds.example12-rebase-X-to-Y` only after the D16
   join and before the D18 relation migration.  Nothing is deleted in this
   pre-flight.
6. Prove the Stage 3 naturality laws for center rename, coherent decay,
   target insertion/pullback, target bind lift/store move, structural
   extension, and smart-comma construction against the final D16 schedule.
7. Only after items 1--6, begin Stage 4+: add the functional-origin field to
   the live rebase declarations, thread it through the eight `⊢²` rules, land
   the T12 peels, and delete obsolete broad machinery.


6. Check record
---------------

The notes probe was spot-checked with:

```sh
cd GTSFImp
PATH=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda28/bin:$PATH \
  agda -i . -i proof/DGG/notes/probes -v0 \
  proof/DGG/notes/probes/D18OriginSchedulePreflight.agda
```

Result: exit 0, no holes or postulates.  The full gate result is recorded in
the commit handoff after the requested final `make check` run.
