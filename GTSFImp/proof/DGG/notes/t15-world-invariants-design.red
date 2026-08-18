# T15: D16 world invariants design

Status: recon and checked declarations only.  No live definition or proof was
changed.  The declarations and counterexample checks in this note are checked
by `proof/DGG/notes/probes/T15WorldInvariantsDesignProbe.agda`.

## Decision

The invariant belongs directly in `World`.  It does not require a two-layer
`RawWorld` definition because its conclusion can use the raw, environment-
indexed type-imprecision relation.  The proposed record is:

```agda
record World (Δᴸ Δᴿ Δ : TyCtx) : Set where
  constructor world
  field
    ηᴸʷ : Δᴸ ↪ᵗ Δ
    ηᴿʷ : Δᴿ ↪ᵗ Δ
    impEnvʷ : ImpEnv Δ
    sourceStoreʷ : TyStore Δᴸ
    targetStoreʷ : TyStore Δᴿ

    preciseMarksAlignedʷ :
      ∀ (Xᴸ : TyVar Δᴸ)
      → impEnvʷ (toRenameᵗ ηᴸʷ Xᴸ) ≡ X⊑X
      → Σ[ Xᴿ ∈ TyVar Δᴿ ]
          toRenameᵗ ηᴿʷ Xᴿ ≡ toRenameᵗ ηᴸʷ Xᴸ

    representationsImpreciseʷ :
      ∀ {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      → toRenameᵗ ηᴸʷ Xᴸ ≡ toRenameᵗ ηᴿʷ Xᴿ
      → impEnvʷ ⊢
          renameᵗ (toRenameᵗ ηᴸʷ)
            (resolveRep sourceStoreʷ (＇ Xᴸ))
          ⊑ renameᵗ (toRenameᵗ ηᴿʷ)
            (resolveRep targetStoreʷ (＇ Xᴿ))
```

`preciseMarksAlignedʷ` is exactly the current `WFWorld` judgment, now a
field.  `representationsImpreciseʷ` is deliberately unconditional on the
center mark.  A `RebaseAt` pivot may be center-aligned at `X⊑★`, and its
store representations still have to be related.  Conditioning the field on
`X⊑X` would leave precisely that runtime alignment unchecked.

The conclusion uses raw `_ ⊢_ ⊑_`, not `_ ⊑ᵂ⟨_⟩_`.  After the record
exists it is definitionally the intended world relation:

```agda
impEnvʷ W ⊢ embedᴸ W (resolveRep (sourceStoreʷ W) (＇ Xᴸ))
          ⊑ embedᴿ W (resolveRep (targetStoreʷ W) (＇ Xᴿ))
```

but spelling out the embeddings avoids a recursive dependency from `World` to
a relation defined by projections from `World`.  In the live migration,
`resolveVar` and `resolveRep` must be moved above `World`; they are currently
declared later in `CastTermImprecision2.agda`.  This is declaration staging,
not a change to type imprecision.

## Empty initial compilation world

An empty store at an intrinsic type context has only structural lifts and no
runtime binding:

```agda
emptyStore : (Δ : TyCtx) → TyStore Δ
emptyStore Nat.zero = store-empty
emptyStore (Nat.suc Δ) = store-lift (emptyStore Δ)

initialWorld : ∀ {Δ} → ImpEnv Δ → World Δ Δ Δ
initialWorld {Δ} μ =
  world id↪ᵗ id↪ᵗ μ (emptyStore Δ) (emptyStore Δ)
    (λ Xᴸ precise → Xᴸ , refl)
    initialRepresentations
```

The probe checks both invariant fields, including
`emptyStore (Nat.suc Δ) ≡ store-lift (emptyStore Δ)` by `refl`.

The recursive `compile-preserves-embedded²` proof already compiles from
`sourceStoreʷ W`; it tolerates this initial world.  The public
`compile-preserves-imprecision²-statement` does not tolerate the change
unchanged: it currently quantifies an arbitrary `Σ`, calls
`initialWorld μ Σ`, and elaborates both inputs from `Σ`.  Its statement and
wrapper must instead elaborate from `emptyStore Δ` and call `initialWorld μ`.
The closed DGG entry at context zero remains definitionally at `store-empty`.
`initialCtx`, the two identity embeddings, and `SourceId` are unaffected.

## Minting and preservation inventory

“In hand” means the current site has enough data or a nearby proved transport
lemma; it does not mean the seven-field constructor has been implemented.

| Builder or transformation | New obligations | Evidence at the site |
| --- | --- | --- |
| `CompilePreservesImprecision2.initialWorld` | Identity precise alignment; reflexive representations in two empty stores. | **In hand and checked.** Remove the arbitrary-store parameter from its public callers. |
| `Examples2.reflWorld` | Identity alignment and reflexivity for the same store on both sides. | **In hand.** |
| `Occupancy.initialWorldᴼ` | Same as canonical `initialWorld`. | **In hand, but obsolete.** Delete this duplicate rather than preserve an alias. |
| `liftWorldBoth v W` | Lift both old invariants; relate the two fresh structural variables. | **In hand.** The fresh pair is `＇ zero ⊑ ＇ zero`; old pairs lift. |
| `liftWorldLeft v W` | Lift old pairs; a precise fresh source mark must have a target occupant. | **Not in hand for generic `v`.** Current compile use is `X⊑★`. Restrict it to a non-precise mark or add a premise ruling out `X⊑X`. |
| `leftOnlyWorld v W A` | Transport old pairs through the source bind; handle the unpaired fresh source. | **Not in hand for generic `v`.** Live parked uses pass `X⊑★`; the signature should expose that requirement. |
| `rightOnlyWorld W B` | Transport old pairs through the target bind; no source maps to the new target-only center. | **In hand.** Existing right-bind store-representation transport has the required shape. |
| `bothBindWorld v W A B` | Transport old pairs and relate the canonical representations of the fresh aligned `A` and `B` cells. | **Not in hand in the builder.** Its arguments contain no `A₀⊑B₀`/resolved-representation witness. This is the principal allocation pressure point. |
| `parked-initial`, `parked-both-bind`, `parked-left-bind`, and `parked-right-bind` | Classify worlds minted by the initial and three bind builders. | **In hand after the builders are strengthened.** `parked-initial` drops `Σ`; `parked-both-bind` must accept and thread the fresh representation witness. |
| `parked-structural-right-insert` | Classify a caller-supplied `TargetInsert` output as parked. | **In hand.** The result is already a valid `World`; the insert and store-following premises add no new field obligation. |
| `evolve-refl`, `evolve-keepᴸ`, and `evolve-keepᴿ` | Reindex a trace without constructing a world. | **No new obligation.** The endpoint worlds already carry both fields. |
| `evolve-both-bind`, `evolve-left-bind`, and `evolve-right-bind` | Remove a leading allocation from an evolution whose starting world was produced by a bind builder. | **In hand after the builders are strengthened.** Only the both-bind surface needs the fresh representation witness. |
| `evolve-structural-right-bind` | Remove a structural target allocation backed by `TargetInsert`. | **In hand.** Its intermediate and final endpoints are already valid worlds. |
| `BothBindTransport²ᵀ` and paired allocation callers | Supply the fresh canonical-representation relation to `bothBindWorld`. | **Partly in hand at callers.** Paired allocation has an `A₀⊑B₀` premise, but the current transport surface passes only the trivial fresh-variable witness `＇ zero ⊑ ＇ zero`. A lemma must turn the allocation premise plus the old invariant into the resolved-representation witness. |
| `CenterRename.renameWorld` | Rename both invariant conclusions and preserve center equality. | **In hand.** Existing `rename-⊑`, `renameStoreRep`, and embedding injectivity provide the ingredients. |
| `WorldDecay.blendWorld` | Use the geometry/stores of the premise world and weaken representation proofs to the blended environment. | **In hand.** An output `X⊑X` mark comes from the premise world; raw imprecision is monotone under the environment decay. |
| `WorldDecay.honestify` | Preserve all aligned store representations while changing only marks; establish precise alignment. | **In hand.** Existing alignment and mark-decay lemmas provide the two fields. |
| `SealPeelToolkit.dynWorld` | Preserve geometry/stores under the all-`X⊑★` environment. | **In hand.** Precise alignment is vacuous and representation proofs weaken to the all-dynamic environment. |
| `TargetBindLift.targetStoreAs W Σᴿ` | Prove the invariant after replacing the target store arbitrarily. | **Not in hand for the raw helper.** Current callers pair it with `TargetStoreMove`/`TargetBindLiftMove`, and `moveStoreRepBindLift` supplies pointwise evidence. Make the raw helper private or require that movement evidence. |
| `TargetExtend.smartAliasInsertWorld` | Transport both invariants through alias insertion. | **In hand.** `TargetInsert` alignment/reflection and resolved-store transport cover old and inserted centers. |
| `TargetExtend.smartFreshInsertWorld` | Transport both invariants through fresh insertion. | **In hand.** The smart guard plus `TargetInsert` transport covers the new geometry. |
| `TargetExtend.insertRebaseWorld ins Wᵖ` | Mix `Wᵖ`'s source/environment/store with the inserted target of another world. | **Not in hand for arbitrary `Wᵖ`.** Require `RebaseAt`/frozen-target evidence tying `Wᵖ` to the insertion source, or replace the raw constructor with a checked builder. |
| `liftBothTargetInsert` and `liftLeftTargetInsert` | Lift a `TargetInsert` across the corresponding world builders. | **In hand after those builders are valid.** These records relate already constructed endpoints. |
| `smartAliasTargetInsert` and `smartFreshTargetInsert` | Package the two smart inserted worlds as `TargetInsert` results. | **In hand with their builders.** Their current geometry, resolve, and environment transport is exactly the preservation evidence. |
| `rightBindTargetInsert` and `keepRightBindTargetInsert` | Package `rightOnlyWorld`, optionally under `liftWorldBoth`. | **In hand with those builders.** |
| `insertRebaseTargetInsert`, its reverse and pullback variants, and their commuting result packages | Package `insertRebaseWorld` endpoints as `TargetInsert` results. | **Blocked exactly where `insertRebaseWorld` is blocked.** Once that builder requires rebase/frozen-target evidence, these functions already receive or derive it. |
| Other `TargetInsert` results | Relate an input and an already constructed output world. | **No extra minting obligation.** Once outputs are valid `World`s, existing alignment and resolve transport explain preservation. |
| `sameWorldRebaseAt`, rename/move/insert/right-bind `RebaseAt` transformers, and `RebaseAtᴸ`/`ᴿ`/tag wrappers | Relate already valid worlds and identify or transport a pivot. | **No global minting obligation.** `RebaseAt.storeRepresentations` becomes derivable from `representationsImpreciseʷ` and `pivotAligned`; keep it only during staged migration, then remove the redundancy. |
| `EnvDecay`, `decayRebaseAt`, `SameRuntime` | Transport relations between already valid worlds. | **In hand.** `decayRebaseAt` already transports the pivot representation proof. |
| `TermImpDecay` world patterns | Destructure a `World` while transporting derivations. | **Mechanical blast only.** Constructor patterns must bind or ignore two more fields; no new world is minted there. |

### Direct worlds and fixtures

Every direct `world` application must prove both fields.  The finite probes in
`SmartCommaWitness`, `MovedLinkProbe`, `TagBoundaryProbe`, `SealPeelProbe`,
`CenterCrossingProbe`, `ChainRideProbe`, `SourceStarProbe`,
`StarRepChainProbe`, and `TerminusRebuildProbe` already carry alignment and/or
pivot representation facts from which the fields can be proved by finite case
analysis.  `CastTermImprecision2`'s Example 12 dynamic and natural-number chain
worlds are likewise locally supported.

The remaining live direct constructors are the named builders in the table,
`Examples2.reflWorld`, the two initial-world definitions, and the concrete
fixture families just listed.  Scratch and archived probe modules below
`proof/DGG/notes/` also contain five-field snapshots; they are not additional
minting APIs and should be updated only if retained in the extra notes include,
otherwise deleted under the repository's completed-arc policy.

There are three deliberate failures of the merged `WFWorld` field:

* The Example 12 left-path worlds in `CastTermImprecision2` mark source centers
  precise that are not occupied by their one-variable target embedding.
* `Examples2`'s `left-path-world₃/₄/₅` with the `XZ` target omit the
  precise source center occupied only by the `YZ` variant.
* `ExtraCastRight2Counterexample.post-world` is explicitly proved not to be a
  `WFWorld` today.

Those worlds become unconstructible.  The first two fixture families must be
decayed at the unoccupied centers or redesigned; the counterexample post-world
should disappear.  `ExtraCastRight2Counterexample.pre-world` and its decayed
variant already have the required local facts.

### Pressure points

1. `bothBindWorld` needs a fresh resolved-representation witness.  It cannot be
   manufactured from its present parameters.
2. Generic `liftWorldLeft v` and `leftOnlyWorld v` cannot preserve precise-mark
   alignment when `v = X⊑X`; their interfaces must exclude that case or gain a
   target occupant.
3. `insertRebaseWorld` needs an explicit relation between its independently
   supplied premise world and the world being target-inserted.
4. `targetStoreAs` cannot accept an arbitrary replacement store; movement
   evidence must be part of the checked construction path.
5. The live Example 12 left-path and `Examples2` `XZ` worlds already violate
   the invariant being merged from `WFWorld`.
6. The public compile theorem and all parked/occupancy initial-world surfaces
   must drop their arbitrary initial store, even though the recursive compiler
   proof itself is compatible.

## Kill-check

The branch `agent/gtsf-beta-closings` was fetched and the D8a caller-supply and
occurrence-feasibility probes were reconstructed.  T10 Probe 1 was reconstructed
from `T10Probe1ParkedWorldPreservation.agda`.  The checked verdict is negative:

| Configuration | Aligned source/target | Resolved representations | Verdict |
| --- | --- | --- | --- |
| D8a `W` | source `X` / old target `Y` | `ℕ ⊑ ℕ` by `ι⊑ι` | Satisfies both new fields. |
| D8a `Wᵖ` | source `X` / fresh target `Y` at `X⊑★` | `ℕ ⊑ ℕ` by `ι⊑ι` | Satisfies both new fields. |
| T10 Probe 1 `W` | source `X` / old target `Y` | `★ ⊑ ★` by `★⊑★` | Satisfies both new fields. |
| T10 Probe 1 `Wᵖ` | source `X` / fresh target `Y` at `X⊑★` | `★ ⊑ ★` by `★⊑★` | Satisfies both new fields. |

Thus **none of the D8a or T10 substitution counterexamples dies under this
local World invariant**.  Each endpoint world is locally representation-
coherent.  The failure is cross-world: a value related to the old target
occupant at `W` cannot be retargeted to that old occupant after the source
pivot is reparked onto a fresh target occupant at `Wᵖ`.  Killing these
counterexamples requires a rebase/evolution stability invariant, provenance,
or a restriction on changing the source-to-target partner, not merely local
representation imprecision.

The probe exports the checked witnesses
`d8a-refuting-worlds-satisfy` and `t10-probe1-worlds-satisfy`.

## Migration and blast radius

Direct record construction occurs in `CastTermImprecision2`,
`CompilePreservesImprecision2`, `Occupancy`, `Examples2`, `CenterRename`,
`WorldDecay`, `SealPeelToolkit`, `TargetBindLift`, `TargetExtend`, and the
finite proof/probe worlds listed above.  Direct constructor pattern matching is
concentrated in `WorldDecay` and especially `TermImpDecay`.  Projection-only
consumers largely survive the field addition, while every constructor call and
constructor pattern changes arity.

The current live users of external `WFWorld` are
`CastTermImprecision2`, `ExtraCastRight2Counterexample`,
`SmartCommaWitness`, `MovedLinkProbe`, `TagBoundaryProbe`,
`SealPeelToolkit`, `WorldDecay`, and `SealPeelProbe`.  Their evidence becomes a
projection or disappears.  Initial-world users in
`CompilePreservesImprecision2`, `DynamicGradualGuaranteeProof`,
`GroundingMint`, `Occupancy`, `ParkedWorldDef`, and `Phase3DeepDives` must move
to the empty-store signature.

A low-risk LG-1-style sequence is:

1. Hoist `resolveVar`/`resolveRep`.  Against the existing five-field record,
   introduce a temporary, non-public `WorldInvariants W` companion containing
   exactly the two drafted fields.  Prove preservation for the core builders
   and require the companion at theorem boundaries, so failures are visible.
2. Resolve the pressure points: strengthen both-bind allocation, restrict
   left-only minting, guard store replacement and insertion/rebase, and repair
   or retire invalid fixture worlds.
3. After D15 lands, merge the companion fields into `World` atomically, change
   constructor calls and patterns to the seven-field shape, replace `WFWorld`
   arguments by the projection, and delete both `WFWorld` and the temporary
   companion.  Do not retain a compatibility alias in this closed-world repo.
4. Remove `RebaseAt.storeRepresentations` once all callers use the world field,
   and consolidate `initialWorldᴼ` into the canonical empty-store constructor.

PR #171 (`agent/gtsf-partner-redesign`, fetched head `faec619c`) changes 43
`GTSFImp` files and touches `CastTermImprecision2`, `TargetExtend`,
`CenterRename`, `TargetBindLift`, `TermImpDecay`, and many downstream inversion
and catchup modules.  Its direct change to `CastTermImprecision2` is the D15
partner/conceal surface rather than this record, but its semantic and arity
blast overlaps almost every migration site.  Land D15 first, then rebase D16
and perform step 3.  The temporary companion work can be prepared before that
merge, but it must not become a second permanent world API.

## Validation

The standalone probe is safe, has no postulates, holes, or option pragmas, and
is checked with Agda 2.8 using:

```text
agda --safe -v0 -i . -i proof/DGG/notes/probes \
  proof/DGG/notes/probes/T15WorldInvariantsDesignProbe.agda
```

This command exited 0.  The required repository gate was then run exactly as:

```text
cd GTSFImp && \
  PATH=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda28/bin:$PATH \
  make check
```

It exited 0 after checking `All.agda`, `LegacyAll.agda`, and reporting
`postulate-check: OK (no postulates; NON_COVERING at legacy baseline)`.
