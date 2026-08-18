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

    unmatchedTargetsDynamicʷ :
      ∀ (Xᴿ : TyVar Δᴿ)
      → (∀ (Xᴸ : TyVar Δᴸ)
          → toRenameᵗ ηᴸʷ Xᴸ ≢ toRenameᵗ ηᴿʷ Xᴿ)
      → resolveRep targetStoreʷ (＇ Xᴿ) ≡ ★
```

`preciseMarksAlignedʷ` is exactly the current `WFWorld` judgment, now a
field.  `representationsImpreciseʷ` is deliberately unconditional on the
center mark.  A `RebaseAt` pivot may be center-aligned at `X⊑★`, and its
store representations still have to be related.  Conditioning the field on
`X⊑X` would leave precisely that runtime alignment unchecked.

`unmatchedTargetsDynamicʷ` says exactly that a target pivot with no
center-aligned source pivot resolves to `★`.  Equality is the right conclusion,
not a second representation-path predicate: `resolveRep` is already the
canonical transitive path resolver.  This leaves matched pivots unrestricted;
in particular, the checked paths ending at `ℕ` remain legal while their target
pivot has a source partner.

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
    (λ Xᴿ unmatched → ⊥-elim (unmatched Xᴿ refl))
```

The probe checks all three invariant fields, including
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
lemma; it does not mean the eight-field constructor has been implemented.

| Builder or transformation | New obligations | Evidence at the site |
| --- | --- | --- |
| `CompilePreservesImprecision2.initialWorld` | Identity precise alignment; reflexive representations in two empty stores; no unmatched target. | **In hand and checked.** Remove the arbitrary-store parameter from its public callers. |
| `Examples2.reflWorld` | Identity alignment and reflexivity for the same store on both sides; no unmatched target. | **In hand.** |
| `Occupancy.initialWorldᴼ` | Same as canonical `initialWorld`. | **In hand, but obsolete.** Delete this duplicate rather than preserve an alias. |
| `liftWorldBoth v W` | Lift all old invariants; relate the fresh structural pair. | **In hand.** The fresh target is matched, and old unmatched targets remain unmatched with lifted `★` representations. |
| `liftWorldLeft v W` | Lift old pairs; a precise fresh source mark must have a target occupant. | **Not in hand for generic `v`.** Current compile use is `X⊑★`. Restrict it to a non-precise mark or add a premise ruling out `X⊑X`. |
| `leftOnlyWorld v W A` | Transport old pairs through the source bind; handle the unpaired fresh source. | **Not in hand for generic `v`.** Live parked uses pass `X⊑★`; the signature should expose that requirement. |
| `rightOnlyWorld W B` | Transport old pairs; prove the fresh unmatched target resolves to `★`. | **Not in hand for generic `B`.** Require `resolveRep (targetStoreʷ W) B ≡ ★`. It is definitional for `B = ★` and for `B = ＇ zero` immediately after binding `★`. |
| `bothBindWorld v W A B` | Transport old pairs and relate the canonical representations of the fresh aligned `A` and `B` cells. | **Not in hand in the builder for representation imprecision.** Its fresh target is matched, so invariant (4) adds no obligation. |
| `parked-initial`, `parked-both-bind`, `parked-left-bind`, and `parked-right-bind` | Classify worlds minted by the initial and three bind builders. | **In hand after the builders are strengthened.** `parked-right-bind` inherits the new resolved-`★` premise. |
| `parked-structural-right-insert` | Classify a caller-supplied `TargetInsert` output as parked. | **In hand.** The result is already a valid `World`; the insert and store-following premises add no new field obligation. |
| `evolve-refl`, `evolve-keepᴸ`, and `evolve-keepᴿ` | Reindex a trace without constructing a world. | **No new obligation.** The endpoint worlds already carry all three fields. |
| `evolve-both-bind`, `evolve-left-bind`, and `evolve-right-bind` | Remove a leading allocation from an evolution whose starting world was produced by a bind builder. | `evolve-right-bind` must expose the same resolved-`★` premise as `rightOnlyWorld`; the other two add no invariant-(4) work. |
| `evolve-structural-right-bind` | Remove a structural target allocation backed by `TargetInsert`. | **In hand at this consumer.** `W₁` is already a valid `World`; its projection proves the fresh target is `★`. The minting burden remains at the `TargetInsert` output builder. |
| `BothBindTransport²ᵀ` and paired allocation callers | Supply the fresh canonical-representation relation to `bothBindWorld`. | **Partly in hand at callers.** Paired allocation has an `A₀⊑B₀` premise, but the current transport surface passes only the trivial fresh-variable witness `＇ zero ⊑ ＇ zero`. A lemma must turn the allocation premise plus the old invariant into the resolved-representation witness. |
| `CenterRename.renameWorld` | Rename all invariant conclusions and preserve center equality. | **In hand.** Existing `rename-⊑`, `renameStoreRep`, and embedding injectivity provide the ingredients. |
| `WorldDecay.blendWorld` | Use the geometry/stores of the premise world and weaken representation proofs to the blended environment. | **In hand.** An output `X⊑X` mark comes from the premise world; raw imprecision is monotone under the environment decay. Invariant (4) is unchanged because geometry and stores are unchanged. |
| `WorldDecay.honestify` | Preserve all aligned store representations while changing only marks; establish precise alignment. | **In hand.** Existing alignment and mark-decay lemmas provide the first two fields; invariant (4) is unchanged because geometry and stores are unchanged. |
| `SealPeelToolkit.dynWorld` | Preserve geometry/stores under the all-`X⊑★` environment. | **In hand.** Precise alignment is vacuous and representation proofs weaken to the all-dynamic environment; invariant (4) is inherited unchanged. |
| `TargetBindLift.targetStoreAs W Σᴿ` | Prove the invariants after replacing the target store arbitrarily. | **Not in hand for the raw helper.** Besides pairwise representation evidence, movement must preserve `resolveRep ... (＇ Xᴿ) ≡ ★` for every unmatched target. Make the raw helper private or require the movement evidence. |
| `TargetExtend.smartAliasInsertWorld` | Transport all invariants through alias insertion. | **In hand after the input insert is valid.** Old-source freezing reflects any unmatched output target back to the smart premise world. |
| `TargetExtend.smartFreshInsertWorld` | Transport all invariants through fresh insertion. | **In hand after the input insert is valid.** Old-source freezing and target reflection provide the invariant-(4) transport. |
| `TargetExtend.insertRebaseWorld ins Wᵖ` | Mix `Wᵖ`'s source/environment/store with the inserted target of another world. | **Not in hand for arbitrary `Wᵖ`, and invariant (4) exposes the exact failure.** A repark can make a non-`★` old target newly unmatched. Require a checked rebase premise that rules this out. |
| `liftBothTargetInsert` and `liftLeftTargetInsert` | Lift a `TargetInsert` across the corresponding world builders. | **In hand after those builders are valid.** These records relate already constructed endpoints. |
| `smartAliasTargetInsert` and `smartFreshTargetInsert` | Package the two smart inserted worlds as `TargetInsert` results. | **In hand with their builders.** Their current geometry, resolve, and environment transport is exactly the preservation evidence. |
| `rightBindTargetInsert` and `keepRightBindTargetInsert` | Package `rightOnlyWorld`, optionally under `liftWorldBoth`. | **Not in hand at the root for generic `B`.** Strengthen `rightBindTargetInsert` with the same resolved-`★` premise as `rightOnlyWorld`; `keepRightBindTargetInsert` then transports it. |
| `insertRebaseTargetInsert`, its reverse and pullback variants, and their commuting result packages | Package `insertRebaseWorld` endpoints as `TargetInsert` results. | **Blocked exactly where `insertRebaseWorld` is blocked.** Once that builder requires rebase/frozen-target evidence, these functions already receive or derive it. |
| Other `TargetInsert` results | Relate an input and an already constructed output world. | **No extra minting obligation.** Once outputs are valid `World`s, existing alignment and resolve transport explain preservation. |
| `sameWorldRebaseAt`, rename/move/insert/right-bind `RebaseAt` transformers, and `RebaseAtᴸ`/`ᴿ`/tag wrappers | Relate already valid worlds and identify or transport a pivot. | **No global minting obligation.** `RebaseAt.storeRepresentations` becomes derivable from `representationsImpreciseʷ` and `pivotAligned`; keep it only during staged migration, then remove the redundancy. |
| `EnvDecay`, `decayRebaseAt`, `SameRuntime` | Transport relations between already valid worlds. | **In hand.** `decayRebaseAt` already transports the pivot representation proof. |
| `TermImpDecay` world patterns | Destructure a `World` while transporting derivations. | **Mechanical blast only.** Constructor patterns must bind or ignore three more fields; no new world is minted there. |

### Invariant-(4) right-only minting inventory

For `rightOnlyWorld W B`, the fresh target variable is `Fin.zero`.  No source
variable maps to its fresh center, and its representation computes to

```agda
resolveRep (store-bind (targetStoreʷ W) B) (＇ Fin.zero)
  ≡ ⇑ᵗ (resolveRep (targetStoreʷ W) B).
```

Consequently the strengthened builder must receive
`resolveRep (targetStoreʷ W) B ≡ ★` (or the immediately lifted equality).
The current generic signature cannot prove it.

| Catch-up minting path | What it binds | Is resolved `★` in hand? |
| --- | --- | --- |
| `structural-target-inst-step`; `inst-cast-alloc-prefix`; `GroundingPreserve.β-inst-*` | `★` | **Yes, definitionally.** |
| Concrete `Λ⊑Λ²` two-bind route, including smart-alias, smart-fresh, and rebase transport | First `★`, then `＇ Fin.zero` pointing to that first cell | **Yes.** Both resolutions are definitional in the concrete route, and `ΛRouteOneWindowFacts.firstTargetZeroResolves` / `targetZeroResolves` already carry them for caller-supplied and transported plans. |
| `AllValueViewStepCatalogᵀ` when coupled to the right-only world extension | `β-Λ`, `β-reveal-∀`, and `β-conceal-∀` bind arbitrary `A`; `β-gen` binds arbitrary `C`; `β-∀` is `keep` | **Not in hand for the allocating cases.** The reduction catalog alone gives no resolved-`★` proof; the catch-up world extension must obtain one from a narrowed structural case or an added premise. |
| `StructuralTargetGenStepProof`, `StructuralTargetLambdaStepProof`, `StructuralTargetConversionStepProof`, `StructuralGenDescentProof`, and `spine-typed-Λ-child` | `＇ X` for an arbitrary old target pivot `X` | **VIOLATING SURFACE.** No premise says `resolveRep (targetStoreʷ W) (＇ X) ≡ ★`.  A matched `X` may legally resolve to `ℕ`, so invariant (4) rejects the newly minted alias. |
| `GroundingPreserve.β-gen-*` | Arbitrary argument `C` | **VIOLATING SURFACE.** Occupancy/atomicity does not imply that `C` resolves to `★`. |
| `RightBindWorldExtendᴿᵀ`, `RightBindKeepWorldExtendᴿᵀ`, `RightBindRightBindWorldExtendᴿᵀ`, `right-bind-under-left-lift`, and the smart alias/fresh bind helpers | Generic `B`/`C` | **VIOLATING AS GENERIC APIs.** Their safe concrete calls are the `★` then `＇ zero` route above; the signatures must nevertheless thread a resolved-`★` witness. |
| `TransportTermImprecisionProof.mapCtxᴾ-right-bind`, its `evolve-right-bind` case, and other `B₀` callers | Generic `B₀` already named in `rightOnlyWorld W B₀` | **Not locally derivable.** Thread the strengthened builder's witness through these surfaces. |
| `StructuralWorldExtendᴿ.structural-bind`, `StructuralNamePostPlan.target-bind-child`, `structural-target-bind-step`, peel/descent packages, `parked-structural-right-insert`, and `evolve-structural-right-bind` | A caller-supplied `TargetInsert` plus `targetStoreʷ W₁ ≡ store-bind ... B` | **In hand at the consumer, not at the mint.** `W₁ : World` supplies invariant (4) after migration.  Every constructor of that `W₁` must prove it; `TargetInsert` plus the store equation alone does not manufacture the fact. |
| `rightBindTargetInsert`, `rightBindTargetWindowInsert`, `keepRightBindTargetInsert`, and right-bind rebase/insert wrappers | Whatever the underlying `rightOnlyWorld` binds | **Same flag as the underlying bind.** Strengthen the root `rightBindTargetInsert` with the resolved-`★` witness; wrappers only transport it. |

The structural `TargetInsert` consumers therefore need no redundant new
premise once `World` contains the field.  The direct `rightOnlyWorld` and
`rightBindTargetInsert` constructors do need the premise, and the variable-
alias call sites above must either derive it from a genuine representation
fact or stop using a right-only world for that allocation.

### Direct worlds and fixtures

Every direct `world` application must prove all three fields.  Fixtures whose
target stores resolve only to `★` can prove invariant (4) by finite case
analysis.  Non-`★` fixtures need an occupancy audit: every target pivot with
that representation must be center-aligned with a source pivot in that exact
world.

This audit newly rejects several `CastTermImprecision2` Example 12 fixtures.
`example12-world-X` keeps its `ℕ` target matched and can satisfy invariant (4),
but `example12-world-Y` and `example12-world-Z` leave that target unmatched.
Both `example12-nat-chain-world-X` and `example12-nat-chain-world-Y` have two
target pivots resolving to `ℕ` and only one source pivot, so each leaves one
non-`★` target unmatched.  These are the same reparking shape exposed by the
D8a probe and must be retired or redesigned.  The all-`★` finite probes remain
locally supported.

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
2. `rightOnlyWorld` and `rightBindTargetInsert` need the bound type to resolve
   to `★`.  Generic `B`/`B₀` catch-up surfaces and the `＇ X` structural
   allocation sites do not currently carry that evidence.
3. Generic `liftWorldLeft v` and `leftOnlyWorld v` cannot preserve precise-mark
   alignment when `v = X⊑X`; their interfaces must exclude that case or gain a
   target occupant.
4. `insertRebaseWorld` needs an explicit relation between its independently
   supplied premise world and the world being target-inserted; invariant (4)
   must remain true when a source pivot changes partners.
5. `targetStoreAs` cannot accept an arbitrary replacement store; movement
   evidence must preserve both pairwise representations and unmatched `★`
   resolutions.
6. The live Example 12 left-path and `Examples2` `XZ` worlds violate the
   invariant being merged from `WFWorld`; the Example 12 `Y`/`Z` and
   natural-number chain worlds additionally violate invariant (4).
7. The public compile theorem and all parked/occupancy initial-world surfaces
   must drop their arbitrary initial store, even though the recursive compiler
   proof itself is compatible.

## Kill-check

The D8a and T10 Probe 1 geometries were rechecked with invariant (4) as an
actual field of the probe's eight-field `World`.

| Configuration | Matched target | Unmatched target | Resolved unmatched representation | Verdict under (4) |
| --- | --- | --- | --- | --- |
| D8a `W` | old target `Fin.suc Fin.zero` | fresh target `Fin.zero` | `ℕ` | **Rejected.** |
| D8a `Wᵖ` | fresh target `Fin.zero` | old target `Fin.suc Fin.zero` | `ℕ` | **Rejected.** The old occupant loses its source partner and is non-`★`. |
| T10 Probe 1 `W` | old target `Fin.suc Fin.zero` | fresh target `Fin.zero` | `★` | **Accepted.** |
| T10 Probe 1 `Wᵖ` | fresh target `Fin.zero` | old target `Fin.suc Fin.zero` | `★` | **Accepted.** The old occupant loses its partner but already resolves to `★`. |

**INVARIANT (4) KILLS THE D8a COUNTEREXAMPLE.**  In particular, the reparked
`Wᵖ` cannot be constructed because its old target occupant is unmatched and
resolves to `ℕ`.  This resolves the D8a.4 groundedness question: a non-`★`
old occupant cannot survive as an ungrounded leftover after the source pivot
reparks.  The probe proves the stronger fact that D8a's other endpoint `W` is
also invalid, because the then-fresh non-`★` occupant is unmatched there.

**Invariant (4) does not kill T10 Probe 1.**  Both unmatched occupants resolve
to `★`, so both endpoint worlds satisfy all three added fields and the
cross-world T10 failure remains.

The checked negative witnesses are `d8a-W-violates-invariant4` and
`d8a-Wᵖ-violates-invariant4`; `t10-W` and `t10-Wᵖ` are checked full `World`
values, with `t10-probe1-worlds-satisfy` retaining the representation proof.

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
   exactly the three drafted fields.  Prove preservation for the core builders
   and require the companion at theorem boundaries, so failures are visible.
2. Strengthen `rightOnlyWorld` and `rightBindTargetInsert` with a resolved-`★`
   premise.  Thread it through `evolve-right-bind`, the generic `B₀` transport
   surfaces, parked constructors, and smart wrappers.  Keep the `★` then
   `＇ zero` route; add real evidence or redesign the arbitrary `＇ X`, `C`,
   and generic-`B` sites.
3. Resolve the remaining pressure points: strengthen both-bind allocation,
   restrict left-only minting, guard store replacement and insertion/rebase,
   and repair or retire invalid fixture worlds.  Use invariant (4), rather
   than a cross-world compatibility alias, to reject non-`★` repark outputs.
4. After D15 lands, merge the companion fields into `World` atomically, change
   constructor calls and patterns to the eight-field shape, replace `WFWorld`
   arguments by the projection, and delete both `WFWorld` and the temporary
   companion.  Do not retain a compatibility alias in this closed-world repo.
5. Remove `RebaseAt.storeRepresentations` once all callers use the world field,
   and consolidate `initialWorldᴼ` into the canonical empty-store constructor.

PR #171 (`agent/gtsf-partner-redesign`, fetched head `faec619c`) changes 43
`GTSFImp` files and touches `CastTermImprecision2`, `TargetExtend`,
`CenterRename`, `TargetBindLift`, `TermImpDecay`, and many downstream inversion
and catchup modules.  Its direct change to `CastTermImprecision2` is the D15
partner/conceal surface rather than this record, but its semantic and arity
blast overlaps almost every migration site.  Land D15 first, then rebase D16
and perform step 4.  The temporary companion work can be prepared before that
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
