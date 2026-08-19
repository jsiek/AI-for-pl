# T15: D16 world invariants design

Status: recon and checked declarations only.  No live definition or proof was
changed.  The declarations and counterexample checks in this note are checked
by `proof/DGG/notes/probes/T15WorldInvariantsDesignProbe.agda`.

## Decision

The invariant belongs directly in `World`.  It does not require a two-layer
`RawWorld` definition because its conclusion can use the raw, environment-
indexed type-imprecision relation.

`TyStore` currently exposes the relational lookup `_∋_⦂_`, but that
relation intentionally has no entry for `Fin.zero` under `store-lift`.  D16
needs a total one-step view, including structural binders, so the probe drafts
the following canonical `lookupStore` primitive:

```agda
lookupStore : ∀ {Δ} → TyStore Δ → TyVar Δ → Ty Δ
lookupStore (store-lift Σ) Fin.zero = ＇ Fin.zero
lookupStore (store-lift Σ) (Fin.suc X) = ⇑ᵗ (lookupStore Σ X)
lookupStore (store-bind Σ A) Fin.zero = ⇑ᵗ A
lookupStore (store-bind Σ A) (Fin.suc X) = ⇑ᵗ (lookupStore Σ X)
```

This returns exactly one direct store entry, lifted into the store's current
scope; it never follows a variable entry.  The recommended record uses the
chain-permissive form of invariant (4):

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
            (lookupStore sourceStoreʷ Xᴸ)
          ⊑ renameᵗ (toRenameᵗ ηᴿʷ)
            (lookupStore targetStoreʷ Xᴿ)

    unmatchedTargetsDynamicʷ :
      ∀ (Xᴿ : TyVar Δᴿ)
      → (∀ (Xᴸ : TyVar Δᴸ)
          → toRenameᵗ ηᴸʷ Xᴸ ≢ toRenameᵗ ηᴿʷ Xᴿ)
      → lookupStore targetStoreʷ Xᴿ ≡ ★
        ⊎ Σ[ Yᴿ ∈ TyVar Δᴿ ]
            (lookupStore targetStoreʷ Xᴿ ≡ ＇ Yᴿ)
          × (∀ (Xᴸ : TyVar Δᴸ)
              → toRenameᵗ ηᴸʷ Xᴸ ≢ toRenameᵗ ηᴿʷ Yᴿ)
```

`preciseMarksAlignedʷ` is exactly the current `WFWorld` judgment, now a
field.  `representationsImpreciseʷ` is deliberately unconditional on the
center mark.  A `RebaseAt` pivot may be center-aligned at `X⊑★`, and its
store representations still have to be related.  Conditioning the field on
`X⊑X` would leave precisely that runtime alignment unchecked.

The direct field makes chain coherence derivable rather than primitive.  If
aligned `Xᴸ` and `Xᴿ` have variable entries `＇ Yᴸ` and `＇ Yᴿ`, their direct
entries are related.  The only imprecision derivation between two variables
identifies their embedded heads, so `Yᴸ` and `Yᴿ` are center-aligned and the
field applies again.  Induction on decreasing store age repeats this argument
down the chain.  The probe checks the induction step with this statement:

```agda
variableEntryChainCoherence : ∀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ)
    {Xᴸ Yᴸ : TyVar Δᴸ} {Xᴿ Yᴿ : TyVar Δᴿ}
  → CenterAligned W Xᴸ Xᴿ
  → lookupStore (sourceStoreʷ W) Xᴸ ≡ ＇ Yᴸ
  → lookupStore (targetStoreʷ W) Xᴿ ≡ ＇ Yᴿ
  → CenterAligned W Yᴸ Yᴿ
    × (impEnvʷ W ⊢
        renameᵗ (toRenameᵗ (ηᴸʷ W))
          (lookupStore (sourceStoreʷ W) Yᴸ)
        ⊑ renameᵗ (toRenameᵗ (ηᴿʷ W))
          (lookupStore (targetStoreʷ W) Yᴿ))
```

### Design sub-question: strict or chain-permissive (4)?

The two direct-entry candidates are:

1. **STRICT**

   ```agda
   unmatchedTargetsDynamicʷ :
     ∀ (Xᴿ : TyVar Δᴿ)
     → (∀ (Xᴸ : TyVar Δᴸ)
         → toRenameᵗ ηᴸʷ Xᴸ ≢ toRenameᵗ ηᴿʷ Xᴿ)
     → lookupStore targetStoreʷ Xᴿ ≡ ★
   ```

2. **CHAIN-PERMISSIVE** (shown in the proposed record): the entry is literally
   `★`, or it is `＇ Yᴿ` and `Yᴿ` is itself unmatched.  Since a bound variable
   can mention only an older variable, repeated use terminates at literal `★`.

**Recommendation: choose CHAIN-PERMISSIVE.**  The live `Λ⊑Λ²` catch-up route
first right-binds `★` and then right-binds `＇ Fin.zero`.  Both fresh cells are
unmatched at bind time: `rightOnlyWorld` skips every source center and keeps the
fresh target center.  The second cell points to the first, still-unmatched `★`
cell.  The strict form rejects this established safe route, while the permissive
form accepts it and still derives `★` termination.  The probe constructs
`alias-chain-world` under the permissive field and proves
`alias-chain-rejects-strict`.

The other structural `＇ X` bind sites are also fresh unmatched cells, not
matched cells.  However, their arbitrary old head `X` may already be matched;
none of their signatures says it is unmatched.  Therefore even the permissive
form correctly leaves those generic sites unproved.

The conclusion uses raw `_ ⊢_ ⊑_`, not `_ ⊑ᵂ⟨_⟩_`.  After the record
exists it is definitionally the intended world relation:

```agda
impEnvʷ W ⊢ embedᴸ W (lookupStore (sourceStoreʷ W) Xᴸ)
          ⊑ embedᴿ W (lookupStore (targetStoreʷ W) Xᴿ)
```

but spelling out the embeddings avoids a recursive dependency from `World` to
a relation defined by projections from `World`.  In the live migration,
`lookupStore` belongs in `TyStore`; no representation-chain resolver must be
moved above `World`, and the live resolver remains available to consumers that
actually need a transitive representative.

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
| `liftWorldBoth v W` | Lift all old invariants; relate the fresh structural pair. | **In hand.** The fresh target is matched.  Each old direct entry is merely shifted; a variable head and its unmatched proof shift pointwise. |
| `liftWorldLeft v W` | Lift old pairs; a precise fresh source mark must have a target occupant. | **Not in hand for generic `v`.** Current compile use is `X⊑★`. Restrict it to a non-precise mark or add a premise ruling out `X⊑X`. |
| `leftOnlyWorld v W A` | Transport old pairs through the source bind; handle the unpaired fresh source. | **Not in hand for generic `v`.** Live parked uses pass `X⊑★`; the signature should expose that requirement. |
| `rightOnlyWorld W B` | Transport old pairs; classify the fresh unmatched direct entry `⇑ᵗ B`. | **Not in hand for generic `B`.** Under the recommended form, accept `B = ★`, or `B = ＇ X` when `X` is proved unmatched in `W`. Strict accepts only the first case. |
| `bothBindWorld v W A B` | Transport old pairs and relate the direct entries of the fresh aligned `A` and `B` cells. | **Simplified and in hand when the allocation premise relates `A` and `B`.** Rename that premise through the fresh center; no chain-resolution bridge is needed.  Its fresh target is matched, so invariant (4) adds no obligation. |
| `parked-initial`, `parked-both-bind`, `parked-left-bind`, and `parked-right-bind` | Classify worlds minted by the initial and three bind builders. | **In hand after the builders are strengthened.** `parked-right-bind` inherits the new direct-entry classification premise. |
| `parked-structural-right-insert` | Classify a caller-supplied `TargetInsert` output as parked. | **In hand.** The result is already a valid `World`; the insert and store-following premises add no new field obligation. |
| `evolve-refl`, `evolve-keepᴸ`, and `evolve-keepᴿ` | Reindex a trace without constructing a world. | **No new obligation.** The endpoint worlds already carry all three fields. |
| `evolve-both-bind`, `evolve-left-bind`, and `evolve-right-bind` | Remove a leading allocation from an evolution whose starting world was produced by a bind builder. | `evolve-right-bind` must expose the same direct-entry classification premise as `rightOnlyWorld`; the other two add no invariant-(4) work. |
| `evolve-structural-right-bind` | Remove a structural target allocation backed by `TargetInsert`. | **In hand at this consumer.** `W₁` is already a valid `World`; its projection classifies the fresh direct entry. The minting burden remains at the `TargetInsert` output builder. |
| `BothBindTransport²ᵀ` and paired allocation callers | Supply the fresh direct-entry relation to `bothBindWorld`. | **Simplified.** The existing allocation premise `A₀⊑B₀` transports pointwise to the fresh entries.  The old resolved-representation bridge and its dependence on the old invariant disappear. |
| `CenterRename.renameWorld` | Rename all invariant conclusions and preserve center equality. | **Simplified.** Prove one `lookupStore`/store-renaming commutation lemma and apply `rename-⊑` pointwise; no transitive representative transport is needed. |
| `WorldDecay.blendWorld` | Use the geometry/stores of the premise world and weaken representation proofs to the blended environment. | **In hand.** An output `X⊑X` mark comes from the premise world; raw imprecision is monotone under the environment decay. Invariant (4) is unchanged because geometry and stores are unchanged. |
| `WorldDecay.honestify` | Preserve all aligned store representations while changing only marks; establish precise alignment. | **In hand.** Existing alignment and mark-decay lemmas provide the first two fields; invariant (4) is unchanged because geometry and stores are unchanged. |
| `SealPeelToolkit.dynWorld` | Preserve geometry/stores under the all-`X⊑★` environment. | **In hand.** Precise alignment is vacuous and representation proofs weaken to the all-dynamic environment; invariant (4) is inherited unchanged. |
| `TargetBindLift.targetStoreAs W Σᴿ` | Prove the invariants after replacing the target store arbitrarily. | **Not in hand for the raw helper, but the premise is simpler.** Require pointwise direct-entry imprecision plus preservation of the literal-`★`/unmatched-head classification; no path equality is needed. Make the raw helper private or require that evidence. |
| `TargetExtend.smartAliasInsertWorld` | Transport all invariants through alias insertion. | **Simplified after the input insert is valid.** Lookup commutes pointwise with the insertion; old-source freezing reflects both an unmatched target and an unmatched variable head back to the premise world. |
| `TargetExtend.smartFreshInsertWorld` | Transport all invariants through fresh insertion. | **Simplified after the input insert is valid.** Pointwise lookup transport plus old-source freezing and target reflection preserve both branches of invariant (4). |
| `TargetExtend.insertRebaseWorld ins Wᵖ` | Mix `Wᵖ`'s source/environment/store with the inserted target of another world. | **Not in hand for arbitrary `Wᵖ`, and invariant (4) exposes the exact failure.** A repark can make a non-`★` old target newly unmatched. Require a checked rebase premise that rules this out. |
| `liftBothTargetInsert` and `liftLeftTargetInsert` | Lift a `TargetInsert` across the corresponding world builders. | **In hand after those builders are valid.** These records relate already constructed endpoints. |
| `smartAliasTargetInsert` and `smartFreshTargetInsert` | Package the two smart inserted worlds as `TargetInsert` results. | **In hand with their builders.** Their geometry and pointwise lookup transport provide the preservation evidence. |
| `rightBindTargetInsert` and `keepRightBindTargetInsert` | Package `rightOnlyWorld`, optionally under `liftWorldBoth`. | **Not in hand at the root for generic `B`.** Strengthen `rightBindTargetInsert` with the same direct-entry classification premise as `rightOnlyWorld`; `keepRightBindTargetInsert` then shifts it. |
| `insertRebaseTargetInsert`, its reverse and pullback variants, and their commuting result packages | Package `insertRebaseWorld` endpoints as `TargetInsert` results. | **Blocked exactly where `insertRebaseWorld` is blocked.** Once that builder requires rebase/frozen-target evidence, these functions already receive or derive it. |
| Other `TargetInsert` results | Relate an input and an already constructed output world. | **No extra minting obligation.** Once outputs are valid `World`s, the fields and pointwise lookup transport explain preservation. |
| `sameWorldRebaseAt`, rename/move/insert/right-bind `RebaseAt` transformers, and `RebaseAtᴸ`/`ᴿ`/tag wrappers | Relate already valid worlds and identify or transport a pivot. | **No global minting obligation.** `RebaseAt.storeRepresentations` follows by the derived chain-coherence induction from `representationsImpreciseʷ` and `pivotAligned`; keep it only during staged migration, then remove it. |
| `EnvDecay`, `decayRebaseAt`, `SameRuntime` | Transport relations between already valid worlds. | **In hand.** `decayRebaseAt` already transports the pivot representation proof. |
| `TermImpDecay` world patterns | Destructure a `World` while transporting derivations. | **Mechanical blast only.** Constructor patterns must bind or ignore three more fields; no new world is minted there. |

### Invariant-(4) right-only minting inventory

For `rightOnlyWorld W B`, the fresh target variable is `Fin.zero`.  No source
variable maps to its fresh center, and its direct entry computes to

```agda
lookupStore (store-bind (targetStoreʷ W) B) Fin.zero ≡ ⇑ᵗ B
```

Consequently strict requires `⇑ᵗ B ≡ ★`.  Chain-permissive requires that
equality or `⇑ᵗ B ≡ ＇ Yᴿ` with `Yᴿ` unmatched in the new world.  For
`B = ＇ X`, the latter reduces to the old pivot `X` being unmatched in `W`;
the new head is `Fin.suc X`.  The current generic signature proves neither
classification.

| Catch-up minting path | What it binds | Is the direct obligation in hand? |
| --- | --- | --- |
| `structural-target-inst-step`; `inst-cast-alloc-prefix`; `GroundingPreserve.β-inst-*` | `★` | **Yes, definitionally.** |
| Concrete `Λ⊑Λ²` two-bind route, including smart-alias, smart-fresh, and rebase transport | First `★`, then `＇ Fin.zero` pointing to that first cell | **Yes only under CHAIN-PERMISSIVE.** The first cell is literal `★`; the second points to that still-unmatched first cell. Strict rejects the second bind. Existing resolver equalities can be replaced by direct entry equalities plus the unmatched-head proof. |
| `AllValueViewStepCatalogᵀ` when coupled to the right-only world extension | `β-Λ`, `β-reveal-∀`, and `β-conceal-∀` bind arbitrary `A`; `β-gen` binds arbitrary `C`; `β-∀` is `keep` | **Not in hand for the allocating cases.** The catalog does not classify the direct entry; the catch-up extension needs a narrowed case or an added premise. |
| `StructuralTargetGenStepProof`, `StructuralTargetLambdaStepProof`, `StructuralTargetConversionStepProof`, `StructuralGenDescentProof`, and `spine-typed-Λ-child` | `＇ X` for an arbitrary old target pivot `X` | **VIOLATING SURFACE under both choices.** The fresh alias cell is definitely unmatched because it is made by `rightOnlyWorld`; its head `Fin.suc X` is unmatched exactly when old `X` was unmatched. No premise supplies that fact, and `X` may be matched. |
| `GroundingPreserve.β-gen-*` | Arbitrary argument `C` | **VIOLATING SURFACE.** Occupancy/atomicity does not classify `⇑ᵗ C` as literal `★` or an unmatched variable. |
| `RightBindWorldExtendᴿᵀ`, `RightBindKeepWorldExtendᴿᵀ`, `RightBindRightBindWorldExtendᴿᵀ`, `right-bind-under-left-lift`, and the smart alias/fresh bind helpers | Generic `B`/`C` | **VIOLATING AS GENERIC APIs.** Thread the direct-entry classification.  The safe `★`-then-`＇ zero` calls use the two different permissive branches. |
| `TransportTermImprecisionProof.mapCtxᴾ-right-bind`, its `evolve-right-bind` case, and other `B₀` callers | Generic `B₀` already named in `rightOnlyWorld W B₀` | **Not locally derivable.** Thread the strengthened builder's direct classification through these surfaces; this is pointwise and no longer mentions a resolved path. |
| `StructuralWorldExtendᴿ.structural-bind`, `StructuralNamePostPlan.target-bind-child`, `structural-target-bind-step`, peel/descent packages, `parked-structural-right-insert`, and `evolve-structural-right-bind` | A caller-supplied `TargetInsert` plus `targetStoreʷ W₁ ≡ store-bind ... B` | **In hand at the consumer, not at the mint.** `W₁ : World` supplies the direct classification.  Every constructor of `W₁` must prove it; `TargetInsert` plus the store equation alone does not. |
| `rightBindTargetInsert`, `rightBindTargetWindowInsert`, `keepRightBindTargetInsert`, and right-bind rebase/insert wrappers | Whatever the underlying `rightOnlyWorld` binds | **Same flag as the underlying bind.** Strengthen the root with the direct classification; wrappers transport it pointwise. |

The structural `TargetInsert` consumers therefore need no redundant new
premise once `World` contains the field.  The direct `rightOnlyWorld` and
`rightBindTargetInsert` constructors do need the premise, and the variable-
alias call sites above must prove that the old head is unmatched or stop using
a right-only world for that allocation.

### Direct worlds and fixtures

Every direct `world` application must prove all three fields.  Fixtures whose
unmatched target entries are literal `★` can prove invariant (4) immediately.
Under the recommended form, an unmatched variable entry is also accepted only
when its head is unmatched.  A non-variable, non-`★` direct entry must be
center-aligned with a source pivot in that exact world.

Directness sharpens the `CastTermImprecision2` Example 12 audit:

* `example12-world-X` directly aligns `ℕ` with `ℕ`; its unmatched `Y`
  points to unmatched `Z`, whose entry is `★`.  It satisfies both direct fields
  under CHAIN-PERMISSIVE, but strict would reject the `Y` indirection.
* `example12-world-Y` directly aligns source `ℕ` with target entry `＇ Z`, so
  it already fails `representationsImpreciseʷ`; it also leaves direct `ℕ` at
  `X` unmatched.
* `example12-world-Z` directly aligns `ℕ ⊑ ★`, but leaves direct `ℕ` at
  `X` unmatched.  Its unmatched `Y` also points to the now-matched `Z`, which
  the permissive form deliberately rejects.
* `example12-nat-chain-world-X` has valid direct `ℕ ⊑ ℕ` at `X`, but its
  unmatched `Y` points to that matched `X`; invariant (4) rejects it.
  `example12-nat-chain-world-Y` additionally tries to align direct `ℕ` with
  `＇ X`, and leaves direct `ℕ` at `X` unmatched.
* In the left-path family, direct entries validate the `X` and `Z` pairings,
  while the `Y` pairing changes from a transitively valid `★ ⊑ ★` to an
  invalid direct `＇ Z ⊑ ★` under its precise mark.  All three worlds still
  fail the separate `preciseMarksAlignedʷ` audit described below.

Thus direct lookup rejects chain-depth-skewed pairings instead of hiding the
skew behind a terminal representative.  The all-literal-`★` finite probes
remain locally supported.

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

1. `bothBindWorld` now needs only the fresh direct-entry relation.  Existing
   paired allocation premises can supply it pointwise; the old chain transport
   surface should be deleted rather than adapted.
2. `rightOnlyWorld` and `rightBindTargetInsert` need a direct classification of
   the bound entry.  Generic `B`/`B₀` surfaces do not carry it.  The structural
   `＇ X` sites specifically need `X` to be unmatched, which is not currently a
   premise.
3. Generic `liftWorldLeft v` and `leftOnlyWorld v` cannot preserve precise-mark
   alignment when `v = X⊑X`; their interfaces must exclude that case or gain a
   target occupant.
4. `insertRebaseWorld` needs an explicit relation between its independently
   supplied premise world and the world being target-inserted; invariant (4)
   must remain true when a source pivot changes partners.
5. `targetStoreAs` cannot accept an arbitrary replacement store; movement
   evidence must preserve direct pairwise entries and both branches of the
   unmatched-target classification.
6. The live Example 12 left-path and `Examples2` `XZ` worlds violate the
   invariant being merged from `WFWorld`.  Directness also rejects the
   chain-depth-skewed Example 12 `Y` pairings; the unmatched direct-entry audit
   rejects the `Y`/`Z` and natural-number chain worlds as detailed above.
7. The public compile theorem and all parked/occupancy initial-world surfaces
   must drop their arbitrary initial store, even though the recursive compiler
   proof itself is compatible.

## Kill-check

The D8a and T10 Probe 1 geometries were rechecked with invariant (4) as an
actual field of the probe's eight-field `World`.

| Configuration | Matched target | Unmatched target | Direct unmatched entry | Verdict under strict / permissive (4) |
| --- | --- | --- | --- | --- |
| D8a `W` | old target `Fin.suc Fin.zero` | fresh target `Fin.zero` | `ℕ` | **Rejected.** |
| D8a `Wᵖ` | fresh target `Fin.zero` | old target `Fin.suc Fin.zero` | `ℕ` | **Rejected.** The old occupant loses its source partner and its direct entry is neither `★` nor a variable. |
| T10 Probe 1 `W` | old target `Fin.suc Fin.zero` | fresh target `Fin.zero` | `★` | **Accepted.** |
| T10 Probe 1 `Wᵖ` | fresh target `Fin.zero` | old target `Fin.suc Fin.zero` | `★` | **Accepted.** The old occupant loses its partner but its entry is literally `★`. |

**BOTH DIRECT FORMS OF INVARIANT (4) KILL BOTH D8a WORLDS.**  In `W`, the
fresh unmatched occupant has direct entry `ℕ`; in `Wᵖ`, the old unmatched
occupant also has direct entry `ℕ`.  Neither failure depends on following a
chain.  The checked definitional equalities are `d8a-fresh-direct-entry` and
`d8a-old-direct-entry`, and the negative witnesses use the weaker,
chain-permissive field.  Therefore the strict field rejects them a fortiori.

**Invariant (4) does not kill T10 Probe 1.**  Both unmatched occupants have
literal `★` direct entries, so both endpoint worlds satisfy all three added
fields and the cross-world T10 failure remains.

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

1. Add the total one-step `lookupStore` to `TyStore`.  Against the existing
   five-field record, introduce a temporary, non-public `WorldInvariants W`
   companion containing exactly the three drafted fields.  Prove preservation
   for the core builders and require the companion at theorem boundaries.
2. Strengthen `rightOnlyWorld` and `rightBindTargetInsert` with the selected
   direct-entry classification.  Thread it through `evolve-right-bind`, the
   generic `B₀` surfaces, parked constructors, and smart wrappers.  Under the
   recommended form, retain the `★`-then-`＇ zero` route; add unmatched-head
   evidence or redesign the arbitrary `＇ X`, `C`, and generic-`B` sites.
3. Replace resolved-representation transport with pointwise lookup transport:
   use the allocation premise directly in both-bind, add lookup commutation for
   center renaming/insertion, restrict left-only minting, guard store
   replacement and insertion/rebase, and repair or retire invalid fixtures.
   Use invariant (4) to reject non-`★` repark outputs.
4. After D15 lands, merge the companion fields into `World` atomically, change
   constructor calls and patterns to the eight-field shape, replace `WFWorld`
   arguments by the projection, and delete both `WFWorld` and the temporary
   companion.  Do not retain a compatibility alias in this closed-world repo.
5. Derive chain coherence by store-age induction, remove
   `RebaseAt.storeRepresentations` once callers use that lemma, and consolidate
   `initialWorldᴼ` into the canonical empty-store constructor.

PR #171 (`agent/gtsf-partner-redesign`, fetched head `faec619c`) changes 43
`GTSFImp` files and touches `CastTermImprecision2`, `TargetExtend`,
`CenterRename`, `TargetBindLift`, `TermImpDecay`, and many downstream inversion
and catchup modules.  Its direct change to `CastTermImprecision2` is the D15
partner/conceal surface rather than this record, but its semantic and arity
blast overlaps almost every migration site.  Land D15 first, then rebase D16
and perform step 4.  The temporary companion work can be prepared before that
merge, but it must not become a second permanent world API.

## Recon addendum: invariant (5)

The user's additional runtime discipline is compatible with the direct-entry
design above.  During Stage 1 it should be a fourth field of the temporary
`WorldInvariants` companion; when the companion is merged, it becomes the
ninth field of `World`.  The checked draft in
`notes/probes/T15Invariant5ReconProbe.agda` is:

```agda
    dynamicStarSourcesUnoccupied :
      ∀ (Xᴸ : TyVar Δᴸ)
      → CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ) ≡ X⊑★
      → lookupStore (CTI2.sourceStoreʷ W) Xᴸ ≡ ★
      → ∀ (Xᴿ : TyVar Δᴿ)
      → toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ
        ≢ toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ
```

This is deliberately a direct-source-entry condition.  It neither follows a
source representation chain nor inspects the target store.  The conclusion
says exactly that the source center has no target occupant.  The probe also
checks the field for the amended empty-store `initialWorld`: every direct
entry in `emptyStore` is its structurally bound variable, never `★`.

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
