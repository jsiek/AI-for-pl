# T14 partner-premise redesign reconnaissance

Scope: this note reconstructs the role of the live
`SourceConcealPartnerOK` premise in `conceal⊑²`, records the transport
friction it causes, and compares three replacement designs.

Files read for this pass include:

- `proof/DGG/CastTermImprecision2.agda`
- `proof/DGG/GroundingMint.agda`
- `proof/DGG/GroundingPreserve.agda`
- `proof/DGG/Occupancy.agda`
- `proof/DGG/SealTransferCore.agda`
- `proof/DGG/TermImpDecay.agda`
- `proof/DGG/CenterRename.agda`
- `proof/DGG/TargetExtend.agda`
- `proof/DGG/TargetBindLift.agda`
- `proof/DGG/Catchup/*.agda`
- `proof/DGG/Inversion/*.agda`
- `proof/DGG/notes/CTI-TIGHTENING-CALIBRATION.md`
- `proof/DGG/notes/TIGHTEN3-PREFLIGHT.md`
- `proof/DGG/notes/PEDIGREE-DESIGN-MEMO.md`
- `proof/DGG/notes/PHASE3-DEEPDIVE-REPORT.md`
- `proof/DGG/notes/M5-INST-INVERSION-DESIGN.md`
- `proof/DGG/notes/m5-inst-inversion-lambda-lifted-target-pivot-blocked.red`
- `proof/DGG/notes/m5-inst-inversion-source-strip-post-obligation-blocked.red`
- `proof/DGG/notes/ProjectionMismatchStarRepScratch.agda`
- origin-only notes on `origin/agent/gtsf-ns4-stage2`:
  `t5-conceal-equal-partner-proposal.red`,
  `t5-target-wrapper-strip-proposal.red`,
  `t5-target-wrapper-strip-stop.red`,
  and `t5-lambda-strict-one-bind-proposal.red`

## 1. What the partner premise protects

### The live premise

The live source-side conceal rule in `CastTermImprecision2` has the
following shape:

```agda
conceal⊑² :
  SourceConcealPartnerOK W′ M c Xᴿ? M′ →
  ImpEnvMono W W′ →
  TagRebaseAtᴸ W′ W Xᴸ? Xᴿ? →
  SameCtx Γ Γ′ →
  ...
  W ∣ Γ ⊢² M ⊑ M′ ∶ p →
  W′ ∣ Γ′ ⊢² M ↓ c ⊑ M′ ∶ q
```

The premise is term-shaped, but its source-seal branch is also a world
occupancy gate:

```agda
data SourceConcealPartnerOK W P c Xᴿ? M′ where
  seal-partner-ok :
    SealPartnerOK W X P R Xᴿ? M′ →
    SourceConcealPartnerOK W P (seal X R) Xᴿ? M′
  fun-conceal-target :
    SourceConcealPartnerOK W P (fun A B) Xᴿ? M′
  all-conceal-target :
    SourceConcealPartnerOK W P (all A B) Xᴿ? M′
  id-conceal-target :
    SourceConcealPartnerOK W P (id A) Xᴿ? M′
```

For source seal conceals, the key branch is:

```agda
star-rep-target :
  NoTargetOccupantAtSource W X →
  Rep★PartnerOK W X P Xᴿ? M′ →
  SealPartnerOK W X P ★ Xᴿ? M′
```

The shape predicate under `Rep★PartnerOK` distinguishes the cases in
which a target term may be treated as a legitimate partner for a source
`seal X ★`:

- `rep★-untagged`: the target is not a top-level tag/projection.
- `rep★-nonvar-tag`: the target is tagged with a non-variable ground.
- `rep★-var-tag`: the target is tagged with an aligned target name.
- `rep★-matched-inner-tags`: source and target both have inner tags,
  and the inner target tag is aligned with the inner source tag.
- `rep★-round-trip`: source `seal X ★` followed by source `X!` may be
  handled recursively.

The critical point is that the apparently syntactic premise is carrying
two different facts:

1. A source-only see-through window is only available when the source
   pivot has no target occupant.
2. If the target is already visibly protected by a tag/seal, the visible
   protection must be the right kind of protection. An arbitrary top-level
   target variable projection is not enough.

### Minting

There is no direct `SourceConcealPartnerOK` construction in
`compile-preserves-embedded²`; grep finds no direct uses of
`SourceConcealPartnerOK`, `SealPartnerOK`, `MatchedConcealPartnerOK`, or
`Rep★PartnerOK` in `CompilePreservesImprecision2.agda`. The compile-side
minting is instead world-level:

- `GroundingMint.agda` records that the initial compile world occupies
  the centers that already exist on both sides.
- It also records that a source-only fresh lift has
  `NoTargetOccupantAtSource` at the new source pivot.
- Thus compile images do not mint arbitrary term-shape partner evidence;
  they mint worlds in which the occupancy facts needed by the source
  seal premise are either present or impossible.

Runtime allocation is where the target occupant is minted:

- `β-inst-allocation-atomic` in `GroundingPreserve.agda` proves that
  `rightOnlyWorld W ★` immediately occupies target pivot `zero`, and
  simultaneously exposes the β-inst contractum and its reveal/cast shape.
- `β-gen-allocation-atomic` proves the analogous fact for
  `rightOnlyWorld W C`.
- `Occupancy.agda` contains the lower-level facts
  `β-inst-allocation-occupies-targetᴼ` and
  `β-gen-allocation-occupies-targetᴼ`.

This is the important allocation discipline: a target-only allocation
does not merely extend the target store; it closes the source-only
see-through window for the corresponding center in the same step that
creates the generated target representation.

`SealTransferCore.agda` is the main proof-level re-emission site. It
constructs new partner packages after source seal descent, target
transport, and dynamic source payload transfer. In particular, its
source-seal output rebuilds:

```agda
matched-seal-star-partner
  (rep★-round-trip (transport-rep★-partner-ok-tag ... partner))

seal-partner-ok
  (star-rep-target no-target
    (rep★-round-trip (transport-rep★-partner-ok-tag ... partner)))
```

So the premise is minted at three layers:

- world occupancy at compile and allocation boundaries;
- target shape produced by allocation/reveal/cast transfer;
- explicit relation evidence re-emitted by catch-up and seal-transfer
  proofs.

### Preservation

The live tree preserves partner evidence by hand across every world and
term movement that can occur around source conceal:

- `TermImpDecay.agda`:
  `decayRep★PartnerOK`, `decaySealPartnerOK`,
  `decaySourceConcealPartnerOK`, and
  `decayMatchedConcealPartnerOK`.
- `CenterRename.agda`:
  `renameRep★PartnerOK`, `renameSealPartnerOK`,
  `renameSourceConcealPartnerOK`, and
  `renameMatchedConcealPartnerOK`.
- `TargetExtend.agda`:
  target insertion/extension versions of the same partner transports.
- `TargetBindLift.agda`:
  `moveRep★PartnerOK`, `moveNoTargetOccupantAtSource`,
  `moveSealPartnerOK`, `moveSourceConcealPartnerOK`, and
  `moveMatchedConcealPartnerOK`.
- `SealTransferCore.agda`:
  `transport-rep★-partner-ok`,
  `transport-rep★-partner-ok-dyn`,
  `premise-partner-from-tag-rebase`,
  `transport-rep★-partner-ok-tag`, and the dynamic payload partner
  constructors.
- `Catchup/StructuralCatchupRightDef.agda`:
  endpoint fields such as `source-conceal-endpoint-partner`, plus
  nested target-cast partner transformers.
- `Catchup/TargetCastStepInversionProof.agda` and
  `Catchup/ExtraCastRightAtProof.agda`:
  case-specific target-step inversions that either rebuild or refute
  partner evidence.

The preservation burden is not incidental. `SourceConcealPartnerOK`
depends simultaneously on:

- the premise world, because alignment and occupancy are world-indexed;
- the target endpoint term, because `NotTopTag`, top-level target tags,
  and name-protected target seals are syntactic;
- the source pivot, because `NoTargetOccupantAtSource W X` is destroyed
  by target allocation at the same center.

### Consumers

Grep over the proof tree shows that the premise is consumed far beyond
the declaration site. The largest direct users are:

- `Catchup/ExtraCastRightAtProof.agda`
- `Catchup/StructuralCatchupRightDef.agda`
- `CenterRename.agda`
- `TargetChainProof.agda`
- `SourceStripWorkerProof.agda`
- `SealTransferCore.agda`
- `TargetBindLift.agda`
- `TargetExtend.agda`
- `TermImpDecay.agda`
- `TargetWalkSupport.agda`
- `SourceStripColumnView.agda`
- `Inversion/RightInjInversion2Proof.agda`

The important consumer patterns are:

- `TargetWalkSupport` turns partner evidence into source-seal and
  target-seal views.
- `TargetChainProof` case-splits on `star-rep-target`,
  `plain-target`, `name-protected-target`, every `Rep★PartnerOK`
  constructor, and `matched-seal-star-partner`.
- `SourceStripColumnView` and `SourceStripWorkerProof` use the partner
  cases to decide whether a source seal may be stripped or must be
  routed to a protected target shape.
- `RightInjInversion2Proof` reconstructs source conceal partners when
  peeling target injections.
- `ExtraCastRightAtProof` uses the premise to reject projection-mismatch
  target steps.

So a redesign of the premise is not localized to `conceal⊑²`; it changes
the interface for source-strip, target-walk, target-chain, target-step
inversion, and seal-transfer proofs.

### The motivating bad square

The checked scratch module
`proof/DGG/notes/ProjectionMismatchStarRepScratch.agda` reconstructs the
bad square that the live premise rules out.

The setup is a one-cell world in which source `X` and target `Y` are
center-aligned, and both stores represent the center by `★`. The source
has a sealed star representation:

```agda
source-term =
  (($ (κℕ 0)) ⟨ ℕ!ˢ ⟩) ↓ seal X ★
```

The target is only an `ℕ`-tagged payload:

```agda
target-tagged =
  ($ (κℕ 0)) ⟨ ℕ! ⟩
```

The tempting, unsound relation is:

```agda
probe-world ∣ [] ⊢²
  source-term ⟨ X! ⟩ ⟨ X? ⟩
  ⊑
  target-tagged ⟨ Y? ⟩
  ∶ probe-q
```

where `probe-q` is the precise endpoint relation
`＇ X ⊑ᵂ⟨ probe-world ⟩ ＇ Y`.

Without the partner premise on `conceal⊑²`, the source-side
`seal X ★` could be related to the bare target `target-tagged`, and the
outer source `X! ; X?` could then be related to target `Y?`. That creates
an unearned target-name pairing: the type endpoint says `X` and `Y`, but
the target term is really protected by `ℕ!`, not by a `Y` seal/tag.

Diagram:

    source-term ⟨ X! ⟩ ⟨ X? ⟩     ⊑     target-tagged ⟨ Y? ⟩
              |                                     |
              | tag/untag returns                   | tag/untag bad
              v                                     v
          source-term                         blame

The scratch proves both sides of the operational behavior:

- `source-projection-returns`: the source side reduces back to
  `source-term`.
- `mismatch-steps-to-blame`: the target side reduces to `blame`.

It also proves that the live relation cannot derive the bad input:

- `target-tagged-partner-empty`
- `source-sealed-target-tagged-empty`
- `source-tagged-target-tagged-empty`
- `source-projected-target-tagged-empty`
- `projection-mismatch-empty`

The decisive live check is that the one-cell world is occupied:

```agda
one-center-occupied :
  NoTargetOccupantAtSource probe-world X → ⊥
```

Therefore the only plausible `SealPartnerOK` branch for source
`seal X ★`, namely `star-rep-target`, is impossible. The other branches
cannot match the top-level target projection shape. This is exactly the
protection provided by the premise.

`CTI-TIGHTENING-CALIBRATION.md` records the same conclusion in the S-OCC
calibration:

- in the pre-occupied state, source-only see-through is allowed;
- in the aligned-occupied state, `NoTargetOccupantAtSource` is empty;
- the bad square is underivable;
- a pure world-only tightening was checked insufficient because the same
  world can still be paired with a bad target term if the target term
  shape is ignored.

## 2. Why the premise hurts

### Transport is both world-indexed and endpoint-indexed

`SourceConcealPartnerOK` is not just an invariant about a world. It also
mentions the target endpoint term. This means a proof that changes the
target endpoint by reduction, stripping, insertion, decay, or rebase must
produce a new partner proof for the new endpoint.

The LG-3 notes record the failure of a generic transformer:

- `lg3i-source-conceal-endpoint-partner-resister.red` says source-conceal
  replay needs an endpoint-specific partner
  `SourceConcealPartnerOK child.W′ M c ... child.N′`.
- `lg3af-target-conversion-endpoint-partner-resister.red` records a
  checked counterexample: `plain-target not-↑` can justify a wrapper
  target `M′ ↑ id↑ A`, but there need not be any partner proof for the
  reduct `M′`.

So generic target conversion does not preserve the premise. The current
solution is to thread exact endpoint partner continuations through
structural catch-up results.

### D4 / higher-order lift friction

`PHASE3-DEEPDIVE-REPORT.md` reconstructs the D4 higher-order shared-arg
allocation trace. The important shape is:

- old shared pivots must keep their center images;
- fresh allocating pivots must appear at zero on the allocating side;
- wrapper descent may use same-world rebase at the fresh pivot;
- parked extensions must not accidentally move an old target pivot.

This is already difficult for type/world transport. Partner evidence adds
another layer because source-seal premises carry both occupancy and target
endpoint shape. Even when the target/store rebase is right, the partner
proof may no longer mention the endpoint term at the right lifted world.

`m5-inst-inversion-lambda-lifted-target-pivot-blocked.red` shows the same
shape in the positive left-lift depth setting. The direct prefix route
puts the abstract target pivot at `suc zero`, while the recursive caller
wants the generated target pivot at `suc (suc zero)`. Existing
`TargetStoreMove` and `CenterRename` machinery cannot reorder target
embeddings past source-only binders. Any partner evidence indexed by those
embeddings inherits the same blocked transport problem.

### T5d / stage2 target-wrapper strip friction

The origin-only `agent/gtsf-ns4-stage2` notes show the current in-flight
lift drafts hitting the premise in two places:

- `t5-conceal-equal-partner-proposal.red`:
  the source-conceal equal branch needs
  `SourceConcealPartnerOK` after structural target catch-up. The world
  part is produced by `structural-tag-rebase-atᴸ`, but the target package
  does not carry enough endpoint partner information.
- `t5-target-wrapper-strip-stop.red`:
  a wrapper target can be justified by `plain-target not-↑` or
  `plain-target not-↓`, but after β-reveal/β-conceal strip the child
  endpoint is arbitrary `⇑ᵗᵐ V`. There is no constructor that turns
  `plain-target not-↑` into a partner proof for that child endpoint.

This is the same endpoint-index problem in a stricter setting: the
premise is easy to satisfy for the wrapper, but the proof needs it for
the reduct.

### Premise-world pedigree and index drift

`PEDIGREE-DESIGN-MEMO.md` records the earlier pedigree tension:

- freed pedigree was unsound;
- anchored-inner solved some cases but still allowed arbitrary packages;
- the conservative repair was premise-world protection.

The addendum notes that live indices once drifted between premise-world
and conclusion-world target pivots. That is the structural reason many
transport proofs are delicate: the premise wants to be anchored at the
world where the target endpoint was inspected, while the conclusion wants
the post-rebase world and type witness.

### Blast radius

The current premise creates a large re-proof surface because many modules
case directly on its constructors. A redesign touches at least:

- `CastTermImprecision2`: constructors and rule statements.
- `SealTransferCore`: dynamic source-payload transfer and source-seal
  re-emission.
- `TargetWalkSupport`, `TargetChainProof`, `TargetDescent*`: partner
  inversion/view logic.
- `SourceStripColumnView`, `SourceStripProof`, `SourceStripWorkerProof`:
  source-strip routing.
- `Catchup/StructuralCatchupRightDef`,
  `Catchup/TargetCastStepInversionProof`,
  `Catchup/ExtraCastRightAtProof`: endpoint partner transformation and
  target-step inversion.
- `TermImpDecay`, `CenterRename`, `TargetExtend`, `TargetBindLift`:
  mechanical transports.

The pain is therefore real, but it is pain around a live soundness
condition, not accidental proof ornamentation.

## 3. Alternative designs

### A. World-level pairing

Move the source/target seal-pairing invariant into the world. Today the
world tracks left and right embeddings, imprecision environment, and both
stores. A world-level redesign would add a cell invariant for centers:

```agda
data SealCell W X : Set where
  source-open :
    NoTargetOccupantAtSource W X →
    SealCell W X

  paired :
    (Y : TyVar Δᴿ) →
    CenterAligned W X Y →
    StoreRepImp W X Y →
    SealCell W X
```

or equivalently a world field:

```agda
sealCellʷ : (X : TyVar Δᴸ) → SealCell W X
```

Then source-seal conceal could be stated without a target-shape premise:

```agda
conceal⊑² :
  SealCell W′ X →
  ImpEnvMono W W′ →
  TagRebaseAtᴸ W′ W Xᴸ? Xᴿ? →
  ...
  W ∣ Γ ⊢² M ⊑ M′ ∶ p →
  W′ ∣ Γ′ ⊢² M ↓ seal X R ⊑ M′ ∶ q
```

The allocation discipline would be built into the world constructors:

- source-only lift mints `source-open`;
- right-only allocation converts the relevant fresh center to `paired`
  or otherwise marks it occupied;
- both-bind allocation mints an aligned `paired` cell;
- rebase/lift/decay constructors must preserve or transform the cell
  invariant.

Transport story:

- Good: rebases and lifts can preserve the invariant by construction if
  all world-evolution constructors carry cell actions.
- Bad: this only transports world occupancy. It does not, by itself,
  inspect the target term. The S-WORLD calibration already checked that a
  pure world-only repair still admits the projection-mismatch bad square
  when paired with an arbitrary bad target term in the same world.

Proof mass:

- Very high. This changes `World`, every `liftWorld*`,
  `leftOnlyWorld`, `rightOnlyWorld`, `bothBindWorld`, world renaming,
  target extension, decay, compile image worlds, and every theorem that
  transports `_⊑ᵂ⟨ W ⟩_`.
- It can delete some explicit partner-transport lemmas only after the
  same work is reintroduced as world-evolution obligations.

Soundness risk:

- High if this is interpreted as "world pairing replaces term shape."
  World occupancy is necessary, but the counterexample target has the
  same world and the wrong target term shape.
- Moderate if the world stores only the occupancy/gating part and the
  matched/generated target shape remains in target-chain or matched
  conceal evidence.

Assessment: useful as an internal representation of occupancy, but not a
complete replacement for the partner premise unless paired with a separate
target-shape/provenance discipline.

### B. Witness-level pairing

Fold the pairing into `_⊑ᵂ⟨ W ⟩_` itself. The current definition erases to
the underlying type imprecision relation:

```agda
A ⊑ᵂ⟨ W ⟩ B =
  impEnvʷ W ⊢ embedᴸ A ⊑ embedᴿ B
```

A witness-level redesign would replace this with an indexed relation that
carries the world facts at variable endpoints:

```agda
data _⊑ᵂ⟨_⟩_ : Ty Δᴸ → World Δᴸ Δᴿ → Ty Δᴿ → Set where
  var-star-open :
    NoTargetOccupantAtSource W X →
    ＇ X ⊑ᵂ⟨ W ⟩ ★

  var-var-paired :
    (Y : TyVar Δᴿ) →
    CenterAligned W X Y →
    StoreRepImp W X Y →
    PairOK W X Y →
    ＇ X ⊑ᵂ⟨ W ⟩ ＇ Y

  fun :
    B₁ ⊑ᵂ⟨ W ⟩ A₁ →
    A₂ ⊑ᵂ⟨ W ⟩ B₂ →
    A₁ ⇒ A₂ ⊑ᵂ⟨ W ⟩ B₁ ⇒ B₂

  all :
    ... →
    `∀ A ⊑ᵂ⟨ W ⟩ `∀ B

  ...
```

Then `conceal⊑²` would get the needed source-open or paired fact from
the type witness `q`/`p`, instead of a separate
`SourceConcealPartnerOK` argument.

Transport story:

- Good: once every rebase/lift/decay theorem is by induction on enriched
  `_⊑ᵂ⟨ W ⟩_`, partner preservation travels with type-witness
  preservation. There is no separate partner proof to keep aligned.
- Bad: all type-imprecision transport lemmas now become partner
  transport lemmas. This moves the proof mass rather than removing it.

Proof mass:

- Very high. This changes the public shape of `_⊑ᵂ⟨ W ⟩_` and affects
  every proof that pattern matches on type imprecision, including
  substitution/transport, rebase, monotonicity, compile preservation,
  source-id equality, and cast/reveal/conceal typing congruences.

Soundness risk:

- Type witnesses still do not see target term shape. If this design
  drops `Rep★PartnerOK` completely, it repeats the world-only failure:
  the witness can say `＇ X ⊑ᵂ ＇ Y`, while the target term is protected
  by `ℕ!`.
- To be sound, the witness would need to carry term provenance or the
  term relation would still need matched/generated target-shape evidence.
  Carrying term provenance in type imprecision is conceptually awkward
  and would make `_⊑ᵂ⟨ W ⟩_` less canonical.

Assessment: elegant only if the desired invariant is purely type/world
level. The live bad square is not purely type/world level, so this
redesign is probably too invasive for too little simplification.

### C. Occupancy-style gating

Keep the S-OCC insight, but make it the visible rule premise instead of
burying it under the full source-conceal partner enumeration.

The current source-seal branch is:

```agda
star-rep-target :
  NoTargetOccupantAtSource W X →
  Rep★PartnerOK W X P Xᴿ? M′ →
  SealPartnerOK W X P ★ Xᴿ? M′
```

An occupancy-style redesign would split source-seal see-through from
matched/generated target-shape cases:

```agda
data SourceConcealOK W P c Xᴿ? M′ : Set where
  seal-star-open :
    NoTargetOccupantAtSource W X →
    SourceConcealOK W P (seal X ★) Xᴿ? M′

  seal-nonstar-plain :
    NotTopTag M′ →
    SourceConcealOK W P (seal X R) Xᴿ? M′

  seal-name-protected :
    CenterAligned W X Y →
    SourceConcealOK W P (seal X R) (just Y)
      ((M′ ↓ seal Y S) ⟨ c ⟩)

  fun-conceal-target :
    SourceConcealOK W P (fun A B) Xᴿ? M′

  all-conceal-target :
    SourceConcealOK W P (all A B) Xᴿ? M′

  id-conceal-target :
    SourceConcealOK W P (id A) Xᴿ? M′
```

The stricter variant is to allow `seal-star-open` only in genuinely
source-only worlds and require occupied/matched source-seal behavior to
go through `conceal⊑conceal²` or `packaged-seal-star²`:

```agda
conceal⊑²-seal-star-open :
  NoTargetOccupantAtSource W′ X →
  ...
  W ∣ Γ ⊢² M ⊑ M′ ∶ p →
  W′ ∣ Γ′ ⊢² M ↓ seal X ★ ⊑ M′ ∶ q

conceal⊑conceal² :
  MatchedConcealPartnerOK W M (seal X ★) Xᴿ? M′ →
  ...
  W′ ∣ Γ′ ⊢² M ↓ seal X ★ ⊑ M′ ↓ seal Y R ∶ q
```

The important difference from the live rule is not that all target shape
disappears. It is that the source-only see-through case is governed by a
negative world fact, while matched/generated target-shape facts are kept
with the rules that actually introduce or inspect matched target
protection.

Transport story:

- Good: `NoTargetOccupantAtSource` already has a substantial transport
  library in `Occupancy.agda`: left lift, right-only old-cell transport,
  rebase/tag-rebase transport, center rename, target insert, decay, and
  smart lift facts.
- Good: target endpoint reductions no longer need to preserve a
  `Rep★PartnerOK` proof for the source-only `seal X ★` case if that case
  is stated only as a world no-target premise.
- Remaining pain: non-star plain target and name-protected target cases
  still depend on endpoint shape if they remain in `SourceConcealOK`.
  The T5 wrapper-strip notes show that these should probably be carried
  as endpoint-specific structural continuations, not as a generic global
  transport theorem.

Proof mass:

- Moderate. This still changes the rule surface and the consumers that
  currently case on `SourceConcealPartnerOK`, but it does not change
  `World` or `_⊑ᵂ⟨ W ⟩_`.
- Existing S-OCC lemmas become the main transport substrate, so several
  current `Rep★PartnerOK` transports can be deleted or narrowed.
- `SealTransferCore`, `TargetChainProof`, source-strip proofs, and
  catch-up endpoint packages still need edits because they currently
  expose the live constructors.

Soundness risk:

- Low if the design keeps the live S-OCC restriction: source `seal X ★`
  may see through only when there is no target occupant at source `X`;
  occupied or matched states must use matched/generated target evidence.
- High if "occupancy-style" is read as "drop all target shape." The
  projection-mismatch scratch rules out that interpretation.

Assessment: this is the least disruptive design that addresses the
actual pain. It keeps the checked soundness invariant and moves the
transport-heavy part onto the world occupancy facts that already
transport well.

## 4. Recommendation

Do not drop `SourceConcealPartnerOK` without a replacement. The premise
protects a real DGG failure: it prevents a source `seal X ★` from being
related to a target term whose visible protection is an unrelated tag,
then later treating that target as though it were protected by target
name `Y`.

The best redesign target is the occupancy-style split:

1. Make the source-only `seal X ★` see-through rule require the negative
   world fact directly:

   ```agda
   NoTargetOccupantAtSource W′ X
   ```

2. Keep matched source/target seal behavior in `conceal⊑conceal²` and
   `packaged-seal-star²`, with whatever matched/generated target
   evidence those rules genuinely need.

3. Do not try to prove a generic endpoint transformer from wrapper
   partners to child partners. The checked LG-3 and T5 notes show that
   such a theorem is false. Instead, endpoint-specific structural
   catch-up results should carry the exact child partner evidence they
   produce.

This design keeps the user-visible intent of S-OCC: source-only
see-through is an occupancy gate, not a broad syntactic target-shape
enumeration. It should transport under rebases and lifts better because
the hard premise becomes `NoTargetOccupantAtSource`, which already has
transport infrastructure. It also avoids the two larger rewrites:

- world-level pairing, which is attractive for occupancy but unsound if
  it replaces target-term shape entirely;
- witness-level pairing, which makes every type-imprecision transport
  theorem a partner-transport theorem and still cannot inspect the target
  term.

The practical next design step should be a preflight that introduces a
new source-open rule beside the current rules, rewrites exactly one
source-strip or target-chain consumer to use the no-target premise
directly, and checks whether the remaining `plain-target` and
`name-protected-target` cases can be moved into structural endpoint
packages rather than preserved globally.
