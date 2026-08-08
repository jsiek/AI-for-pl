# M2 rebase redesign dossier

Branch: `agent/gtsf-extra-cast-right`

Scope: design pass only.  No `GTSFImp/` source file was edited.  The checked
validation artifact is `M2RebaseRedesignScratch.agda` at the repository root.

## Executive summary

The current live `RebaseAt` relation permits the target pivot to move, provided
the old target center is anchored by some source variable.  The M2 redesign
should remove that freedom:

- source pivots may still re-park;
- every old target variable keeps the same center across a rebase;
- fresh target pivots are introduced only by parked world evolution and enter at
  `Fin.zero`;
- `anchorᴿ` should be deleted, not weakened.

The replacement discipline is stronger and simpler than the current anchoring
condition.  It makes the refutation probes fail at constructor formation time:
the moved-old-target rebase premise has no restricted witness.

## Proposed restricted surface

Replace the target side of `RebaseAt` with an all-target frozen field:

```agda
record RebaseAt {Δᴸ Δᴿ Δ} (W W′ : World Δᴸ Δᴿ Δ)
    (Xᴸ : TyVar Δᴸ) (Xᴿ : TyVar Δᴿ) : Set where
  constructor rebase-at
  field
    sameRuntime : SameRuntime W W′
    ηᴸ-off-pivot : ∀ {Y} → Y ≢ Xᴸ
      → toRenameᵗ (ηᴸʷ W′) Y ≡ toRenameᵗ (ηᴸʷ W) Y
    ηᴿ-frozen : ∀ Y
      → toRenameᵗ (ηᴿʷ W′) Y ≡ toRenameᵗ (ηᴿʷ W) Y
    pivotAligned :
      toRenameᵗ (ηᴸʷ W′) Xᴸ ≡ toRenameᵗ (ηᴿʷ W′) Xᴿ
    storeRepresentations : StoreRepImp W′ Xᴸ Xᴿ
```

Notes:

- `ηᴿ-frozen` replaces both `ηᴿ-off-pivot` and `anchorᴿ`.
- `ηᴸ-off-pivot` stays because source re-parking remains intentional.
- `rebase-varᴸ` stays, but it can only carry a `RebaseAt` whose target side is
  frozen.
- `rebase-varᴿ` stays, but target-side wrappers may no longer move an old
  target variable's center.  They may still expose a source re-park under a
  target conversion.
- `rebase-idᴸ`, `rebase-idᴿ`, and `rebase-onlyᴸ` keep their current shapes.
- `sameWorldRebaseAt` becomes the same constructor with `ηᴿ-frozen = λ _ → refl`.
- Fresh target allocation is not a rebase.  It belongs to parked world evolution;
  old variables are shifted, and the fresh target variable is `Fin.zero`.

I recommend the all-target field over a pivot-only field because it removes a
recurring case split on `Fin._≟_ Y Xᴿ`, and it directly matches the parked
lemmas already being added under `proof/DGG/Parked/`.

## Use-site inventory

| Surface | Current world-moving premise | Downstream consumers | Movement classification | M2 action |
| --- | --- | --- | --- | --- |
| `RebaseAt` | Runtime stores fixed, source/target embeddings may change at their pivots, `anchorᴿ` justifies a moved target pivot. | `CastTermImprecision2`, `TermImpDecay`, `CenterRename`, `ExtraCastRight2`, `SealTransferCore`, `SealChain`, `SealChainView`, `Repark`, examples and probes. | Source and target can currently move. | Replace target movement with `ηᴿ-frozen`; delete `anchorᴿ`. |
| `rebase-idᴸ` | No pivot, same world. | Target/source reveal-conceal decay, extra-cast inversion, examples. | Neither. | Keep unchanged. |
| `rebase-varᴸ` | Source-side conversion with paired rebase. | `reveal⊑²`, `conceal⊑²`, `TermImpDecay`, `CenterRename`, `ExtraCastRight2`, `SealTransferCore`, examples, probes. | Should move source only; currently can smuggle target movement. | Keep; now accepts only frozen-target `RebaseAt`. |
| `rebase-onlyᴸ` | Source variable has no aligned target variable and world stays fixed. | `LambdaImpProbe`, `TermImpDecay`, `CenterRename`, `ExtraCastRight2` inversion branches. | Neither target nor world movement; source-only variable view. | Keep. |
| `rebase-idᴿ` | No pivot, same world. | `⊑reveal²`, `⊑conceal²`, decay and examples. | Neither. | Keep unchanged. |
| `rebase-varᴿ` | Target-side conversion with paired rebase. | Example 12 target reveals/conceals, `TermImpDecay`, `CenterRename`, `Repark`, `SealChain`, probes. | Should expose source re-parking under target syntax; currently can move old target pivots. | Keep; target side frozen. |
| `⊑reveal²` | Consumes `RebaseAtᴿ W W′ Xᴿ?`. | Example 12 target reveal path, left-path checkpoints, decay, center rename, repark/view code. | Target wrapper; valid M2 uses are source re-parks or identity. | No constructor type change beyond restricted `RebaseAtᴿ`. |
| `⊑conceal²` | Consumes `RebaseAtᴿ W′ W Xᴿ?`. | Example 12 target seal path, CenterCrossing input, SealPeel/TagBoundary probes. | Target wrapper; old target movement is disallowed. | Same shape, restricted premise. |
| `reveal⊑²` | Consumes `RebaseAtᴸ W W′ Xᴸ?`. | Left source wrappers, extra-cast inversion, examples. | Source wrapper; may re-park source, target frozen. | Same shape, restricted premise. |
| `conceal⊑²` | Consumes `RebaseAtᴸ W′ W Xᴸ?`. | Seal-transfer, probes, counterexample files. | Source wrapper; currently several probes use target-moving witnesses. | Same shape; target-moving callers must become negative records or be rewritten. |
| `reveal⊑reveal²` | Consumes paired `RebaseAt W Wᵖ Xᴸ Xᴿ`. | Example 12 checkpoint and left-path paired checkpoints. | Valid for same-world/source re-park; left-path has target-moving cases. | Same constructor; reject target-moving left-path witnesses. |
| `conceal⊑conceal²` | Consumes paired `RebaseAt Wᵖ W Xᴸ Xᴿ`. | Seal examples/probes and decay. | Same as paired reveal. | Same constructor; restricted paired rebase. |
| `Λ⊑Λ²`, `Λ⊑²` | Use `liftWorldBoth`/`liftWorldLeft`, not `RebaseAt`. | Compile proof, examples, extra-cast inversion. | Fresh binder movement only. | Keep; prove target frozen under lift by `zero = refl`, `suc = cong Fin.suc`. |
| All other term-imprecision constructors | No world-moving premise. | All downstream modules. | Neither. | No M2 change. |

## Auxiliary inventory

| Auxiliary | Current role | Downstream consumers | Movement classification | M2 action |
| --- | --- | --- | --- | --- |
| `sameWorldRebaseAt` | Builds identity rebase and discharges `anchorᴿ` by contradiction. | Example 12 same-world checkpoints, SourceStarProbe, Phase3DeepDives, ChainRide/SealPeel inner links. | Neither. | Keep; fill `ηᴿ-frozen` with `λ _ → refl`. |
| `anchorᴿ` | Allows target pivot movement when the old target center has a source occupant. | `CenterRename.renameRebaseAt`, `ExtraCastRight2.liftRebaseAt`, `ExtraCastRight2.composeSealRebase`, `SealTransferCore.composeSourceRebase`, `MovedLinkProbe`. | Target move enabler. | Delete.  Consumers shrink. |
| `ηᴿ-off-pivot` | Keeps non-pivot target variables fixed. | Decay, center rename, source-star/center-crossing refutations, repark. | Neither for non-pivots; paired with `anchorᴿ` for target pivot movement. | Replace calls with `ηᴿ-frozen Y`. |
| `seal-rebase-target` | Converts `RebaseAtᴸ Wᵖ W (just X)` plus `X ⊑ Y` into paired `RebaseAt Wᵖ W X Y`. | `ExtraCastRight2.target-seal-variable-view`, `right-inj-inversion²`, `SealTransferCore`, CenterCrossing probe. | Should preserve source re-park; does not need target movement. | Keep.  It still rules out `rebase-onlyᴸ`; result inherits `ηᴿ-frozen`. |
| `target-seal-rebase-source` | Converts `RebaseAtᴿ W₄ W₁ (just Y)` plus `X ⊑ Y` into paired `RebaseAt W₄ W₁ X Y`. | `SealTransferCore.seal-transfer`. | Should be target-frozen. | Keep; result is the incoming restricted `rb`. |
| `decayRebaseAt` | Transports a rebase through environment mark decay. | `TermImpDecay.⊢²-decay`, `ExtraCastRight2`, `SealTransferCore`. | Neither; decay keeps embeddings equal. | Reconstruct with the same `ηᴿ-frozen` proof. |
| `renameRebaseAt` | Renames center context around a rebase. | `CenterRename.⊢²-rename-center`. | Neither; embeds equality through center renaming. | Map `ηᴿ-frozen Y` with `rename-embedding-eq`. |
| `liftRebaseAt` | Lifts a rebase through a both-side type binder. | `ExtraCastRight2` and inversion code. | Fresh `zero`; old target variables become `suc`. | Replace lifted anchor by `ηᴿ-frozen zero = refl`, `ηᴿ-frozen (suc Y) = cong Fin.suc (...)`. |
| `liftRebaseAtᴸ` | Wrapper-level lift for source-side rebases. | `ExtraCastRight2`. | Mirrors underlying rebase; `rebase-onlyᴸ` still same-world. | Mechanical after `liftRebaseAt`. |
| `composeSealRebase` | Composes an outer source-seal rebase with an inner link. | `ExtraCastRight2.right-inj-inversion²`. | Currently composes target anchors. | Replace anchor composition with transitivity of `ηᴿ-frozen`. |
| `composeSourceRebase` | Same composition pattern in seal transfer. | `SealTransferCore`. | Currently composes target anchors. | Same transitivity replacement. |
| `Repark.reparkWorld` and `reparkRebaseAt*` | Reparks around an arbitrary old target pivot `Yₚ`. | No direct imports found outside `Repark.agda`; view code inside the module uses every wrapper constructor. | Target-moving old pivot. | Delete, park as obsolete design record, or replace with source-only/fresh-target parked evolution. Do not keep arbitrary target repark. |
| `CastTermImprecision2Typing` store lemmas | Read `sameRuntime` from rebases. | Typing-preservation support. | Neither. | Constructor arity update only. |
| `SealChainView.nodesOf` | Pattern matches wrapper constructors for diagnostic chain extraction. | Seal-chain diagnostics. | Neither; observes rebases but does not construct movement. | Pattern updates only. |
| `ParkedTargetStable`, `ParkedFreshZero`, `ParkedNoCrossing` | New sibling-session parked lemmas. | Volatile `proof/DGG/Parked/*`. | Encodes frozen old targets and fresh `zero`. | Align `RebaseAt.ηᴿ-frozen` with these lemmas. |

## Module audit

| Module | Rebase usage | Target-moving hits | M2 disposition |
| --- | --- | --- | --- |
| `WorldDecay` | Defines environment decay only. | None. | No semantic change. |
| `TermImpDecay` | `decayRebaseAt` plus recursive cases for all wrapper constructors. | None introduced by decay. | Add one field transport for `ηᴿ-frozen`. |
| `WorldSupport` | Support/agreement predicates. | None. | No direct change. |
| `CenterRename` | `renameRebaseAt`, `renameRebaseAtᴸ`, `renameRebaseAtᴿ`, term rename. | None; currently transports `anchorᴿ`. | Delete anchor transport; map frozen equality. |
| `Repark` | Reparks arbitrary target pivot and transports terms. | Yes, by design. | Not compatible with M2 as written; apparently unreferenced. Prefer removal/parking or source-only replacement. |
| `ExtraCastRight2` | Lift, `seal-rebase-target`, composition, inversion branches. | Anchor plumbing only; target movement is not needed for the intended inversion. | Shrinks: lift/compose become equality transport. |
| `SealTransferCore` | `target-seal-rebase-source`, `composeSourceRebase`, source seal transfer. | Anchor plumbing; residual H-multi interfaces may still assume target chains. | Keep source transfer; remove anchor composition; expect H-multi remnants to shrink or die. |
| `SealTransfer` | Thin consumer of `SealTransferCore`. | Indirect only. | Constructor arity updates. |
| `SealChain` | Interface record carries several `RebaseAt` assumptions. | H-multi/source-chain remnants can describe target-moving chains. | Treat as residual design surface; after M2 target-moving records are impossible. |
| `SealChainView` | Observes constructors. | None. | Pattern updates only. |
| `RightInjInversion` v1 | No direct rebase hits in the audit. | None found. | Only indirect dependency risk. |
| `Examples2` | Example 12, nat chain, left-path checkpoints. | Original Example 12 and nat chain are target-frozen source re-parks. Left-path `XZ -> YZ` rebases move old target centers. | Keep original Example 12; rewrite or retire target-moving left-path checkpoints. |
| `CompilePreservesImprecision2` | No direct rebase or wrapper constructors found by `rg`. | None. | Should survive unchanged except import/interface fallout. |
| `ReachabilityCatalog` | No direct rebase hits; depends on checkpoints. | Indirect via examples/deep dives. | Gate after examples are migrated. |
| `Phase3DeepDives` | Two `sameWorldRebaseAt` witnesses. | None. | Constructor arity update only. |
| `CenterCrossingProbe` | `rb-target-input` is source-moving with target fixed; `rb-outer` moves old target `Y₀`. | Yes: `rb-outer` / output-side analogue. | Flip moved-old-target premise to checked emptiness; keep stable input if still useful. |
| `SourceStarProbe` | Same-world rebases. | None. | Still valid as a separate refutation record. |
| `MovedLinkProbe` | Uses `anchorᴿ` to refute a moved target link. | Yes, negative only. | Refutation becomes immediate from `ηᴿ-frozen`. |
| `SealPeelProbe` | Outer and inner target input rebases move old target `Y`. | Yes. | Convert to negative/stale design record or rewrite using source re-parking. |
| `TagBoundaryProbe` | Target-side wrappers but target embeddings are fixed. | None found. | Should migrate with constructor arity updates. |
| `ChainRideProbe` | `raₗ` and `link₂` model an H-multi chain. | Yes: target `Y` moves through the chain. | This becomes impossible under M2; keep only as obsolete/refutation record if needed. |
| `ExtraCastRight2Counterexample` | `Z-Y-rebase` and `Z-Y-rebaseᵈ` move old target `Y`. | Yes. | Becomes impossible; retain only as stale-mark design history if wanted. |
| `LambdaImpProbe` | Uses `rebase-onlyᴸ`; also refutes aligned rebases. | None. | Unchanged except constructor arity in negative mentions. |

## Scratch statement validation

The root scratch module models the restricted surface over the current live
relation:

- `TargetFrozen W W′ = ∀ Y → ηᴿ W Y ≡ ηᴿ W′ Y`.
- `RebaseAtᵣ` packages a current `CTI2.RebaseAt` plus `TargetFrozen`.
- Restricted `RebaseAtᴸᵣ` and `RebaseAtᴿᵣ` expose only identity, variable
  rebase through `RebaseAtᵣ`, and existing `rebase-onlyᴸ`.
- Restricted wrappers `⊑reveal²ᵣ` and `reveal⊑reveal²ᵣ` forget the wrapper and
  call the current constructors, so the examples validate the proposed statement
  without changing the live relation.

Checked results:

- `example12-function-checkpoint₁ᵣ` rebuilds the representative Example 12
  source re-parking path with target centers frozen.  The needed rebases
  `X -> Z`, `Z -> Y`, and same-world `X` all supply `λ _ → refl` for
  `TargetFrozen`.
- `no-center-crossing-pairedᵣ` proves that the moved-old-target paired rebase
  shape `RebaseAtᵣ CCP.W′ CCP.W Fin.zero Fin.zero` is empty.
- `no-center-crossing-outerᴿᵣ` proves that the target-wrapper shape
  `RebaseAtᴿᵣ CCP.W′ CCP.W (just Fin.zero)` is empty.
- `compile-preserves-imprecision²-gate` has the exact current type
  `CPI2.compile-preserves-imprecision²-statement` and is discharged by the live
  `compile-preserves-imprecision²` theorem.

Important naming nuance: the current `CenterCrossingProbe.input-target-seal-variable`
itself uses `rb-target-input : RebaseAt Wᵖ W′ X₁ Y₀`, where target `Y₀` is
already stable.  The actual crossing freedom exploited by the refutation arc is
the outer/output premise `rb-outer : RebaseAt W′ W X₀ Y₀` and its target-wrapper
analogue; those are exactly the shapes refuted in scratch.

## Implementation migration plan

1. Edit `CastTermImprecision2.agda`.
   Replace `ηᴿ-off-pivot` and `anchorᴿ` with `ηᴿ-frozen`.
   Update `sameWorldRebaseAt` and all local `rebase-at` witnesses.
   Expected breakage: constructor arity and field-name errors.

2. Update direct example witnesses.
   Original Example 12 and nat-chain rebases should use `λ _ → refl`.
   Same-world witnesses use `sameWorldRebaseAt`.
   Left-path `XZ -> YZ` witnesses that move target centers must be rewritten as
   source re-parking checks or retired from the gate if they only document the
   rejected behavior.

3. Update transport modules.
   In `TermImpDecay`, pass through `ηᴿ-frozen`.
   In `CenterRename`, use `rename-embedding-eq π (ηᴿ-frozen rb Y)`.
   In `ExtraCastRight2.liftRebaseAt`, prove frozen targets by cases on the
   lifted variable: `zero = refl`, `suc Y = cong Fin.suc (...)`.

4. Update seal rebase extraction.
   Keep `seal-rebase-target`; it remains the proof that a source-side
   `rebase-varᴸ` plus an `X⊑X` obligation reveals the paired pivot, and it still
   rules out `rebase-onlyᴸ`.
   Keep `target-seal-rebase-source`; it should just return the incoming
   restricted paired rebase after the same alignment inversion.

5. Update composition.
   In `composeSealRebase` and `composeSourceRebase`, delete the anchor-search
   branches and compose target frozen equalities by `trans`.

6. Retire target-repark machinery.
   `Repark.agda` currently exists to repark arbitrary old target pivots.  That
   operation contradicts M2.  Since no external imports were found, either remove
   it from the active surface or replace it with source-only/fresh-target parked
   evolution lemmas.

7. Convert probes and stale counterexamples.
   `CenterCrossingProbe`, `MovedLinkProbe`, `SealPeelProbe`, `ChainRideProbe`,
   and `ExtraCastRight2Counterexample` should no longer build positive
   target-moving rebases.  Keep the useful ones as negative design records, with
   contradictions from `ηᴿ-frozen`.

8. Sweep observers and typing helpers.
   `CastTermImprecision2Typing` needs field/constructor updates only.
   `SealChainView` needs pattern updates only.
   `RightInjInversion` v1 had no direct hits in this audit, but should be
   checked after the dependent modules move.

9. Run the full M2 gates.
   Use the plan's command shape:
   `AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 <file>`.

Gate list:

- `GTSFImp/proof/DGG/CastTermImprecision2.agda`
- `GTSFImp/proof/DGG/Examples2.agda`
- `GTSFImp/proof/DGG/CompilePreservesImprecision2.agda`
- `GTSFImp/proof/DGG/ReachabilityCatalog.agda`
- `GTSFImp/proof/DGG/Phase3DeepDives.agda`
- `GTSFImp/proof/DGG/WorldDecay.agda`
- `GTSFImp/proof/DGG/TermImpDecay.agda`
- `GTSFImp/proof/DGG/WorldSupport.agda`
- `GTSFImp/proof/DGG/CenterRename.agda`
- `GTSFImp/proof/DGG/ExtraCastRight2.agda`
- `GTSFImp/proof/DGG/SealTransferCore.agda`
- `GTSFImp/proof/DGG/SealTransfer.agda`
- `GTSFImp/proof/DGG/SealChain.agda`
- `GTSFImp/proof/DGG/SealChainView.agda`
- `GTSFImp/proof/DGG/CastTermImprecision2Typing.agda`
- `GTSFImp/proof/DGG/RightInjInversion.agda`, if still part of the active gate
- active probes kept as design records
- volatile `GTSFImp/proof/DGG/Parked/*.agda` after the sibling session settles

Do not rely on `GTSFImp/All.agda` during the concurrent parked-file work unless
the sibling session has stopped changing it.

## Expected shrinkage

- Delete the `anchorᴿ` field and all anchor transport/composition code.
- `CenterRename.renameRebaseAt` loses the local `renamed-anchor` proof.
- `ExtraCastRight2.liftRebaseAt` loses `lift-anchor`.
- `ExtraCastRight2.composeSealRebase` and
  `SealTransferCore.composeSourceRebase` lose their anchor-search branches.
- `MovedLinkProbe` no longer needs an anchor-specific refutation.
- `Repark.agda` is the strongest deletion candidate because it implements the
  old arbitrary-target-repark operation and appears unreferenced.
- `SealChain` H-multi remnants and parts of `SealTransferCore` should shrink
  once target crossing is impossible instead of merely anchored.

## Verification transcript

Scratch typecheck:

```text
$ AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 M2RebaseRedesignScratch.agda
$
```

Line-length check for scratch:

```text
$ awk 'length($0)>80 { print FNR ":" length($0) ":" $0 }' M2RebaseRedesignScratch.agda
$
```

Compile theorem rebase audit:

```text
$ rg -n "rebase|RebaseAt|⊑reveal²|⊑conceal²|reveal⊑²|conceal⊑²|reveal⊑reveal²|conceal⊑conceal²" GTSFImp/proof/DGG/CompilePreservesImprecision2.agda
# no matches
```

`Repark` external-use audit:

```text
$ rg -n "import proof\\.DGG\\.Repark|open import proof\\.DGG\\.Repark|proof\\.DGG\\.Repark" GTSFImp/proof/DGG GTSFImp/All.agda
GTSFImp/proof/DGG/Repark.agda:1:module proof.DGG.Repark where
```

Repository status relevant to this pass:

```text
?? GTSFImp/proof/DGG/Parked/
?? M2RebaseRedesignScratch.agda
?? M2-REBASE-REDESIGN.md
```

The `Parked/` directory is from the concurrent sibling session and was not
edited in this pass.

## Pre-flight: left-path rebuilds

Enumeration of moved-old-target witnesses in `Examples2`:

- `left-path-rebase-XZ-to-YZ-Y₃` moves target `Y` from center `0` in
  `left-path-world₃` to center `1` in `left-path-world₃-YZ`.
- `left-path-rebase-XZ-to-YZ-Y₄` moves target `Y` from center `0` in
  `left-path-world₄` to center `1` in `left-path-world₄-YZ`.

The affected checkpoints are exactly the transitive users of those witnesses:

- `left-path-checkpoint₃`: rebuilt as `left-path-checkpoint₃-YZᵣ`.
- `left-path-checkpoint₄`: rebuilt as `left-path-checkpoint₄-YZᵣ`.
- `left-path-checkpoint₅`: rebuilt as `left-path-checkpoint₅-YZᵣ`.
- `left-path-checkpoint₆`: rebuilt as `left-path-checkpoint₆-YZᵣ`.
- `left-path-checkpoint₇`: rebuilt as `left-path-checkpoint₇-YZᵣ`.
- `left-path-checkpoint₈`: rebuilt as `left-path-checkpoint₈-YZᵣ`.
- `left-path-checkpoint₉`: rebuilt as `left-path-checkpoint₉-YZᵣ`.
- `left-path-checkpoint₁₀`: rebuilt as `left-path-checkpoint₁₀-YZᵣ`.

All eight rebuilds type-check under the scratch restricted surface:
`RebaseAtᵣ` packages the live `RebaseAt` with `TargetFrozen`, Y/Z rebases are
same-world parked rebases, and the X boundary uses `rebase-onlyᴸᵣ`.  The
semantic term pairs and reduction-step endpoints are the same as the live
checkpoints, but the baked XZ conclusions were replaced by the parked YZ worlds
where target centers do not move.

Not in the moved-target set: `left-path-checkpoint₀` through
`left-path-checkpoint₂` are pre-XZ/YZ, and `left-path-checkpoint₁₁` through
`left-path-checkpoint-final` do not transitively use either
`left-path-rebase-XZ-to-YZ-Y₃` or `left-path-rebase-XZ-to-YZ-Y₄`.

Pre-flight transcript:

```text
$ rg -n "left-path-rebase-XZ-to-YZ-Y[₃₄]|left-path-Y-revealed|left-path-argument-Y|left-path-Y-unsealed" GTSFImp/proof/DGG/Examples2.agda
# hits are the two moved rebases and their helper users

$ AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 M2RebaseRedesignScratch.agda
$

$ awk 'length($0) > 80 { printf "%d:%d:%s\n", NR, length($0), $0 }' M2RebaseRedesignScratch.agda
$
```

Outcome: no resisters.  The left-path examples were documenting admissible
source-side parking choices, not a need for M2 to preserve old-target movement.
