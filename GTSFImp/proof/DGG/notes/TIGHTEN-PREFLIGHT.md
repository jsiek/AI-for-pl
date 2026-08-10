# Rep-`★` Partner Tightening Pre-flight

Scope:

- Root scratch only: `TightenPreflightScratch.agda`.
- No edits under `GTSFImp/`.
- No commits.
- Checked with:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 TightenPreflightScratch.agda
```

Result: the scratch type-checks.

## Tightened Predicate

The scratch packages the current live rule behind a stricter predicate:

```agda
CenterAligned W X Y =
  toRenameᵗ (CTI2.ηᴸʷ W) X ≡ toRenameᵗ (CTI2.ηᴿʷ W) Y
```

`Rep★PartnerOK W X Xᴿ? M′` admits:

- `rep★-untagged`: `M′` is not a top-level tag.
- `rep★-nonvar-tag`: `M′` is a top-level injection at a non-variable ground.
- `rep★-var-tag`: `M′` is a top-level injection at `＇ Y`, with
  `Xᴿ? = just Y` and `CenterAligned W X Y`.

The scratch then derives restricted wrappers:

- `SealPartnerOKᵀ`
- `SourceConcealPartnerOKᵀ`
- `conceal⊑²ᵀ`

These forget back to the current `CTI2` relation, so this is a pre-flight
package and not a live relation edit.

Relevant checked scratch locations:

- Tightened predicate: `TightenPreflightScratch.agda:63`.
- Restricted wrapper: `TightenPreflightScratch.agda:89`.
- Restricted `conceal⊑²ᵀ`: `TightenPreflightScratch.agda:163`.
- No-target variable tag impossible: `TightenPreflightScratch.agda:424`.
- Misaligned variable tag impossible: `TightenPreflightScratch.agda:447`.
- Misaligned variable `TagRebaseAtᴸ` impossible:
  `TightenPreflightScratch.agda:459`.

## Verdict

**INVALID AS A DIRECT TIGHTENING.**

The concrete probes mostly survive, but the proven generic transfer machinery
does not. `SealTransferCore.agda` has a reachable generic re-emission of
`star-rep-target` against an arbitrary `U`; under the tightening, there is no
available proof that `U` is untagged, non-variable-tagged, or aligned
variable-tagged.

## Gate Table

| Gate | Verdict | Evidence |
| --- | --- | --- |
| Examples2 `star-rep-target` scan | passes-as-is | `rg -n "star-rep-target" GTSFImp/proof/DGG/Examples2.agda` has no hits. |
| Example 12 checkpoints | passes-as-is | Imported gates check in `TightenPreflightScratch.agda:358` through `379`; no direct rep-`★` partner use. |
| Examples2 nat-chain | passes-as-is | Imported gates check in `TightenPreflightScratch.agda:381` through `389`; no direct rep-`★` partner use. |
| Examples2 left-path | passes-as-is | Live checkpoints `0..3` and final check in `TightenPreflightScratch.agda:391` through `394`. The old checkpoint `4..14` block is commented out upstream; the exported final endpoint survives. |
| Catalog initial/checkpoint derivations touching rep-`★`-style seals | passes-as-is | Imported gates check in `TightenPreflightScratch.agda:397` through `407`: adversarial source chain initial/checkpoint, skew/tag-boundary star-inst initial, star-inst checkpoint, higher-order-shared-arg initial, and D4 checkpoint. No direct `star-rep-target` hit in these catalog files. |
| TerminusRebuildProbe Instance A input/output | passes-as-is | Instance A output uses paired seal transfer, and the direct `dyn-id` input is negative/empty. No tightened rep-`★` partner needed. |
| TerminusRebuildProbe Instance B inner source seal | passes-as-is via non-variable tag | Inner partner is `U₀ = dyn-id`, a top-level function injection, so it uses `rep★-nonvar-tag` in `terminus-B-inner-okᵀ` at `TightenPreflightScratch.agda:186`. |
| TerminusRebuildProbe Instance B output | passes-as-is | Rebuilt as `terminus-B-outputᵀ` at `TightenPreflightScratch.agda:222`; it goes through the checked inner non-variable-tag gate and paired seals. |
| TerminusRebuildProbe Instance B tagged input | passes-via-alignment-clause | `InstanceB` placement says `W: X=0, Y=0, Y₂=1`; `Wᵖ: X=1, Y=0, Y₂=1`. The outer tag `Y` is aligned with source `X` in `W`, checked by `terminus-B-X/Y-aligned` at `TightenPreflightScratch.agda:253`; tagged input rebuilt at `TightenPreflightScratch.agda:267`. The inner `Y₂` is aligned with `X` in `Wᵖ`. |
| StarRepChainProbe dependency | passes-as-is via non-variable tag | The source rep-`★` partner is `$0 ⟨ℕ!ᴿ⟩`, a non-variable `ℕ` tag. Rebuilt output: `star-rep-chain-outputᵀ` at `TightenPreflightScratch.agda:304`. |
| ChainRideProbe dependency | passes-as-is via non-variable tag | The source rep-`★` partner is a non-variable `ℕ` tag. Rebuilt premise: `chain-ride-premiseᵀ` at `TightenPreflightScratch.agda:324`. |
| TagBoundaryProbe dependency | passes-as-is via non-variable tag | The source rep-`★` partner is a non-variable `ℕ` tag. Rebuilt seal: `tag-boundary-source-seal²ᵀ` at `TightenPreflightScratch.agda:344`. |
| InitialPairScratch `mid-output` | passes-as-is via non-variable tag | Rebuilt through `StarRepChainProbe` as `initialpair-mid-outputᵀ` at `TightenPreflightScratch.agda:413`. |
| InitialPairScratch `mid-input` | passes-as-is | Imported gate checks at `TightenPreflightScratch.agda:417`; its rep-`★` dependency is the same non-variable `ℕ` tag path. |
| InitialPairScratch `initial-Pᶜ⊑Qᶜ` | passes-as-is | Imported gate checks at `TightenPreflightScratch.agda:418`; no new rep-`★` obligation. |
| SourceStripProof direct use | passes-via-alignment-clause | `SourceStripProof.agda:75` re-emits through `CTI2.tag-rebase-varᴸ rb`; this carries alignment and maps to the tightened variable-tag branch. |
| TargetDescentProof | FAIL, inherited from `SealTransferCore` | No direct `star-rep-target` hit, but it imports and relies on `SealTransferCore` for target-star peel. |
| TargetChainProof | FAIL, inherited from `SealTransferCore` | No direct `star-rep-target` hit, but it imports and relies on `SealTransferCore`. |
| TargetStripProof | FAIL, inherited from `SealTransferCore` | No direct `star-rep-target` hit, but it imports and relies on `SealTransferCore`. |
| SealTransferCore | **FAIL** | Reachable generic derivation at `GTSFImp/proof/DGG/SealTransferCore.agda:351` re-emits a source rep-`★` seal against arbitrary `U`. Tightening needs a `Rep★PartnerOK ... U`, but only `Value U` is available. |
| TargetWalkSupport direct view | needs refinement, not a construction gate | Direct classifications at `TargetWalkSupport.agda:760` and `783` currently collapse all current `star-rep-target` uses to one view. A tightened live relation would need a refined view, but the construction failure is already in `SealTransferCore`. |
| Payoff: plain star-rep head with no aligned target variable | formation-impossible checked | `plain-star-rep-head-no-target-empty` at `TightenPreflightScratch.agda:467`. |
| Payoff: injected star-rep head with no aligned target variable | formation-impossible checked | `injected-star-rep-head-no-target-empty` at `TightenPreflightScratch.agda:481`. |
| Payoff: variable-ground tag with misalignment | formation-impossible checked | Direct rep-`★` emptiness at `TightenPreflightScratch.agda:447`; full `TagRebaseAtᴸ` misalignment emptiness at `TightenPreflightScratch.agda:459`. |

## Failing Derivation

The failing reachable/proven gate is the generic branch of
`SealTransferCore.agda`:

```agda
CTI2.conceal⊑²
  (CTI2.seal-partner-ok CTI2.star-rep-target)
  (dyn-mono {W = W₁} {W′ = Wᵖ})
  (CTI2.tag-rebase-varᴸ
    (TD.decayRebaseAt (SPT.dynWorld-decay Wᵖ)
      (SPT.dynWorld-decay W₁) rbᵖ))
  (WD.decaySameCtx (SPT.dynWorld-decay W₁)
    (SPT.dynWorld-decay Wᵖ) scᵖ)
  (CTI2.⊢↓-sealˣ Z∈′)
  (TD.⊢²-decay (SPT.dynWorld-decay Wᵖ) prem)
  (dyn-var-star {W = W₁} {X = Z})
```

The target partner there is the arbitrary `U` from the transferred premise.
The branch has `Value U`, but it has no top-level target-shape classifier and
no alignment proof if `U` is a variable-ground tag. Therefore the tightened
predicate cannot be supplied generically.

## Bottom Line

The tightened condition is effective for the intended open worker shapes:
unaligned/no-target variable-ground tag heads are impossible. However, it is not
valid as a drop-in tightening of the live relation because `SealTransferCore`
is reachable proven machinery and fails without additional classification or a
different re-emission strategy.
