# Rep-`★` Partner Tightening Pre-flight 3

Scope:

- Root scratch only: `Tighten3PreflightScratch.agda`.
- No edits under `GTSFImp/`.
- Checked against the round-2 tightening tree on
  `agent/gtsf-extra-cast-right`.

Toolchain:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 <file>
```

## Candidate Modeled

The scratch models a premise-world partner surface:

- `Rep★PartnerOK₃ Wᵖ X P Xᴿ? M′`.
- `SealPartnerOK₃ Wᵖ X P R Xᴿ? M′`.
- `SourceConcealPartnerOK₃ Wᵖ P c Xᴿ? M′`.

The alignment-bearing clauses use the premise world `Wᵖ`:

- `rep★-outer-var-tag₃` requires `CenterAligned₃ Wᵖ X Y`.
- `rep★-matched-inner-tags₃` requires `CenterAligned₃ Wᵖ X₂ Y₂`.
- `star-rep-target₃` and `seal-partner-ok₃` carry that premise-world
  evidence through.  `name-protected-target₃` has no alignment premise.

Main scratch locations:

- Predicate model: `Tighten3PreflightScratch.agda:54`.
- Premise-world decay sanity check: `Tighten3PreflightScratch.agda:135`.
- `TargetChainProof:85` shape: `Tighten3PreflightScratch.agda:186`.
- Explicit `X₂ = X` shape: `Tighten3PreflightScratch.agda:209`.
- `TargetDescentProof:138` shape: `Tighten3PreflightScratch.agda:230`.
- `RightInjInversion2Proof:612` shape:
  `Tighten3PreflightScratch.agda:250`.
- No-target and worker payoff shapes:
  `Tighten3PreflightScratch.agda:274`, `:287`, `:305`, and `:321`.
- Bare-payload variable-tag mismatch exclusion:
  `Tighten3PreflightScratch.agda:336`.

## Verdict Table

| Check | Verdict | Evidence |
|---|---|---|
| `TargetChainProof:85` partner obligation | **Pass in scratch under premise-world formulation.** | `target-chain-85-partner₃` consumes `p₂ : ＇ X₂ ⊑ᵂ⟨ Wᵖ ⟩ ＇ Y₂`; it does not need to transport alignment back to conclusion world `W`. |
| `TargetChainProof:85`, same-name path `X₂ = X` | **Pass.** | `target-chain-85-same-pivot-partner₃` proves the exact reachable case where payload tag and seal pivot share the source name. |
| `TargetDescentProof:138` shape | **Pass.** | `target-descent-138-partner₃` is the same premise-world witness over `W′`; this agrees with the current explicit-premise direction. |
| `RightInjInversion2Proof:612` shape | **Pass.** | `right-inj-612-partner₃` consumes the branch's already-extracted premise-world alignment. The current live proof also still checks by restructuring. |
| Source-strip worker no-target variable tag | **Pass; still formation-impossible.** | `source-seal-var-tag-no-target-empty₃` excludes `SourceConcealPartnerOK₃ Wᵖ ... nothing (U₂⟨Y₂!⟩)`. |
| Source-strip worker post-cast variant | **Pass; still formation-impossible.** | `source-seal-var-tag-no-target-after-cast-empty₃` preserves the same impossibility after an inert source cast. |
| ℕ-payload/no-target shape | **Pass; still formation-impossible.** | `nat-payload-var-tag-no-target-empty₃` still reduces to no-target variable-tag emptiness. |
| Bare-payload variable-tag mismatch poison | **Pass for the modeled mismatch.** | `bare-payload-var-tag-mismatch-empty₃` excludes the case when the source is not an inner var-tag payload and the target var tag is not premise-world aligned to the outer source pivot. |
| Prior probe/example/catalog gates | **Pass unmodified.** | See command transcript below. The root scratch also imports gates for `StarRepChainProbe`, `Examples2`, `InitialPairScratch`, and `CompilePreservesImprecision2`. |
| Live `TargetChainProof` | **Still blocked, as expected.** | `GTSFImp/` was not edited; the live file still has the known implicit `partner` meta at `TargetChainProof.agda:85,10-33`. |

Bottom line: the candidate is viable for the round-3 blocker, including the
reachable `X₂ = X` trace shape.  The make-or-break worker emptiness payoff did
not regress.

## Constructor Use-Site Classification

`CompilePreservesImprecision2.agda` has no direct uses of
`rep★-var-tag`, `rep★-matched-inner-tags`, `star-rep-target`,
`plain-target`, `name-protected-target`, or `seal-partner-ok`; the initial
derivations do not hold conclusion-only partner evidence.

| Site | Constructor use | World evidence held | Premise-world impact |
|---|---|---|---|
| `SealTransferCore.agda:131-136` | `dynRep★PartnerOK` pattern/rebuilds `rep★-*` | Carries whatever world the input partner has. | OK if the input partner is reindexed to the relevant premise world before decay. |
| `SealTransferCore.agda:145-148` | `stripSealRep★PartnerOK` rebuilds `rep★-*` | Carries input partner world. | OK for untagged/nonvar/outer-var paths; matched-inner cannot arise from a stripped source seal by formation. |
| `SealTransferCore.agda:377-379` | Re-emits `seal-partner-ok (star-rep-target ...)` | Current code builds from `partner` at the outer transfer world and decays to `dynWorld W₁`. | **Needs live refactor.** Under the candidate, this recursive `conceal⊑²` premise is `dynWorld Wᵖ`, so the partner must come from or be decayed to the premise world, not `dynWorld W₁`. |
| `TermImpDecay.agda:130-160` | Decay pattern/rebuild for `rep★-*`, `star-rep-target`, `plain-target`, `name-protected-target`, `seal-partner-ok` | Current helper decays `ok` with the outer-world decay. | **Needs small live edit.** If `conceal⊑²` stores premise-world `ok`, the `tag-rebase-varᴸ` branch should decay it with `blend-decay {W′ = W′}`; scratch `decaySourceConcealPartnerOK₃` checks the local transport. |
| `TargetWalkSupport.agda:765-795` | Partner-view destructors | Holds evidence from the input partner. | Needs index plumbing only: the view should expose premise-world rep evidence when the input rule stores premise-world evidence. |
| `TargetWalkSupport.agda:829-830` | `plain-target not-↓` re-emission | No alignment evidence. | OK at any premise world. |
| `SourceStripProof.agda:75-77` | `rep★-var-tag (RebaseAt.pivotAligned rb)` | **Conclusion-world** evidence, because `RebaseAt Wᵖ Wᵒ X Y` stores `pivotAligned` in `Wᵒ`. | **Hazard.** For the premise-world relation, either use a premise-world alignment if one is available, or switch this target shape to `name-protected-target`, which requires no alignment. |
| `SourceStripWorkerProof.agda:242` | `plain-target not-↓` | No alignment evidence. | OK at any premise world. |
| `SourceStripWorkerProof.agda:362` | Bare `star-rep-target` in the still-open worker area | No explicit partner evidence. | Remains intentionally not discharged by the candidate; the scratch no-target lemmas show the bad variable-tag cases are still unformable. |
| `RightInjInversion2Proof.agda:523-524` | `plain-target not-↓` | No alignment evidence. | OK at any premise world. |
| `RightInjInversion2Proof.agda:584-585` | `plain-target not-↓` | No alignment evidence. | OK at any premise world. |
| `StarRepChainProbe.agda:183-184` | `rep★-nonvar-tag nonvar-base` | No alignment evidence. | OK at any premise world. |
| `ChainRideProbe.agda:203-204` | `rep★-nonvar-tag nonvar-base` | No alignment evidence. | OK at any premise world. |
| `TagBoundaryProbe.agda:210-211` | `rep★-nonvar-tag nonvar-base` | No alignment evidence. | OK at any premise world. |
| `TerminusRebuildProbe.agda:394-395` | `rep★-nonvar-tag nonvar-fun` | No alignment evidence. | OK at any premise world. |
| `TerminusRebuildProbe.agda:429-431` | `rep★-var-tag (pivotAligned rb-X-Y)` | Same-world evidence; here premise and conclusion are both `W`. | OK as written for this example; the target is also `name-protected-target`-shaped if that path is preferred. |
| `Examples2.agda:2066` | `plain-target ()` in an emptiness proof | No alignment evidence. | OK at any premise world. |
| `ExtraCastRight2Counterexample.agda:235` | `plain-target ()` in an emptiness proof | No alignment evidence. | OK at any premise world. |
| `LambdaImpProbe.agda:220` | `plain-target ()` in an emptiness proof | No alignment evidence. | OK at any premise world. |
| `TerminusRebuildProbe.agda:200` | `plain-target ()` in a helper emptiness proof | No alignment evidence. | OK at any premise world. |

No live use site currently constructs `rep★-matched-inner-tags` directly; the
scratch witnesses show where it would be used for the three stopped shapes.

## Command Transcript

Successful checks:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 Tighten3PreflightScratch.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/Examples2.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/StarRepChainProbe.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 InitialPairScratch.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/CompilePreservesImprecision2.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/ChainRideProbe.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/TagBoundaryProbe.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/TerminusRebuildProbe.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/LambdaImpProbe.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/Phase3DeepDives.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/Parked/ParkedD4CheckpointLemma.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/ReachabilityCatalog.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/CompileImageShape.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/CastTermImprecision.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/TermImpDecay.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/TargetWalkSupport.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/TargetDescentProof.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/RightInjInversion2Proof.agda
```

Expected stopped checks without live wiring:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/TargetChainProof.agda
# unsolved meta: TargetChainProof.agda:85,10-33

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda
# blocked through imported TargetChainLemma/TargetChainProof.agda:85,10-33
```
