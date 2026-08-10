# Rep-`★` Partner Tightening Pre-flight 5

Scope:

- Root scratch only: `Tighten5PreflightScratch.agda`.
- No source edits under `GTSFImp/`.
- Checked on branch `agent/gtsf-extra-cast-right`.

Toolchain:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 <file>
```

## Candidate Modeled

The scratch relation `Rep★PartnerOK₅` orthogonalizes the tag cases:

- `rep★-matched-inner-tags₅` now requires `X₂ ≢ X`, so it only records
  non-pivot inner source tags.
- Same-pivot source tags are represented by `rep★-round-trip₅`, with the
  exposed value equality supplied in scratch by `same-pivot-value-round-trip₅`.
- Transport is restricted to the paired target pivot `just Y`; this is the
  surface needed by `MatchedConcealPartnerOK` and avoids the invalid arbitrary
  target-pivot transport for `rep★-var-tag`.

## Verdict Table

| Check | Verdict | Evidence |
|---|---|---|
| Scratch type-checks | **Pass** | `Tighten5PreflightScratch.agda` checks with the requested toolchain. |
| Matched-inner restriction | **Pass** | `rep★-matched-inner-tags₅` at `Tighten5PreflightScratch.agda:64` carries `X₂ ≢ X`; there is no same-source-pivot matched-inner constructor. |
| Transport principle totality | **Pass** | `transportRep★PartnerOK₅` at `:234` covers all constructors. The matched-inner branch uses `transport-non-pivot-aligned₅` at `:223`; the round-trip branch recurses structurally. |
| Dyn-decayed transport | **Pass** | `transportRep★PartnerOK-dyn₅` at `:254` applies the same induction after `TD.decayRebaseAt (SPT.dynWorld-decay Wᵖ) (SPT.dynWorld-decay W) rb`. |
| Same-pivot round-13 head | **Pass in scratch; live still red until wired.** | `same-pivot-value-round-trip₅` at `:299` and `round13-same-pivot-matched-conceal₅` at `:313` replace the old `alignedᵖ : CenterAligned Wᵖ X Y₂` same-pivot matched-inner path by a round-trip witness. |
| Non-pivot round-13 head | **Pass** | `round13-non-pivot-matched-conceal₅` at `:330` transports the restricted matched-inner witness using `X₂ ≢ X`. |
| One-common-world tagged-transfer package | **Pass** | `TaggedTransferOutput₅` at `:357` stores both the premise and `MatchedConcealPartnerOK₅` in the same world; `tagged-transfer-output-dyn₅` at `:378` builds it via dyn transport. |
| `TargetChainProof:88` emission shape | **Pass in scratch; live still red until wired.** | `target-chain-88-emits₅` at `:392` erases the scratch partner to live `CTI2.MatchedConcealPartnerOK` and constructs the actual `CTI2.conceal⊑conceal²` output. |
| Emptiness payoffs | **Pass** | `var-tag-no-target-empty₅`, `nat-payload-var-tag-no-target-empty₅`, `source-seal-var-tag-no-target-empty₅`, and the after-cast variant at `:415`, `:430`, `:448`, `:464` type-check. |
| Poison and laundering exclusions | **Pass** | Bare payload, different-name round-trip, and non-`★` round-trip exclusions at `:483`, `:521`, `:556` type-check. The non-`★` matched-inner subcase now closes directly by `X ≢ X`. |
| Same-name matched-inner use sites | **Pass / no live re-derivation sites found.** | `rg` found no direct `CTI2.rep★-matched-inner-tags` construction in `StarRepChainProbe`, `Examples2`, or `ReachabilityCatalog`. `Examples2` matched-star sites use `rep★-nonvar-tag` and `rep★-untagged`; those gates pass. |

No transport induction case failed. In particular, the potentially bad
same-pivot matched-inner case is absent by construction; it must be represented
as a `rep★-round-trip₅` witness.

## Gate Table

| Command target | Result | Note |
|---|---|---|
| `Tighten5PreflightScratch.agda` | Pass | Candidate model checks. |
| `GTSFImp/proof/DGG/CastTermImprecision2.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/TermImpDecay.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/SealTransferCore.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Inversion/TargetWalkSupport.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/StarRepChainProbe.agda` | Pass | No matched-inner re-derivation needed. |
| `GTSFImp/proof/DGG/ChainRideProbe.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/TagBoundaryProbe.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/TerminusRebuildProbe.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/LambdaImpProbe.agda` | Fail | Existing mismatch at `LambdaImpProbe.agda:234`: `ok` is in `probe-world₀`-embedding shape, but the clause expects `SourceConcealPartnerOK probe-world₁ ...`. Not a round-trip re-derivation failure. |
| `GTSFImp/proof/DGG/Examples2.agda` | Pass | Matched-star uses are `rep★-nonvar-tag`/`rep★-untagged`, not same-name matched-inner. |
| `GTSFImp/proof/DGG/Phase3DeepDives.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Parked/ParkedD4CheckpointLemma.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/ReachabilityCatalog.agda` | Pass | No direct matched-inner construction found. |
| `GTSFImp/proof/DGG/CompileImageShape.agda` | Pass | Read-only gate. |
| `InitialPairScratch.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/CompilePreservesImprecision2.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Inversion/TargetDescentProof.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Inversion/RightInjInversion2Proof.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Inversion/TargetChainProof.agda` | Fail | Known live red at `TargetChainProof.agda:88`; scratch confirms the needed partner/package shape but it is not wired into `GTSFImp/`. |
| `GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda` | Fail | Fails through imported `TargetChainProof.agda:88`. |

## Bottom Line

The candidate is viable in scratch. The transport principle works once
`matched-inner` is restricted to `X₂ ≢ X`, and the same-pivot case is handled
by the recursive round-trip constructor. The full output package that
`TargetChainProof:88` needs is modeled with one common world and erases to the
current live paired-conceal constructor shape.

The live tree is not globally green because `TargetChainProof:88` still needs
the new package wired into `GTSFImp/`, `SourceStripWorkerProof` imports that red
head, and `LambdaImpProbe.agda:234` has a separate world-index mismatch.
