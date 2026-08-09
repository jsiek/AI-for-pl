# Rep-`★` Partner Tightening Pre-flight 4

Scope:

- Root scratch only: `Tighten4PreflightScratch.agda`.
- No edits under `GTSFImp/`.
- Checked on branch `agent/gtsf-extra-cast-right`.

Toolchain:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 <file>
```

## Candidate Modeled

The scratch uses a structurally recursive same-name see-through constructor:

```agda
rep★-round-trip₄ :
  Rep★PartnerOK₄ Wᵖ X P Xᴿ? M′ →
  Rep★PartnerOK₄ Wᵖ X ((P ↓ seal X ★)⟨X!⟩) Xᴿ? M′
```

The restriction is syntactic in the constructor result:

- the wrapper seal name is the same source name `X` being formed;
- the wrapper tag ground is the same variable ground `＇ X`;
- the wrapper seal representation is exactly `★`.

There is no see-through clause for `(P ↓ seal Z ★)⟨Z!⟩` when `Z` is not the
formed source seal name, and no see-through clause for `(P ↓ seal X R)⟨X!⟩`
when `R` is non-`★`.

The analogous source/matched conceal surfaces are modeled by
`source-round-trip-seal-star₄` and `matched-round-trip-seal-star₄`; both route
through `rep★-round-trip₄` instead of adding broader arbitrary-conceal
see-through.

## Verdict Table

| Check | Verdict | Evidence |
|---|---|---|
| T4 scratch type-checks | **Pass** | `Tighten4PreflightScratch.agda` checks with the requested toolchain. |
| Same-name rep-`★` see-through | **Pass** | `rep★-round-trip₄` at `Tighten4PreflightScratch.agda:85` is strictly positive and preserves the carried partner evidence. |
| Analogous conceal partner predicates | **Pass** | `source-round-trip-seal-star₄` and `matched-round-trip-seal-star₄` at `:165` and `:179` rewrap only the same-name star-seal case. |
| `TargetChainProof:88` blocked head | **Pass in scratch; live still red.** | `target-chain-88-reemit-partner₄` at `:265` proves `Rep★PartnerOK₄ Wᵖ X (((P⟨X₂!⟩) ↓ seal X ★)⟨X!⟩) (just Y) (U⟨Y₂!⟩)` from `linkS : RebaseAt Wᵖ Wᵀ X Y` and `aligned-inner : CenterAligned₄ Wᵖ X₂ Y₂`. The witness is `rep★-round-trip₄ (rep★-matched-inner-tags₄ aligned-inner)`. |
| Matched-conceal re-emission witness | **Pass in scratch.** | `target-chain-88-matched-conceal₄` at `:293` builds the exact first argument wanted by paired conceal. |
| `SourceStripWorkerProof:420` twin | **Pass in scratch; live blocked through `TargetChainProof`.** | `source-strip-worker-420-shape₄` at `:386` pairs `composeOuterRebase₄ rb link` with the same round-trip partner witness in post-transfer world `W₂`. |
| No-target var-tag payoff | **Pass.** | `var-tag-no-target-empty₄` at `:402` recurses through `rep★-round-trip₄`; a round-trip wrapper cannot turn `nothing` into `just Y`. |
| ℕ-tagged payload/no-target worker shape | **Pass.** | `nat-payload-var-tag-no-target-empty₄` at `:417` is still immediate from no-target var-tag emptiness. |
| Source-seal no-target worker shapes | **Pass.** | `source-seal-var-tag-no-target-empty₄` and `source-seal-var-tag-no-target-after-cast-empty₄` at `:435` and `:451` still reduce to the rep no-target impossibility. |
| Bare-payload var-tag mismatch poison | **Pass with the intended bare guard.** | `bare-payload-var-tag-mismatch-empty₄` at `:470` excludes ordinary bare payloads by requiring both “not an inner tag” and “not a same-name round-trip wrapper.” |
| Different-name round-trip laundering | **Pass.** | `different-name-round-trip-no-launder₄` at `:508` blocks the see-through case by `Z ≢ X`; the remaining top-tag cases require explicit outer/wrapper alignment. |
| Non-rep-`★` laundering | **Pass.** | `non-rep★-round-trip-no-launder₄` at `:543` blocks the see-through constructor because it would force `NonStar ★`. |
| Prior gates unmodified | **Fail in the current worktree. LOUD.** | Several live gate files are already red without touching `GTSFImp/`; see the gate table below. |

## Compatibility Sweep

| Site | Compatibility outcome |
|---|---|
| `TargetSealTerminal` enrichment | Needs live surface change if extraction will re-emit paired `seal ★`: the terminal record should carry `MatchedConcealPartnerOK` for its premise. Scratch model `TargetSealTerminal₄` at `:580` includes `partnerᵒ₄`. |
| `target-seal★-extract` / descent extract | Should consume the enriched terminal partner instead of attempting paired re-emission from only `premiseᵒ`. Scratch `target-seal-terminal-extract-partner₄` at `:598` models the needed extraction. |
| `plain-star-rep-premise` | Still cannot synthesize arbitrary `Rep★PartnerOK` for arbitrary target `U`. It should gain an explicit partner premise or restrict the target shape. Scratch `plain-star-rep-premise-partner₄` at `:604` models the premise-to-source-conceal conversion only after the partner is supplied. |
| Descent partner decay/extract paths | The new round-trip constructor is stable under decay: `decayRep★PartnerOK₄` at `:193` recurses through the constructor, and source/matched conceal decay follows from that. |
| `TargetSealTerminal` re-emission against matched inner tags | Compatible with the candidate, provided the terminal stores the matched partner from the post-transfer premise world rather than rebuilding it in the conclusion world. |

## Gate Table

| Command target | Result | Note |
|---|---|---|
| `Tighten4PreflightScratch.agda` | Pass | Candidate model checks. |
| `GTSFImp/proof/DGG/CastTermImprecision2.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/TermImpDecay.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Inversion/TargetWalkSupport.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/StarRepChainProbe.agda` | Fail | Stale paired conceal application at `StarRepChainProbe.agda:190`. |
| `GTSFImp/proof/DGG/ChainRideProbe.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/TagBoundaryProbe.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/TerminusRebuildProbe.agda` | Fail | Partner world mismatch at `TerminusRebuildProbe.agda:212`. |
| `GTSFImp/proof/DGG/LambdaImpProbe.agda` | Fail | Fails through `Examples2.agda:537`. |
| `GTSFImp/proof/DGG/Examples2.agda` | Fail | Stale paired conceal application at `Examples2.agda:537`. |
| `GTSFImp/proof/DGG/Phase3DeepDives.agda` | Fail | Fails through `Examples2.agda:537`. |
| `GTSFImp/proof/DGG/Parked/ParkedD4CheckpointLemma.agda` | Fail | Fails through `Examples2.agda:537`. |
| `GTSFImp/proof/DGG/ReachabilityCatalog.agda` | Fail | Fails through `Examples2.agda:537`. |
| `GTSFImp/proof/DGG/CompileImageShape.agda` | Fail | Fails through `Examples2.agda:537`. |
| `InitialPairScratch.agda` | Fail | Fails through `Examples2.agda:537`. |
| `GTSFImp/proof/DGG/CompilePreservesImprecision2.agda` | Fail | Fails through `Examples2.agda:537`. |
| `GTSFImp/proof/DGG/Inversion/TargetDescentProof.agda` | Fail | Stale `{partner = partner}` implicit at `TargetDescentProof.agda:141`. |
| `GTSFImp/proof/DGG/Inversion/RightInjInversion2Proof.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Inversion/TargetChainProof.agda` | Fail | Known blocked head at `TargetChainProof.agda:88`. |
| `GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda` | Fail | Stops through imported `TargetChainProof.agda:88` before its own line 420 body. |

## Bottom Line

The same-name rep-`★` round-trip see-through clause is viable in scratch for
the round-9 partner head and the SourceStripWorker twin, and it preserves the
requested emptiness and poison exclusions.

The preflight is **not globally green** because prior live gates are already
red in this worktree. Since `GTSFImp/` was intentionally not edited, those live
failures remain for the actual wiring pass.
