# Rep-`★` Partner Tightening Pre-flight 7

Scope:

- Root scratch only: `Tighten7PreflightScratch.agda`.
- No edits under `GTSFImp/`.
- Checked on branch `agent/gtsf-extra-cast-right`.

Toolchain:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 <file>
```

## Candidate Modeled

The scratch relation `Rep★PartnerOK₇` uses an anchored `just` round-trip
branch plus a separate `nothing` branch:

```agda
rep★-round-trip-just₇ :
  CenterAligned W X Yᵖ →
  Rep★PartnerOK₇ W X P (just Yᵖ) U →
  Rep★PartnerOK₇ W X ((P ↓ seal X ★)⟨X!⟩) (just Y) U

rep★-round-trip-nothing₇ :
  Rep★PartnerOK₇ W X P nothing U →
  Rep★PartnerOK₇ W X ((P ↓ seal X ★)⟨X!⟩) nothing U
```

The split is the strongest version of the proposed shape that still gives the
old `nothing`-pedigree recursion without allowing a `just` variable tag to
become `nothing`.

## Verdict Table

| Check | Verdict | Evidence |
|---|---|---|
| T7 scratch type-checks | **Pass** | `Tighten7PreflightScratch.agda` checks with the requested toolchain. |
| Round-16 source-seal sub-head | **Pass locally** | `round16-source-seal-subhead₇` at `Tighten7PreflightScratch.agda:280` uses `pivotAligned rbᵖ : CenterAligned W₂ X Yᵖ` as the anchor and emits outer `(just Y)`. |
| `nothing`-pedigree variant | **Pass** | `rep★-round-trip-nothing₇` at `:94` and `transportRep★PartnerOK-nothing₇` at `:219` preserve the propagated `nothing` case. |
| Transport over anchored `just` round-trips | **Fail / unavailable** | A total transport from inner `just Yᵖ` to new pivot `just Y` cannot be defined: the direct `rep★-var-tag₇` branch leaves the target term tagged by `Yᵖ`, while the result type expects a target tag at `Y`. |
| Wrong-pedigree round-trip attack | **FAIL - ATTACK SUCCEEDS** | `wrong-pedigree-round-trip-launder₇` at `:412` still builds outer `just Yᵒ` from an anchored inner `just Yᵢ`. |
| No-target variable-tag attack | **Pass / closed** | `var-tag-no-target-empty₇` at `:433` and `source-seal-var-tag-no-target-empty₇` at `:449` refute the round-6 no-target laundering shape. |
| Round-15 concrete counterexample | **FAIL - reopened** | `round15-counterexample-package₇` at `:513` constructs the arbitrary-`Y₂` package from the inner anchored `Y`. |
| Bare-payload poison | **Pass** | `bare-payload-var-tag-mismatch-empty₇` at `:306` still rejects bare payloads that are neither inner tags nor round-trip wrappers. |
| Different-name round-trip | **Pass** | `different-name-round-trip-no-launder₇` at `:344` still blocks `(P ↓ seal Z ★)⟨Z!⟩` when `Z ≢ X`. |
| Non-rep-`★` laundering | **Pass** | `non-rep★-round-trip-no-launder₇` at `:379` still blocks `(P ↓ seal X R)⟨X!⟩` for `NonStar R`. |
| `⊑cast²` / paired-seal support gates | **Pass** | `CastTermImprecision2`, `SealTransferCore`, `TargetWalkSupport`, `TargetDescentProof`, and `RightInjInversion2Proof` all check read-only. |

## Loud Result

LOUD: the candidate is not viable as a live relation change.

Anchoring the recursive premise is not enough, because the outer `just Y`
pedigree is still unconstrained.  The scratch file type-checks the same
essential laundering:

```agda
rep★-round-trip-just₇ aligned (rep★-var-tag₇ aligned)
```

with arbitrary outer `Yᵒ`.  The `nothing` split closes the no-target attack,
but the wrong-`just` attack and the round-15 arbitrary-`Y₂` package remain.

The transport story is also worse than the round-16 local head suggests.  At a
pivot rebase, the alignment proof can move to `pivotAligned rb`, but the target
term itself does not change from a `Yᵖ` tag to a `Y` tag.  Therefore a total
induction transporting anchored `just` witnesses across rebase-at-`X` is not
available in this model.

## Gate Table

| Command target | Result | Note |
|---|---|---|
| `Tighten7PreflightScratch.agda` | Pass | Candidate model and counterexamples check. |
| `SourceStarPackageCounterScratch.agda` | Pass | Prior live negative instance still checks. |
| `GTSFImp/proof/DGG/CastTermImprecision2.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/TermImpDecay.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/SealTransferCore.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Inversion/TargetWalkSupport.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/StarRepChainProbe.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/ChainRideProbe.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/TagBoundaryProbe.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/TerminusRebuildProbe.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/LambdaImpProbe.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Examples2.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Inversion/TargetDescentProof.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Inversion/RightInjInversion2Proof.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Inversion/TargetChainProof.agda` | Fail | Known live red at `TargetChainProof.agda:88`. |
| `GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda` | Fail | Fails through imported `TargetChainProof.agda:88`. |

## Bottom Line

Do not wire this candidate into `GTSFImp/`.  The round-16 source-seal sub-head
does discharge, and the no-target empties recover, but arbitrary outer
`just`-pedigree laundering remains and the required anchored transport
principle is not definable over unchanged target syntax.
