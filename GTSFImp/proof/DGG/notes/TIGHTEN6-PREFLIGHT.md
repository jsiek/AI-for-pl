# Rep-`★` Partner Tightening Pre-flight 6

Scope:

- Root scratch only: `Tighten6PreflightScratch.agda`.
- No edits under `GTSFImp/`.
- Checked on branch `agent/gtsf-extra-cast-right`.

Toolchain:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 <file>
```

## Candidate Modeled

The scratch relation `Rep★PartnerOK₆` frees the recursive round-trip premise:

```agda
rep★-round-trip₆ : ∀ {P Xᴿ? Xᴿ?ᵢ M′ A μ}
  → Rep★PartnerOK₆ W X P Xᴿ?ᵢ M′
  → Rep★PartnerOK₆ W X ((P ↓ seal X ★)⟨X!⟩) Xᴿ? M′
```

The analogous source/matched conceal surfaces are modeled by
`source-round-trip-seal-star₆` and `matched-round-trip-seal-star₆`.

## Verdict Table

| Check | Verdict | Evidence |
|---|---|---|
| T6 scratch type-checks | **Pass** | `Tighten6PreflightScratch.agda` checks with the requested toolchain. |
| Round-16 source-seal sub-head | **Pass locally** | `round16-source-seal-subhead₆` at `Tighten6PreflightScratch.agda:209` accepts a transported live inner partner with pedigree `just Yᵖ` and rewraps it under outer `just Y`. |
| Conceal-surface analogue | **Pass syntactically** | `source-round-trip-seal-star₆` at `:181` and `matched-round-trip-seal-star₆` at `:195` mirror the freed premise. |
| Transport over arbitrary freed witnesses | **Fail / unsafe** | The freed round-trip can hide an inner wrong-pedigree `rep★-var-tag₆`; a general transport would then need to move a pivot tag for `Yᵢ` across a rebase for outer `Y`. The attack witness is `wrong-pedigree-round-trip-launder₆` at `:340`. |
| Bare-payload poison | **Pass** | `bare-payload-var-tag-mismatch-empty₆` at `:234` still blocks truly bare payloads via the “not a round-trip wrapper” guard. |
| Different-name round-trip | **Pass** | `different-name-round-trip-no-launder₆` at `:272` still blocks `(P ↓ seal Z ★)⟨Z!⟩` when `Z ≢ X`. |
| Non-rep-`★` round-trip | **Pass** | `non-rep★-round-trip-no-launder₆` at `:307` still blocks `(P ↓ seal X R)⟨X!⟩` for `NonStar R`. |
| New wrong-pedigree laundering attack | **FAIL - ATTACK SUCCEEDS** | `wrong-pedigree-round-trip-launder₆` at `:340` builds outer `just Yᵒ` from an inner `just Yᵢ` tag. `wrong-pedigree-matched-conceal₆` at `:424` lifts it to matched conceal. |
| Emptiness payoffs | **FAIL - broken** | `var-tag-no-target-launder₆` at `:361` and `source-seal-var-tag-no-target-launder₆` at `:382` inhabit the no-target shapes that the `...-empty₅` lemmas were supposed to refute. |
| Round-15 concrete counterexample | **FAIL - reopened** | `round15-counterexample-package₆` at `:452` constructs the previously impossible package from `SourceStarPackageCounterScratch`: the live `no-output-package` still rejects it, but the freed relation accepts it by changing inner `just Y` to outer `just Y₂`. |

## Loud Result

LOUD: the laundering attack succeeds. The candidate is not viable as stated.

The decisive issue is not the immediate round-16 sub-head. That local shape
does discharge when the inner transported partner is the current disciplined
live relation. The problem is that the freed constructor also permits:

```agda
rep★-round-trip₆ (rep★-var-tag₆ aligned)
```

to retarget an exposed target variable tag from an inner pedigree to any outer
pedigree, including `nothing`. That breaks both the no-target emptiness payoff
and the prior round-15 negative instance.

## Gate Table

| Command target | Result | Note |
|---|---|---|
| `Tighten6PreflightScratch.agda` | Pass | Candidate model and counterexamples check. |
| `SourceStarPackageCounterScratch.agda` | Pass | Prior negative live instance still checks. |
| `Tighten5PreflightScratch.agda` | Fail | Stale against current live `CTI2.rep★-matched-inner-tags` arity at `Tighten5PreflightScratch.agda:174`. |
| `GTSFImp/proof/DGG/CastTermImprecision.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/TermImpDecay.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/SealTransferCore.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Inversion/TargetWalkSupport.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/StarRepChainProbe.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/ChainRideProbe.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/TagBoundaryProbe.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/TerminusRebuildProbe.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/LambdaImpProbe.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Examples2.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Phase3DeepDives.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Parked/ParkedD4CheckpointLemma.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/ReachabilityCatalog.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/CompileImageShape.agda` | Pass | Read-only gate. |
| `InitialPairScratch.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/CompilePreservesImprecision2.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Inversion/TargetDescentProof.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Inversion/RightInjInversion2Proof.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Inversion/TargetChainProof.agda` | Fail | Known live red at `TargetChainProof.agda:88`. |
| `GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda` | Fail | Fails through imported `TargetChainProof.agda:88`. |

## Bottom Line

Do not wire this candidate into `GTSFImp/` as stated. It solves the local
pedigree mismatch by making the outer pedigree unconstrained, but that also
allows wrong-pedigree and no-target laundering.
