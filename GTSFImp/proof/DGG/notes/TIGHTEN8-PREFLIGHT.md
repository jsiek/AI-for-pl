# Rep-`★` Partner Tightening Pre-flight 8

Scope:

- Root scratch only: `Tighten8PreflightScratch.agda`.
- No edits under `GTSFImp/`.
- Checked on branch `agent/gtsf-extra-cast-right`.

Toolchain:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 <file>
```

## Candidate Modeled

Option B is modeled as a rule-surface change, not as a live
`Rep★PartnerOK` clause change.

- `Rep★PartnerOK` keeps the live propagated round-trip clause.
- `MatchedConcealPartnerOK₈` takes a `Maybe (TyVar Δᴿ)` package index.
- `TaggedTransferOutput₈` carries both:
  - `pedigree₈ : PremisePartnerAt W X Xᴿ?`
  - `partner₈ : MatchedConcealPartnerOK₈ W P (seal X ★) Xᴿ? U`
- `emit-tagged-transfer₈` keeps the conclusion-world target `Y` only in
  `RebaseAt Wᵖ W X Y` and target seal typing.

The hard round-16 source-seal sub-head uses:

```agda
CTI2.rep★-round-trip
  (STC.transport-rep★-partner-ok rbᵖ partner)
```

at index `just Yᵖ`, where `Yᵖ` is witnessed by
`CTI2.RebaseAt.pivotAligned rbᵖ` in the premise world `W₂`.  The outer
`link : RebaseAt W₂ W₀ X Y` is accepted by the paired emission but is not used
to rewrite the partner pedigree.

## Verdict Table

| Check | Verdict | Evidence |
|---|---|---|
| T8 scratch type-checks | **Pass** | `Tighten8PreflightScratch.agda` checks with the requested toolchain. |
| 1. Round-16 source-seal sub-head | **Pass** | `round16-source-seal-subhead₈` and `emit-tagged-transfer-peel₈` at `Tighten8PreflightScratch.agda:179` and `:194` build the package at `just Yᵖ`; consecutive rebases no longer require `Yᵖ ≡ Y`. |
| 2. `⊑cast²` sub-head | **Pass** | `round16-cast-subhead-package₈` at `:160` builds the premise with `CTI2.cast⊑² (id (＇ X) !) D₂ ★⊑★` and keeps the partner pedigree at `just Yᵖ`. |
| 2. Paired-seal emit head | **Pass** | `emit-tagged-transfer₈` at `:132` consumes the package index independently from the conclusion `Y`. |
| 3. Round-15 counterexample stays closed | **Pass** | `round15-counterexample-stays-closed₈` at `:399` rejects the arbitrary `B.Y₂` package by `PremisePartnerAt` uniqueness; `round15-live-output-partner-still-empty₈` reuses the live negative proof. |
| 4. Wrong-pedigree round-trip laundering | **Pass** | `wrong-pedigree-round-trip-blocked₈` at `:230` blocks package formation when the requested package pedigree is not the premise-world pairing. |
| 4. No-target var-tag laundering | **Pass** | `var-tag-no-target-empty₈` at `:242` and `source-seal-var-tag-no-target-empty₈` at `:257` remain empty under propagated round-trip. |
| 5. Worker emptiness payoffs | **Pass** | `worker-source-seal-var-tag-no-target-after-cast-empty₈` at `:273` preserves the source-strip worker no-target shape. |
| 6. Bare payload exclusion | **Pass** | `bare-payload-var-tag-mismatch-empty₈` at `:289` still refutes the bare payload/top target-var tag mismatch. |
| 6. Different-name exclusion | **Pass** | `different-name-round-trip-no-launder₈` at `:327` still rejects `(P ↓ seal Z ★)⟨Z!⟩` when `Z ≢ X`. |
| 6. Non-rep-`★` exclusion | **Pass** | `non-rep★-round-trip-no-launder₈` at `:362` still rejects `(P ↓ seal X R)⟨X!⟩` for `NonStar R`. |
| 7. Consumer sweep | **Pass with surface edits** | No site was found that needs a reverse bridge from conclusion `Y` to premise `Yᵖ`. Several live surfaces still spell the old `Y` index and must be generalized to the package index. |

No LOUD failure for checks 3-5: the arbitrary-pedigree package, wrong-pedigree
round-trip, no-target var-tag, and worker empty shapes all stay closed.

## Consumer Sweep

| Site | Current evidence | B classification |
|---|---|---|
| `SealTransferCore.TaggedTransferOutput` / helpers (`SealTransferCore.agda:226`, `:235`, `:248`) | Transported partner plus `RebaseAt.pivotAligned rb` in the package world. | Native premise-world pairing after changing the record index from conclusion `Y` to package `Xᴿ?`. |
| `SealTransferCore.emit-tagged-transfer` (`:262`) | Consumes an already-built package and a separate `RebaseAt Wᵖ W X Y`. | Native consumer; `Y` should remain only in `RebaseAt` and target seal typing. |
| `SealTransferCore` paired-seal peel (`:507`) | Inner `partner : Rep★PartnerOK Wᵖ ... (just Yᵖ)` and `rbᵖ : RebaseAt ... X Yᵖ`. | Native; this is the round-16 site modeled by `round16-source-seal-subhead₈`. |
| `SourceStarProbe.agda:143` | Same-world `link₁` and `rep★-nonvar-tag`. | Native; premise and conclusion worlds coincide. |
| `CenterCrossingProbe.agda:210` | Inner rebase `rb-inner` and `rep★-nonvar-tag`. | Native; the star partner is tied to the inner premise pair. |
| `TerminusRebuildProbe.agda:406`, `:422` | Star partners at `rb-X-Y₂`; outer target chain uses separate `Y`. | Native; premise-world package is `Y₂`, not the outer `Y`. |
| `Examples2.agda:2575`, `:2687` | Same-world rebases `left-path-rebase-Z-YZ₄` / `left-path-rebase-Y-YZ₄`; partners are nonvar/untagged. | Native; no conclusion-only bridge needed. |
| `Examples2.agda:537`, `:1027`; `StarRepChainProbe.agda:190`; `ExtraCastRight2Counterexample.agda:170`; `TerminusRebuildProbe.agda:220` | `matched-seal-nonstar`. | No `Rep★` pedigree payload. |
| `TargetChainProof.agda:88` | Live code has the known package-less re-emission. | Needs the revised package from `round16-cast-subhead-package₈`; no `Yᵖ ≡ Y` bridge required. |
| `TargetDescentDef.agda:27`, `TargetDescentProof.agda:113` | Live `TargetSealTerminal` / `makePartner` still name `Y`. | Surface edit: terminal data should store package index/evidence. The continuation hook is already the right insertion point. |
| `TargetStripProof.agda:770`, `:899`, `:905`, `:912`, `:956`, `:960` | Mostly inversion/elimination of existing paired rules; `wrap-star-cast-final` has the same package-less shape as target-chain. | Eliminations are unaffected; the re-emission site should consume the revised package. |
| `SourceStripWorkerProof.agda:250`, `:254`, `:424` | Existing final re-emissions preserve `ok` or hit the target-chain package-less shape. | Preserving `ok` is native; package-less re-emission is repaired by the same revised package. |
| `CompilePreservesImprecision2.agda` | No direct `conceal⊑conceal²` / `matched-seal-star-partner` sites found by grep. | No B-specific consumer surface. |
| `TagBoundaryProbe.agda`, `ChainRideProbe.agda`, `LambdaImpProbe.agda` | No direct paired-seal emission site in the grep sweep. | No B-specific consumer surface. |

## Gate Table

| Command target | Result | Note |
|---|---|---|
| `Tighten8PreflightScratch.agda` | Pass | Candidate model and all local checks. |
| `SourceStarPackageCounterScratch.agda` | Pass | Prior round-15 live negative instance still checks. |
| `GTSFImp/proof/DGG/SealTransferCore.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Inversion/TargetDescentProof.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/CompilePreservesImprecision2.agda` | Pass | Read-only gate; no direct paired-seal sites found. |
| `GTSFImp/proof/DGG/Examples2.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/SourceStarProbe.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/CenterCrossingProbe.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/StarRepChainProbe.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/TagBoundaryProbe.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/TerminusRebuildProbe.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Inversion/TargetStripProof.agda` | Pass | Read-only gate. |
| `GTSFImp/proof/DGG/Inversion/TargetChainProof.agda` | Fail | Known live red at `TargetChainProof.agda:88`; the scratch package is the modeled repair. |
| `GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda` | Fail | Fails through imported `TargetChainProof.agda:88`. |

## Bottom Line

Option B passes the root scratch pre-flight.  The propagated round-trip clause
remains sound, and changing the paired-rule package index to the premise-world
partner discharges the round-16 source-seal sub-head without a consecutive
rebase uniqueness theorem.

The live update would still be a rule-surface migration: `TaggedTransferOutput`,
`MatchedConcealPartnerOK`, `TargetSealTerminal`, and the package-producing
consumers need to thread `Xᴿ?` plus `PremisePartnerAt`.  The sweep did not find
a site that needs a reverse bridge from conclusion `Y` back to premise `Yᵖ`.
