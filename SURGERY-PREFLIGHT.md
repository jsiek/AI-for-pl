# Surgery Pre-Flight

Branch: `agent/gtsf-extra-cast-right`

Scope: scratch-only.  No `GTSFImp/` source edits and no commits.

Checked scratch:

- `SurgeryPreflightScratch.agda`
- Existing baseline: `TagDisciplineScratch.agda`

## Stop Verdict

STOP: category 2 has a real resister in the exact
`TerminusRebuildProbe` stack.

The outer tagged-partner shapes are admitted by the dossier restriction, but
the probe stack also uses direct source-seal descent against `dyn-id`.  Since
`dyn-id` is a top-level cast and not a name-protected sealed target, the
restricted gate rejects those auxiliary premises:

- `terminus-instanceA-direct-dyn-id-empty`
- `terminus-instanceB-inner-dyn-id-empty`

This is not a `GTSFImp/` edit blocker caused by Agda churn; it is a semantic
pre-flight failure for the proposed restriction as stated.

## Verdict Table

| Item | Verdict | Checked evidence |
|---|---|---|
| M3 `cast⊑cast²` stuck input | Derivable-and-must-be-proven.  The target is `(U ↓ seal Y S) ⟨Y!⟩`, so the new side condition is `name-tagged-target`. | `m3-cast⊑cast²-input` |
| M3 `cast⊑²` stuck input | Derivable-and-must-be-proven.  The source cast can be folded before the outer source seal while the target remains name-tagged. | `m3-cast⊑²-source-to-tag`, `m3-cast⊑²-premise`, `m3-cast⊑²-input` |
| M3 nested `conceal⊑²` stuck input | Not eliminated by the target-shape gate when the inner source-seal descent is also name-protected at the same target name.  The recursive worker still needs the structural proof or a separate impossibility lemma. | `m3-nested-conceal-target-ok` |
| M3 `rebase-onlyᴸ` stuck input | Formation-impossible for the tagged M3 source-spine input.  There is no target name, and `((U ↓ seal Y S) ⟨Y!⟩)` is top-level tagged. | `m3-rebase-only-input-empty` |
| Terminus Instance A tagged partner | The visible tagged partner survives. | `terminus-instanceA-tagged-partner-ok`, `terminus-instanceA-live-tagged-input` |
| Terminus Instance A direct terminus helper | Rejected by the restriction: `U = dyn-id` is top-level tagged but not name-tagged. | `terminus-instanceA-direct-dyn-id-empty` |
| Terminus Instance B tagged partner | The visible tagged partner survives. | `terminus-instanceB-tagged-partner-ok`, `terminus-instanceB-live-tagged-input` |
| Terminus Instance B inner payload helper | Rejected by the restriction: `U₀ = dyn-id` is top-level tagged but not name-tagged. | `terminus-instanceB-inner-dyn-id-empty` |
| `seal-descent-at-var-＇` re-emission | Survives.  It is target-only conceal re-emission and does not use a source-seal/top-level-tag partner. | `seal-descent-at-var-＇-reemit-instance` |
| `left-path-argument₄` old wrapper | Formation-impossible under the restricted source-seal rule: it is a `rebase-onlyᴸ` source seal against `$ 7 ⟨ℕ!⟩`. | `left-path-argument₄-old-wrapper-empty` |
| `left-path-argument₄` semantic payload | Survives by shifting to the data payload comparison, matching the M2 pre-flight precedent. | `left-path-argument₄-payload-survives` |

## Transcript

Successful checks:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 TagDisciplineScratch.agda
# exit 0

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 SurgeryPreflightScratch.agda
# exit 0

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/TerminusRebuildProbe.agda
# exit 0

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/TargetDescentProof.agda
# exit 0

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/Examples2.agda
# exit 0
```

Local repo-only Agda home attempt:

```sh
AGDA_DIR=$PWD/scratchpad/agda-home agda -i GTSFImp -v0 TagDisciplineScratch.agda
# exit 42
# Failed to find source of module Data.Empty
```

The successful checks used the user-provided Agda home because the repository
does not contain a self-contained standard-library source.

## Consequence

Do not proceed to the live relation surgery as currently specified.  The
restriction correctly rejects the old representation-tag mismatch and the
known `left-path-argument₄` wrapper, but it also rejects the exact dyn-id
payload helpers in the committed terminus-rebuild probe.  The next design step
is to either refine `SealTargetOK` so benign dynamic payload tags are allowed,
or replace the affected terminus stack with a fully name-protected payload
construction before editing `CastTermImprecision2.agda`.
