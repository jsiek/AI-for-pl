# Surgery Pre-Flight

Branch: `agent/gtsf-extra-cast-right`

Scope: scratch/dossier only.  No `GTSFImp/` source edits and no commits.

Checked scratch:

- `SurgeryPreflightScratch.agda`
- Existing baseline: `TagDisciplineScratch.agda`

## Stop Verdict

STOP for review, 2026-08-08: the refined predicate validates, but the
`rep = ＇ X₂` chain edge is a design decision and should be reviewed before
live relation surgery.

The previous name-or-untagged predicate was too strong because it rejected
benign source-seal descents whose seal representation is `★` and whose target
partner is a normal dynamic tag, for example `dyn-id` tagged at `★ ⇒ ★`.
The refined predicate keys on the source seal representation instead:

- `rep = ★`: any target partner is admitted, including top-level tags at any
  ground.
- `rep ≠ ★`: an untagged partner is admitted, and a top-level tagged partner
  is admitted only when it is name-protected at the aligned target seal name:
  `((M ↓ seal Y S) ⟨Y!⟩)`.

The chain-edge answer is conservative: `rep = ＇ X₂` is not `★`, even when the
store chain later reaches a `★` representation.  Parametricity treats `＇ X₂`
as opaque at the outer seal.  A direct ground tag such as `($ 0) ⟨ℕ!⟩` would
choose and reveal a representation before the aligned-name chain has been
followed.  The checked witness `chain-variable-rep-direct-tag-empty` therefore
rejects the direct chain probe target.  The valid chain constructions must
re-emit target seals through names, or descend until the source seal
representation is literally `★`, where arbitrary dynamic tags are allowed.

## Verdict Table

| Item | Refined verdict | Checked evidence |
|---|---|---|
| Mismatch premise, source seal rep `ℕ` | Underivable in the refined scratch relation: `($ 0) ⟨ℕ!⟩` is a direct representation-ground tag, not a name-protected target. | `refined-restricted-mismatch-premise-empty`, `mismatch-target-not-ok-refined-nat` |
| Name-tagged positive, source seal rep `ℕ` | Derivable: the target tag is the aligned seal-name tag. | `name-tag-target-ok-refined`, `sealed-source-name-tag-positiveʳᵗᵈ` |
| Dyn-id descent, source seal rep `★` | Derivable: `rep = ★` admits the target's ordinary dynamic tag at `★ ⇒ ★`. | `terminus-instanceB-inner-dyn-id-ok`, `terminus-instanceB-inner-dyn-id-live` |
| Terminus Instance A tagged partner | Survives by name protection even though the source rep is `∀X⇒X`.  Its direct dyn-id helper remains rejected because that source rep is not `★`. | `terminus-instanceA-tagged-partner-ok`, `terminus-instanceA-live-tagged-input`, `terminus-instanceA-direct-dyn-id-empty` |
| Terminus Instance B tagged partner | Survives; both the visible target tag and the inner dyn-id descent are admitted by `rep = ★`. | `terminus-instanceB-tagged-partner-ok`, `terminus-instanceB-live-tagged-input`, `terminus-instanceB-inner-dyn-id-ok` |
| M3 `cast⊑cast²` stuck input | Derivable-and-must-be-proven.  The outer source seal has rep `★`. | `m3-cast⊑cast²-input` |
| M3 `cast⊑²` stuck input | Derivable-and-must-be-proven.  The source cast can still be folded before the source seal, with rep `★`. | `m3-cast⊑²-source-to-tag`, `m3-cast⊑²-premise`, `m3-cast⊑²-input` |
| M3 nested `conceal⊑²` stuck input | Not eliminated by the refined gate. | `m3-nested-conceal-target-ok` |
| M3 `rebase-onlyᴸ` stuck input | Changed from the previous pre-flight: derivable, because the source seal rep is `★` even though no target name is exposed. | `m3-rebase-only-input-ok` |
| Chain edge, source seal rep `＇ X₂` | Direct ground-tag partner rejected.  The chain must stay name-protected or move to a literal `★` seal before arbitrary tags are allowed. | `chain-variable-rep-direct-tag-empty` |
| `seal-descent-at-var-＇` re-emission | Survives.  It is target-only conceal re-emission, not a source-seal/direct-tag partner. | `seal-descent-at-var-＇-reemit-instance` |
| `left-path-argument₄` old wrapper | Still formation-impossible: source seal rep is `ℕ`, no target name is present, and the target is `$ 7 ⟨ℕ!⟩`. | `left-path-argument₄-old-wrapper-empty` |
| `left-path-argument₄` semantic payload | Survives by shifting to the data payload comparison. | `left-path-argument₄-payload-survives` |
| Cambridge Example 12 gates | Unchanged. | `example12-checkpoint₁-gate-refined`, `example12-paired-seal-gate-refined` |
| `compile-preserves-imprecision²` gate shape | Unchanged. | `compile-preserves-imprecision²-gate-refined` |

## Transcript

Successful checks:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 SurgeryPreflightScratch.agda
# exit 0

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 TagDisciplineScratch.agda
# exit 0

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 MismatchProbeScratch.agda
# exit 0, confirming the live relation still admits the old probe

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/TerminusRebuildProbe.agda
# exit 0

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/TargetDescentProof.agda
# exit 0

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/Examples2.agda
# exit 0

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/CompilePreservesImprecision2.agda
# exit 0

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/CompileImageShape.agda
# exit 0

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/Phase3DeepDives.agda
# exit 0
```

Additional live worker check, not part of the scratch-only gate:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda
# exit 42
# Existing unsolved metas in the current modified worktree:
#   SourceStripWorkerProof.agda:726, 749, 836, 847, 941, 1002, 1029
```

## Consequence

Do not proceed to live relation surgery yet.  The refined predicate fixes the
known over-restriction for `rep = ★` and still blocks the representation leak
for `rep = ℕ`.  The remaining review point is the explicit policy choice for
`rep = ＇ X₂`: this scratch treats it as opaque/non-`★`, which rejects direct
ground-tag partners and requires chain proofs to stay name-protected until a
literal `★` representation is reached.
