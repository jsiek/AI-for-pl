# Tag Discipline Dossier

Investigation target: branch `agent/gtsf-extra-cast-right`, read-only over
`GTSFImp/`, with root scratch only.

Checked scratch:

- `SurgeryPreflightScratch.agda`
- Historical baseline: `TagDisciplineScratch.agda`

Refinement status, 2026-08-08: the earlier name-or-untagged target predicate
was too strong.  The replacement discipline keys on the source seal's
representation.

## Collapse Location

The live mismatch premise in `MismatchProbeScratch.agda` is:

```agda
input-relation : InputRelation
input-relation =
  CTI2.conceal⊑² (λ _ eq → eq) (CTI2.rebase-varᴸ U-Y-rebase)
    CTI2.same-[] source-U-seal-typed
    (CTI2.⊑cast² ℕ! (CTI2.κ⊑κ² (κℕ 0) ι⊑ι) ι⊑★)
    probe-p
```

This is the full derivation tree:

1. `CTI2.κ⊑κ² (κℕ 0) ι⊑ι`
   derives `$ 0 ⊑ $ 0 : ℕ ⊑ ℕ`.
2. `CTI2.⊑cast² ℕ! ... ι⊑★`
   derives `$ 0 ⊑ ($ 0) ⟨ℕ!⟩ : ℕ ⊑ ★`.
3. `U-Y-representation = store-rep-imp ι⊑★`.
   This is admitted because `StoreRepImp` resolves store representations:
   `resolveVar source-store U = ℕ` and `resolveVar target-store Y = ★`.
4. `U-Y-rebase = CTI2.sameWorldRebaseAt refl U-Y-representation`.
   The source seal name `U` and target variable `Y` are center-aligned.
5. `CTI2.rebase-varᴸ U-Y-rebase`
   packages that rebase for the source-side wrapper.
6. `source-U-seal-typed = CTI2.⊢↓-sealˣ source-U∋`.
7. `CTI2.conceal⊑² ...`
   derives
   `($ 0) ↓ seal U ℕ ⊑ ($ 0) ⟨ℕ!⟩ : ＇U ⊑ ★`.

The collapse is exactly the combination of:

- `conceal⊑²`, which lets a source-side seal descend against an arbitrary
  target term;
- `RebaseAtᴸ.rebase-varᴸ`, which remembers a target name only indirectly;
- `StoreRepImp.store-rep-imp`, whose obligation is representation-transparent
  through `resolveVar`;
- `⊑cast²`, which can put the target at the representation ground `ℕ!`.

The relation therefore preserves enough name alignment to derive `＇U ⊑ ＇Y`
but not enough target-shape discipline to prevent the immediate target partner
from being tagged at `ℕ` rather than at the seal name `Y`.

## Why The Old Predicate Was Too Strong

The first candidate restriction was:

- accept targets whose top constructor is not `_⟨_⟩`;
- accept name-protected targets of the form `((M ↓ seal Y R) ⟨Y!⟩)`;
- reject every other top-level tag.

That killed the mismatch, but it also killed known benign descents in the
terminus rebuild stack.  The representative bad rejection is a source seal
whose representation is literally `★` and whose target partner is an ordinary
dynamic value such as:

```agda
dyn-id = (ƛ (` 0)) ⟨ ★⇒★! ⟩
```

There is no representation to leak when the source seal representation is
`★`.  Rejecting all non-name top-level tags at that point over-constrains
ordinary gradual dynamics.

## Refined Discipline

Chosen refinement, 2026-08-08: add a side condition to source-side seal
descent that takes the source seal representation `R` as an input.

In scratch this is `SealPartnerOK R Xᴿ? M′`:

- `star-rep-target`: if `R = ★`, any target partner `M′` is admitted,
  including top-level tags at any ground.
- `plain-target`: if the target partner has no top-level `_⟨_⟩`, it is
  admitted for any `R`.
- `name-protected-target`: if an aligned target name is available and
  `M′ = (M ↓ seal Y S) ⟨Y!⟩`, it is admitted for any `R`.

For `R ≠ ★`, those are the only admitted cases.  A direct top-level ground tag
that is not the aligned seal-name tag is rejected.  This preserves the intended
positive form:

```agda
($ 0) ↓ seal U ℕ
  ⊑ (($ 0 ⟨ℕ!⟩) ↓ seal Y ★) ⟨Y!⟩
```

and rejects the mismatch:

```agda
($ 0) ↓ seal U ℕ
  ⊑ ($ 0) ⟨ℕ!⟩
```

## Chain Edge: `rep = ＇ X₂`

The conservative answer is to treat `＇ X₂` as non-`★`.

The reason is parametricity at the outer seal.  A representation variable is
opaque at the point where the source seal is introduced.  Even if a later store
chain eventually resolves `X₂` to `★`, allowing an immediate partner such as
`($ 0) ⟨ℕ!⟩` would choose and expose a ground before the aligned-name chain has
been followed.

The checked scratch witness is:

```agda
chain-variable-rep-direct-tag-empty :
  SealPartnerOK (＇ Fin.suc Fin.zero) (just Fin.zero) CRP.U
  → ⊥
```

where `CRP.U` is the direct tagged target from the chain probe.  Valid chain
proofs must either keep the partner untagged, keep the top-level tag
name-protected, or re-emit target seals until the source seal representation is
literally `★`, where `star-rep-target` permits ordinary dynamic tags.

This matches the current target-chain proof shape: variable-payload target
seals are re-emitted through `target-seal＇-reemit`, and the arbitrary-tag case
is reserved for the literal `★` terminus.

## Scratch Validation

`SurgeryPreflightScratch.agda` checks these refined facts:

| Item | Refined verdict | Checked evidence |
|---|---|---|
| Mismatch premise, source seal rep `ℕ` | Underivable in the refined scratch relation. | `refined-restricted-mismatch-premise-empty`, `mismatch-target-not-ok-refined-nat` |
| Name-tagged positive, source seal rep `ℕ` | Derivable. | `name-tag-target-ok-refined`, `sealed-source-name-tag-positiveʳᵗᵈ` |
| Dyn-id descent, source seal rep `★` | Derivable. | `terminus-instanceB-inner-dyn-id-ok`, `terminus-instanceB-inner-dyn-id-live` |
| Terminus Instance A tagged partner | Survives by name protection; the direct dyn-id helper remains rejected because the source rep is `∀X⇒X`, not `★`. | `terminus-instanceA-tagged-partner-ok`, `terminus-instanceA-live-tagged-input`, `terminus-instanceA-direct-dyn-id-empty` |
| Terminus Instance B tagged partner | Survives; both visible and inner dyn-id forms are admitted by `rep = ★`. | `terminus-instanceB-tagged-partner-ok`, `terminus-instanceB-live-tagged-input`, `terminus-instanceB-inner-dyn-id-ok` |
| M3 `cast⊑cast²` stuck input | Derivable-and-must-be-proven. | `m3-cast⊑cast²-input` |
| M3 `cast⊑²` stuck input | Derivable-and-must-be-proven. | `m3-cast⊑²-source-to-tag`, `m3-cast⊑²-premise`, `m3-cast⊑²-input` |
| M3 nested `conceal⊑²` stuck input | Not eliminated by the refined gate. | `m3-nested-conceal-target-ok` |
| M3 `rebase-onlyᴸ` stuck input | Changed verdict: derivable, because the source seal rep is `★`. | `m3-rebase-only-input-ok` |
| Chain edge, source seal rep `＇ X₂` | Direct ground-tag partner rejected. | `chain-variable-rep-direct-tag-empty` |
| `seal-descent-at-var-＇` re-emission | Survives; it is target-only re-emission. | `seal-descent-at-var-＇-reemit-instance` |
| `left-path-argument₄` old wrapper | Still rejected: source seal rep is `ℕ` and no aligned target name is present. | `left-path-argument₄-old-wrapper-empty` |
| `left-path-argument₄` semantic payload | Survives. | `left-path-argument₄-payload-survives` |
| Cambridge Example 12 gates | Unchanged. | `example12-checkpoint₁-gate-refined`, `example12-paired-seal-gate-refined` |
| `compile-preserves-imprecision²` gate shape | Unchanged. | `compile-preserves-imprecision²-gate-refined` |

The older `TagDisciplineScratch.agda` still checks as a historical baseline,
including the representative catalog gates from the first dossier pass.

Validation transcript:

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

Additional non-gate check against the current modified worker file:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda
# exit 42
# Existing unsolved metas in the current modified worktree:
#   SourceStripWorkerProof.agda:726, 749, 836, 847, 941, 1002, 1029
```

## Migration Plan

1. `GTSFImp/proof/DGG/CastTermImprecision.agda`
   - Add a public source-seal partner predicate keyed by the source seal
     representation.
   - Refine `RebaseAtᴸ` or add a sibling source-seal rebase witness that keeps
     the optional aligned target name visible.
   - Add the predicate as a premise to source-side seal descent.  The premise
     should be representation-keyed, not merely target-shape keyed.
   - Leave `conceal⊑conceal²`, target-only wrappers, `StoreRepImp`, and
     `compile-preserves-imprecision²` constructors alone unless the proof
     migration exposes a real need.

2. `GTSFImp/proof/DGG/Examples2.agda`
   - Keep Cambridge Example 12 derivations unchanged.
   - Rewrite `left-path-argument₄` and downstream checkpoints that depend on
     it so the target argument is name-protected before any top-level tag, or
     move the checkpoint to a name-aligned point.

3. `GTSFImp/proof/DGG/Inversion/*`
   - Add cases for the new representation-keyed side-condition premise in
     existing `conceal⊑²` branches.
   - Do not rely on the side condition to eliminate `rep = ★` top-level tags;
     those branches remain proof obligations.
   - For `rep = ＇ X₂`, keep direct ground-tag partners impossible and route
     chain proofs through target-seal re-emission or a literal `★` terminus.

4. Probes and historical records
   - Keep `MismatchProbeScratch.agda` as a live-regression record of the old
     relation.
   - Use `SurgeryPreflightScratch.agda` as the refined scratch gate.
   - Update `ExtraCastRight2Counterexample.agda`: its direct
     representation-tag source-seal shape should become stale, while the
     name-tagged positive variant should replace it.

5. Gates
   - Re-run `CastTermImprecision.agda`, `Examples2.agda`,
     `CompilePreservesImprecision2.agda`, `CompileImageShape.agda`,
     `Phase3DeepDives.agda`, and the M3 inversion files after the live relation
     is patched.

## ExtraCastRight² Impact

With the refined discipline restored, the original `ExtraCastRight²`
value-conclusion statement should become provable again for this mismatch
family: the direct target `($ 0) ⟨ℕ!⟩` cannot be the partner of a source seal
whose representation is `ℕ`.  The surviving tagged partner is the
name-protected shape `((...) ↓ seal Y R) ⟨Y!⟩`; applying the extra `Y?`
projection then cancels at the same ground instead of stepping to
`tag-untag-bad`.

This does not prove the whole M3 theorem by itself.  In particular,
`rep = ★` direct tags remain legal, and `rep = ＇ X₂` must be handled as an
opaque chain edge rather than collapsed into the `★` case.
