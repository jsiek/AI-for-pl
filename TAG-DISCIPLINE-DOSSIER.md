# Tag Discipline Dossier

Investigation target: branch `agent/gtsf-extra-cast-right`, read-only over
`GTSFImp/`, with root scratch only.

Checked scratch: `TagDisciplineScratch.agda`.

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

## Why It Was Admitted

The shape was admitted deliberately during the stale-mark repair, not because
Cambridge Example 12 needed it.

The original import commit `f8ec889` records a bare-seal right-injection
counterexample: a displaced source variable kept a stale precise mark, so the
post-tag-cancellation relation was empty. Commit `c55606b` repaired that by
allowing imprecision marks to decay and adding `WFWorld`. In that version of
`ExtraCastRight2Counterexample.agda`, the repaired output used:

```agda
repaired-seal² =
  CTI2.conceal⊑² (λ _ eq → eq) (CTI2.rebase-varᴸ U-Y-rebaseᵈ)
    CTI2.same-[] source-U-seal-typed repaired-base² U-to-starᵈ
```

where `repaired-base²` is `$ 0 ⊑ ($ 0) ⟨ℕ!⟩ : ℕ ⊑ ★`.

After M2 (`1ce5afd`), the target-moving outer stale/dynamized rebases became
empty by `ηᴿ-frozen`, but the repaired sealed-source/right-representation-tag
shape remained as design history and as a live derivable source-only
`conceal⊑²` pattern. The mismatch probe (`59b1336`) then showed that this
left `ExtraCastRight²` refutable as stated.

## Candidate Evaluation

### Restrict Source-Seal Target Partners

Chosen. Add a side condition to source-side seal descent: if the target partner
is top-level tagged, it must be protected/name-tagged at the aligned target seal
name; otherwise the target partner must not be top-level tagged.

In scratch this is `SealTargetOK`:

- `plain-target` for targets whose top constructor is not `_⟨_⟩`;
- `name-tagged-target` for `((M ↓ seal Y R) ⟨Y!⟩)`.

This kills the probe because `($ 0) ⟨ℕ!⟩` is a top-level tag but not a
name-tagged sealed target. It preserves the intended positive form:
`($ 0) ↓ seal U ℕ ⊑ (($ 0 ⟨ℕ!⟩) ↓ seal Y ★) ⟨Y!⟩`.

Expected breakage: `Examples2.left-path-argument₄` currently uses the rejected
source-only pattern:

```agda
($ 7) ↓ example12-target-X-seal
  ⊑ $ 7 ⟨ left-path-ℕ!₂ ⟩
```

with `CTI2.conceal⊑²` and `rebase-onlyᴸ`. That proof should be migrated to a
name-protected checkpoint or avoided by shifting the comparison to a point where
the target has a real aligned seal name. Cambridge Example 12 proper uses paired
seal/reveal checkpoints and is not on this path.

### Make `StoreRepImp` Opaque at Seals

Not sufficient alone. The probe's `U` and `Y` are already center-aligned, so an
opaque name-level rebase obligation could still be discharged by `X⊑X`; the
unrestricted `conceal⊑²` plus `⊑cast²` would still put the target at `ℕ!`.
It also risks needless churn in all rebase witnesses.

### Add Mark/World Honesty

Not sufficient alone. The probe world uses dynamic marks at both centers, so the
existing `WFWorld`-style mark honesty is vacuous. A stronger world-level
honesty fact would have to talk about target tag shape, which is really the
constructor-side discipline above.

## Scratch Validation

`TagDisciplineScratch.agda` checks these statement-first facts:

- `restricted-mismatch-premise-empty`: the restricted fragment cannot derive
  the probe premise.
- `name-tag-target-ok`: the name-tagged partner shape is allowed.
- `sealed-source-name-tag-positiveᵗᵈ`: a sealed source relates to its
  name-tagged target partner.
- `example12-checkpoint₁-gate` and `example12-paired-seal-gate`: representative
  Example 12 gates are unchanged.
- `representative-catalog-initial-gate` and
  `representative-catalog-image-gate`: representative catalog gates still check.
- `compile-preserves-imprecision²-gate`: the compiler theorem surface is still
  available unchanged.

Validation transcript:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 TagDisciplineScratch.agda
# exit 0

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 MismatchProbeScratch.agda
# exit 0, confirming the live relation still admits the old probe

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/CastTermImprecision2.agda
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

## Migration Plan

1. `GTSFImp/proof/DGG/CastTermImprecision2.agda`
   - Add a public target-shape predicate for source-side seal partners.
   - Refine `RebaseAtᴸ` or add a sibling source-seal rebase witness that keeps
     the optional aligned target name visible.
   - Add the predicate as a premise to source-side seal descent. Prefer a
     structural variant for composite `Conv↓` pivots rather than a one-off rule
     for atomic `seal`.
   - Leave `conceal⊑conceal²`, target-only wrappers, `StoreRepImp`, and
     `compile-preserves-imprecision²` constructors alone unless the proof
     migration exposes a real need.

2. `GTSFImp/proof/DGG/Examples2.agda`
   - Keep Cambridge Example 12 derivations unchanged.
   - Rewrite `left-path-argument₄` and downstream checkpoints that depend on
     it so the target argument is name-protected before any top-level tag, or
     move the checkpoint to a name-aligned point.

3. `GTSFImp/proof/DGG/Inversion/*`
   - Add cases for the new side-condition premise in the existing
     `conceal⊑²` branches.
   - In the right-tag projection case, use the side condition to refute the
     direct representation-tag target. The surviving name-tag case reduces by
     matching the seal-name ground.

4. Probes and historical records
   - Keep `MismatchProbeScratch.agda` as a live-regression record of the old
     relation.
   - Convert `TagDisciplineScratch.agda` into checked negative/positive tests
     after the live relation is patched.
   - Update `ExtraCastRight2Counterexample.agda`: its current
     `repaired-seal²` should become stale under the restored discipline, while
     the name-tagged positive variant should replace it.

5. Gates
   - Re-run `CastTermImprecision2.agda`, `Examples2.agda`,
     `CompilePreservesImprecision2.agda`, `CompileImageShape.agda`,
     `Phase3DeepDives.agda`, and then the M3 inversion files once the sibling
     Inversion worktree is ready.

## ExtraCastRight² Impact

With the discipline restored, the original `ExtraCastRight²` value-conclusion
statement should become provable again for this family: the mismatch branch is
refutable at the lemma level because the direct target `($ 0) ⟨ℕ!⟩` cannot be
the partner of a source seal at `U`. The surviving tagged partner is the
name-tagged shape `((...) ↓ seal Y R) ⟨Y!⟩`; applying the extra `Y?` projection
then cancels at the same ground instead of stepping to `tag-untag-bad`.

This does not prove the whole M3 theorem by itself, but it removes the concrete
counterexample that forced a blame/outcome disjunct.
