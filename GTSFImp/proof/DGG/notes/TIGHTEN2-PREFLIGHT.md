# Rep-`★` Partner Tightening Pre-flight 2

Scope:

- Root scratch only: `Tighten2PreflightScratch.agda`.
- No edits under `GTSFImp/`.
- Checked against the stopped migration edits on
  `agent/gtsf-extra-cast-right`.

Toolchain:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 <file>
```

## Refined Predicate

The scratch models a hypothetical source-payload-indexed `Rep★PartnerOK₂`:

- `rep★-untagged`: target partner is not a top-level tag.
- `rep★-nonvar-tag`: target partner is a top-level injection at a non-variable
  ground.
- `rep★-outer-var-tag`: target partner is a variable injection at `Y`, and
  the outer seal source name `X` is center-aligned with `Y`.
- `rep★-matched-inner-tags`: target partner is `U₂⟨Y₂!⟩`, the source seal
  payload is `V₂⟨X₂!⟩`, and `X₂` is center-aligned with `Y₂`.  The outer seal
  target pivot remains separate.

Main scratch locations:

- Predicate: `Tighten2PreflightScratch.agda:44`.
- Matched-inner fourth clause: `Tighten2PreflightScratch.agda:70`.
- TargetChain/TargetDescent partner witnesses:
  `Tighten2PreflightScratch.agda:88` and `:117`.
- RightInj partner witness: `Tighten2PreflightScratch.agda:137`.
- No-target variable-tag emptiness:
  `Tighten2PreflightScratch.agda:163`.
- ℕ-tagged payload/no-target emptiness:
  `Tighten2PreflightScratch.agda:176`.
- Ground-target caveat witness:
  `Tighten2PreflightScratch.agda:230`.

## Verdict Table

| Check | Verdict | Evidence |
|---|---|---|
| `TargetChainProof:85` hidden `partner` obligation | Formation-dischargeable under the payload-indexed predicate. | `target-chain-85-partner` builds the partner from `p₂ : ＇ X₂ ⊑ᵂ ＇ Y₂` using `variable-obligation-aligns`. |
| `TargetDescentProof:138` hidden `partner` obligation | Formation-dischargeable under the same condition. | `target-descent-138-partner` is the same witness shape. |
| `RightInjInversion2Proof:612` hidden `partner` obligation | Formation-dischargeable. | The branch already extracts `aligned`; `right-inj-612-partner` consumes that directly. |
| Matched-inner clause vs bare payload | Excluded for the matched-inner route. | `bare-payload-matched-inner-empty`. |
| Two open worker clauses, ℕ-tagged payloads | Still formation-impossible. | `nat-payload-var-tag-no-target-empty`; `LambdaImpProbe.agda` also still checks. |
| Prior probe/example/catalog gates | Pass against the stopped tree. | See command transcript below. |
| Literal ground-tag poison if `rep★-nonvar-tag` is retained | **Not excluded by this candidate.** | `ground-target-still-admitted` shows arbitrary non-variable target tags remain admitted. |

## Important Caveat

The fourth clause fixes the variable-tagged partner that is aligned with the
inner `(X₂,Y₂)` tag pair rather than the outer `(X,Y)` seal pair.

It does **not** remove the current `rep★-nonvar-tag` admission.  Therefore, if
the required poison check is the literal ProjectionMismatch shape with a
ground-tagged target partner such as `$0⟨ℕ!⟩`, then the current-plus-fourth
candidate is not a clean tightening: that shape remains formable through the
non-variable-target clause.

This is separate from the two open worker clauses.  Those stay empty because
their target variable-tag partner has no target pivot and their source payloads
are ℕ-tagged, so they cannot enter through the matched-inner clause.

## Command Transcript

Successful scratch and gate checks:

```sh
agda -i GTSFImp -v0 Tighten2PreflightScratch.agda
agda -i GTSFImp -v0 GTSFImp/proof/DGG/Examples2.agda
agda -i GTSFImp -v0 GTSFImp/proof/DGG/TerminusRebuildProbe.agda
agda -i GTSFImp -v0 GTSFImp/proof/DGG/StarRepChainProbe.agda
agda -i GTSFImp -v0 GTSFImp/proof/DGG/ChainRideProbe.agda
agda -i GTSFImp -v0 GTSFImp/proof/DGG/TagBoundaryProbe.agda
agda -i GTSFImp -v0 GTSFImp/proof/DGG/Phase3DeepDives.agda
agda -i GTSFImp -v0 GTSFImp/proof/DGG/Parked/ParkedD4CheckpointLemma.agda
agda -i GTSFImp -v0 GTSFImp/proof/DGG/ReachabilityCatalog.agda
agda -i GTSFImp -v0 GTSFImp/proof/DGG/CompileImageShape.agda
agda -i GTSFImp -v0 InitialPairScratch.agda
agda -i GTSFImp -v0 GTSFImp/proof/DGG/LambdaImpProbe.agda
agda -i GTSFImp -v0 GTSFImp/proof/DGG/CompilePreservesImprecision2.agda
```

Known stopped live checks remain stopped at the requested metas:

```sh
agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/TargetChainProof.agda
# unsolved meta: TargetChainProof.agda:85,10-33

agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/TargetDescentProof.agda
# unsolved meta: TargetDescentProof.agda:138,10-33

agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/RightInjInversion2Proof.agda
# unsolved meta: RightInjInversion2Proof.agda:612,12-36
```

## Bottom Line

The candidate fourth clause is viable for the three variable-tag partner
obligations and does **not** resurrect the two open worker clauses.

It is not sufficient, by itself, to keep the literal ground-tag poison excluded
while retaining `rep★-nonvar-tag`.
