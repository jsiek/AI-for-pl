Round 5 blocked red note: TargetChainProof seal-transfer partner

Landed and checked locally:

- `CastTermImprecision2.conceal⊑²` now indexes
  `SourceConcealPartnerOK` by the recursive premise world `W′`.
- `TermImpDecay` decays the `tag-rebase-varᴸ` source-conceal partner with
  `blend-decay {W′ = W′} {Wᵈ = Wᵈ}`.
- `SealTransferCore` reconstructs the recursive source-seal partner at
  `dynWorld Wᵖ`; untagged/non-variable target payloads stay
  `star-rep-target`, and value variable tags are rebuilt as
  `name-protected-target` by inverting the target value.

Green checks:

```text
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/CastTermImprecision2.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/TermImpDecay.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/SealTransferCore.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/TargetWalkSupport.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/TargetDescentProof.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/RightInjInversion2Proof.agda
```

Remaining blocker:

```text
Unsolved metas at the following locations:
  /home/runner/AI-for-pl/GTSFImp/proof/DGG/Inversion/TargetChainProof.agda:85,10-33
```

At that call, Agda must synthesize the implicit argument to
`STC.seal-transfer`:

```agda
CTI2.Rep★PartnerOK W X V (just Y) U
```

Known context at the call site:

```agda
sv : SpineValue V
inert : Inert c
vU : Value U
X∈ : sourceStoreʷ W ∋ X ⦂ ★
Y∈ : targetStoreʷ W ∋ Y ⦂ ★
q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)
D : W ∣ γ ⊢² V ⊑ U ↓ seal Y ★ ∶ q
```

Failed route:

I tried replacing the `seal-transfer` call in the `S = ★` branch with a
direct source-side `conceal⊑²` using `plain-target not-↓`.  That is not
type-correct: after `CTI2.cast⊑² c D`, the target is still
`U ↓ seal Y ★`, so the premise would need a proof of `★ ⊑ᵂ⟨ W ⟩ ＇ Y`,
not `★⊑★`.

The needed lemma is therefore still a call-site partner synthesis lemma,
not a direct wrapper:

```agda
target-seal★-partner : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {γ : CTI2.CtxImp W}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
  → SpineValue V
  → Value U
  → CTI2.sourceStoreʷ W ∋ X ⦂ ★
  → CTI2.targetStoreʷ W ∋ Y ⦂ ★
  → W ∣ γ ⊢² V ⊑ U ↓ seal Y ★ ∶ q
  → CTI2.Rep★PartnerOK W X V (just Y) U
```

That lemma must use the supervisor correction: in the top variable-tag
payload case, conclude the partner predicate itself.  The proof should not
try to prove a bare `CenterAligned W X₂ Y₂`, because a source-seal layer can
be admitted by matched-inner payload evidence without aligning that outer
source variable to the target tag.
