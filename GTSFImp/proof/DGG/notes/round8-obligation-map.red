Round 8 obligation map: seal partner re-emission ring

Command used for the primary red:

```text
agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/TargetChainProof.agda
```

Primary red:

```text
GTSFImp/proof/DGG/Inversion/TargetChainProof.agda:88,3-90,29
(q₁ : _B_133 ⊑ᵂ⟨ W ⟩ _B′_134) →
W ∣ γ ⊢² _M_129 ↓ _c_138 ⊑ _M′_130 ↓ _c′_139 ∶ q₁
!=< W ∣ γ ⊢² V ⟨ c ⟩ ↓ seal X ★ ⊑ U ↓ seal Y ★ ∶ q
```

The missing explicit first argument to `CTI2.conceal⊑conceal²` is:

```agda
CTI2.MatchedConcealPartnerOK W₂
  (V ⟨ c ⟩) (Conversion.seal X ★) Y U
```

equivalently:

```agda
CTI2.Rep★PartnerOK W₂ X (V ⟨ c ⟩) (just Y) U
```

Why this is not just a local omitted argument:

The source-seal branch after `STC.seal-transfer` may have this shape:

```text
Wᵖ ∣ γᵖ ⊢² P ⟨ X! ⟩ ⊑ U₂ ⟨ Y₂! ⟩ ∶ ★⊑★
------------------------------------------------ matched source/target seal
W₁ ∣ γ₁ ⊢² (P ⟨ X! ⟩ ↓ seal X ★)
  ⊑ (U₂ ⟨ Y₂! ⟩ ↓ seal Y ★) ∶ X⊑Y
```

`seal-transfer` strips the target seal and returns a conclusion world such as
`dynWorld W₁`, while the inner matched-tag alignment `X ~ Y₂` belongs to the
premise world `Wᵖ`.  The re-emitted paired star seal needs partner evidence in
the post-transfer world for:

```agda
(P ⟨ X! ⟩ ↓ seal X ★) ⟨ X! ⟩
```

against `U₂ ⟨ Y₂! ⟩`.  In general, neither `rep★-var-tag` nor
`rep★-matched-inner-tags` can build this:

- `rep★-var-tag` needs the target top tag to be the outer `Y`.
- `rep★-matched-inner-tags` needs `CenterAligned W₂ X Y₂`.
- the available `CenterAligned` evidence can be in `Wᵖ`, not `W₂`.

This is the same witness ring as round 6, shifted from the pre-transfer
payload to the post-transfer casted payload.  It should not be discharged by
inventing an alignment.

Verified green during this audit:

- `GTSFImp/proof/DGG/CastTermImprecision2.agda`
- `GTSFImp/proof/DGG/CastTermImprecision2Typing.agda`
- `GTSFImp/proof/DGG/SealTransferCore.agda`
- `GTSFImp/proof/DGG/TermImpDecay.agda`
- `GTSFImp/proof/DGG/Inversion/TargetWalkSupport.agda`

Surprise reds during this audit:

- `GTSFImp/proof/DGG/Inversion/TargetDescentProof.agda:141`
  still passes `{partner = partner}` to `STC.seal-transfer`, whose live
  signature no longer accepts that implicit argument.
- `GTSFImp/proof/DGG/CenterRename.agda:478`
  reuses `ok` after center renaming without renaming the partner evidence.
- `GTSFImp/proof/DGG/Examples2.agda:537`
  has stale paired-seal re-emission syntax with no matched partner argument.
- `GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda`
  currently reaches the `TargetChainProof` red first, but contains the same
  stale/re-emission shapes at lines 254, 361, and 420.

Obligation classification

Evidence-local / already principled:

- `CastTermImprecision2.agda:388-495`: defines the partner evidence surface:
  `Rep★PartnerOK`, `SealPartnerOK`, `SourceConcealPartnerOK`, and
  `MatchedConcealPartnerOK`.
- `TermImpDecay.agda:120-184`, `359-418`: partner evidence is structurally
  decayed through `EnvDecay`.  This checks.
- `SealTransferCore.agda:125-154`, `369-393`: matched paired-seal partner
  evidence is converted into a source-conceal partner after decay.  This
  checks, but it does not create the later post-transfer paired-seal partner.
- `TargetWalkSupport.agda:688-796`: views over source-seal partner evidence.
  These are eliminators/classifiers, not new synthesis of the missing paired
  partner.
- `TargetWalkSupport.agda:829-832`: `target-source-var-chain` emits a
  source-only seal using `plain-target not-↓`; evidence is local.
- `RightInjInversion2Proof.agda:523-525`, `584-587`: source-only re-emission
  uses `plain-target not-↓`; evidence is local.
- `SourceStripProof.agda:74-79`: source-only star re-emission uses
  `rep★-var-tag (pivotAligned rb)`; evidence is local.
- Probe source-only non-variable cases such as `TagBoundaryProbe.agda:210`,
  `ChainRideProbe.agda:203`, `StarRepChainProbe.agda:182`,
  and `TerminusRebuildProbe.agda:394` use `rep★-nonvar-tag`; evidence is local.

Needs a local API update, not a new lemma:

- `CenterRename.agda:477-502`: `ok` must be transported/renamed in the same way
  as `SourceConcealPartnerOK` and `MatchedConcealPartnerOK` are decayed in
  `TermImpDecay`; reusing it directly changes the world indices.
- `TargetDescentProof.agda:141`: remove the stale `{partner = partner}` call to
  `STC.seal-transfer` if this helper remains.  The partner premise is no longer
  consumed there.
- `TargetChainProof.agda:50-82`, `TargetChainProof.agda:155-168`,
  `TargetStripProof.agda:899-914`, `TargetStripProof.agda:956-960`,
  `SourceStripWorkerProof.agda:250-259`, and similar refutation branches:
  pattern clauses must bind the new `ok` argument before `mono`; most of these
  clauses throw it away.
- `Examples2.agda:537`, `Examples2.agda:1025`, `Examples2.agda:2571`,
  `Examples2.agda:2680`, `SourceStarProbe.agda:143`,
  `CenterCrossingProbe.agda:210`, `StarRepChainProbe.agda:190`,
  and `TerminusRebuildProbe.agda:220/404/417`: paired-seal examples need
  explicit `matched-seal-star-partner (...)` evidence.  Most are untagged or
  non-variable target payloads and should be evidence-local.

Needs a real lemma or a surface change:

- `TargetChainProof.agda:88`: needs
  `Rep★PartnerOK W₂ X (V ⟨ c ⟩) (just Y) U` after `seal-transfer`.
  This is the active blocker and is suspicious for the source-seal/matched-inner
  case described above.
- `SourceStripWorkerProof.agda:420`: same post-transfer paired-star re-emission
  shape as `TargetChainProof.agda:88`, with an extra outer rebase composition.
  It will need the same resolution.
- `TargetDescentProof.agda:164`: `target-seal★-extract` re-emits a paired star
  seal from `TargetSealTerminal`, but that record does not carry
  `MatchedConcealPartnerOK` or `Rep★PartnerOK`.  Either the terminal surface must
  store the partner, or extraction needs a new explicit partner premise.
- `TargetStripProof.agda:740` and `TargetStripProof.agda:1118`: direct
  `seal-transfer` calls currently have no explicit partner, which matches the
  live signature.  Their returned terminal data later has the same extraction
  risk if paired re-emission is required.
- `SourceStripWorkerProof.agda:361`: `plain-star-rep-premise` currently tries
  `CTI2.star-rep-target` without a `Rep★PartnerOK` argument.  The statement
  has arbitrary target `U`, so this is not evidence-local unless the statement
  is strengthened with a partner premise or restricted to an untagged target.

Suspicious / likely underivable without changing the partner surface:

- Any attempt to prove a general lemma of the shape
  `SpineValue V → Inert c → Value U → W ∣ γ ⊢² V ⊑ U ∶ X⊑★ →
  Rep★PartnerOK W X (V ⟨ c ⟩) (just Y) U` must handle source-seal heads in the
  derivation.  When the source-seal partner is `rep★-matched-inner-tags`, its
  alignment is a premise-world fact, not a conclusion-world fact.
- The concrete round-6 counter-shape still applies after transfer with the
  source payload wrapped by another inert source tag; the required final partner
  asks for the outer source tag to align with the target payload's inner tag.

No Agda source changes were made for this map.
