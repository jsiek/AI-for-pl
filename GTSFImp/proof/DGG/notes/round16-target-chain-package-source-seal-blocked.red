Round 16 blocked case: source-seal sub-head of the site-shaped
source-star package still lacks a target-pedigree bridge.

Checked commands:

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/\
abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home \
  agda -i GTSFImp -v0 GTSFImp/proof/DGG/SealTransferCore.agda

This is green after backing out the exploratory helper.

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/\
abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home \
  agda -i GTSFImp -v0 \
  GTSFImp/proof/DGG/Inversion/TargetChainProof.agda

Still red at TargetChainProof.agda:88, exactly as before:

  (q₁ : _B_133 ⊑ᵂ⟨ W ⟩ _B′_134) →
  W ∣ γ ⊢² _M_129 ↓ _c_138 ⊑ _M′_130 ↓ _c′_139 ∶ q₁
  !=<
  W ∣ γ ⊢² V ⟨ c ⟩ ↓ seal X ★ ⊑ U ↓ seal Y ★ ∶ q

The attempted site-shaped package builder for the peeled premise needs:

  CTI2.Rep★PartnerOK W₂ X
    ((P ↓ seal X ★) ⟨ id (＇ X) ! ⟩)
    (just Y) U

in the source-seal sub-head of the peeled premise:

  D₂ =
    CTI2.conceal⊑²
      (CTI2.seal-partner-ok
        (CTI2.star-rep-target partner))
      monoᵖ (CTI2.tag-rebase-varᴸ rbᵖ) scᵖ
      (CTI2.⊢↓-sealˣ X∈ᵖ) prem q₂

where:

  rbᵖ     : CTI2.RebaseAt W₃ W₂ X Yᵖ
  partner : CTI2.Rep★PartnerOK W₃ X P (just Yᵖ) U

The natural round-trip construction is:

  CTI2.rep★-round-trip
    (STC.transport-rep★-partner-ok rbᵖ partner)

but `transport-rep★-partner-ok rbᵖ partner` has target pedigree
`just Yᵖ`, while the outer target peel requires `just Y`.
Agda reports the core mismatch as:

  Yᵖ != Y
  when checking rbᵖ has type CTI2.RebaseAt W₃ W₂ X Y

The outer target-only peel does provide:

  link : CTI2.RebaseAt W₂ W₀ X Y

but `CTI2.RebaseAt.pivotAligned link` is an alignment in the outer
world `W₀`, not in the peeled world `W₂`.  Therefore it does not identify
the source-seal descent target `Yᵖ` with the outer target peel `Y`.
The existing uniqueness tools (`target-pedigree-unique`,
`tag-target-pedigree-unique`) require rebases over the same world pair, so
they do not apply to:

  rbᵖ  : CTI2.RebaseAt W₃ W₂ X Yᵖ
  link : CTI2.RebaseAt W₂ W₀ X Y

This is the exact sub-head that prevents completing:

  emit-tagged-transfer-peel :
    SpineValue V →
    Inert c →
    Value U →
    sourceStoreʷ W ∋ X ⦂ ★ →
    targetStoreʷ W ∋ Y ⦂ ★ →
    W ∣ γ ⊢² V ⊑ (U ↓ seal Y ★) ∶ q →
    STC.TaggedTransferOutput W γ (V ⟨ c ⟩) U X Y

without either a new pedigree theorem relating consecutive same-source
rebases to the outer target peel, or a stronger premise that carries the
needed `Yᵖ ≡ Y` equality.
