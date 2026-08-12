Round 13 stop note: tagged transfer hits the same-pivot matched-inner-tags
head.

Command used to confirm the live red before analysis:

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/\
abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home \
  agda -i GTSFImp -v0 \
  GTSFImp/proof/DGG/Inversion/TargetChainProof.agda

Live red remains:

GTSFImp/proof/DGG/Inversion/TargetChainProof.agda:88,3-90,29

The requested tagged-transfer wrapper can package the old reconstructed
premise and the matched partner in the same output world for the easy
`Rep★PartnerOK` heads:

  rep★-untagged
  rep★-nonvar-tag
  rep★-var-tag
  rep★-round-trip, recursively

The blocker is the `rep★-matched-inner-tags` subhead when the inner source tag
uses the same source variable as the outer source seal.

Problem head inside the paired-star seal-transfer case:

  D =
    CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {γᵖ = γᵖ}
      (CTI2.matched-seal-star-partner
        (CTI2.rep★-matched-inner-tags
          {Y = Y} {X₂ = X} {Y₂ = Y₂} alignedᵖ))
      monoᵖ rbᵖ scᵖ
      (CTI2.⊢↓-sealˣ X∈ᵖ)
      (CTI2.⊢↓-sealˣ Y∈)
      prem .q

where:

  rbᵖ : CTI2.RebaseAt Wᵖ W X Y
  alignedᵖ :
    CTI2.CenterAligned Wᵖ X Y₂
  partner :
    CTI2.Rep★PartnerOK Wᵖ X
      (V₂ ⟨ X! ⟩) (just Y) (U₂ ⟨ Y₂! ⟩)
  prem :
    Wᵖ ∣ γᵖ ⊢² V₂ ⟨ X! ⟩ ⊑ U₂ ⟨ Y₂! ⟩ ∶ ★⊑★

The tagged wrapper would have to return one common world W₂ with both:

  W₂ ∣ γ₂ ⊢²
    ((V₂ ⟨ X! ⟩) ↓ seal X ★) ⟨ X! ⟩
      ⊑ U₂ ⟨ Y₂! ⟩ ∶ ★⊑★

and

  CTI2.MatchedConcealPartnerOK W₂
    (((V₂ ⟨ X! ⟩) ↓ seal X ★) ⟨ X! ⟩)
    (seal X ★) Y (U₂ ⟨ Y₂! ⟩)

Choosing W₂ = SPT.dynWorld W gives the premise via the existing
dyn-decay reconstruction, but the partner would need:

  CTI2.CenterAligned (SPT.dynWorld W) X Y₂

The available facts only give:

  CTI2.CenterAligned Wᵖ X Y₂
  CTI2.RebaseAt Wᵖ W X Y

The rebase changes the source pivot X.  It freezes target embeddings and
preserves non-pivot source embeddings, but it gives no equality between
`toRenameᵗ (ηᴸʷ Wᵖ) X` and `toRenameᵗ (ηᴸʷ W) X`.

Choosing W₂ = SPT.dynWorld Wᵖ gives the round-trip partner directly via
`decay-rep★-round-trip`, but then the premise requires rebuilding the source
seal in Wᵖ, which needs a same-world source tag rebase/mark for the outer seal:

  CTI2.TagRebaseAtᴸ (SPT.dynWorld Wᵖ) (SPT.dynWorld Wᵖ)
    (just X) (just Y)

The available `rbᵖ` aligns X with Y in W, not in Wᵖ.

`target-pedigree-unique` does not apply in this head.  It identifies two
target pivots when both are witnessed by `RebaseAt` values with the same
premise and conclusion worlds.  Here we have only:

  rbᵖ : CTI2.RebaseAt Wᵖ W X Y
  alignedᵖ : CTI2.CenterAligned Wᵖ X Y₂

There is no `CTI2.RebaseAt Wᵖ W X Y₂`: constructing it would require exactly
the missing conclusion-world alignment `CenterAligned W X Y₂`.

This is not a missing hidden argument at `TargetChainProof.agda:88`.  The
tagged-transfer surface still needs either:

  1. a proven transport principle for round-trip `Rep★PartnerOK` across a
     source-pivot rebase that covers this same-pivot matched-inner-tags case;
     or
  2. a stricter partner relation/theorem that rules out or separately records
     the same-pivot target tag pedigree.

Adding a new constructor to `Rep★PartnerOK` would make the package easy, but it
would weaken the discipline of the partner relation rather than prove the
missing transport.
