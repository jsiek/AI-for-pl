Round 14 stop note: target-chain package needs source-star partner extraction.

Command:

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/\
abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home \
  agda -i GTSFImp -v0 \
  GTSFImp/proof/DGG/Inversion/TargetChainProof.agda

Current live red remains:

GTSFImp/proof/DGG/Inversion/TargetChainProof.agda:88,3-90,29

  (q₁ : _B_133 ⊑ᵂ⟨ W ⟩ _B′_134) →
  W ∣ γ ⊢² _M_129 ↓ _c_138 ⊑ _M′_130 ↓ _c′_139 ∶ q₁
  !=<
  W ∣ γ ⊢² V ⟨ c ⟩ ↓ seal X ★ ⊑ U ↓ seal Y ★ ∶ q

The already-modeled part is now live and green:

  STC.transport-rep★-partner-ok :
    RebaseAt Wᵖ W X Y
    → CTI2.Rep★PartnerOK Wᵖ X P (just Y) U
    → CTI2.Rep★PartnerOK W X P (just Y) U

  STC.transport-rep★-partner-ok-dyn :
    RebaseAt Wᵖ W X Y
    → CTI2.Rep★PartnerOK (SPT.dynWorld Wᵖ) X P (just Y) U
    → CTI2.Rep★PartnerOK (SPT.dynWorld W) X P (just Y) U

  STC.TaggedTransferOutput W γ P U X Y =
    W ∣ γ ⊢² P ⊑ U ∶ ★⊑★
    × CTI2.MatchedConcealPartnerOK W P (seal X ★) Y U

The remaining unmodeled live obligation is producing that package from
`seal-transfer` in all branches.  The paired-source/paired-target branch can
use the modeled transport:

  partner :
    CTI2.Rep★PartnerOK Wᵖ X P (just Y) U

  prem :
    Wᵖ ∣ γᵖ ⊢² P ⊑ U ∶ ★⊑★

  rbᵖ :
    CTI2.RebaseAt Wᵖ W X Y

But the target-only peel branch of `seal-transfer` returns only:

  link : CTI2.RebaseAt W₂ W X Y
  D₂   : W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂
  q₂   : (＇ X) ⊑ᵂ⟨ W₂ ⟩ ★

To re-emit line 88 without weakening the paired-conceal side condition, one
needs an additional source-star rebuild/package theorem, for example:

  source-star-cast-package : ∀ {Δᴸ Δᴿ Δ}
      {W : CTI2.World Δᴸ Δᴿ Δ} {γ : CTI2.CtxImp W}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X) ∼ ★}
      {q : (＇ X) ⊑ᵂ⟨ W ⟩ ★}
    → SpineValue V
    → Inert c
    → Value U
    → CTI2.sourceStoreʷ W ∋ X ⦂ ★
    → W ∣ γ ⊢² V ⊑ U ∶ q
    → STC.TaggedTransferOutput W γ (V ⟨ c ⟩) U X Y

or, equivalently, a branch-sensitive `seal-transfer` result that returns
both:

  W₂ ∣ γ₂ ⊢² V ⟨ c ⟩ ⊑ U ∶ ★⊑★

and:

  CTI2.MatchedConcealPartnerOK W₂
    (V ⟨ c ⟩) (seal X ★) Y U

in the same `W₂`.

This obligation is distinct from the round-13 same-pivot matched-inner-tags
transport issue: that transport is now handled by the `X₂ ≢ X`
orthogonalization plus recursive `rep★-round-trip`.  The new missing theorem
extracts or rebuilds the source-star partner from the peeled `★` premise when
the transfer branch did not directly expose a `Rep★PartnerOK ... (just Y) ...`
witness.
