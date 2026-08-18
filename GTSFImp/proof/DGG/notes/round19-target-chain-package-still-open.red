Round 19 current blocker: TargetChainProof.agda:88 still needs the
branch-sensitive source-star package.

Focused command:

agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/TargetChainProof.agda

Current error:

  GTSFImp/proof/DGG/Inversion/TargetChainProof.agda:88,3-90,29

  (q₁ : _B_133 ⊑ᵂ⟨ W ⟩ _B′_134) →
  W ∣ γ ⊢² _M_129 ↓ _c_138 ⊑ _M′_130 ↓ _c′_139 ∶ q₁
  !=<
  W ∣ γ ⊢² V ⟨ c ⟩ ↓ seal X ★ ⊑ U ↓ seal Y ★ ∶ q

Live context at the site:

  sv     : SpineValue V
  inert  : Inert c
  vU     : Value U
  X∈     : sourceStoreʷ W ∋ X ⦂ ★
  Y∈     : targetStoreʷ W ∋ Y ⦂ ★
  D      : W ∣ γ ⊢² V ⊑ U ↓ seal Y ★ ∶ q

  STC.seal-transfer sv vU X∈ D
    = W₂ , γ₂ , link , mono₂ , sc₂ , q₂ , D₂

  link : CTI2.RebaseAt W₂ W X Y
  q₂   : (＇ X) ⊑ᵂ⟨ W₂ ⟩ ★
  D₂   : W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂

The old direct paired re-emission no longer applies because
`CTI2.conceal⊑conceal²` now requires matched seal-star partner evidence.
The needed package is still:

  Σ[ Xᴿ? ∈ Maybe (TyVar Δᴿ) ]
    STC.TaggedTransferOutput W₂ γ₂ (V ⟨ c ⟩) U X Xᴿ?

plus the source-side premise:

  W₂ ∣ γ₂ ⊢² (V ⟨ c ⟩) ↓ seal X ★ ⊑ U ∶ q₂

The permissive shortcut "any target at ★ is a valid seal-star partner" was
not added: `SourceStarPackageCounterScratch.agda` still type-checks and
refutes arbitrary output packages for the bad round-15/InstanceB target.

