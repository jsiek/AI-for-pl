Round 17 stopped: option-B package surface leaves TargetChainProof.agda:88
needing a branch-sensitive transfer package.

Checked context:

agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/TargetChainProof.agda

Current red:

  GTSFImp/proof/DGG/Inversion/TargetChainProof.agda:88,3-90,29

  (q₁ : _B_133 ⊑ᵂ⟨ W ⟩ _B′_134) →
  W ∣ γ ⊢² _M_129 ↓ _c_139 ⊑ _M′_130 ↓ _c′_140 ∶ q₁
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
  D₂   : W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂
  q₂   : (＇ X) ⊑ᵂ⟨ W₂ ⟩ ★

What option B changes:

  STC.emit-tagged-transfer no longer needs the package target to be the
  conclusion-world Y.  It can consume:

    STC.TaggedTransferOutput W₂ γ₂ (V ⟨ c ⟩) U X Xᴿ?

  for any premise-world package index Xᴿ?, then use `link` only for the
  conclusion-world target seal.

Missing live package:

  Σ[ Xᴿ? ∈ Maybe (TyVar Δᴿ) ]
    STC.TaggedTransferOutput W₂ γ₂ (V ⟨ c ⟩) U X Xᴿ?

Equivalently, besides the premise:

  CTI2.cast⊑² c D₂ ★⊑★ :
    W₂ ∣ γ₂ ⊢² V ⟨ c ⟩ ⊑ U ∶ ★⊑★

the re-emission needs a matched partner in that same W₂:

  CTI2.MatchedConcealPartnerOK W₂
    (V ⟨ c ⟩) (seal X ★) Xᴿ? U

Why this is not the old `Yᵖ ≡ Y` bridge:

The preflight scratch validates the source-seal sub-head when the inner
source-only descent exposes:

  rbᵖ     : CTI2.RebaseAt W₃ W₂ X Yᵖ
  partner : CTI2.Rep★PartnerOK W₃ X P (just Yᵖ) U

and the package is built in W₂ at `just Yᵖ`:

  CTI2.rep★-round-trip
    (STC.transport-rep★-partner-ok rbᵖ partner)

That avoids comparing Yᵖ with the outer Y.

The live `seal-transfer` result, however, returns only `link`, `q₂`, and
`D₂`.  It does not return the branch-local `rbᵖ`/`partner` evidence needed
to build the new `TaggedTransferOutput` package.  A general theorem that
packages every `D₂` at an arbitrary target name is still refuted by
`SourceStarPackageCounterScratch`; the new needed theorem must be
existential/branch-sensitive and preserve the premise-world package index.

No postulate or hole was added for this obligation.
