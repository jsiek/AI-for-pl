Round 11 stop note: TargetChainProof paired-star re-emission still needs a
single-world source-star bridge.

Command:

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/\
abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home \
  agda -i GTSFImp -v0 \
  GTSFImp/proof/DGG/Inversion/TargetChainProof.agda

Live red:

GTSFImp/proof/DGG/Inversion/TargetChainProof.agda:88,3-90,29
(q₁ : _B_133 ⊑ᵂ⟨ W ⟩ _B′_134) →
W ∣ γ ⊢² _M_129 ↓ _c_138 ⊑ _M′_130 ↓ _c′_139 ∶ q₁
!=< W ∣ γ ⊢² V ⟨ c ⟩ ↓ seal X ★ ⊑ U ↓ seal Y ★ ∶ q
when checking that the inferred type of an application
  (q₁ : _B_133 ⊑ᵂ⟨ W ⟩ _B′_134) →
  W ∣ γ ⊢² _M_129 ↓ _c_138 ⊑ _M′_130 ↓ _c′_139 ∶ q₁
matches the expected type
  W ∣ γ ⊢² V ⟨ c ⟩ ↓ seal X ★ ⊑ U ↓ seal Y ★ ∶ q

Adding the hidden first argument leaves the real obligation:

  CTI2.MatchedConcealPartnerOK W₂
    (V ⟨ c ⟩) (seal X ★) Y U

and this witness must be in the same premise world W₂ as

  W₂ ∣ γ₂ ⊢² V ⟨ c ⟩ ⊑ U ∶ ★⊑★ .

The problem case is the paired-star branch harvested inside
SealTransferCore:

  CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {γᵖ = γᵖ}
    (CTI2.matched-seal-star-partner partner)
    monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ X∈ᵖ)
    (CTI2.⊢↓-sealˣ Y∈) prem .p

where

  partner :
    CTI2.Rep★PartnerOK Wᵖ X P (just Y) U

  prem :
    Wᵖ ∣ γᵖ ⊢² P ⊑ U ∶ ★⊑★

  rbᵖ :
    CTI2.RebaseAt Wᵖ W X Y

Route A needs a rebuild in one premise world, not the reusable source-seal
conclusion-world derivation.  The bridge should expose a package of this
shape:

  source-star-paired-bridge : ∀ {Δᴸ Δᴿ Δ}
      {W W⁺ : CTI2.World Δᴸ Δᴿ Δ}
      {γ : CTI2.CtxImp W} {γ⁺ : CTI2.CtxImp W⁺}
      {P : Term Δᴸ} {U : Term Δᴿ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X) ∼ ★}
      {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → Inert c
    → Value U
    → CTI2.ImpEnvMono W W⁺
    → CTI2.RebaseAt W⁺ W X Y
    → CTI2.SameCtx γ γ⁺
    → CTI2.sourceStoreʷ W ∋ X ⦂ ★
    → CTI2.targetStoreʷ W ∋ Y ⦂ ★
    → CTI2.Rep★PartnerOK W⁺ X P (just Y) U
    → W⁺ ∣ γ⁺ ⊢² P ⊑ U ∶ ★⊑★
    → Σ[ Wᵇ ∈ CTI2.World Δᴸ Δᴿ Δ ]
      Σ[ γᵇ ∈ CTI2.CtxImp Wᵇ ]
        ( CTI2.ImpEnvMono W Wᵇ
        × CTI2.RebaseAt Wᵇ W X Y
        × CTI2.SameCtx γ γᵇ
        × Wᵇ ∣ γᵇ ⊢² (P ↓ seal X ★) ⟨ c ⟩ ⊑ U ∶ ★⊑★
        × CTI2.MatchedConcealPartnerOK Wᵇ
            ((P ↓ seal X ★) ⟨ c ⟩) (seal X ★) Y U )

The intended implementation may choose Wᵇ = W⁺ only if it can also derive the
same-world source-seal plumbing:

  same-world-source-star : ∀ {Δᴸ Δᴿ Δ}
      {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
      {γᵖ : CTI2.CtxImp Wᵖ}
      {P : Term Δᴸ} {U : Term Δᴿ}
      {X : TyVar Δᴸ} {Yᵖ : TyVar Δᴿ}
    → CTI2.sourceStoreʷ Wᵖ ∋ X ⦂ ★
    → CTI2.targetStoreʷ Wᵖ ∋ Yᵖ ⦂ ★
    → CTI2.Rep★PartnerOK Wᵖ X P (just Yᵖ) U
    → Wᵖ ∣ γᵖ ⊢² P ⊑ U ∶ ★⊑★
    → Σ[ qᵖ ∈ (＇ X) ⊑ᵂ⟨ Wᵖ ⟩ ★ ]
      Σ[ rbᵖᵖ ∈ CTI2.TagRebaseAtᴸ Wᵖ Wᵖ (just X) (just Yᵖ) ]
        Wᵖ ∣ γᵖ ⊢² (P ↓ seal X ★) ⊑ U ∶ qᵖ

This is exactly where the current evidence stops.  `rbᵖ :
RebaseAt Wᵖ W X Y` aligns X and Y in the conclusion world W, not in Wᵖ.
`ImpEnvMono W Wᵖ` only preserves already-dynamic marks, so it does not by
itself produce the Wᵖ obligation

  (＇ X) ⊑ᵂ⟨ Wᵖ ⟩ ★ .

The decayed variant may be the right package instead:

  decayed-source-star-bridge : ∀ {Δᴸ Δᴿ Δ}
      {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
      {γ : CTI2.CtxImp W} {γᵖ : CTI2.CtxImp Wᵖ}
      {P : Term Δᴸ} {U : Term Δᴿ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X) ∼ ★}
    → Inert c
    → Value U
    → CTI2.ImpEnvMono W Wᵖ
    → CTI2.RebaseAt Wᵖ W X Y
    → CTI2.SameCtx γ γᵖ
    → CTI2.sourceStoreʷ W ∋ X ⦂ ★
    → CTI2.targetStoreʷ W ∋ Y ⦂ ★
    → CTI2.Rep★PartnerOK Wᵖ X P (just Y) U
    → Wᵖ ∣ γᵖ ⊢² P ⊑ U ∶ ★⊑★
    → Σ[ γᵈ ∈ CTI2.CtxImp (SPT.dynWorld Wᵖ) ]
        ( CTI2.ImpEnvMono W (SPT.dynWorld Wᵖ)
        × CTI2.RebaseAt (SPT.dynWorld Wᵖ) W X Y
        × CTI2.SameCtx γ γᵈ
        × (SPT.dynWorld Wᵖ) ∣ γᵈ ⊢²
            (P ↓ seal X ★) ⟨ c ⟩ ⊑ U ∶ ★⊑★
        × CTI2.MatchedConcealPartnerOK (SPT.dynWorld Wᵖ)
            ((P ↓ seal X ★) ⟨ c ⟩) (seal X ★) Y U )

This version uses `SPT.dynWorld-decay Wᵖ` to obtain the `X⊑★` mark and
`TD.decayRebaseAt` to keep the outer rebase pointed from the rebuilt premise
world back to W.  It still needs a public partner-decay/rebuild lemma:

  decay-rep★-round-trip : ∀ {Δᴸ Δᴿ Δ}
      {W : CTI2.World Δᴸ Δᴿ Δ}
      {P : Term Δᴸ} {U : Term Δᴿ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X) ∼ ★}
    → Inert c
    → CTI2.Rep★PartnerOK W X P (just Y) U
    → CTI2.Rep★PartnerOK (SPT.dynWorld W) X
        ((P ↓ seal X ★) ⟨ c ⟩) (just Y) U

`TermImpDecay` and `SealTransferCore` have private partner-decay helpers, but
no public helper with this final round-trip shape.

Pedigree wrinkle:

When the source-star partner is obtained from an inner `TagRebaseAtᴸ`, the
target variable in the partner is not definitionally the outer seal name Y.
The needed identification should be separated:

  target-pedigree-unique : ∀ {Δᴸ Δᴿ Δ}
      {Wᵖ W : CTI2.World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y Yᵖ : TyVar Δᴿ}
    → CTI2.RebaseAt Wᵖ W X Y
    → CTI2.TagRebaseAtᴸ Wᵖ Wᵖ (just X) (just Yᵖ)
    → CTI2.targetStoreʷ W ∋ Y ⦂ ★
    → CTI2.targetStoreʷ W ∋ Yᵖ ⦂ ★
    → Yᵖ ≡ Y

As written, `store-lookup-unique` only identifies the types looked up at the
same variable; it does not identify two different target variables.  The lemma
therefore needs an additional rebase-target uniqueness premise, or a proven
fact that both memberships arise from the same target rebase pivot.

Route B transport would need the following stronger operation:

  transport-source-star-premise : ∀ {Δᴸ Δᴿ Δ}
      {Wᵖ Wᵈ : CTI2.World Δᴸ Δᴿ Δ}
      {γᵖ : CTI2.CtxImp Wᵖ} {γᵈ : CTI2.CtxImp Wᵈ}
      {P : Term Δᴸ} {U : Term Δᴿ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X) ∼ ★}
    → CTI2.SameCtx γᵈ γᵖ
    → CTI2.Rep★PartnerOK Wᵖ X P (just Y) U
    → Wᵈ ∣ γᵈ ⊢² (P ↓ seal X ★) ⟨ c ⟩ ⊑ U ∶ ★⊑★
    → Wᵖ ∣ γᵖ ⊢² (P ↓ seal X ★) ⟨ c ⟩ ⊑ U ∶ ★⊑★

No existing decay/rename lemma has this direction: `TermImpDecay` requires
identical embeddings, and `CenterRename` only embeds into a larger center
context.  The live Wᵈ/Wᵖ mismatch is a source-rebase movement, not a pure
mark decay or center extension.

Until one of these packages is proved, line 88 cannot be fixed by only
supplying the hidden partner argument.
