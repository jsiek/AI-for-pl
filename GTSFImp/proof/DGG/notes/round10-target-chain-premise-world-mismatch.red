Round 10 stop note: TargetChainProof paired-star re-emission has a
premise-world mismatch not modeled by the scratch witness.

Command:

agda -i GTSFImp -v0 \
  GTSFImp/proof/DGG/Inversion/TargetChainProof.agda

Current live red after removing the temporary probe clause:

GTSFImp/proof/DGG/Inversion/TargetChainProof.agda:88,3-90,29
(q₁ : _B_133 ⊑ᵂ⟨ W ⟩ _B′_134) →
W ∣ γ ⊢² _M_129 ↓ _c_138 ⊑ _M′_130 ↓ _c′_139 ∶ q₁
!=< W ∣ γ ⊢² V ⟨ c ⟩ ↓ seal X ★ ⊑ U ↓ seal Y ★ ∶ q
when checking that the inferred type of an application
  (q₁ : _B_133 ⊑ᵂ⟨ W ⟩ _B′_134) →
  W ∣ γ ⊢² _M_129 ↓ _c_138 ⊑ _M′_130 ↓ _c′_139 ∶ q₁
matches the expected type
  W ∣ γ ⊢² V ⟨ c ⟩ ↓ seal X ★ ⊑ U ↓ seal Y ★ ∶ q

Known missing first argument:

CTI2.MatchedConcealPartnerOK W₂
  (V ⟨ c ⟩) (seal X ★) Y U

Attempted head-first harvest shape:

D =
  CTI2.⊑conceal² mono rbᴿ sc (CTI2.⊢↓-sealˣ Y∈)
    Dᵖ q

Dᵖ =
  CTI2.conceal⊑²
    (CTI2.seal-partner-ok (CTI2.star-rep-target partner))
    monoᵖ (CTI2.tag-rebase-varᴸ linkᵖ) scᵖ
    (CTI2.⊢↓-sealˣ X∈′) prem pᵈ

The scratch witness provides:

CTI2.rep★-round-trip partner

but this witness lives in the inner source-seal premise world, the world of
`partner` and `prem`.

The live paired outer constructor also needs its premise derivation in that
same world.  The available derivation for the source-seal payload is `Dᵖ`, whose
conclusion world is the source-seal conclusion world, not the inner partner
world.

More concretely, after composing the outer target-seal rebase and the inner
source-seal rebase, Agda accepts that the final paired constructor wants

CTI2.ImpEnvMono W Wᵖ
CTI2.RebaseAt Wᵖ W X Y
CTI2.SameCtx γ γᵖ
CTI2.MatchedConcealPartnerOK Wᵖ
  ((P ↓ seal X ★) ⟨ X! ⟩) (seal X ★) Y U

but the reusable premise derivation has type

Wᵈ ∣ γᵈ ⊢² (P ↓ seal X ★) ⊑ U ∶ pᵈ

so `CTI2.cast⊑² c Dᵖ ★⊑★` is in `Wᵈ`, not `Wᵖ`.

A stricter same-target-name probe also exposed that `partner`'s target pedigree
is introduced by the inner `TagRebaseAtᴸ`; Agda does not definitionally know it
is the outer target seal name `Y`.

This is not the old missing-argument meta alone.  It is a new live obligation:
bridge the source-seal conclusion derivation into the harvested partner world,
or enrich the partner/terminal surface so the final paired constructor can use
the source-seal conclusion-world derivation with the premise-world partner
pedigree.  I did not make that relation/surface change.
