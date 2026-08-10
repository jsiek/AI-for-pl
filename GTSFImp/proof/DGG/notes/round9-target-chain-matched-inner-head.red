Round 9 stopped red: TargetChainProof source-seal matched-inner head

Command used for the live check:

```text
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/\
abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home \
  agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/TargetChainProof.agda
```

Live red after removing the temporary probe:

```text
GTSFImp/proof/DGG/Inversion/TargetChainProof.agda:88,3-90,29
(q1 : _B_133 ⊑ᵂ⟨ W ⟩ _B'_134) →
W ∣ γ ⊢² _M_129 ↓ _c_138 ⊑ _M'_130 ↓ _c'_139 ∶ q1
!=< W ∣ γ ⊢² V ⟨ c ⟩ ↓ seal X ★ ⊑ U ↓ seal Y ★ ∶ q
```

The missing first argument is still:

```agda
CTI2.MatchedConcealPartnerOK W₂
  (V ⟨ c ⟩) (Conversion.seal X ★) Y U
```

equivalently:

```agda
CTI2.Rep★PartnerOK W₂ X (V ⟨ c ⟩) (just Y) U
```

Head-first obstruction found while probing the pre-transfer route:

```agda
D =
  CTI2.⊑conceal²
    monoT rbT scT (CTI2.⊢↓-sealˣ Y∈T) Dpayload q

Dpayload =
  CTI2.conceal⊑²
    (CTI2.seal-partner-ok
      (CTI2.star-rep-target
        (CTI2.rep★-matched-inner-tags aligned-inner)))
    monoS (CTI2.tag-rebase-varᴸ linkS) scS
    (CTI2.⊢↓-sealˣ X∈S) prem p★
```

Target payload shape:

```agda
U = U₂ ⟨ _! {G = ＇ Y₂} cY₂ ⟩
```

Source payload shape at the paired-star re-emission:

```agda
V ⟨ c ⟩ = (P ↓ Conversion.seal X ★) ⟨ _! {G = ＇ X} cX ⟩
```

Available evidence:

- `linkS` gives `CTI2.RebaseAt Wp WT X Y`, hence
  `CTI2.CenterAligned WT X Y` at the carried target pivot.
- `aligned-inner` gives `CTI2.CenterAligned Wp X₂ Y₂` for the inner
  source payload tag carried by the rule's premise partner.
- The target-seal head can give `CTI2.RebaseAt WT W X Y`, again for
  the outer target seal pivot `Y`.

Required evidence for the only applicable tagged-target constructor:

```agda
CTI2.rep★-matched-inner-tags :
  CTI2.CenterAligned Wp X Y₂ →
  CTI2.Rep★PartnerOK Wp X
    ((P ↓ Conversion.seal X ★) ⟨ _! {G = ＇ X} cX ⟩)
    (just Y)
    (U₂ ⟨ _! {G = ＇ Y₂} cY₂ ⟩)
```

The failed probe branch attempted to use `linkS` for that final alignment.
Agda correctly rejected it:

```text
TargetChainProof.agda:120,35-39
Y != Y₂ of type Fin Δᴿ
when checking that the expression link has type
CTI2.RebaseAt W′ ... X Y₂
```

Why this branch was not refuted:

- `rep★-matched-inner-tags` explicitly allows the target payload tag `Y₂`
  to differ from the carried target pivot `Y`.
- `TagRebaseAtᴸ` supplies alignment only for the carried pivot `Y`.
- The existing same-pivot composition lemmas require the same target pivot;
  they cannot compose an `X ~ Y` rebase into an `X ~ Y₂` witness.
- This is not one of the no-target emptiness shapes, because the source-seal
  partner is carried with `tag-rebase-varᴸ linkS`.

No imprecision relation changes were made.  The temporary helper used to expose
this head was removed; only the local `ok` binders in the earlier
`TargetChainProof` refutation clauses remain.
