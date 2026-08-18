Round 7 blocked red: paired-star re-emission now needs a payload partner

Command:

```text
agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/TargetChainProof.agda
```

Current red:

```text
/home/runner/AI-for-pl/GTSFImp/proof/DGG/Inversion/TargetChainProof.agda:88,3-90,29
(q₁ : _B_133 ⊑ᵂ⟨ W ⟩ _B′_134) →
W ∣ γ ⊢² _M_129 ↓ _c_138 ⊑ _M′_130 ↓ _c′_139 ∶ q₁
!=< W ∣ γ ⊢² V ⟨ c ⟩ ↓ seal X ★ ⊑ U ↓ seal Y ★ ∶ q
when checking that the inferred type of an application
  (q₁ : _B_133 ⊑ᵂ⟨ W ⟩ _B′_134) →
  W ∣ γ ⊢² _M_129 ↓ _c_138 ⊑ _M′_130 ↓ _c′_139 ∶ q₁
matches the expected type
  W ∣ γ ⊢² V ⟨ c ⟩ ↓ seal X ★ ⊑ U ↓ seal Y ★ ∶ q
```

Root cause:

`SealTransferCore.seal-transfer` now correctly harvests the premise-world
payload partner from the matched paired-seal rule.  To make that evidence
available, I added a narrow `MatchedConcealPartnerOK` premise to
`CastTermImprecision2.conceal⊑conceal²`; its star-seal case carries:

```agda
Rep★PartnerOK Wᵖ X source-payload (just Y) target-payload
```

This makes `SealTransferCore.agda` check, but every construction of a paired
star seal now has to provide its own payload partner.  The first such
re-emission is `TargetChainProof.agda:88`:

```agda
CTI2.conceal⊑conceal² ? mono₂ link sc₂
  (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈)
  (CTI2.cast⊑² c D₂ ★⊑★) q
```

The required missing witness is:

```agda
CTI2.MatchedConcealPartnerOK W₂
  (V ⟨ c ⟩) (Conversion.seal X ★) Y U
```

equivalently, for the star constructor:

```agda
CTI2.Rep★PartnerOK W₂ X (V ⟨ c ⟩) (just Y) U
```

Known context at the site:

```agda
sv     : SpineValue V
inert  : Inert c
vU     : Value U
X∈     : sourceStoreʷ W ∋ X ⦂ ★
Y∈     : targetStoreʷ W ∋ Y ⦂ ★
D      : W ∣ γ ⊢² V ⊑ U ↓ seal Y ★ ∶ q

STC.seal-transfer sv vU X∈ D
  = W₂ , γ₂ , link , mono₂ , sc₂ , q₂ , D₂

link : RebaseAt W₂ W X Y
D₂   : W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂
```

Why this is the new blocker:

The round-6 false lemma was the caller-side attempt to synthesize a partner
for the uncast source payload.  After moving partner ownership into the
matched seal rule, the next consumer that re-emits a paired star seal must
construct the corresponding partner for the *casted* source payload
`V ⟨ c ⟩`.  That is a separate lemma, likely an inert-source-tag partner
lemma using `inert : Inert c`, `link : RebaseAt W₂ W X Y`, `vU`, and `D₂`.

No postulate or hole was added.
