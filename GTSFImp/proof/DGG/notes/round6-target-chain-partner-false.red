Round 6 blocked red note: target-seal★-partner is false as stated

Requested lemma:

```agda
target-seal★-partner : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {γ : CTI2.CtxImp W}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {q : (＇ X) CTI2.⊑ᵂ⟨ W ⟩ (＇ Y)}
  → SpineValue V
  → Value U
  → CTI2.sourceStoreʷ W ∋ X ⦂ ★
  → CTI2.targetStoreʷ W ∋ Y ⦂ ★
  → W CTI2.∣ γ CTI2.⊢² V ⊑ U ↓ seal Y ★ ∶ q
  → CTI2.Rep★PartnerOK W X V (just Y) U
```

This is not derivable under the current live `Rep★PartnerOK` predicate.  I
checked a temporary scratch module, then deleted it, with:

```text
agda -i GTSFImp -v0 TargetChainPartnerCounterScratch.agda
```

The scratch module checked.

Counter-witness shape:

```agda
source-inner   = dyn-id ↓ seal X ★
source-payload = source-inner ⟨ X! ⟩
source         = source-payload ↓ seal X ★

target-inner   = dyn-id ↓ seal Y₂ ★
target-payload = target-inner ⟨ Y₂! ⟩
target         = target-payload ↓ seal Y ★
```

with `X` aligned to `Y` in `W`, `X` aligned to `Y₂` in the premise world
`Wᵖ`, and both target store entries dynamic:

```agda
X∈  : sourceStoreʷ W ∋ X ⦂ ★
Y∈  : targetStoreʷ W ∋ Y ⦂ ★
Y₂∈ : targetStoreʷ W ∋ Y₂ ⦂ ★
q   : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)
```

The premise required by the requested lemma is inhabited:

```agda
inner-seal² :
  Wᵖ ∣ [] ⊢² source-inner ⊑ target-inner ∶ X⊑Y₂
inner-seal² =
  CTI2.conceal⊑conceal² (λ Z eq → eq) rb-X-Y₂ CTI2.same-[]
    source-seal-⊢ target-Y₂-seal-⊢ dyn-id² X⊑Y₂

payload² :
  Wᵖ ∣ [] ⊢² source-payload ⊑ target-payload ∶ ★⊑★
payload² =
  CTI2.cast⊑cast² X! Y₂! inner-seal² ★⊑★

outer² :
  W ∣ [] ⊢² source ⊑ target ∶ q
outer² =
  CTI2.conceal⊑conceal² mono-W-Wᵖ rb-chain CTI2.same-[]
    source-seal-⊢ target-Y-seal-⊢ payload² q
```

but the requested conclusion is empty:

```agda
no-partner :
  CTI2.Rep★PartnerOK W X source (just Y) target-payload → ⊥
no-partner (CTI2.rep★-untagged ())
no-partner (CTI2.rep★-nonvar-tag ())
```

Agda reports the omitted `rep★-matched-inner-tags` case as impossible because
its source index is a top-level tagged payload, while the goal source index is
the already sealed term:

```text
V₂ ⟨ cX ! ⟩ ≟ source-payload ↓ seal X ★
```

The `rep★-var-tag` case is also impossible in the concrete witness because the
goal carries `just Y` while the payload is tagged at `Y₂`.

Root cause:

The matched source/target seal branch can derive the premise via matched inner
payload tags:

```text
source-payload  ⊑  target-payload
      ↓ seal X ★       ↓ seal Y ★
source          ⊑  target
```

but `STC.seal-transfer` asks for

```agda
CTI2.Rep★PartnerOK W X source (just Y) target-payload
```

instead of a partner indexed by the inner payload needed to rebuild the
source-only seal after stripping the target seal:

```agda
CTI2.Rep★PartnerOK Wᵖ X source-payload (just Y) target-payload
```

This is the pre-cast/sealed-source versus matched-inner payload mismatch from
`TIGHTEN2-BLOCKED.red`, now exposed at `TargetChainProof.agda:85`.

Current red remains:

```text
Unsolved metas at:
  GTSFImp/proof/DGG/Inversion/TargetChainProof.agda:85,10-33
```
