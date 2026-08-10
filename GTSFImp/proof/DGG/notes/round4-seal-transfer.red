Round 4 blocked red note: SealTransferCore premise-world partner attempt

Attempted live changes:
- `conceal⊑²` was changed to require
  `SourceConcealPartnerOK W′ M c Xᴿ? M′`.
- `TermImpDecay` tag-rebase-var branch was changed to decay partner
  evidence with `blend-decay {W′ = W′} {Wᵈ = Wᵈ}`.
- `SealTransferCore` was then refactored to remove the old hidden
  conclusion-world `partner` from `seal-transfer` and rebuild recursive
  `star-rep-target` evidence from the stripped premise.

Blocking Agda goal:

```text
/home/runner/AI-for-pl/GTSFImp/proof/DGG/SealTransferCore.agda:163,3-199,50
I'm not sure if there should be a case for the constructor
_∣_⊢²_⊑_∶_.•⊑², because I get stuck when trying to solve the
following unification problems (inferred index ≟ expected index):
  M ⦂∀ C [ A ] ≟ V
  M′ ≟ U₂ ⟨ idᵍ (＇ Y₂) ! ⟩
  {substᵗ (singleSubᵗ A) C} ≟ {＇ X₂}
  {B} ≟ {★}
  r ≟ p
when checking the definition of sourceVarTargetTagAligned
```

The missing lemma shape is:

```agda
sourceVarTargetTagAligned : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {X₂ : TyVar Δᴸ} {Y₂ : TyVar Δᴿ}
    {V : Term Δᴸ} {U₂ : Term Δᴿ}
    {μᴿ : Env∼ Δᴿ} {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {p : (＇ X₂) ⊑ᵂ⟨ W ⟩ ★}
  → SpineValue V
  → W ∣ γ ⊢² V
      ⊑ (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ (idᵍ (＇ Y₂)) ⟩)
      ∶ p
  → CTI2.CenterAligned W X₂ Y₂
```

The simple target-only cast case closes by
`SPT.right-var-obligation-view`. The blocker is extracting the same
alignment through non-syntax-directed derivations such as `•⊑²`, where
Agda cannot rule out computed source indices like `C [ A ]ᵗ ≡ ＇ X₂`.
This needs a dedicated inversion lemma over `SpineValue` and the
`_∣_⊢²_⊑_∶_` derivation, not just the local line-377 reindex.
