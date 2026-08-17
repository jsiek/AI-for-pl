T12 two-sided peel restatements
===============================

Status: statement draft only.  No live DGG module or relation file was edited.

Checked statement probe:

`proof/DGG/notes/probes/T12TwoSidedPeelRestatementProbe.agda`

Focused well-formedness command:

```text
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home \
  agda --safe -i GTSFImp -i GTSFImp/proof/DGG/notes/probes -v0 \
  GTSFImp/proof/DGG/notes/probes/T12TwoSidedPeelRestatementProbe.agda
```

Result: pass.


Design rule
-----------

The replacement design is evidence-forced:

- wrapper peels are two-sided synchronized;
- target keep steps are consumed only by narrow caller-supplied continuations;
- parked evidence for premise worlds is supplied as input and never derived
  from a rebase.


1. Two-sided synchronized peel family
------------------------------------

### Paired conceal-reveal peel

Before context:

```agda
W ∣ γ ⊢²
  ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R)
  ⊑ ((V₀′ ↓ seal Xᴿ R′) ↑ unseal Xᴿ R′) ∶ q

((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R) —→[ keep ] V₀
((V₀′ ↓ seal Xᴿ R′) ↑ unseal Xᴿ R′) —→[ keep ] V₀′
```

After context, matching Probe 3's checked `after-both-peel-same-q` shape:

```agda
W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q
```

Candidate statement:

```agda
PairedConcealRevealPeelᵀ : Set
PairedConcealRevealPeelᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {R : Ty Δᴸ} {R′ : Ty Δᴿ}
    {q : R ⊑ᵂ⟨ W ⟩ R′}
  → Value V₀
  → Value V₀′
  → W ∣ γ ⊢²
      ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R)
      ⊑ ((V₀′ ↓ seal Xᴿ R′) ↑ unseal Xᴿ R′) ∶ q
  → ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R) —→[ keep ] V₀
  → ((V₀′ ↓ seal Xᴿ R′) ↑ unseal Xᴿ R′) —→[ keep ] V₀′
  → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q
```

### Source-only variant, target already unsealed

Probe 2 rules out the still-sealed target endpoint for a partnered non-variable
representation: `R ⊑ᵂ⟨ W ⟩ ＇ Y` is not generally expressible.  The source-only
variant is therefore sound only when the caller supplies positive evidence that
the current target payload was already opened by a target conceal-reveal keep
step.

Before context:

```agda
TargetOpenedByConcealReveal V₀′ R′

W ∣ γ ⊢²
  ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R)
  ⊑ V₀′ ∶ q

((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R) —→[ keep ] V₀
```

After context:

```agda
W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q
```

Candidate statement:

```agda
record TargetOpenedByConcealReveal {Δᴿ : TyCtx}
    (V′ : Term Δᴿ) (R′ : Ty Δᴿ) : Set where
  field
    opened-payload : Term Δᴿ
    opened-pivot : TyVar Δᴿ
    opened-value : Value opened-payload
    opened-step :
      ((opened-payload ↓ seal opened-pivot R′)
        ↑ unseal opened-pivot R′) —→[ keep ] V′

SourceOnlyConcealRevealPeelᵀ : Set
SourceOnlyConcealRevealPeelᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
    {Xᴸ : TyVar Δᴸ} {R : Ty Δᴸ} {R′ : Ty Δᴿ}
    {q : R ⊑ᵂ⟨ W ⟩ R′}
  → Value V₀
  → Value V₀′
  → TargetOpenedByConcealReveal V₀′ R′
  → W ∣ γ ⊢²
      ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R)
      ⊑ V₀′ ∶ q
  → ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R) —→[ keep ] V₀
  → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q
```


2. Supplied parked evidence for conversion frames
------------------------------------------------

### Variant A: direct supplied `ParkedWorld` input

Each frame case receives both the outer world's parked evidence and the premise
world's parked evidence.  The rebase is still present as a wrapper-typing
ingredient, but no frame is allowed to manufacture `ParkedWorld Wᵖ` from
`ParkedWorld W` and the rebase.

```agda
record SimConversionFramesSuppliedParkedᵀ : Set₁ where
  field
    source-reveal-frame :
      ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
        {γᵖ : CtxImp Wᵖ}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ?}
        {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
        {q : A′ ⊑ᵂ⟨ W ⟩ B}
        {c : Conv↑ Δᴸ A A′}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
      → ParkedWorld W
      → ParkedWorld Wᵖ
      → ImpEnvMono W Wᵖ
      → RebaseAtᴸ W Wᵖ Xᴸ?
      → SameCtx {W = W} {W′ = Wᵖ} [] γᵖ
      → sourceStoreʷ W ⊢↑[ Xᴸ? ] c
      → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
      → W ∣ [] ⊢² M ↑ c ⊑ M′ ∶ q
      → M ↑ c —→[ χᴸ ] N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A′ ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B ]
          (M′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

    target-reveal-frame :
      ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
        {γᵖ : CtxImp Wᵖ}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {Xᴿ?}
        {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
        {q : A ⊑ᵂ⟨ W ⟩ B′}
        {c′ : Conv↑ Δᴿ B B′}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
      → ParkedWorld W
      → ParkedWorld Wᵖ
      → ImpEnvMono W Wᵖ
      → RebaseAtᴿ W Wᵖ Xᴿ?
      → SameCtx {W = W} {W′ = Wᵖ} [] γᵖ
      → targetStoreʷ W ⊢↑[ Xᴿ? ] c′
      → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
      → W ∣ [] ⊢² M ⊑ M′ ↑ c′ ∶ q
      → M —→[ χᴸ ] N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B′ ]
          (M′ ↑ c′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

    source-conceal-frame :
      ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
        {γᵖ : CtxImp Wᵖ}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ? Xᴿ?}
        {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
        {q : A′ ⊑ᵂ⟨ W ⟩ B}
        {c : Conv↓ Δᴸ A A′}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
      → ParkedWorld W
      → ParkedWorld Wᵖ
      → SourceConcealPartnerOK Wᵖ M c Xᴿ? M′
      → ImpEnvMono W Wᵖ
      → TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
      → SameCtx {W = W} {W′ = Wᵖ} [] γᵖ
      → sourceStoreʷ W ⊢↓[ Xᴸ? ] c
      → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
      → W ∣ [] ⊢² M ↓ c ⊑ M′ ∶ q
      → M ↓ c —→[ χᴸ ] N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A′ ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B ]
          (M′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

    target-conceal-frame :
      ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
        {γᵖ : CtxImp Wᵖ}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {Xᴿ?}
        {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
        {q : A ⊑ᵂ⟨ W ⟩ B′}
        {c′ : Conv↓ Δᴿ B B′}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
      → ParkedWorld W
      → ParkedWorld Wᵖ
      → ImpEnvMono W Wᵖ
      → RebaseAtᴿ Wᵖ W Xᴿ?
      → SameCtx {W = W} {W′ = Wᵖ} [] γᵖ
      → targetStoreʷ W ⊢↓[ Xᴿ? ] c′
      → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
      → W ∣ [] ⊢² M ⊑ M′ ↓ c′ ∶ q
      → M —→[ χᴸ ] N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B′ ]
          (M′ ↓ c′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)
```

### Variant B: boundary-stack input

This variant packages the outer parked evidence, premise parked evidence, and
the boundary certificate together.  The checked probe uses current
`CatchupBoundary` as the local analogue of the PR #162-style
`TargetBlameBoundary` stack.

```agda
record SuppliedBoundaryStack {Δᴸ Δᴿ Δ}
    (kind : CatchupBoundaryKind)
    (Xᴸ? : Maybe (TyVar Δᴸ)) (Xᴿ? : Maybe (TyVar Δᴿ))
    (W Wᵖ : World Δᴸ Δᴿ Δ) : Set₁ where
  field
    boundary-outer-parked : ParkedWorld W
    boundary-premise-parked : ParkedWorld Wᵖ
    boundary-certificate : CatchupBoundary kind Xᴸ? Xᴿ? W Wᵖ
```

Full candidate statement:

```agda
record SimConversionFramesBoundaryStackᵀ : Set₁ where
  field
    source-reveal-frame :
      ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
        {γᵖ : CtxImp Wᵖ}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ? Xᴿ?}
        {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
        {q : A′ ⊑ᵂ⟨ W ⟩ B}
        {c : Conv↑ Δᴸ A A′}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
      → SuppliedBoundaryStack source-reveal-boundary Xᴸ? Xᴿ? W Wᵖ
      → ImpEnvMono W Wᵖ
      → RebaseAtᴸ W Wᵖ Xᴸ?
      → SameCtx {W = W} {W′ = Wᵖ} [] γᵖ
      → sourceStoreʷ W ⊢↑[ Xᴸ? ] c
      → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
      → W ∣ [] ⊢² M ↑ c ⊑ M′ ∶ q
      → M ↑ c —→[ χᴸ ] N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A′ ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B ]
          (M′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

    target-reveal-frame :
      ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
        {γᵖ : CtxImp Wᵖ}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {Xᴸ? Xᴿ?}
        {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
        {q : A ⊑ᵂ⟨ W ⟩ B′}
        {c′ : Conv↑ Δᴿ B B′}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
      → SuppliedBoundaryStack target-reveal-boundary Xᴸ? Xᴿ? W Wᵖ
      → ImpEnvMono W Wᵖ
      → RebaseAtᴿ W Wᵖ Xᴿ?
      → SameCtx {W = W} {W′ = Wᵖ} [] γᵖ
      → targetStoreʷ W ⊢↑[ Xᴿ? ] c′
      → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
      → W ∣ [] ⊢² M ⊑ M′ ↑ c′ ∶ q
      → M —→[ χᴸ ] N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B′ ]
          (M′ ↑ c′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

    source-conceal-frame :
      ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
        {γᵖ : CtxImp Wᵖ}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ? Xᴿ?}
        {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
        {q : A′ ⊑ᵂ⟨ W ⟩ B}
        {c : Conv↓ Δᴸ A A′}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
      → SuppliedBoundaryStack source-conceal-boundary Xᴸ? Xᴿ? W Wᵖ
      → SourceConcealPartnerOK Wᵖ M c Xᴿ? M′
      → ImpEnvMono W Wᵖ
      → TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
      → SameCtx {W = W} {W′ = Wᵖ} [] γᵖ
      → sourceStoreʷ W ⊢↓[ Xᴸ? ] c
      → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
      → W ∣ [] ⊢² M ↓ c ⊑ M′ ∶ q
      → M ↓ c —→[ χᴸ ] N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A′ ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B ]
          (M′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

    target-conceal-frame :
      ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
        {γᵖ : CtxImp Wᵖ}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {Xᴸ? Xᴿ?}
        {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
        {q : A ⊑ᵂ⟨ W ⟩ B′}
        {c′ : Conv↓ Δᴿ B B′}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
      → SuppliedBoundaryStack target-conceal-boundary Xᴸ? Xᴿ? W Wᵖ
      → ImpEnvMono W Wᵖ
      → RebaseAtᴿ Wᵖ W Xᴿ?
      → SameCtx {W = W} {W′ = Wᵖ} [] γᵖ
      → targetStoreʷ W ⊢↓[ Xᴿ? ] c′
      → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
      → W ∣ [] ⊢² M ⊑ M′ ↓ c′ ∶ q
      → M —→[ χᴸ ] N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B′ ]
          (M′ ↓ c′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)
```

Comparison: the direct `ParkedWorld` variant is the smallest repair to the
current `SimConversionFramesᵀ` surface and makes the D6 fallback explicit.  The
boundary-stack variant is better if downstream catchup/blame code needs to
remember why the premise world exists; it centralizes parked evidence and the
boundary shape in one input, at the cost of an extra certificate value that
one-step frame replay may not otherwise inspect.


3. Restated T1 dispatcher keep-outcome surfaces
------------------------------------------------

Old surface being replaced:

```agda
target-reveal/conceal-keep-rel :
  ∀ {M N N₁}
  → W ∣ γ ⊢² M ⊑ N ↑/↓ c ∶ qC
  → (N ↑/↓ c) —→[ keep ] N₁
  → Value N₁
  → W ∣ γ ⊢² M ⊑ N₁ ∶ qC
```

Replacement surface: the dispatcher receives narrow continuation records.  A
target reveal `conceal-reveal` keep step is discharged only by the paired peel
or by the source-only peel with `TargetOpenedByConcealReveal` evidence.  Target
conceal `id-conceal` keep steps get the analogous two-sided/source-opened
continuations.

```agda
record TargetRevealKeepOutcomeContinuationsᵀ : Set₁ where
  field
    paired-conceal-reveal :
      PairedConcealRevealPeelᵀ
    source-opened-conceal-reveal :
      SourceOnlyConcealRevealPeelᵀ


record TargetConcealKeepOutcomeContinuationsᵀ : Set₁ where
  field
    paired-id-conceal :
      ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {q : A ⊑ᵂ⟨ W ⟩ B}
      → Value V₀
      → Value V₀′
      → W ∣ γ ⊢²
          (V₀ ↓ id↓ A)
          ⊑ (V₀′ ↓ id↓ B) ∶ q
      → (V₀ ↓ id↓ A) —→[ keep ] V₀
      → (V₀′ ↓ id↓ B) —→[ keep ] V₀′
      → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q

    source-opened-id-conceal :
      ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {q : A ⊑ᵂ⟨ W ⟩ B}
      → Value V₀
      → Value V₀′
      → W ∣ γ ⊢² (V₀ ↓ id↓ A) ⊑ V₀′ ∶ q
      → (V₀ ↓ id↓ A) —→[ keep ] V₀
      → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q


record RestatedDispatcherKeepOutcomesᵀ : Set₁ where
  field
    target-reveal-outcomes : TargetRevealKeepOutcomeContinuationsᵀ
    target-conceal-outcomes : TargetConcealKeepOutcomeContinuationsᵀ
```
