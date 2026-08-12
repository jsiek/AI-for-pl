# M5 smart-comma rule statement

Gate: M-1 only.  This note drafts the rule and pre-flights its statement in
`M5SmartCommaRuleScratch.agda`.  No live relation file is edited here.

## Informal rule

Cambridge Example 4 has two derivations.  The first uses split/extend; the
second uses `⊒Λ (with smart comma ,,)`.  The relevant informal clauses are:

    Γ, α:=☆, Δ ,, α:=★  =  Σ, α:=id_★, Δ
    Γ ,, α:=★           =  Σ, α:=★        if α ∉ dom(Σ)

The CTI2 A3 reading is:

- after right instantiation, the target store already contains generated slots
  `β := ＇α` and `α := ★`;
- if the pending source binder has no old source variable already aligned at
  target alias center cβ, the smart source comma may merge the pending source
  binder with cβ instead of front-lifting a fresh source center;
- the merged premise world keeps target embeddings frozen, lifts the source
  store, maps the new source variable to cβ, keeps old source variables fixed,
  and marks both cβ and cα as `X⊑★`;
- other one-sided source binders may still enter fresh, but the A3 migration
  needs the fresh center behind the generated target window, not in front of it.

The dynamic marks are not optional under current CTI2 reveal evidence:
`StoreRepImp` canonicalizes `β` through `α` to `★`, so the generated reveals
need `＇cβ ⊑ ★` and `＇cα ⊑ ★`.

## Decision

Use a separate constructor, not a generalization of the existing `Λ⊑²`
constructor.

Rationale: this keeps the migration diff smaller and preserves all existing
plain `Λ⊑²` callers and proofs.  M-2 will add one guarded constructor case to
consumers instead of changing the premise world of an existing constructor.
The trade-off is one more syntax-directed case in every `⊢²` eliminator, with
some duplicated typing/inversion proof structure from `Λ⊑²`.

The existing `Λ⊑Λ²` and plain `Λ⊑²` clauses stay untouched.

## Exact surface

The M-1 scratch states the proposed live surface as an extended relation
`_∣_⊢²ˢ_⊑_∶_` with `from-⊢²` embedding the current relation and one new
constructor.  The live M-2 constructor would have this shape inside
`CastTermImprecision2._∣_⊢²_⊑_∶_`:

```agda
Λ⊑²-smart-comma :
    ∀ {Δᵐ}
      {Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ}
      {γᵐ : CtxImp Wᵐ}
      {V : Term (suc Δᴸ)} {M : Term Δᴿ}
      {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
      {p : A ⊑ᵂ⟨ Wᵐ ⟩ B}
  → NonVar A
  → Fin.zero ∈ᵗ A
  → SmartCommaLiftᴸ W Wᵐ
  → SmartLiftCtxᴸ {W = W} {Wᵐ = Wᵐ} γ γᵐ
  → Value V
  → ⟨ Δᴿ , targetStoreʷ W , tgtCtxʷ γ ⟩ ⊢ M ⦂ B
  → Wᵐ ∣ γᵐ ⊢² V ⊑ M ∶ p
  → (q : `∀ A ⊑ᵂ⟨ W ⟩ B)
    -------------------------------------------
  → W ∣ γ ⊢² Λ V ⊑ M ∶ q
```

The helper premises are:

```agda
data SmartLiftCtxᴸ {Δᴸ Δᴿ Δ Δᵐ}
    {W : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ} :
    CtxImp W → CtxImp Wᵐ → Set where
  smart-lift-[] : SmartLiftCtxᴸ [] []

  smart-lift-∷ : ∀ {γ γᵐ A B p pᵐ}
    → SmartLiftCtxᴸ γ γᵐ
    → SmartLiftCtxᴸ (ctx-imp A B p ∷ γ)
        (ctx-imp (⇑ᵗ A) B pᵐ ∷ γᵐ)

data SmartCommaLiftᴸ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    ∀ {Δᵐ} → World (suc Δᴸ) Δᴿ Δᵐ → Set where
  smart-fresh-behind :
    ∀ {Δᵐ} {Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ}
    → SmartFreshBehindGuard W Wᵐ
    → SmartCommaLiftᴸ W Wᵐ

  smart-merge-alias :
    ∀ {Wᵐ : World (suc Δᴸ) Δᴿ Δ} {β α}
    → SmartAliasMergeGuard W Wᵐ β α
    → SmartCommaLiftᴸ W Wᵐ
```

The alias guard is the smart-comma merge guard:

```agda
record SmartAliasMergeGuard {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ)
    (Wᵐ : World (suc Δᴸ) Δᴿ Δ)
    (β α : Fin.Fin Δᴿ) : Set where
  field
    β:=＇α : targetStoreʷ W ∋ β ⦂ ＇ α
    α:=★ : targetStoreʷ W ∋ α ⦂ ★
    sourceStore-lifted :
      sourceStoreʷ Wᵐ ≡ store-lift (sourceStoreʷ W)
    targetStore-same :
      targetStoreʷ Wᵐ ≡ targetStoreʷ W
    target-frozen : ∀ Xᴿ
      → toRenameᵗ (ηᴿʷ Wᵐ) Xᴿ ≡ toRenameᵗ (ηᴿʷ W) Xᴿ
    pending-at-alias :
      toRenameᵗ (ηᴸʷ Wᵐ) Fin.zero ≡ toRenameᵗ (ηᴿʷ W) β
    old-source-frozen : ∀ Xᴸ
      → toRenameᵗ (ηᴸʷ Wᵐ) (Fin.suc Xᴸ)
        ≡ toRenameᵗ (ηᴸʷ W) Xᴸ
    no-old-source-at-alias : ∀ Xᴸ
      → toRenameᵗ (ηᴸʷ W) Xᴸ ≢ toRenameᵗ (ηᴿʷ W) β
    alias-mark-dynamic :
      impEnvʷ Wᵐ (toRenameᵗ (ηᴿʷ W) β) ≡ X⊑★
    name-mark-dynamic :
      impEnvʷ Wᵐ (toRenameᵗ (ηᴿʷ W) α) ≡ X⊑★
```

The fresh-behind guard is needed for D1's remaining one-sided outer source
binder:

```agda
record SmartFreshBehindGuard {Δᴸ Δᴿ Δ Δᵐ}
    (W : World Δᴸ Δᴿ Δ)
    (Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ) : Set where
  field
    oldCenters : Δ ↪ᵗ Δᵐ
    sourceStore-lifted :
      sourceStoreʷ Wᵐ ≡ store-lift (sourceStoreʷ W)
    targetStore-same :
      targetStoreʷ Wᵐ ≡ targetStoreʷ W
    target-frozen : ∀ Xᴿ
      → toRenameᵗ (ηᴿʷ Wᵐ) Xᴿ
        ≡ toRenameᵗ oldCenters (toRenameᵗ (ηᴿʷ W) Xᴿ)
    old-source-frozen : ∀ Xᴸ
      → toRenameᵗ (ηᴸʷ Wᵐ) (Fin.suc Xᴸ)
        ≡ toRenameᵗ oldCenters (toRenameᵗ (ηᴸʷ W) Xᴸ)
    fresh-not-target : ∀ Xᴿ
      → toRenameᵗ (ηᴿʷ Wᵐ) Xᴿ
        ≢ toRenameᵗ (ηᴸʷ Wᵐ) Fin.zero
    fresh-mark-dynamic :
      impEnvʷ Wᵐ (toRenameᵗ (ηᴸʷ Wᵐ) Fin.zero) ≡ X⊑★
```

## Pre-flight status

Checked command:

```sh
env AGDA_DIR=/home/runner/AI-for-pl/.agda-cache agda -l standard-library \
  -i GTSFImp -i . -v0 M5SmartCommaRuleScratch.agda
```

- E4: `CHECKED-OK`.
  `e4-smart-preflight` instantiates `Λ⊑²-smart-comma` with
  `e4-merge-guard`, `e4-post-rel`, `e4-target-post-⊢`, and the A3 witnesses
  from `M5SmartCommaCalibrationScratch.agda`
  (`a3-e4-inner-rebaseᴿ`, `a3-e4-outer-rebaseᴿ`,
  `a3-e4-term-var-leaf-ok`, `a3-e4-type-leaf-ok`).  This is the
  smart-comma counterpart of the existing depth-0 package
  `Λ⊑Λ²-post-body-transport`; it coexists with A0 rather than replacing it.
- D1: `CHECKED-OK` at the finite blocker site.
  `d1-inner-smart-preflight` instantiates the alias merge at the inner pending
  binder and constructs the reveal-wrapped target package with
  `d1-post-rel`, `d1-merge-guard`, `a3-d1-inner-rebaseᴿ`,
  `a3-d1-outer-rebaseᴿ`, `a3-d1-term-var-leaf-ok`, and
  `a3-d1-type-leaf-ok`.  `d1-top-smart-preflight` also checks the two-rule
  shape: top fresh-behind via `d1-fresh-guard`, then inner alias merge.  Its
  outer occurrence and `q`/intermediate `p` arguments are left explicit because
  those are existing `Λ⊑²` side arguments, not new smart-comma premises.
- Existing clauses: `CHECKED-OK` by construction.
  The scratch embeds the current relation with `from-⊢²`; it does not restate
  or modify `Λ⊑Λ²` or the plain `Λ⊑²` clause.  The smart merge is available
  only through `SmartAliasMergeGuard`; no unguarded merge path exists.

## M-2 migration inventory

Grep command:

```sh
rg -l "x⊑x²|ƛ⊑ƛ²|·⊑·²|Λ⊑Λ²|Λ⊑²|•⊑•²|•⊑²|κ⊑κ²|\
cast⊑cast²|⊑cast²|⊑reveal²|⊑conceal²|cast⊑²|reveal⊑²|\
conceal⊑²|reveal⊑reveal²|conceal⊑conceal²|packaged-seal-star²|\
blame⊑²|⊕⊑⊕²" GTSFImp/proof/DGG -g '*.agda'
```

Riskiest-first migration estimate:

| Module | Hits | Estimated M-2 case cost |
| --- | ---: | --- |
| `Catchup/InstInversionProof.agda` | 223 | XL. Frontier owner; add the productive smart case, then route M5 direct before reviving center-map exchange work. |
| `Inversion/RightInjInversion2Proof.agda` | 126 | XL. Main right-injection inversion; every new source-Λ/right shape must be classified. |
| `Inversion/SourceStripWorkerProof.agda` | 90 | L. M4 worker with source-head stripping; likely one substantial smart-Λ case. |
| `Inversion/TargetStripProof.agda` | 63 | L. Target wrapper inversion; smart case should mostly pass through but must preserve guard evidence. |
| `Inversion/TargetChainProof.agda` | 49 | L. Chain assembly over target wrappers; add recursive smart case. |
| `CenterRename.agda` | 40 | L. Rename transport for arbitrary premise worlds; fresh-behind old-center embedding is the risk. |
| `TargetExtend.agda` | 47 | L. World/ctx target extension lemmas need smart-guard transport. |
| `TermImpDecay.agda` | 52 | M. Structural decay; smart marks are already dynamic, but premise world is not `liftWorldLeft`. |
| `CastTermImprecision2Typing.agda` | 40 | M. Source/target typing cases mirror plain `Λ⊑²`; helper erasure likely straightforward. |
| `TargetBindLift.agda` | 47 | M. Existing lift helper library; either add smart helper lemmas or leave untouched if consumers avoid it. |
| `Catchup/InstInversionDef.agda` | 33 | M. Package types may need smart-premise variants. |
| `CompilePreservesImprecision2.agda` | 18 | M. Compiler output probably still uses existing constructors; add impossible/pass-through case if eliminating. |
| `ExtraCastRight2.agda` | 1 | M. Dispatcher should gain the M5 smart route after proof modules land. |
| `Catchup/ExtraCastRightProof.agda` | 2 | S. Likely pass-through/import fallout. |
| `Inversion/TargetWalkSupport.agda` | 25 | M. Support lemmas for target walks; add smart guard preservation if consumed by strip/chain. |
| `Inversion/TargetDescentProof.agda` | 3 | S. Small direct case split. |
| `Inversion/SourceStripProof.agda` | 1 | S. Wrapper around worker. |
| `Inversion/SourceStripColumnView.agda` | 11 | M. View datatype may need a smart-Λ column. |
| `Inversion/RightInjInversion2Def.agda` | 2 | S. Definitions only unless view indices change. |
| `SealTransferCore.agda` | 17 | M. Rebase helpers may need no-op smart cases if guard evidence is transported through seals. |
| `CastTermImprecision2.agda` | 21 | M. Live constructor plus helper definitions; this is the only relation edit in M-2. |
| `Examples2.agda` | 141 | S/M. Mostly construction examples; add one smart example, fix imports if constructor exports shift. |
| `ReachabilityScreen.agda` | 6 | S. Screen likely construction-only. |
| `Phase3DeepDives.agda` | 8 | S. Probe/example adjustments. |
| `Parked/ParkedD4CheckpointProof.agda` | 8 | S. Parked proof, low priority unless integration target imports it. |
| `TerminusRebuildProbe.agda` | 22 | S. Probe. |
| `LambdaImpProbe.agda` | 22 | S. Probe. |
| `SourceStarProbe.agda` | 3 | S. Probe. |
| `StarRepChainProbe.agda` | 5 | S. Probe. |
| `TagBoundaryProbe.agda` | 8 | S. Probe. |
| `MovedLinkProbe.agda` | 2 | S. Probe. |
| `CenterCrossingProbe.agda` | 4 | S. Probe. |
| `ChainRideProbe.agda` | 3 | S. Probe. |
| `ExtraCastRight2Counterexample.agda` | 12 | S. Counterexample/probe; ensure smart constructor does not invalidate the stated counterexample. |

Scratch files under `GTSFImp/proof/DGG/notes/` also grep constructor names.
They are not migration blockers, but stale scratches may fail broad checks:

| Scratch module | Hits | Estimated cost |
| --- | ---: | --- |
| `notes/M2RebaseRedesignScratch.agda` | 76 | S. Historical scratch. |
| `notes/SurgeryPreflightScratch.agda` | 22 | S. Historical scratch. |
| `notes/TightenPreflightScratch.agda` | 15 | S. Historical scratch. |
| `notes/TwoPostulatesHuntScratch.agda` | 11 | S. Historical scratch. |
| `notes/Tighten9PreflightScratch.agda` | 5 | S. Historical scratch. |
| `notes/TagDisciplineScratch.agda` | 4 | S. Historical scratch. |
| `notes/TargetStripScratch.agda` | 3 | S. Historical scratch. |
| `notes/BodyStripCheck.agda` | 2 | S. Historical scratch. |
| `notes/ChainRideCoreScratch.agda` | 2 | S. Historical scratch. |
| `notes/ChainRideInterfaceScratch.agda` | 2 | S. Historical scratch. |
| `notes/ProjectionMismatchStarRepScratch.agda` | 2 | S. Historical scratch. |
| `notes/SourceStripStarRepScratch.agda` | 2 | S. Historical scratch. |
| `notes/TargetStripNonvarCounterScratch.agda` | 2 | S. Historical scratch. |
| `notes/ChainRideRedesignScratch.agda` | 1 | S. Historical scratch. |
| `notes/Tighten5PreflightScratch.agda` | 1 | S. Historical scratch. |
| `notes/Tighten6PreflightScratch.agda` | 1 | S. Historical scratch. |
| `notes/Tighten7PreflightScratch.agda` | 1 | S. Historical scratch. |
| `notes/Tighten8PreflightScratch.agda` | 1 | S. Historical scratch. |
