# T3 non-final source-star view proposal

Date: 2026-08-17

Status: reconnaissance only.  No proof surface or definition has been changed.

## Scope

This note classifies the remaining legacy `NON_COVERING` pragmas in
`Inversion/SourceStripWorkerProof.agda` plus the single
`Inversion/SourceStripColumnView.agda` pragma after the Option-A quarantine.
The central obstruction is still the one-bit view:

```agda
data WrapStarCastFinalView ... where
  wrap-star-cast-final-ready :
    WrapStarCastFinalInput W W′ γ γ′ V U Xᴸ X₂ Y S c p₂ q
    → WrapStarCastFinalView W W′ γ γ′ V U Xᴸ X₂ Y S c p₂ q

  wrap-star-cast-nonfinal :
    WrapStarCastFinalView W W′ γ γ′ V U Xᴸ X₂ Y S c p₂ q
```

`wrap-star-cast-final-view` maps every non-final result from
`target-source-star-at` and `target-source-star-chain` to
`wrap-star-cast-nonfinal`.  Callers only consume
`wrap-star-cast-final-ready`, so the non-final cases are hidden by the caller's
legacy pragma.

The row family collapsed by this view is exactly:

- `target-source-star-residual`
- `target-source-star-paired`
- `target-source-star-payload`
- `target-source-star-chain-residual`
- `target-source-star-chain-paired`
- `target-source-star-chain-payload`

`target-source-star-var-residual` is not currently collapsed here because the
`S = ＇ Y₂` branch uses `target-source-star-chain`, not
`target-source-star-at`.

## Inventory

Legend:

- "Impossible" means semantically empty but still needs a checked emptiness
  argument if the pragma is removed.
- "Collapsed" means reachable under the current inputs but hidden by
  `wrap-star-cast-nonfinal`.
- "Independent" means broad-dispatch or compiled-clause debt unrelated to the
  non-final source-star collapse.

### `SourceStripWorkerProof`

`source-spine-strip-worker-cast-cast`

- Impossible: injected non-variable source endpoints `‵ ι`, `_ ⇒ _`, and
  `` `∀ _ `` are ruled out by `right-var-obligation-view`; inert
  `fun`, `all`, and `genᵥ` rows are ruled out by
  `tagged-target-nonvar-nonstar-spine-⊥`.
- Collapsed: the variable-injection `cast⊑cast²` row calls
  `wrap-star-cast-final-view`; all six non-final rows above are hidden.
- Independent: broad `SourceSpineStrip` rows where the function is called with
  a non-cast spine or a non-`cast⊑cast²` derivation.

`source-spine-strip-worker-cast-step-nonvar`

- Impossible: type-instantiated values, variable-cast values whose typing view
  cannot expose a source seal, and non-variable inert rows, using
  `var-value-view` and `tagged-target-nonvar-nonstar-spine-⊥`.
- Collapsed: none.
- Independent: broad `SourceSpineStrip` rows outside the intended cast-step
  non-variable subproblem.

`source-spine-strip-worker-cast-step-over-seal-star`

- Impossible: the `SPT.var-consistency-view cVar = inj₂ ()` row.
- Collapsed: after `inj₁ refl`, the helper calls
  `wrap-star-cast-final-view`; all six non-final rows are hidden.
- Independent: none in the specialized type.  However, the caller originally
  pattern-matches `star-rep-target no-target ...`; that `no-target` evidence is
  not passed into this helper.  If retained, the whole star-rep variable row is
  likely empty by occupancy.

`source-spine-strip-worker-cast-step-over-seal-name`

- Impossible: none apparent from the current narrow inputs.
- Collapsed: the sole body calls `wrap-star-cast-final-view`; all six
  non-final rows are hidden and are reachable for the name-protected target.
- Independent: none in the specialized type.

`source-spine-strip-worker-cast-step-over-seal`

- Impossible: the source `M ⦂∀ C [ A ]` value row; non-matching
  `SourceConcealPartnerOK`/`SealPartnerOK` rows such as plain targets and
  non-variable star-rep partners should be discharged by target top-shape or
  nonstar arguments.
- Collapsed: none directly; it delegates the star and name rows to the two
  helpers above.
- Independent: partner-view dispatch rows that are neither the checked
  `rep★-var-tag` nor `name-protected-target` cases.

`source-spine-strip-worker-cast-step-wrap`

- Impossible: no local semantic impossibility beyond the intended variable
  injection shape.
- Collapsed: the variable-injection `cast⊑² (⊑cast² ...)` row calls
  `wrap-star-cast-final-view`; all six non-final rows are hidden.
- Independent: broad `SourceSpineStrip` rows outside this cast-step wrapper.

`source-spine-strip-worker-cast-step`

- Impossible: the source `M ⦂∀ C [ A ]` value row and the source-seal routing
  rows already delegated to `source-spine-strip-worker-cast-step-over-seal`.
- Collapsed: the variable-injection `⊑cast²` row calls
  `wrap-star-cast-final-view`; all six non-final rows are hidden.
- Independent: the fallback non-variable cast-step route delegates to
  `source-spine-strip-worker-cast-step-nonvar`.

`source-spine-strip-worker-cast`

- Impossible: none directly in the dispatcher.
- Collapsed: none directly; collapsed rows arrive through
  `source-spine-strip-worker-cast-cast` and
  `source-spine-strip-worker-cast-step`.
- Independent: broad top-spine dispatch rows and the three-way CTI head
  dispatch.

`source-spine-strip-worker-seal-nonvar`

- Impossible: source-instantiation value rows and name-protected target rows
  where a function/all spine would have to match a target variable seal,
  discharged by `tagged-target-nonvar-nonstar-spine-⊥`.
- Collapsed: none.
- Independent: broad rows outside the non-variable sealed-source subproblem.

`source-spine-strip-worker-seal-cast`

- Impossible: source-instantiation value rows and the
  `SPT.var-consistency-view cVar = inj₂ ()` row.  The
  `star-rep-target no-target (rep★-var-tag ...)` row should also now be
  refutable by occupancy if the ignored `no-target` proof is retained.
- Collapsed: three calls to `wrap-star-cast-final-view` hide non-final rows:
  the star-rep variable branch, the name-protected `cast⊑cast²` branch, and
  the name-protected `cast⊑² (⊑cast² ...)` branch.
- Independent: broad sealed-source/cast dispatch rows outside those three
  branches.

`source-spine-strip-worker-seal-source`

- Impossible: source-instantiation values and
  `SPT.var-consistency-view cVar = inj₂ ()`; non-variable/plain partner rows
  should be top-shape or nonstar impossible.
- Collapsed: none.
- Independent: partner-view dispatch rows not yet separated into dedicated
  checked emptiness lemmas.

`source-spine-strip-worker-seal-D`

- Impossible: CTI heads incompatible with a source-seal left term remain
  semantic inversion obligations.
- Collapsed: none directly; collapsed rows arrive through
  `source-spine-strip-worker-seal-cast`.
- Independent: dispatcher pressure over the sealed derivation `D`.

`source-spine-strip-worker-seal`

- Impossible: none directly.
- Collapsed: none directly; collapsed rows arrive through
  `source-spine-strip-worker-seal-D`.
- Independent: broad top-spine dispatch.  The intended caller supplies
  `sv-seal`, but the type is still `SourceSpineStrip`.

`source-spine-strip-worker-reveal-fun`

- Impossible: `reveal⊑²` over a function spine is discharged by
  `tagged-target-nonvar-nonstar-spine-⊥`.
- Collapsed: none.
- Independent: broad top-spine dispatch.  Removing the pragma did not produce
  a quick coverage diagnostic; Agda entered compiled-clause pressure.

`source-spine-strip-worker-conceal-fun`

- Impossible: `conceal⊑²` over a function spine is discharged by
  `tagged-target-nonvar-nonstar-spine-⊥`.
- Collapsed: none.
- Independent: broad top-spine dispatch.

`source-spine-strip-worker-reveal-all`

- Impossible: `reveal⊑²` over an all spine is discharged by
  `tagged-target-nonvar-nonstar-spine-⊥`.
- Collapsed: none.
- Independent: broad top-spine dispatch.

`source-spine-strip-worker-conceal-all`

- Impossible: `conceal⊑²` over an all spine is discharged by
  `tagged-target-nonvar-nonstar-spine-⊥`.
- Collapsed: none.
- Independent: broad top-spine dispatch.

`source-spine-strip-worker`

- Impossible: none directly.
- Collapsed: none directly; it delegates to the cast/seal families above.
- Independent: outer dispatcher compiled-clause pressure.  Its source clauses
  are syntactically exhaustive over `SpineValue`, but removing the pragma
  caused a long coverage recheck rather than a quick green close.

### `SourceStripColumnView`

`source-column-seal-D-case`

- Impossible: Agda reports exactly these missing inner-premise rows under
  `conceal⊑² (⊢↓-sealˣ _)`:
  `Λ⊑²`, `Λ⊑²-smart-comma`, `•⊑²`, `cast⊑cast²`, `cast⊑²`,
  `reveal⊑²`, `conceal⊑²`, and `blame⊑²`.  The existing view handles only the
  direct target-cast row and the two checked source-seal rows.
- Collapsed: none.
- Independent: none; this small view needs ordinary emptiness lemmas.

## Occupancy and grounding audit

The live occupancy definitions are now strong enough to refute a class of rows
that predates LG-1/LG-2:

```agda
rebase-occupies-source :
  ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTI2.World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → CTI2.RebaseAt W′ W X Y
  → CTI2.Occupied W′ (toRenameᵗ (CTI2.ηᴸʷ W′) X)

rebase-no-target-at-source-⊥ :
  ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTI2.World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → CTI2.RebaseAt W′ W X Y
  → CTI2.NoTargetOccupantAtSource W′ X
  → ⊥
```

The proof is direct: `RebaseAt.pivotAligned` identifies the source pivot with
the target image of `Y`, so `Y` is the occupant.

This refutes star-rep rows that simultaneously carry
`star-rep-target no-target ...` and a `tag-rebase-varᴸ link`.  The current
code often discards `no-target` before delegating, for example by passing only
`cVar` to `source-spine-strip-worker-cast-step-over-seal-star`.  A local repair
can either keep that evidence in the helper input or discharge the branch
before delegation.

The LG-2 grounding minting theorems do not refute the general collapsed family
inside `SourceStripWorkerProof`: those workers quantify over arbitrary
`CTI2.World`s, while `GroundingMint.CompileImageWorld` describes compile
recursion worlds.  They would be useful only for callers that additionally
carry `CompileImageWorld W` and a precise-source fact.

## Proposed input-view redesign

The minimal repair is to replace the one-bit non-final constructor with a
row-preserving view.  The final input stays unchanged, so existing final
consumers keep their proof term:

```agda
data WrapStarCastView {Δᴸ Δᴿ Δ}
    (W W′ : World Δᴸ Δᴿ Δ)
    (γ : CtxImp W) (γ′ : CtxImp W′)
    (V : Term Δᴸ) (U : Term Δᴿ)
    (Xᴸ X₂ : TyVar Δᴸ) (Y : TyVar Δᴿ) :
    (S : Ty Δᴿ)
    → {ν : Env∼ Δᴸ}
    → (c : ν ⊢ (＇ X₂) ∼ ★)
    → (p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y))
    → (q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y))
    → Set where
  wrap-star-final-ready :
    WrapStarCastFinalInput W W′ γ γ′ V U Xᴸ X₂ Y S c p₂ q
    → WrapStarCastView W W′ γ γ′ V U Xᴸ X₂ Y S c p₂ q

  wrap-star-at-residual : ∀ {P}
    → X₂ ≡ Xᴸ
    → V ≡ P ↓ seal Xᴸ ★
    → sourceStoreʷ W′ ∋ Xᴸ ⦂ ★
    → targetStoreʷ W′ ∋ Y ⦂ ★
    → RebaseAt W′ W′ Xᴸ Y
    → W′ ∣ γ′ ⊢² P ↓ seal Xᴸ ★ ⊑ U ↓ seal Y ★ ∶ p₂
    → WrapStarCastView W W′ γ γ′ V U Xᴸ X₂ Y ★ c p₂ q

  wrap-star-at-paired : ∀ {P Wᵖ γᵖ p★}
    → X₂ ≡ Xᴸ
    → V ≡ P ↓ seal Xᴸ ★
    → CTI2.ImpEnvMono W′ Wᵖ
    → RebaseAt Wᵖ W′ Xᴸ Y
    → CTI2.SameCtx γ′ γᵖ
    → sourceStoreʷ W′ ∋ Xᴸ ⦂ ★
    → targetStoreʷ W′ ∋ Y ⦂ ★
    → CTI2.MatchedConcealPartnerOK Wᵖ P (seal Xᴸ ★) (just Y) U
    → Wᵖ ∣ γᵖ ⊢² P ⊑ U ∶ p★
    → WrapStarCastView W W′ γ γ′ V U Xᴸ X₂ Y ★ c p₂ q

  wrap-star-at-payload : ∀ {P Wᵖ γᵖ pᵖ}
    → X₂ ≡ Xᴸ
    → V ≡ P ↓ seal Xᴸ ★
    → CTI2.ImpEnvMono W′ Wᵖ
    → RebaseAt Wᵖ W′ Xᴸ Y
    → CTI2.SameCtx γ′ γᵖ
    → sourceStoreʷ W′ ∋ Xᴸ ⦂ ★
    → targetStoreʷ W′ ∋ Y ⦂ ★
    → Wᵖ ∣ γᵖ ⊢² P ↓ seal Xᴸ ★ ⊑ U ∶ pᵖ
    → WrapStarCastView W W′ γ γ′ V U Xᴸ X₂ Y ★ c p₂ q

  wrap-star-chain-residual : ∀ {P Y₂}
    → V ≡ P ↓ seal Xᴸ ★
    → sourceStoreʷ W ∋ Xᴸ ⦂ ★
    → targetStoreʷ W ∋ Y ⦂ (＇ Y₂)
    → RebaseAt W W Xᴸ Y
    → W ∣ γ ⊢² P ↓ seal Xᴸ ★
        ⊑ U ↓ seal Y (＇ Y₂) ∶ q
    → WrapStarCastView W W′ γ γ′ V U Xᴸ X₂ Y (＇ Y₂) c p₂ q

  wrap-star-chain-paired : ∀ {P Uᵖ Yᵖ Wᵖ γᵖ Y₂ p★}
    → V ≡ P ↓ seal Xᴸ ★
    → sourceStoreʷ W ∋ Xᴸ ⦂ ★
    → targetStoreʷ W ∋ Y ⦂ (＇ Y₂)
    → RebaseAt W W Xᴸ Y
    → W ∣ γ ⊢² P ↓ seal Xᴸ ★
        ⊑ U ↓ seal Y (＇ Y₂) ∶ q
    → CTI2.ImpEnvMono W Wᵖ
    → RebaseAt Wᵖ W Xᴸ Y
    → CTI2.SameCtx γ γᵖ
    → CTI2.MatchedConcealPartnerOK Wᵖ P (seal Xᴸ ★) (just Yᵖ) Uᵖ
    → Wᵖ ∣ γᵖ ⊢² P ⊑ Uᵖ ∶ p★
    → WrapStarCastView W W′ γ γ′ V U Xᴸ X₂ Y (＇ Y₂) c p₂ q

  wrap-star-chain-payload : ∀ {P Uᵖ Wᵖ γᵖ Y₂ pᵖ}
    → V ≡ P ↓ seal Xᴸ ★
    → sourceStoreʷ W ∋ Xᴸ ⦂ ★
    → targetStoreʷ W ∋ Y ⦂ (＇ Y₂)
    → RebaseAt W W Xᴸ Y
    → W ∣ γ ⊢² P ↓ seal Xᴸ ★
        ⊑ U ↓ seal Y (＇ Y₂) ∶ q
    → CTI2.ImpEnvMono W Wᵖ
    → RebaseAt Wᵖ W Xᴸ Y
    → CTI2.SameCtx γ γᵖ
    → Wᵖ ∣ γᵖ ⊢² P ↓ seal Xᴸ ★ ⊑ Uᵖ ∶ pᵖ
    → WrapStarCastView W W′ γ γ′ V U Xᴸ X₂ Y (＇ Y₂) c p₂ q
```

The producer changes mechanically: every old
`wrap-star-cast-nonfinal` clause returns the corresponding row constructor
with the fields already supplied by `TargetSourceStarAtResult` or
`TargetSourceStarChainResult`.

Consumers then have two choices:

1. Star-rep branches that still have `NoTargetOccupantAtSource` use
   `rebase-no-target-at-source-⊥` and never enter the old final-only path.
2. Name-protected and ordinary cast-wrapper branches consume the residual,
   paired, and payload rows by returning a branch result that carries the
   row-sensitive residual to the target-cast consumer, following the pattern
   already used by the target-strip repair.

The second choice is a source-strip surface redesign, not a local proof trick.
The existing final-only helpers:

```agda
source-wrap-star-cast-branch
source-cast-seal-branch
source-seal-cast-branch
```

must return a row-sensitive branch package instead of demanding
`WrapStarCastFinalInput` immediately.  Candidate package shape:

```agda
data SourceWrapStarCastBranchResult ... : Set where
  source-wrap-final :
    SourceSpineStripBranch ... → SourceWrapStarCastBranchResult ...

  source-wrap-residual :
    -- residual square from `wrap-star-at-residual` or
    -- `wrap-star-chain-residual`, plus the same outer rebases
    -- and source/target memberships needed to reattach it later
    ...
    → SourceWrapStarCastBranchResult ...

  source-wrap-paired :
    -- matched partner row, carrying `MatchedConcealPartnerOK`
    -- and the payload square at `Wᵖ`
    ...
    → SourceWrapStarCastBranchResult ...

  source-wrap-payload :
    -- payload row, carrying the source-sealed payload square
    -- at `Wᵖ`
    ...
    → SourceWrapStarCastBranchResult ...
```

This is the source-side analogue of the target-strip Option-A repair: do not
manufacture a final stripped premise from a non-final residual.  Preserve the
row until the caller has the matching target cast and can consume it with the
existing paired/payload machinery.

## Mechanical probes performed

- Removing `SourceStripColumnView.source-column-seal-D-case` failed quickly
  with the eight inner-premise rows listed above.
- Removing `source-spine-strip-worker` caused a long coverage recheck and was
  stopped; no quick green close.
- Removing `source-spine-strip-worker-reveal-fun` likewise entered long
  compiled-clause checking and was stopped.

No pragma was mechanically closed in this pass.  The Makefile baseline should
remain `18` for `SourceStripWorkerProof` and `1` for
`SourceStripColumnView` until a row-preserving view or the small independent
emptiness lemmas are implemented.
