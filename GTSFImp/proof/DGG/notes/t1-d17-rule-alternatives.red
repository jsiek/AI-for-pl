# T1 D17 rule alternatives

Status: declarations-only design.  No live definition or proof was changed.
The declarations and the target identity-conceal replay rows below are checked
by `proof/DGG/notes/probes/T1D17RuleAlternativesProbe.agda` under `--safe`.

The D14(c) retry established a real rule defect, not a missing transport lemma.
For the live non-`★` source-seal clause, `NotTopTag (N ↓ id↓ B)` is always
available from the outer syntax, while the target keep step exposes `N`, which
may be a top tag.  The checked `repaired-structural-value-dispatcher-empty`
counterexample therefore rules out the present declaration.

This note shows three concrete replacement surfaces.  Every **Current** block
below is copied verbatim from `proof/DGG/CastTermImprecision2.agda`; every
**Changed** block is a proposed replacement, not an implementation.

## Option (a): before-step classification by the target type

The only small pre-step fact found that both rules out the counterexample and
survives the keep step is the target type index itself: add the target type to
`SourceConcealOK` and require `NonStar B` for the plain non-`★` seal case.
Identity reveal/conceal preserves `B`, so the evidence replays unchanged.

### Current `SourceConcealOK` (verbatim)

```agda
data SourceConcealOK {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  seal-nonstar-plain-ok : ∀ {P X R Xᴿ? M′}
    → NonStar R
    → NotTopTag M′
      ----------------------------------------------------
    → SourceConcealOK W P (seal X R) Xᴿ? M′

  seal-nonstar-name-protected-ok : ∀ {P X R Y S M μ}
      {c : μ ⊢ (＇ Y) ∼ ★}
    → NonStar R
    → CenterAligned W X Y
      ----------------------------------------------------
    → SourceConcealOK W P (seal X R) (just Y)
        ((M ↓ seal Y S) ⟨ c ⟩)

  fun-conceal-ok : ∀ {P A A′ B B′ Xᴿ? M′}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      ----------------------------------------------------
    → SourceConcealOK W P (c ↦↓ d) Xᴿ? M′

  all-conceal-ok : ∀ {P A B Xᴿ? M′}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      ----------------------------------------------------
    → SourceConcealOK W P (`∀↓ c) Xᴿ? M′

  id-conceal-ok : ∀ {P A Xᴿ? M′}
      ----------------------------------------------------
    → SourceConcealOK W P (id↓ A) Xᴿ? M′
```

### Current `conceal⊑²-source-ok` (verbatim)

```agda
  conceal⊑²-source-ok : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A A′ B Xᴸ? Xᴿ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↓ Δᴸ A A′}
    → SourceConcealOK W′ M c Xᴿ? M′
    → ImpEnvMono W W′
    → TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
    → SameCtx γ γ′
    → sourceStoreʷ W ⊢↓[ Xᴸ? ] c
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢² M ↓ c ⊑ M′ ∶ q
```

### Changed `SourceConcealOK`

```agda
data SourceConcealOK {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → Maybe (TyVar Δᴿ) → Term Δᴿ → Ty Δᴿ → Set where
  seal-nonstar-plain-ok : ∀ {P X R Xᴿ? M′ B}
    → NonStar R
    → NonStar B
      ----------------------------------------------------
    → SourceConcealOK W P (seal X R) Xᴿ? M′ B

  seal-nonstar-name-protected-ok : ∀ {P X R Y S M B μ}
      {c : μ ⊢ (＇ Y) ∼ ★}
    → NonStar R
    → CenterAligned W X Y
      ----------------------------------------------------
    → SourceConcealOK W P (seal X R) (just Y)
        ((M ↓ seal Y S) ⟨ c ⟩) B

  fun-conceal-ok : ∀ {P A A′ B B′ Xᴿ? M′ C}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      ----------------------------------------------------
    → SourceConcealOK W P (c ↦↓ d) Xᴿ? M′ C

  all-conceal-ok : ∀ {P A B Xᴿ? M′ C}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      ----------------------------------------------------
    → SourceConcealOK W P (`∀↓ c) Xᴿ? M′ C

  id-conceal-ok : ∀ {P A Xᴿ? M′ B}
      ----------------------------------------------------
    → SourceConcealOK W P (id↓ A) Xᴿ? M′ B
```

### Changed `conceal⊑²-source-ok`

```agda
  conceal⊑²-source-ok : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A A′ B Xᴸ? Xᴿ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↓ Δᴸ A A′}
    → SourceConcealOK W′ M c Xᴿ? M′ B
    → ImpEnvMono W W′
    → TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
    → SameCtx γ γ′
    → sourceStoreʷ W ⊢↓[ Xᴸ? ] c
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢² M ↓ c ⊑ M′ ∶ q
```

The checked dispatcher reconstruction is the direct replay

```agda
conceal⊑²-source-ok
  (seal-nonstar-plain-ok Rns Bns) mono rb sc c⊢ body-after q
```

with the same `Bns : NonStar B` before and after the target keep.  Thus the
D17 identity-conceal and identity-reveal rows become provable and the checked
counterexample is rejected because it has `B = ★`.  The cost is semantic:
this is not a replacement equivalent to `NotTopTag M′`; it also rejects every
plain non-`★` seal against a target of type `★`, even when the target endpoint
is genuinely untagged.  Mechanically, the new `B` index propagates through
`CastTermImprecision2Typing`, source-strip/target-chain inversion, center
rename, target insert/bind lift, decay, simulation, and catch-up replay.  The
tempting value-view candidate does not improve this option:
`Value M′ × NotTopTag M′` is unavailable before an identity keep because an
identity reveal/conceal wrapper is not a `Value`; a view that peels that
wrapper and classifies the underlying value is precisely option (b).

## Option (b): classify the target value after the keep

This alternative makes the ordering explicit.  The relation records the
target value `V′` exposed by an administrative wrapper, and applies the
unchanged classifier to `V′`, not to the wrapper `M′`.

### Current `SourceConcealOK` (verbatim)

```agda
data SourceConcealOK {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  seal-nonstar-plain-ok : ∀ {P X R Xᴿ? M′}
    → NonStar R
    → NotTopTag M′
      ----------------------------------------------------
    → SourceConcealOK W P (seal X R) Xᴿ? M′

  seal-nonstar-name-protected-ok : ∀ {P X R Y S M μ}
      {c : μ ⊢ (＇ Y) ∼ ★}
    → NonStar R
    → CenterAligned W X Y
      ----------------------------------------------------
    → SourceConcealOK W P (seal X R) (just Y)
        ((M ↓ seal Y S) ⟨ c ⟩)

  fun-conceal-ok : ∀ {P A A′ B B′ Xᴿ? M′}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      ----------------------------------------------------
    → SourceConcealOK W P (c ↦↓ d) Xᴿ? M′

  all-conceal-ok : ∀ {P A B Xᴿ? M′}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      ----------------------------------------------------
    → SourceConcealOK W P (`∀↓ c) Xᴿ? M′

  id-conceal-ok : ∀ {P A Xᴿ? M′}
      ----------------------------------------------------
    → SourceConcealOK W P (id↓ A) Xᴿ? M′
```

### Current `conceal⊑²-source-ok` (verbatim)

```agda
  conceal⊑²-source-ok : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A A′ B Xᴸ? Xᴿ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↓ Δᴸ A A′}
    → SourceConcealOK W′ M c Xᴿ? M′
    → ImpEnvMono W W′
    → TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
    → SameCtx γ γ′
    → sourceStoreʷ W ⊢↓[ Xᴸ? ] c
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢² M ↓ c ⊑ M′ ∶ q
```

### Changed endpoint view

```agda
data TargetValueBeneath {Δ : TyCtx} : Term Δ → Term Δ → Set where
  target-value-here : ∀ {V}
    → Value V
      ----------------------
    → TargetValueBeneath V V

  target-id-reveal : ∀ {V A}
    → Value V
      -------------------------------------
    → TargetValueBeneath (V ↑ id↑ A) V

  target-id-conceal : ∀ {V A}
    → Value V
      -------------------------------------
    → TargetValueBeneath (V ↓ id↓ A) V

  target-conceal-reveal : ∀ {V X R}
    → Value V
      ---------------------------------------------------
    → TargetValueBeneath
        ((V ↓ seal X R) ↑ unseal X R) V
```

### Changed `SourceConcealOK`

`SourceConcealOK` itself remains textually unchanged; its term index is now
instantiated with `V′` by the changed term rule.

```agda
data SourceConcealOK {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  seal-nonstar-plain-ok : ∀ {P X R Xᴿ? M′}
    → NonStar R
    → NotTopTag M′
      ----------------------------------------------------
    → SourceConcealOK W P (seal X R) Xᴿ? M′

  seal-nonstar-name-protected-ok : ∀ {P X R Y S M μ}
      {c : μ ⊢ (＇ Y) ∼ ★}
    → NonStar R
    → CenterAligned W X Y
      ----------------------------------------------------
    → SourceConcealOK W P (seal X R) (just Y)
        ((M ↓ seal Y S) ⟨ c ⟩)

  fun-conceal-ok : ∀ {P A A′ B B′ Xᴿ? M′}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      ----------------------------------------------------
    → SourceConcealOK W P (c ↦↓ d) Xᴿ? M′

  all-conceal-ok : ∀ {P A B Xᴿ? M′}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      ----------------------------------------------------
    → SourceConcealOK W P (`∀↓ c) Xᴿ? M′

  id-conceal-ok : ∀ {P A Xᴿ? M′}
      ----------------------------------------------------
    → SourceConcealOK W P (id↓ A) Xᴿ? M′
```

### Changed `conceal⊑²-source-ok`

```agda
  conceal⊑²-source-ok : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ V′ A A′ B Xᴸ? Xᴿ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↓ Δᴸ A A′}
    → TargetValueBeneath M′ V′
    → SourceConcealOK W′ M c Xᴿ? V′
    → ImpEnvMono W W′
    → TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
    → SameCtx γ γ′
    → sourceStoreʷ W ⊢↓[ Xᴸ? ] c
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢² M ↓ c ⊑ M′ ∶ q
```

At the pre-step relation the row contains

```agda
conceal⊑²-source-ok
  (target-id-conceal vN)
  (seal-nonstar-plain-ok Rns not-top-N)
  mono rb sc c⊢ prem q
```

After the dispatcher takes the target keep step and recursively obtains
`body-after : W′ ∣ γ′ ⊢² P ⊑ N ∶ p`, it consumes the already post-step
classifier as

```agda
conceal⊑²-source-ok
  (target-value-here vN)
  (seal-nonstar-plain-ok Rns not-top-N)
  mono rb sc c⊢ body-after q
```

The D17 row is therefore provable, and the counterexample input is no longer
derivable because its exposed `N` is a top tag.  This has the largest proof
mass: every construction and inversion of `conceal⊑²-source-ok` gains the
endpoint view, and the four-constructor view above covers only the pure
administrative value roots needed by the present dispatcher.  Preserving the
old rule's use against arbitrary non-value targets would require an
evaluation-context and allocation-aware endpoint relation indexed by evolved
worlds.  That would move dynamic semantics into the static imprecision
relation and require changes throughout typing, substitution/rename, decay,
target extension, simulation, and all source-conceal catch-up consumers.

## Option (c): classify the seal pivot in the world

The minimal world-level replacement changes only the fragile plain branch:
a non-`★` source seal may ignore target syntax when its source pivot has no
target occupant.  If a target pivot is aligned, the existing name-protected
branch remains the route.  This rejects the counterexample because its `U`
and `Y` are center-aligned.

### Current `SourceConcealOK` (verbatim)

```agda
data SourceConcealOK {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  seal-nonstar-plain-ok : ∀ {P X R Xᴿ? M′}
    → NonStar R
    → NotTopTag M′
      ----------------------------------------------------
    → SourceConcealOK W P (seal X R) Xᴿ? M′

  seal-nonstar-name-protected-ok : ∀ {P X R Y S M μ}
      {c : μ ⊢ (＇ Y) ∼ ★}
    → NonStar R
    → CenterAligned W X Y
      ----------------------------------------------------
    → SourceConcealOK W P (seal X R) (just Y)
        ((M ↓ seal Y S) ⟨ c ⟩)

  fun-conceal-ok : ∀ {P A A′ B B′ Xᴿ? M′}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      ----------------------------------------------------
    → SourceConcealOK W P (c ↦↓ d) Xᴿ? M′

  all-conceal-ok : ∀ {P A B Xᴿ? M′}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      ----------------------------------------------------
    → SourceConcealOK W P (`∀↓ c) Xᴿ? M′

  id-conceal-ok : ∀ {P A Xᴿ? M′}
      ----------------------------------------------------
    → SourceConcealOK W P (id↓ A) Xᴿ? M′
```

### Current `conceal⊑²-source-ok` (verbatim)

```agda
  conceal⊑²-source-ok : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A A′ B Xᴸ? Xᴿ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↓ Δᴸ A A′}
    → SourceConcealOK W′ M c Xᴿ? M′
    → ImpEnvMono W W′
    → TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
    → SameCtx γ γ′
    → sourceStoreʷ W ⊢↓[ Xᴸ? ] c
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢² M ↓ c ⊑ M′ ∶ q
```

### Changed `SourceConcealOK`

```agda
data SourceConcealOK {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  seal-nonstar-unmatched-ok : ∀ {P X R Xᴿ? M′}
    → NonStar R
    → NoTargetOccupantAtSource W X
      ----------------------------------------------------
    → SourceConcealOK W P (seal X R) Xᴿ? M′

  seal-nonstar-name-protected-ok : ∀ {P X R Y S M μ}
      {c : μ ⊢ (＇ Y) ∼ ★}
    → NonStar R
    → CenterAligned W X Y
      ----------------------------------------------------
    → SourceConcealOK W P (seal X R) (just Y)
        ((M ↓ seal Y S) ⟨ c ⟩)

  fun-conceal-ok : ∀ {P A A′ B B′ Xᴿ? M′}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      ----------------------------------------------------
    → SourceConcealOK W P (c ↦↓ d) Xᴿ? M′

  all-conceal-ok : ∀ {P A B Xᴿ? M′}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      ----------------------------------------------------
    → SourceConcealOK W P (`∀↓ c) Xᴿ? M′

  id-conceal-ok : ∀ {P A Xᴿ? M′}
      ----------------------------------------------------
    → SourceConcealOK W P (id↓ A) Xᴿ? M′
```

### Changed `conceal⊑²-source-ok`

The term rule remains textually identical; its first premise uses the changed
world-indexed classifier.

```agda
  conceal⊑²-source-ok : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A A′ B Xᴸ? Xᴿ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↓ Δᴸ A A′}
    → SourceConcealOK W′ M c Xᴿ? M′
    → ImpEnvMono W W′
    → TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
    → SameCtx γ γ′
    → sourceStoreʷ W ⊢↓[ Xᴸ? ] c
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢² M ↓ c ⊑ M′ ∶ q
```

The dispatcher row reuses the same world fact after the keep:

```agda
conceal⊑²-source-ok
  (seal-nonstar-unmatched-ok Rns no-target)
  mono rb sc c⊢ body-after q
```

This makes both target identity rows provable by construction.  It changes the
admissible split: an unmatched non-`★` seal may now relate to any target
syntax, while a matched pivot must use the existing name-protected route.  The
proof changes concentrate in the `seal-nonstar-plain-ok` construction and
inversion sites, `CenterRename`, `TargetBindLift`, `TargetExtend`,
`TermImpDecay`, source-strip/target-chain, and the source-conceal catch-up
rows.  Existing occupancy transport is reusable, so the term rule and its
target index do not change.

### Interaction with the D16 companion on PR #177

The checked probe restates the proposed D16 `preciseMarksAligned`,
`representationsImprecise`, and chain-permissive `unmatchedTargetsDynamic`
fields in a temporary `D16Companion W`.  It checks two facts needed by this
split:

```agda
no-target-mark-dynamic :
  D16Companion W
  → NoTargetOccupantAtSource W X
  → impEnvʷ W (toRenameᵗ (ηᴸʷ W) X) ≡ X⊑★

matched-pivot-representations :
  D16Companion W
  → CenterAligned W X Y
  → impEnvʷ W ⊢
      renameᵗ (toRenameᵗ (ηᴸʷ W))
        (lookupStore (sourceStoreʷ W) X)
      ⊑ renameᵗ (toRenameᵗ (ηᴿʷ W))
        (lookupStore (targetStoreʷ W) Y)
```

Thus the unmatched branch is certified dynamic by
`preciseMarksAligned`, while the matched/name-protected branch gets the seal
representation comparison from `representationsImprecise`.  The D16
`unmatchedTargetsDynamic` field is the target-side converse and does not by
itself prove `NoTargetOccupantAtSource`; it should not be used in that
direction.  During the temporary-companion phase, threading the whole
companion through `_⊢²_` solely for this rule would create needless proof
mass.  The clean sequence is to use the existing occupancy judgment in the
drafted rule, merge the D16 fields into `World`, and then obtain both facts by
projection.  The temporary companion must be deleted when that merge lands.

## Comparison and recommendation

| Option | Proof mass | Step-stable by construction | D16 synergy | D17 dispatcher row |
| --- | --- | --- | --- | --- |
| (a) Target `NonStar B` | Medium-high: add a target-type index through every classifier transport and consumer | Yes; identity keeps preserve `B` | Weak; it does not use occupancy or representation coherence | Provable, but all dynamic-target plain cases disappear |
| (b) Post-keep `TargetValueBeneath` | Highest: add endpoint views to every source-conceal construction/inversion; general use needs evolved-world evaluation views | Yes; the classifier is already on the exposed value | Moderate; evolved endpoint worlds would eventually need D16 preservation | Provable for the checked administrative value roots |
| (c) `NoTargetOccupantAtSource` | Medium: replace one constructor premise and reuse occupancy transport | Yes; target keep does not change the world | Strong: unmatched pivots are dynamic; matched pivots obtain representation imprecision | Provable; the counterexample's aligned pivot is rejected |

**Recommendation: choose (c).**  It removes the step-fragile term observation
without inserting evaluation into `_⊢²_` or adding an index to every
`SourceConcealOK` use.  It also states the semantic boundary directly: an
unmatched source name may be ignored, while a matched name must stay protected
and its representations are governed by D16.  Before implementation, the
world-level admissibility choice still needs explicit approval because this is
a change to the live term-imprecision relation.

## Validation

The companion probe is standalone, checked with `--safe`, and contains no
postulates, holes, or pragmas.  Its focused Agda 2.8 check exited 0:

```text
agda --safe -v0 -i . -i proof/DGG/notes/probes \
  proof/DGG/notes/probes/T1D17RuleAlternativesProbe.agda
```

The required repository gate was run exactly as

```text
cd GTSFImp && PATH=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda28/bin:$PATH make check
```

It exited 0 after checking `All.agda`, `LegacyAll.agda`, and reporting
`postulate-check: OK (no postulates; NON_COVERING at legacy baseline)`.
