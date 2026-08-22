# Target Strip Slice Design

## Scope

Design-only pass on branch `agent/gtsf-extra-cast-right`.

No `GTSFImp/` files are edited.  The checked scratch file is
`SliceCheck.agda`.

The current frozen surface in
`GTSFImp/proof/DGG/Inversion/TargetStripDef.agda` combines two steps in one
premise:

```agda
Wᵖ ∣ γᵖ ⊢² V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p
```

The proposed slice separates the last target-side tag node from target seal
descent.  The slicing axis is the derivation node, not the syntactic target
term.

## Statement 1: `SealDescentAtVar`

Plain form:

```agda
SealDescentAtVar : Set
SealDescentAtVar =
  ∀ {Wᵒ Wʳ γᵒ γʳ V U A S Xᴸ Y}
    {r : A ⊑ᵂ⟨ Wʳ ⟩ ＇ Y}
  → Value U
  → ImpEnvMono Wᵒ Wʳ
  → RebaseAt Wʳ Wᵒ Xᴸ Y
  → SameCtx γᵒ γʳ
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → Wʳ ∣ γʳ ⊢² V ⊑ U ↓ seal Y S ∶ r
  → TargetStripAt★Data Wᵒ γᵒ V A U Xᴸ
```

Lifted form, needed to preserve the frozen
`TargetStripAt★ᴸData` corollary:

```agda
SealDescentAtVarᴸ : Set
SealDescentAtVarᴸ =
  ∀ {Wᵒ Wʳ γᵒ γʳ γᵇ V U A S Xᴸ Y}
    {r : A ⊑ᵂ⟨ liftWorldLeft X⊑★ Wʳ ⟩ ＇ Y}
  → Value U
  → ImpEnvMono Wᵒ Wʳ
  → RebaseAt Wʳ Wᵒ Xᴸ Y
  → SameCtx γᵒ γʳ
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → LiftCtxᴸ X⊑★ γʳ γᵇ
  → liftWorldLeft X⊑★ Wʳ ∣ γᵇ ⊢²
      V ⊑ U ↓ seal Y S ∶ r
  → TargetStripAt★ᴸData Wᵒ γᵒ V A U Xᴸ
```

The right-variable obligation `r` is intentionally explicit.  In proof, the
first move is the existing `right-var-obligation-view`, which refines `A` to a
source variable.  The statement itself does not mention a tag.

## Statement 2: `TagDispatchAt★`

The tag lemma works over an opaque target payload `N`.

Plain output cases:

```agda
record TagNodeAt★ W γ V A N Y : Set where
  field
    r★ : A ⊑ᵂ⟨ W ⟩ ＇ Y
    premiseᵛ : W ∣ γ ⊢² V ⊑ N ∶ r★

data TagDispatchAt★Case Wᵒ γᵒ Wᵖ γᵖ V A N Xᴸ Y : Set where
  dispatch-tag :
    TagNodeAt★ Wᵖ γᵖ V A N Y
    → TagDispatchAt★Case Wᵒ γᵒ Wᵖ γᵖ V A N Xᴸ Y

  dispatch-source-fold :
    (∀ {U S}
      → N ≡ U ↓ seal Y S
      → Value U
      → targetStoreʷ Wᵒ ∋ Y ⦂ S
      → TargetStripAt★Data Wᵒ γᵒ V A U Xᴸ)
    → TagDispatchAt★Case Wᵒ γᵒ Wᵖ γᵖ V A N Xᴸ Y

  dispatch-nonvar-empty :
    ⊥
    → TagDispatchAt★Case Wᵒ γᵒ Wᵖ γᵖ V A N Xᴸ Y
```

Plain lemma:

```agda
TagDispatchAt★ : Set
TagDispatchAt★ =
  ∀ {Wᵒ Wᵖ γᵒ γᵖ V N A Xᴸ Y ν cY p}
  → Value N
  → ImpEnvMono Wᵒ Wᵖ
  → RebaseAt Wᵖ Wᵒ Xᴸ Y
  → SameCtx γᵒ γᵖ
  → Wᵖ ∣ γᵖ ⊢² V ⊑ N ⟨ cY ⟩ ∶ p
  → TagDispatchAt★Case Wᵒ γᵒ Wᵖ γᵖ V A N Xᴸ Y
```

The lifted form is the same shape with `Wᵖ` replaced by
`liftWorldLeft X⊑★ Wᵖ` in the premise and in the tag-node obligation.  It
returns `TagDispatchAt★ᴸCase`.

`dispatch-tag` is the only branch that hands off to `SealDescentAtVar`.
`dispatch-source-fold` represents recursion through source-side head nodes and
rebuilds at the returned terminus.  `dispatch-nonvar-empty` is for A4/hunt
refutations: a right-variable obligation forces the source type to be a
variable, so non-variable atom cases are empty.

## Reuse Assessment

`SealDescentAtVar` should be mostly a restatement/generalization of proven
target-descent machinery, not a new relation:

- `TargetDescentDef.TargetSealTerminal` and `TargetSealReemit` are the right
  internal packages for the `S = ★` and `S = ＇Y′` branches.
- `TargetDescentProof.target-seal★-descent` already proves the terminal
  `★` branch, but it is specialized to the right-injection source-star shape
  `(V ⟨ c ⟩)` with `SpineValue`, `Inert c`, and `sourceStoreʷ W ∋ X ⦂ ★`.
- `TargetDescentProof.target-seal＇-reemit` is directly reusable for target-only
  variable payload re-emission.
- `TargetChainLemma.target-source-star-at` and `target-source-star-chain`
  remain useful for the right-injection source-star instances, but they are not
  the public seal slice.

The missing adapter is to expose the same terminal/reemit logic at the more
general right-variable premise:

```agda
Wʳ ∣ γʳ ⊢² V ⊑ U ↓ seal Y S ∶ r
```

with `r : A ⊑ᵂ⟨ Wʳ ⟩ ＇Y`.  No tag and no change to the live imprecision
relation are needed.

The lifted seal form is needed if the old `TargetStripAt★ᴸData` surface is
kept.  A plain instantiation of `SealDescentAtVar` under
`liftWorldLeft X⊑★` would produce a terminal package in the lifted world; the
frozen lifted data instead wants the unlifted `W★`, `γ★`, `LiftCtxᴸ`,
`q★ : `∀ A ⊑ ★`, target typing for `U`, and the lifted body premise.

## Shared Fold

Yes: the slicing supports one shared source-head fold, with different algebras.

The shared fold should cover the source-side recursion through constructors
such as `Λ⊑²`, source casts, and source reveal/conceal wrappers.  The terminal
algebras differ:

- `SourceSpineStrip` and `SourceColumnStrip` fold to `SourceCorePremise` plus a
  `CoreRebuild` continuation.
- `TagDispatchAt★` folds to either a tag-node handoff, a folded terminus
  continuation, or an empty non-variable atom.

The target seal chain should remain a separate continuation (`SealDescentAtVar`
and `SealDescentAtVarᴸ`).  Folding source heads and descending target seals are
different axes.

`SliceCheck.agda` records this compatibility as `SharedFoldConsumers` and checks
`walk-from-shared-fold-consumers`.

## Validated Consequences

`SliceCheck.agda` checks:

- `target-strip★-from-slices`:
  `SealDescentAtVar → TagDispatchAt★ → TargetStripAt★`.
- `target-strip★ᴸ-from-slices`:
  `SealDescentAtVarᴸ → TagDispatchAt★ᴸ → TargetStripAt★ᴸ`.
- `source-tag-seal-core-from-slices`, including the `Λ⊑²` branch through
  `target-strip★ᴸ-from-slices`.
- `walk-from-shared-fold-consumers`, showing the source-strip worker surface
  remains compatible with the slices.
- `instanceA-core`, the existing `TerminusRebuildProbe.InstanceA` Λ-core
  package.
- `instanceB-tag-case`, the `TerminusRebuildProbe.InstanceB` variable-chain
  tag-node handoff.

## Validation Transcript

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home \
  agda -i GTSFImp -v0 SliceCheck.agda
```

Exit code: `0`.

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home \
  agda -i GTSFImp -v0 BodyStripCheck.agda
```

Exit code: `0`.
