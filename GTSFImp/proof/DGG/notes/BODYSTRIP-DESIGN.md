# `TARGET-STRIP-AT-★` Design

## Scope

This is a design-only pass for the SourceStrip core block:

`CoreRebuild Wᵒ γᵒ (Λ V) (`∀ A) U Xᴸ Y S`

from a tagged target premise.  No `GTSFImp/` file is edited here.  The checked
scratch file is `BodyStripCheck.agda`.

The missing mutual member strips a target tag at a `★` obligation without a
source seal anchor:

`V ⊑ (U ↓ seal Ỹ S̃) ⟨ c̃ ⟩ ∶ p`

where `p : A ⊑ᵂ⟨ W ⟩ ★`.  Its job is to produce terminal `V ⊑ U` data that can
rebuild one-sided source heads.  For `Λ⊑²`, the body premise is under
`liftWorldLeft X⊑★ W`, so the member also needs a binder-lifted form that
returns an unlifted terminal world plus the corresponding lifted body premise.

## Derivability Table

The input target syntax has a cast at the outermost node.  With a source
`SpineValue`, the possible premise heads are as follows.

| Premise head | Status | Reason / output |
| --- | --- | --- |
| `⊑cast² c̃ prem q` | Derivable only at variable-typed source positions. | The premise has `q : A ⊑ᵂ⟨ W ⟩ ＇ Ỹ`.  By A4, `A ⊑ ＇Y` forces `A` to be a variable.  Therefore every non-variable head, including the binder-lifted function case, is empty here.  Variable cases expose the target seal and continue by the target-payload branch. |
| `cast⊑cast² c c̃ prem q` | Derivable only when the source cast exposes a variable-typed pre-cast position. | This is the positive source-tag/target-tag exposure path used by the chain probes.  If the source pre-cast type is base/function/∀ or a binder-lifted non-variable body, A4 gives the same emptiness.  The output rewraps the source cast with `cast⊑²` after the inner strip. |
| `Λ⊑² Anv z∈A liftγ vV target⊢ prem q` | Derivable; recurse under the binder. | This is the blocking SourceStrip case.  The recursive call must be the lifted member on `prem` under `liftWorldLeft X⊑★ W`.  The returned lifted terminal package rebuilds the head with `Λ⊑²`. |
| `cast⊑² c prem q` | Derivable; recurse down the source spine. | The output package from the recursive call is rewrapped by `cast⊑²`.  If the recursive branch attempts `⊑cast²` at a non-variable source obligation, it is empty by A4. |
| `reveal⊑²` / `conceal⊑²` | Derivable; recurse down the source spine. | The proof carries the source-side `RebaseAtᴸ` and conversion typing and rewraps the output with the same source-only wrapper.  Identity-pivot universal wrappers use `pivot-id-endpoints↑` / `pivot-id-endpoints↓`; pivoted wrappers use the existing rebase/lift machinery. |
| `conceal⊑²` with `seal X R` | Derivable, but the member still has no external source seal anchor. | The anchor is internal to this constructor.  The existing source-star and target-chain reasoning supplies the `S = ★` terminal and `S = ＇Y′` re-emission branches. |
| `•⊑²` | Excluded by `SpineValue`. | Type application is not a value spine.  Existing proofs already use an empty `()` case for this shape. |
| `x⊑x²`, `ƛ⊑ƛ²`, `·⊑·²`, `Λ⊑Λ²`, `•⊑•²`, `κ⊑κ²`, `⊕⊑⊕²` | Underivable at this target syntax. | Their target heads are variable, lambda, application, type abstraction/application, constant, or primitive operation, not an outer cast. |
| `⊑reveal²`, `⊑conceal²`, `reveal⊑reveal²`, `conceal⊑conceal²` | Not an outer-tag head, but used after tag exposure. | Once `⊑cast²` or `cast⊑cast²` exposes `U ↓ seal Ỹ S̃`, the target-seal branch analyzes these forms. |
| `blame⊑²` | Excluded by `SpineValue`. | `blame` is not a source value spine. |

Target payload branch:

| Payload `S̃` | Status | Output shape |
| --- | --- | --- |
| `★` | Derivable terminal. | Produce a terminal package with `Y★ = Ỹ`, `target∈★`, `q★ : A ⊑ᵂ⟨ W★ ⟩ ★`, and `premise★ : W★ ∣ γ★ ⊢² V ⊑ U ∶ q★`. |
| `＇ Y′` | Derivable chain branch. | Expose the inner target value at `Y′`, recurse/continue at the next target seal, then re-emit the target-only seal.  This is the A5/A6 positive shape: pair at the `★` terminus and re-emit outward. |
| `‵ ι`, `A ⇒ B`, `` `∀ A`` | Empty for the reachable variable/tag-exposure configurations. | After tag exposure the source-side obligation needed to pass through `＇ Ỹ` is variable-typed; a variable source cannot relate to these non-variable, non-star payloads.  This is the A3/A4 obstruction. |

Under binders, the same table applies with the world replaced by
`liftWorldLeft X⊑★ W`.  The A4 checked artifact
`lifted-fun-head-empty` confirms that a binder-lifted function head still
cannot satisfy an intermediate `A ⊑ ＇Y` obligation.

## Member Statements

The public result consumed by SourceStrip should be terminal.  The proof can
use an internal one-step branch datatype like `TargetSealDescentResult`, but it
should fold to this terminal package before returning to `SourceTagSealCore`.

Plain terminal package:

```agda
record TargetStripAt★Data
    (Wᵒ : World Δᴸ Δᴿ Δ) (γᵒ : CtxImp Wᵒ)
    (V : Term Δᴸ) (A : Ty Δᴸ)
    (U : Term Δᴿ) (Xᴸ : TyVar Δᴸ) : Set where
  field
    Y★ : TyVar Δᴿ
    W★ : World Δᴸ Δᴿ Δ
    γ★ : CtxImp W★
    mono★ : ImpEnvMono Wᵒ W★
    same★ : SameCtx γᵒ γ★
    boundary★ : RebaseAt W★ Wᵒ Xᴸ Y★
    target∈★ : targetStoreʷ W★ ∋ Y★ ⦂ ★
    q★ : A ⊑ᵂ⟨ W★ ⟩ ★
    premise★ : W★ ∣ γ★ ⊢² V ⊑ U ∶ q★
```

Plain member:

```agda
TargetStripAt★ : Set
TargetStripAt★ =
  ∀ {Wᵒ Wᵖ γᵒ γᵖ V U A S Xᴸ Y ν cY p}
  → Value U
  → ImpEnvMono Wᵒ Wᵖ
  → RebaseAt Wᵖ Wᵒ Xᴸ Y
  → SameCtx γᵒ γᵖ
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → Wᵖ ∣ γᵖ ⊢² V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p
  → TargetStripAt★Data Wᵒ γᵒ V A U Xᴸ
```

Binder-lifted terminal package:

```agda
record TargetStripAt★ᴸData
    (Wᵒ : World Δᴸ Δᴿ Δ) (γᵒ : CtxImp Wᵒ)
    (V : Term (suc Δᴸ)) (A : Ty (suc Δᴸ))
    (U : Term Δᴿ) (Xᴸ : TyVar Δᴸ) : Set where
  field
    Y★ : TyVar Δᴿ
    W★ : World Δᴸ Δᴿ Δ
    γ★ : CtxImp W★
    γ★ᴸ : CtxImp (liftWorldLeft X⊑★ W★)
    lift★ : LiftCtxᴸ X⊑★ γ★ γ★ᴸ
    mono★ : ImpEnvMono Wᵒ W★
    same★ : SameCtx γᵒ γ★
    boundary★ : RebaseAt W★ Wᵒ Xᴸ Y★
    target∈★ : targetStoreʷ W★ ∋ Y★ ⦂ ★
    q★ : `∀ A ⊑ᵂ⟨ W★ ⟩ ★
    body★ : A ⊑ᵂ⟨ liftWorldLeft X⊑★ W★ ⟩ ★
    U⊢★ : ⟨ Δᴿ , targetStoreʷ W★ , tgtCtxʷ γ★ ⟩ ⊢ U ⦂ ★
    premise★ : liftWorldLeft X⊑★ W★ ∣ γ★ᴸ ⊢² V ⊑ U ∶ body★
```

Binder-lifted member:

```agda
TargetStripAt★ᴸ : Set
TargetStripAt★ᴸ =
  ∀ {Wᵒ Wᵖ γᵒ γᵖ γᵇ V U A S Xᴸ Y ν cY p}
  → Value U
  → ImpEnvMono Wᵒ Wᵖ
  → RebaseAt Wᵖ Wᵒ Xᴸ Y
  → SameCtx γᵒ γᵖ
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → LiftCtxᴸ X⊑★ γᵖ γᵇ
  → liftWorldLeft X⊑★ Wᵖ ∣ γᵇ ⊢²
      V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p
  → TargetStripAt★ᴸData Wᵒ γᵒ V A U Xᴸ
```

The extra fields `q★`, `body★`, and `U⊢★` are intentional.  They avoid
reconstructing the exact `∀ A ⊑ ★` inhabitant and target typing from a body
premise at the call site.  They are available in the strip proof and are exactly
what `Λ⊑²` needs.

## Λ-Core Rebuild

Given `TargetStripAt★ᴸData`, the blocked branch is immediate:

```agda
lambda-core-from-target-strip★ᴸ :
  NonVar A
  → zero ∈ᵗ A
  → Value V
  → TargetStripAt★ᴸData Wᵒ γᵒ V A U Xᴸ
  → CoreRebuild Wᵒ γᵒ (Λ V) (`∀ A) U Xᴸ Y S
```

The proof builds a `TargetChainData` whose terminal premise is:

```agda
Λ⊑² Anv z∈A lift★ vV U⊢★ premise★ q★
```

and then returns `core-terminus`.

## Existing Lift Machinery

The needed lift support is already present:

- `liftWorldLeft` is the right shape for `Λ⊑²`; it keeps the target store and
  target term unshifted while the embedded target type is under the skipped
  target renaming.
- `liftWorldBoth-⊑ᵂ` and `liftRebaseAt` already cover both-side binder shifts.
- `renameWorld-liftLeft` and `renameWorld-liftBoth` are definitional (`refl`) in
  `CenterRename`.
- `LiftCtxᴸ` is the context relation needed by the lifted output package.
- `pivot-id-endpoints↑` and `pivot-id-endpoints↓` handle identity-pivot
  universal conversions.
- `TagTransport` already carries the universal-tag obligation transport and
  refutations needed by source reveal/conceal-all wrapper cases.

No change to `CastTermImprecision2` or the live imprecision relation is needed.

## Family Closure

The family closes with `TARGET-STRIP-AT-★` and `TARGET-STRIP-AT-★ᴸ`.

There is no separate doubly-lifted member.  Nested `Λ⊑²` cases call the same
lifted member with the current world already equal to a `liftWorldLeft` world;
another binder simply forms `liftWorldLeft X⊑★ (liftWorldLeft X⊑★ W)`.  This is
the same constructor applied again, not a new relation.

Proof recursion should use the lexicographic measure:

1. Height of the input `⊢²` derivation / source spine above the target tag.
   One-sided source constructors (`Λ⊑²`, `cast⊑²`, `reveal⊑²`, `conceal⊑²`)
   recurse on a strict premise derivation.
2. Target variable-chain depth from `Ỹ : S̃` to a `★` store entry.  The
   `S̃ = ＇Y′` branch follows the target value exposed by canonical forms and
   moves to the next store representation link.

Binder depth is represented in the world parameter and decreases through the
derivation premise; it does not require a third family member.

## Validation Transcript

Checked A4/A5/A6 hunt scratch:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home \
  agda -i GTSFImp -v0 TwoPostulatesHuntScratch.agda
```

Exit code: `0`.

Checked new member interface and consequences:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home \
  agda -i GTSFImp -v0 BodyStripCheck.agda
```

Exit code: `0`.

`BodyStripCheck.agda` validates:

- `lambda-core-from-member`: the blocking `Λ` core implication from the lifted
  member hypothesis.
- `instanceA-core`: instantiation on `TerminusRebuildProbe.InstanceA.body`.
- `walk-from-strip-with-target-strip★`: the walk-from-strip composition boundary
  with `TargetStripAt★`, `TargetStripAt★ᴸ`, and a completed `SourceTagSealCore`.
