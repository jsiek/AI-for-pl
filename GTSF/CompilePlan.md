# `consistency-cast-plan` Status And Work Plan

File Charter:

- Purpose: track the implementation status of `Compile.consistency-cast-plan`.
- Scope: maximal-lower-bound selection for consistency, coercion synthesis from
  imprecision evidence, and final assembly of directed cast plans.
- Dependencies: `Imprecision`, `Coercions`, `Compile`,
  `proof/CompileCoercions`, `proof/ImprecisionProperties`, and
  `proof/MaximalLowerBounds`.

## Current Goal

The compiler needs a directed cast plan for every consistency proof:

```agda
consistency-cast-plan :
  ∀ {Δ A B} →
  Label →
  Δ ⊢ A ~ B →
  CastPlan Δ [] A B
```

`CastPlan Δ Σ A B` chooses a maximal lower bound `C` of `A` and `B`, then
casts from `A` down to `C` and from `C` up to `B`:

```agda
down  : Coercion
down⊢ : Δ ∣ Σ ⊢ down ∶ A =⇒ C

up    : Coercion
up⊢   : Δ ∣ Σ ⊢ up ∶ C =⇒ B
```

The compile-time store is empty at the top level. Polymorphic coercions may
mention future store cells in their typing premises, because the target
reduction rules allocate those cells later. Compilation itself does not grow
the store.

## Done

### Public Compiler Shape

- `Compile.agda` now has the canonical capitalized module/file name.
- `CastPlan` is directed and contains only `down` and `up`.
- `consistency-cast-plan` takes a `Label`.
- Cast-producing gradual source constructors now carry labels.
- `compile` and `compile-value` no longer take a label parameter; recursive
  calls preserve source-node labels, and consistency-cast-plan calls use the
  label from the current gradual application or primitive-operation node.

### Core Imprecision Adjustments

`Imprecision.agda` was updated so endpoint well-formedness is true:

- `∀ⁱ_` carries occurrence proofs for both endpoints.
- `ν` now proves its body is imprecise to `⇑ᵗ B`, matching the typed
  polymorphic rule shape.

### Imprecision Properties

`proof/ImprecisionProperties.agda` now provides:

- well-formed imprecision assumptions and contexts:
  `WfImpAssm`, `WfImpCtx`;
- shift membership and well-formedness lemmas for `⇑ᵢ` and `⇑ᴸᵢ`;
- `idᵢ-wf` and `idᵢ-lookup`;
- endpoint well-formedness:
  `⊑-src-wf`, `⊑-tgt-wf`, and `idᵢ` specializations;
- consistency helpers:
  `~-sym`, `~-refl`, `~-left-wf`, `~-right-wf`, `~-lower-wf`;
- reflection from `⇑ᵗ` well-formedness:
  `WfTy-un⇑ᵗ`;
- reusable `idᵢ` facts and inversions used by the maximal-lower-bound proof:
  variable identity, no-star assumptions, base/variable inversions,
  arrow/forall target views, and shape-impossibility helpers.

### Coercion Synthesis

`proof/CompileCoercions.agda` now provides:

- a typed `Realizes` relation for imprecision assumptions;
- lookup helpers for realized `X ˣ⊑ˣ Y` and `X ˣ⊑★` assumptions;
- `Realizes-⇑ᵢ`, `Realizes-∀ⁱ`, and `realizes-idᵢ`;
- future-store realization helpers for `ν`:
  `Realizes-⇑ᴸᵢ`, `Realizes-ν-inst`, and `Realizes-ν-gen`;
- mutually recursive `coerce-up` and `coerce-down` for all imprecision cases:
  `id★`, `idι`, `idˣ`, `_↦_`, `∀ⁱ_`, `ν`, `tag ι`,
  `tag_⇒_`, and `tagˣ`.

The earlier untyped/simple realization idea was superseded by this typed
version because it carries exactly the coercion evidence needed by
`coerce-up` and `coerce-down`.

### Maximal Lower Bounds

`proof/MaximalLowerBounds.agda` now provides:

- `CommonLowerBound`, `StrictlyBelow`, and `MaximalLowerBound`;
- `CommonLowerBoundᶜ`, `StrictlyBelowᶜ`, and `MaximalLowerBoundᶜ` for the
  generalized proof direction with separate left, right, and output
  imprecision contexts;
- identity-context facts for `idᵢ`, including variable identity and no-star
  facts;
- `ComparableMaximalLowerBound` and `comparable⇒maximal`;
- concrete maximal cases for `★/★`, base/base, base/`★`, `★`/base,
  variable/variable, and arrows;
- `maximal-idᶜ`, which embeds closed identity-context MLB proofs into the
  generalized three-context record;
- generalized comparable/maximal `ᶜ` cases for `★/★`, base/base, base/`★`,
  and `★`/base under arbitrary left/right/output imprecision contexts;
- `maximal-id-var-varᶜ`, the closed identity-context `idˣ`/`idˣ` base case for
  the generalized proof;
- `MlbVarCtx`, a PolyConvert-style variable selector with fields for
  variable/variable, variable/`★`, and `★`/variable cases;
- identity and binder-lifted selector proofs:
  `MlbVarCtx-idᵢ`, `MlbVarCtx-∀∀`, `MlbVarCtx-∀ν`, and `MlbVarCtx-ν∀`;
- generalized variable maximality lemmas from `MlbVarCtx`, plus `MlbCtx`
  wrappers `maximal-var-varᵐ`, `maximal-var-starᵐ`, and
  `maximal-star-varᵐ`;
- arrow and star/arrow composition infrastructure, including generalized
  `ᶜ` composition from component `MaximalLowerBoundᶜ` proofs;
- `BinderMode`, `liftCtx`, and `MlbCtx`, generated from an `idᵢ` seed plus
  the specific selector-preserving lifts `∀∀`, `∀ν`, and `ν∀`;
- a checked counterexample, `no-MlbVarCtx-νν-id1`, showing that the analogous
  selector-preserving `νν` lift is impossible even over the one-variable
  identity context;
- the computational choice context:
  `MlbMode`, `MlbChoiceCtx`, `leftChoice`, `rightChoice`, and `choice-id`.
  The `neither` mode interprets to `X ˣ⊑★` on both sides using the ν-style
  shift, so the candidate-type computation can recurse through ν/ν without
  pretending the fresh variable is selectable in the output context;
- variable selection for candidate types:
  `choice-var-var`, `choice-var-star`, and `choice-star-var`;
- `mlb-type` and `mlb-type-from-lower`, which compute the candidate lower-bound
  type from the two lower-bound derivations.  These functions intentionally do
  not yet prove that the result is maximal;
- forall-lower route classification:
  `ForallForallLower²ᶜ` and `forall-forall-lower²-invᶜ`;
- forall support dispatch:
  `LiftMlb∀∀Support`, `left-∀∀-support`, `right-∀∀-support`,
  `forall-forall-support-dispatch`, and `forall-forall-support-open`.
  The `ff-via-νν` route calls `kνν` directly instead of trying to manufacture
  an `MlbCtx`/`MlbVarCtx` lift;
- the active theorem boundary `choose-mlbᶜ`, which chooses a maximal lower
  bound from the two lower-bound derivations rather than from endpoint shape;
- `choose-mlb-from-lower` and `choose-mlb`, thin top-level wrappers around
  `choose-mlbᶜ`.

The old shape-directed selector, its component-consistency postulates, and its
forall split postulates have been moved to
`proof/MaximalLowerBoundsJunk.agda`. Keep that file as reference material only;
do not import it into the active compiler/metatheory path.

### Assembly

`Compile.consistency-cast-plan` is no longer a standalone postulate. It now:

1. calls `choose-mlb`;
2. uses `coerce-down` on the selected left imprecision proof;
3. uses `coerce-up` on the selected right imprecision proof;
4. assembles the resulting `CastPlan`.

The remaining active postulate is now the single generalized theorem
`choose-mlbᶜ`; the previous shape-specific postulates are isolated in the junk
drawer.

### Current Checks

These passed after integration:

```sh
agda -v0 Compile.agda
agda -v0 proof/CompileCoercions.agda
agda -v0 proof/MaximalLowerBounds.agda
agda -v0 proof/ImprecisionProperties.agda
agda -v0 GradualTerms.agda
agda -v0 Terms.agda
agda -v0 MetaTheory.agda
```

## Left To Do

### 1. Prove `choose-mlbᶜ`

Current theorem boundary:

```agda
choose-mlbᶜ :
  MlbCtx Φᴸ Φᴿ Φᴼ →
  Φᴸ ⊢ C ⊑ A →
  Φᴿ ⊢ C ⊑ B →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ A B
```

The proof should recurse on the two lower-bound derivations, not split first on
the endpoint types.

### 2. Continue Refining `MlbCtx`

`MlbCtx` no longer has the overly broad same-context constructor:

```agda
same : MlbCtx Φ Φ Φ
```

The active version is generated from closed identity contexts and only keeps
the binder lifts that preserve the variable-selector invariant:

```agda
idᵐ : ∀ Δ → MlbCtx (idᵢ Δ) (idᵢ Δ) (idᵢ Δ)
lift∀∀ᵐ :
  MlbCtx Φᴸ Φᴿ Φᴼ →
  MlbCtx (liftCtx ∀ᵇ Φᴸ) (liftCtx ∀ᵇ Φᴿ) (liftCtx ∀ᵇ Φᴼ)
lift∀νᵐ :
  MlbCtx Φᴸ Φᴿ Φᴼ →
  MlbCtx (liftCtx ∀ᵇ Φᴸ) (liftCtx νᵇ Φᴿ) (liftCtx ∀ᵇ Φᴼ)
liftν∀ᵐ :
  MlbCtx Φᴸ Φᴿ Φᴼ →
  MlbCtx (liftCtx νᵇ Φᴸ) (liftCtx ∀ᵇ Φᴿ) (liftCtx ∀ᵇ Φᴼ)
```

The generic `liftᵐ mᴸ mᴿ mᴼ` was too broad for the variable-selector invariant.
For example, an output `ν` context cannot support the top-level `0 ˣ⊑ˣ 0`
obligation created by the `∀/∀` variable/variable selector.

The `ν/ν` case is now known not to fit this selector relation.  After ν-lifting
`idᵢ 1`, the shifted identity assumption is `1 ˣ⊑ˣ 0`, but a variable selector
for the recursive witness would need `1 ˣ⊑ˣ 1`.  The active proof direction is
therefore to keep `MlbCtx` selector-preserving for `∀∀`, `∀ν`, and `ν∀`, and
handle ν/ν through the forall route classifier and `kνν` support branch.

### 3. Port Lower-Bound Context Machinery

Port the useful pieces from
`PolyConvert/agda/extrinsic-inst/proof/ConsistencyAltProperties.agda`:

- any remaining `LowerCtx`-style relations for non-variable binder support,
  especially where they can feed the new forall route dispatch;
- context-shift/support lemmas for the `νν` and mixed-output maximality cases;
- map/weakening lemmas for imprecision derivations under context maps;
- occurrence transport lemmas needed by `∀ⁱ` and `ν`.

### 4. Recover Useful Old Lemmas Selectively

Only pull definitions back from `proof/MaximalLowerBoundsJunk.agda` when they
fit the new lower-bound-driven proof. Good candidates:

- base/star/variable comparability;
- arrow maximality composition;
- star/arrow maximality composition.

Do not revive the old endpoint-shape dispatcher or the shape-specific
postulates.

### 5. Remove Remaining Active Postulate And Recheck

The final active milestone is:

```sh
rg "postulate" GTSF/proof/MaximalLowerBounds.agda
agda -v0 Compile.agda
```

## Remaining Parallel Work

The old shape-specific chunks are obsolete. The remaining parallel work should
support `choose-mlbᶜ` instead.

### Chunk A. Context Relations

Owner area: `MlbCtx` and any helper context relation records.

Goal: design the constructors/fields needed for recursive calls under `∀ⁱ` and
`ν`.

### Chunk B. Context Maps For Imprecision

Owner area: reusable context-map lemmas, preferably in
`proof/ImprecisionProperties.agda` if they are not MLB-specific.

Goal: port the `map-⊑`/`map-νᵢ`/`map-∀ᵢ` style infrastructure from
PolyConvert.

### Chunk C. Base/Variable/Star Cases For `choose-mlbᶜ`

Owner area: first clauses of `choose-mlbᶜ`.

Goal: prove the non-polymorphic cases directly from the two lower-bound
derivations and existing comparability lemmas.

### Chunk D. Arrow Cases For `choose-mlbᶜ`

Owner area: arrow/arrow, star/arrow, and arrow/star recursive clauses.

Goal: reuse the existing arrow composition lemmas without resurrecting the old
component-consistency postulates.

### Chunk E. `∀ⁱ`/`ν` Cases For `choose-mlbᶜ`

Owner area: polymorphic clauses and lift lemmas.

Goal: extend the checked `ForallForallLower²ᶜ`/`LiftMlb∀∀Support` route into
the actual maximality clauses, then adapt the `Lift⊓∀νSupport` and
`Lift⊓ν∀Support` ideas for the mixed endpoint cases.

## Suggested Integration Order

1. Define the context relation shape first.
2. Add context-map and shift lemmas.
3. Fill the easy `choose-mlbᶜ` clauses.
4. Add arrow composition clauses.
5. Finish the `∀ⁱ`/`ν` lift clauses.
6. Remove `choose-mlbᶜ` as a postulate and run the final checks.
