# M5 Instantiation Inversion Design

Date: 2026-08-11. Status: checked design scratch.

Checked artifact:

```text
AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
  M5InstInversionDesignScratch.agda
# exit 0
```

The scratch edits no live module. It states the inversion package that the
blocked M5 relational continuations need, and checks the package-to-surface
bridge:

```agda
inst-inversion→rel-surface : ∀ {fuel}
  → InstInversionPackage fuel
  → InstRelContinuationSurface fuel
```

## Proposed Package

The top-level package is:

```agda
record InstInversionPackage (fuel : ℕ) : Set₁ where
  field
    fuel-step : FuelStepSurface fuel
    inst-prefix : InstCastAllocPrefixᵀ
    all-value-step-catalog : AllValueViewStepCatalogᵀ
    inst-alloc-decrease : inst-alloc-decreaseᵀ
    catchup⁻-embed : Catchup⁻Embedᵀ

    Λ-package : ...
    ∀-package : ...
    gen-package : ...
    reveal-package : ...
    conceal-package : ...
```

Each view field consumes exactly the premises of the matching
`InstRelContinuationSurface` field and returns:

```agda
InstPostCatalogPackage fuel rel vM vM′ c′ B′≢★ c<fuel q
```

The post-catalog package records the target-side information that is missing
from the current M5 relational proof:

- a right-extended world `W₂` and transported context,
- a post-step target term `post`,
- the aligned source obligation `p₂`,
- the relation
  `W₂ ∣ mapCtxᴿ ext₂ γ ⊢² M ⊑ post ∶ p₂`,
- a residual consistency proof
  `residual-cast : ν₂ ⊢ B₂ ∼ applyTys χs₂ B′`,
- residual provenance
  `CatchupCast⁻ p₂ residual-cast (transport⊑ᵂ ext₂ q)`,
- a `spine-descent` package for non-value reducts,
- the final `InstCatchupRightAt` result as `finish`.

The `finish` field is deliberate. It is the composition proof obligation:
allocation prefix, catalog step, post-step relation, residual provenance,
smaller-fuel recursion, and trace/world composition must assemble to the live
surface result. The scratch validates that once a theorem inhabits these
fields, the existing dispatcher closes mechanically.

## Spine Descent

The scratch states a reusable descent target:

```agda
record InstSpineDescentPackage W γ M post p : Set₁ where
  field
    W′ : World ...
    ext : WorldExtendᴿ χs W W′
    final : Term ...
    final-value : Value final
    post-reduction : post —↠[ χs ] final
    final-relation :
      W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ final ∶ transport⊑ᵂ ext p
```

For the `Λ` branch this can be zero descent. For the `∀`, `gen`, `reveal`,
and `conceal` branches, the one catalog step exposes another pending type
application under a smaller target value wrapper. The future proof should
recursively descend on target wrapper depth until the target is a value, then
call the smaller extra-cast worker on the residual provenance.

## Per-View Composition Status

`Λ`: checked as `Λ-package` projecting to `Λ-cont`. The package must derive
the post-`β-Λ` relation, with the target body transported through the two
right-side allocations. No statement-level refutation was found, but the proof
must invert through source casts, source reveals, and source conceals before
using the target `Λ` body relation.

`∀`: checked as `∀-package` projecting to `∀-cont`. The catalog removes
the outer `∀ᶜ` cast and leaves a pending inner type application. The
continuation
therefore needs spine descent plus the residual `CatchupCast⁻`.

`gen`: checked as `gen-package` projecting to `gen-cont`. This branch
carries the catalog's `GenSafe d`, `B₀ ≢ ★`, and occurrence premises. It
also needs
descent because the generated reveal step does not directly produce a final
value.

`reveal`: checked as `reveal-package` projecting to `reveal-cont`. The proof
needs a universal-conversion transport analogue for the target reveal, then
descends through the exposed type application.

`conceal`: checked as `conceal-package` projecting to `conceal-cont`. This is
the reveal case with the target conceal transport direction reversed; it still
needs descent and residual provenance.

## Reuse Map

`SpineValueDef.agda`: direct reuse. `AllValueView` already provides the five
target polymorphic value shapes, and `SpineValue` is the right source-value
view for stripping source wrappers.

`RightInjInversion2Def/Proof/Lemma.agda`: pattern reuse, not direct reuse.
The M3 theorem shows how to rebuild relations through source cast, reveal,
and conceal constructors while preserving the target. Its statement is
tag-target-specific, so M5 needs a new polymorphic-target analogue.
Estimated size: large, about 400 to 700 LOC.

`SourceStripColumnView.agda` and `SourceStripDef/Proof/Lemma.agda`: strong
pattern reuse. The branch-package style transfers: strip source wrapper
columns, expose a core relation, and return finish continuations that rebuild
the original relation. The target boundary predicates must be replaced by
polymorphic-target application predicates.
Estimated size: medium to large, about 300 to 600 LOC.

`TargetChain*` and `TargetWalk*`: little direct reuse. These modules are about
walking target tag/seal chains, source-star pivots, and target variable
alignments. M5 target wrappers are `Λ`, `∀ᶜ`, `gen`, reveal, and conceal,
so
the walk terminus and chain lemmas are new.
Estimated new analogue: medium, about 250 to 500 LOC.

`TagTransport.agda`: partial reuse. The universal reveal/conceal transport
lemmas are the closest match for the source-side wrapper cases, especially
when obligations cross `∀` conversions. M5 likely needs instantiation-shaped
variants aligned with right-only allocation.
Estimated size: medium, about 150 to 300 LOC.

`SealPeelToolkit.agda`: mostly not reusable. Its variable-alignment and seal
partner views are specific to M3's target tag/seal geometry. The technique for
recording refutation views is useful, but the predicates should be new.
Estimated size: small reuse, under 100 LOC.

`TargetWalkSupport.agda`: partial reuse for world and context plumbing:
`ImpEnvMono`, `SameCtx`, binder lifting, and rebase composition patterns are
useful. The target-variable refutations are not.
Estimated size: medium support extraction, about 150 to 250 LOC.

## Risks And Checks

The main risk is the `Λ` branch. In CTI2, `Λ⊑Λ²` gives a body relation
only
when both sides are visible lambdas at the type level:

```agda
liftWorldBoth X⊑X W ∣ γ′ ⊢² V ⊑ V′ ∶ p
```

But `Λ⊑²` relates a source `Λ V` to an arbitrary typed target `M`, and the
source may also be wrapped by `cast⊑²`, `reveal⊑²`, or `conceal⊑²`.
So the
body relation is not a one-constructor inversion from the current premises.
It must be produced by the new source-strip plus target-polymorphic package.

This is not the same shape as the M3 crossing refutation. The target value
is a known polymorphic view, not an aligned tag variable, and no checked
counterexample currently shows the desired post-application relation is false.
The design therefore keeps the relation as a required package field rather
than weakening the live statement.

Residual provenance is another implementation risk. The expected theorem is
that the residual shape `↑ᶜ (close-instᶜ c′)` admits `CatchupCast⁻`
because
the source type is non-`★`; projection constructors require source `★` and
therefore cannot appear at the residual head. This should be proved by
induction on the residual consistency spine, using the intermediate world
obligations harvested from the relation inversion.

The non-value branches must recurse on target wrapper depth. A single catalog
step is insufficient for `∀`, `gen`, `reveal`, and `conceal`; each leaves a
pending type application that only later reaches a target value.
