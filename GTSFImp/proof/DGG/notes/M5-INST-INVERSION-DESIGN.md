# M5 Instantiation Inversion Design

Date: 2026-08-13. Status: the complete hereditary `Λ` package and relational
continuation are live without a split constructor.  The remaining four view
packages share a fuel-free structural value-instantiation descent.  Its typed
state, primary cast-mass layer, and concrete `∀`, `gen`, and `safe-inst`
decreases are checked.  Fixed-mass recursion follows strict imprecision
premises; the nested-accessibility worker is next.

Checked artifact:

```text
env -u AGDA_DIR agda -i GTSFImp -v0 --no-allow-unsolved-metas \
  GTSFImp/proof/DGG/notes/M5InstInversionDesignScratch.agda
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

It also checks the k=1 consumer rewrap:

```agda
Λ⊑Λ²-one-lift-rewrap-preflight
Λ⊑Λ²-one-lift-born-rewrap-preflight
```

The first statement shows the recursive `Λ⊑²` case accepts a one-left-lift
instance of the tower-indexed transport.  The second checks the sound
born-order base route: instantiate the closed depth-0 theorem at
`W := liftWorldLeft X⊑★ W₀`.  The remaining blocker is a term-derivation
exchange from that born-order result into the `liftWorldLeft W₂` world
required by the recursive `Λ⊑²` rewrap.

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
application under a smaller target value wrapper. The branch proof must
descend on target wrapper depth until the target is a value.

Re-evaluation, 2026-08-13: this descent is structural, not an arbitrary
extra-cast call charged to the outer inst cast.  The live theorems

```agda
strict-safe : ν X ≡ X∼X
  → (d : ν ⊢ B₀ ∼ B₁)
  → NonVar B₁
  → X ∈ᵗ B₁
  → GenSafe d

ext-safe : (d : extᵐ ν ⊢ B₀ ∼ B₁)
  → NonVar B₁
  → zero ∈ᵗ B₁
  → GenSafe d
```

classify both the stored consistency and its fresh-name opening.
`GenSafeView` proves that function, universal, and generated cases are inert;
`safe-inst` is the sole case that continues instantiation.  A checked finite
witness now shows it is reachable beneath a generated value cast and that
`β-gen` can expose a non-inert, non-value cast.  Therefore the structural
normalizer must include runtime-name type applications as well as casts and
conversions.  The old `M5AllFuelBoundScratch` arithmetic only refutes
borrowing the outer residual fuel for an arbitrary cast; its concrete opened
cast is inert.

The statement-first structural surface is now:

```agda
StructuralValueInstantiationᵀ =
  ∀ {p : A ⊑ᵂ⟨ W ⟩ `∀ (applyBody (bind R) B)}
    {q : A ⊑ᵂ⟨ W ⟩ applyBody (bind R) B [ ＇ zero ]ᵗ}
  → W ∣ γ ⊢² M ⊑ renameᵗᵐ wk↪ᵗ V ∶ p
  → Value M
  → Value V
  → AllValueView V
  → InstSpineDescentPackage W γ M
      (renameᵗᵐ wk↪ᵗ V ⦂∀ applyBody (bind R) B [ ＇ zero ]) q
```

The source `M` is explicitly a value.  The target is specifically the
weakening of a pre-allocation value and is instantiated at the available
fresh runtime name; an arbitrary raw type argument is intentionally excluded.
The theorem has no residual-cast fuel; its result already carries any
right-store extension and the transported relation.  The M5 finalizer applies
residual-column catch-up only after this structural descent has produced a
value.

## Termination Re-evaluation

The first `pendingAdministrationRank` was not a measure for the complete
machine.  It charged casts and value wrappers but assigned zero to name
applications and conversion frames.  A zero-cost frame can later become a
value wrapper, so the alleged rank may rise.  The unused rank modules have
been removed rather than retained as a misleading public surface.

The checked replacement begins with

```agda
pendingCastMass vV spine = valueCastMass vV + spineCastMass spine
```

It counts consistency syntax wherever it currently resides.  Allocation
preserves this count under value weakening and spine mapping.  The concrete
fresh-open `∀` step, the `gen` step, and the recursive `safe-inst` step each
strictly decrease it.  The typed child spines contain explicit zero-syntax
type transports for the propositional equalities between `replaceTy`, opened
types, and OPE weakening; this localizes transport instead of spreading
`subst` through the worker.

Cast-mass-preserving steps recurse on strict premises of the imprecision
derivation.  The checked `value-type-app-source-view` case split is exhaustive,
and `no-value-source-type-app` recursively eliminates all five admissible
outer rules while retaining an inner source `Value`.  This validates nested
accessibility: ordinary structural recursion at fixed mass, and an
accessibility restart only for the strictly smaller `safe-inst` cast mass.
No secondary numeric potential or public fuel is needed.

The first two fixed-mass clauses are live in
`StructuralValueInstantiationCastProof`.  `source-inert-cast-descent` rebuilds
a source cast around a descended strict premise.  `target-inert-cast-descent`
lifts the premise reduction through the target cast, maps its consistency and
inertness across store changes, and rebuilds the target-only relation at the
final value.  `type-transport-descent` closes the term-invariant transport
frame by proof-index retargeting.

The existential `WorldExtendᴿ` in the public result intentionally hides
center history, so it is too weak for an outer source reveal/conceal rewrap.
The internal worker now uses `StructuralWorldExtendᴿ`, an inductive trace of
`keep` and target-bind insertion steps.  Its erasure theorem returns the
public extension record; future wrapper clauses transform the structural
trace before packaging it.
`structural-rebase-atᴸ` is the first checked transformer: it commutes every
target bind through a source reveal using `insertRebaseAtᴸ`, preserves keeps,
and returns the final rebase needed to rebuild `reveal⊑²`.
`structural-tag-rebase-atᴸ` mirrors this for source conceal, retaining the
premise-to-conclusion orientation and mapping the target pivot across the
complete store-change trace.

Update, 2026-08-13: the live finalizer now treats this package as
authoritative.  `InstPostCatalogPackageAt` requires neither an immediate
catalog-post value nor an immediate catalog-post relation.
`inst-post-at-finish` lifts the descent through the pending residual cast,
transports `CatchupCast⁻` and cast size, and invokes the smaller extra-cast
worker only on the descended value.  Thus the four remaining view branches
produce the relation at the descended value, not at an intermediate raw type
application.

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

## Phase A‴ Addendum: Indexed Post Catalog

The live surface now has:

```agda
record InstPostCatalogPackageAt ...
  (χs₂ : StoreChanges Δᴿ Δᴿ₂)
  (W₂ : World Δᴸ Δᴿ₂ Δ₂)
  (ext₂ : WorldExtendᴿ χs₂ W W₂) : Set₁
```

It fixes the post-catalog world instead of existentially packaging it.
The root bridge packages that indexed result into the old driver-facing
`InstPostCatalogPackage` only once, after composing the indexed
prefix-to-residual trace with the smaller extra-cast worker.

The indexed/CPS blocker is resolved. The next blocker is the `Λ⊑Λ²`
base body transport: the available body premise is in
`liftWorldBoth X⊑X W`, but the post-catalog package needs the body
relation in `liftWorldLeft X⊑★ W₂` against the generated `β-Λ` target
body plus reveal wrappers. See
`m5-inst-inversion-lambda-base-post-blocked.red`.
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

## Phase A⁗ Addendum: Λ Base Transport Surface

The live Def surface now includes the checked concrete two-bind statement:

```agda
Λ⊑Λ²PostBodyTransportᵀ : Set
```

It consumes the original `liftWorldBoth X⊑X W` body premise from a
`Λ⊑Λ²` core and returns the post body relation in
`liftWorldLeft X⊑★ (rightOnlyWorld (rightOnlyWorld W ★) (＇ zero))`,
together with the transported lifted context, the post target
value/typing, the body obligation, and the aligned top `∀` obligation.
The scratch checks:

```agda
Λ⊑Λ²-base-rewrap-preflight :
  Λ⊑Λ²PostBodyTransportᵀ → ...
```

so the base rewrap is mechanical once the transport exists.

The first target insertion now checks with
`TargetExtend.⊢²-target-insert` and `keepRightBindTargetInsert`, producing
the post-`β-Λ` body target `renameᵗᵐ (keep wk↪ᵗ) V′`. Implementation is
blocked at the next store-sensitive step: the inserted body relation is in
target store `store-lift (store-bind Σ ★)`, while the catalogued `β-Λ`
post body lives in `store-bind (store-bind Σ ★) (＇ zero)`. Preservation
has `typing-lift-to-bind` for typing, but CTI2 has no relation-level
analogue for arbitrary `_∣_⊢²_⊑_∶_` derivations. See
`m5-inst-inversion-lambda-post-store-transport-blocked.red`.

## Phase A⁗⁺ Addendum: Fresh Lift-To-Bind Conversion

The approved concrete tower remains the live post-body surface. The scratch
now additionally validates the prefix composition:

```agda
target-insert bind ★
→ fresh lift-to-bind conversion
→ X⊑X-to-X⊑★ decay
```

The fresh conversion world is:

```agda
ΛLiftToBindFreshWorld v W =
  world
    (skip (keep (skip (ηᴸʷ W))))
    (skip (keep (keep (ηᴿʷ W))))
    (instᵐ (extendᵐ v (instᵐ (impEnvʷ W))))
    (store-lift (sourceStoreʷ W))
    (store-bind (store-bind (targetStoreʷ W) ★) (＇ zero))
```

`proof/DGG/TargetBindLift.agda` now checks the reusable foundation:
center-rename normalization, indexed conversion store transport,
pivot-to-store inversion for target conversions, target typing transport, and
target-side `RebaseAt` transport when a target indexed conversion supplies the
pivot store lookup.

The remaining blocker is not target-side. It is the source-side rebase-var
constructors:

```agda
reveal⊑² ... (rebase-varᴸ rb) ... c⊢ M⊑M′ q
conceal⊑² ... (tag-rebase-varᴸ rb) ... c⊢ M⊑M′ q
```

These constructors can carry a `StoreRepImp` whose aligned target pivot is the
fresh abstract target binder, but they provide no target conversion premise
from which to obtain a target store lookup. The fresh lift-to-bind store
changes:

```agda
resolveVar (store-lift (store-bind Σ ★)) zero = ＇ zero
resolveVar (store-bind (store-bind Σ ★) (＇ zero)) zero = ★
```

Before the planned `X⊑X → X⊑★` decay, transporting that `StoreRepImp` would
require `resolveVar sourceStore Xᴸ ⊑ᵂ ★` from only
`resolveVar sourceStore Xᴸ ⊑ᵂ ＇ zero`. See
`m5-inst-inversion-lift-to-bind-source-rebase-blocked.red`.

RESOLVED (2026-08-12): Route 1 reorders the proof so decay happens before
the fresh lift-to-bind conversion.  The checked live composition is:

```agda
target-insert bind ★
→ decay X⊑X to X⊑★ under liftWorldBoth
→ center extension
→ fresh lift-to-bind conversion at the ★ mark
→ generated target reveals via RebaseAtᴿ
→ target typing via target-typing²
```

`Λ⊑Λ²-post-body-transport`, `Λ⊑Λ²-base-package-at`, and the scratch
preflight check.  The remaining recursive assembly blocker is not the base
transport itself.  In the `Λ⊑²` case, body recursion must return its indexed
post package at

```agda
liftWorldLeft X⊑★
  (rightOnlyWorld (rightOnlyWorld W ★) (＇ zero))
```

while the specialized `Λ⊑Λ²` base for the body world lands at

```agda
rightOnlyWorld
  (rightOnlyWorld (liftWorldLeft X⊑★ W) ★)
  (＇ zero)
```

These towers differ by the order of the existing source left lift and the two
generated right binds.  See
`m5-inst-inversion-lambda-recursive-extension-blocked.red`.

## Phase A⁗⁺⁺ Addendum: Left-Lift Tower Surface

The live definition now records the approved depth-indexed surface:

```agda
data Λ⊑Λ²LeftTower W W₂ ext₂ : Set₁

Λ⊑Λ²PostBodyTransportᴸᵀ : Set₁
```

`Λ⊑Λ²LeftTower` has a depth-zero constructor for the concrete two-bind
tower and a successor constructor for lifting both the input world and
the post world by `liftWorldLeft X⊑★`.  The scratch checks:

```agda
Λ⊑Λ²-base-rewrap-preflightᴸ :
  Λ⊑Λ²PostBodyTransportᴸᵀ → ...
```

so a transport at the caller-supplied tower rewraps through `Λ⊑²`
mechanically.

Implementation is blocked in the successor case.  After the first
target insertion under the left tower and the `liftWorldBoth` decay, the
abstract target binder introduced by `liftWorldBoth` remains before the
existing source-only binder.  The lifted two-bind post world needs the
generated target names after that source binder.  `TargetStoreMove`
cannot change target embeddings, `CenterRename` is order-preserving, and
the generated target reveal rebuilds freeze target embeddings through
`RebaseAtᴿ`.  See
`m5-inst-inversion-lambda-lifted-target-pivot-blocked.red`.
