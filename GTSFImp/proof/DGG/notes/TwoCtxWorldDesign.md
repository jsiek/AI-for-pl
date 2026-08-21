# Two-`Ctx` world relation design

## Status and scope

This note proposes replacing the proof-layer family
`World : TyCtx → TyCtx → TyCtx → Set` with a relation on the trusted
runtime typing contexts from `CastTerms`:

```agda
infix 4 _⊑ᶜ_

data _⊑ᶜ_ : Ctx → Ctx → Set
```

The common center remains internal to a relation witness.  It is not a third
index.  The source and target stores and term contexts are the `Σᵉ` and `Γᵉ`
fields of the two endpoint `Ctx` values.

Everything below is **schematic and unproved** as a replacement for the live
world.  `notes/probes/TwoCtxWorldSkeletonProbe.agda` does check the mutual
relation/projection pattern, the constructor-form allocation indices, and the
displayed smart functions under `--safe`.
`notes/probes/TwoCtxWorldInvariantsProbe.agda` checks that every raw
constructor implies the four direct nominal world invariants and checks a
direct-store rebase graph plus its same-world case.  The later rebase-plan
probe checks the corresponding structural function over an explicit plan.  A
general producer of such plans and all live preservation theorems remain
unproved.  This note does not authorize a change to the live term-imprecision
relation.

Later probes check the first nontrivial provenance layers.  The
`TwoCtxSourceRebasePlanProbe` implements one local source/target allocation
commutation and carries it through every later raw history constructor.  The
`TwoCtxAdministrativeAliasFocusProbe` keeps a stable world unchanged while a
boundary-local view consumes exactly one fresh target edge `β := α`.
`TwoCtxAliasFocusModeProbe` stacks those exact one-edge views and checks the
two-boundary `β := α`, `α := ★` reveal spine.
`TwoCtxTypedAliasBoundaryProbe` adds explicit source/target term and type
indices to that surface.  All check under `--safe`; none follows a
representation chain.

## Trusted endpoint structure

The proposal relies on the existing top-level definition:

```agda
record Ctx : Set where
  constructor ⟨_,_,_⟩
  field
    Δᵉ : TyCtx
    Σᵉ : TyStore Δᵉ
    Γᵉ : TermCtx Δᵉ
```

Thus a witness `W : Cᴸ ⊑ᶜ Cᴿ` relates the complete static and runtime
contexts.  It must not be paired with a second list relation carrying the term
contexts again.

## Constructor-form raw surface

The relation should be entirely inductive, with the empty runtime context as
its base case.  Raw constructors expose fresh variables for lifted term
contexts and put equations such as `Γ⁺ ≡ ⇑ᶜ Γ` in premises.  This keeps
defined functions out of the constructor indices.

The following is the intended core surface.  `RightBindFreshᶜ` is a genuine
reusable allocation guard, not authorization to follow representation chains.
For readability, this block and the projection block below display one
intended mutual definition in two pieces.  Whether Agda accepts that mutual
definition is an explicit probe obligation.

```agda
mutual
  data _⊑ᶜ_ : Ctx → Ctx → Set where
    emptyᶜ :
      ⟨ zero , store-empty , [] ⟩ ⊑ᶜ
      ⟨ zero , store-empty , [] ⟩

    bind-termᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → A ⊑ᵀ⟨ W ⟩ B
      → ⟨ Δᴸ , Σᴸ , A ∷ Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , B ∷ Γᴿ ⟩

    skip-centerᶜ : ∀ {Cᴸ Cᴿ}
      → Cᴸ ⊑ᶜ Cᴿ
      → Cᴸ ⊑ᶜ Cᴿ

    lift-both-rawᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → VarImp
      → Γᴸ⁺ ≡ ⇑ᶜ Γᴸ
      → Γᴿ⁺ ≡ ⇑ᶜ Γᴿ
      → ⟨ suc Δᴸ , store-lift Σᴸ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ suc Δᴿ , store-lift Σᴿ , Γᴿ⁺ ⟩

    lift-left-rawᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → Γᴸ⁺ ≡ ⇑ᶜ Γᴸ
      → ⟨ suc Δᴸ , store-lift Σᴸ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩

    bind-left-rawᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → (A : Ty Δᴸ)
      → Γᴸ⁺ ≡ ⇑ᶜ Γᴸ
      → ⟨ suc Δᴸ , store-bind Σᴸ A , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩

    bind-right-rawᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → (B : Ty Δᴿ)
      → RightBindFreshᶜ W B
      → Γᴿ⁺ ≡ ⇑ᶜ Γᴿ
      → ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ suc Δᴿ , store-bind Σᴿ B , Γᴿ⁺ ⟩

    bind-both-rawᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → (A : Ty Δᴸ)
      → (B : Ty Δᴿ)
      → A ⊑ᵀ⟨ W ⟩ B
      → Γᴸ⁺ ≡ ⇑ᶜ Γᴸ
      → Γᴿ⁺ ≡ ⇑ᶜ Γᴿ
      → ⟨ suc Δᴸ , store-bind Σᴸ A , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ suc Δᴿ , store-bind Σᴿ B , Γᴿ⁺ ⟩

    bind-both-star-rawᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → (A : Ty Δᴸ)
      → (B : Ty Δᴿ)
      → A ⊑ᵀ⟨ W ⟩ B
      → ⇑ᵗ A ≢ ★
      → Γᴸ⁺ ≡ ⇑ᶜ Γᴸ
      → Γᴿ⁺ ≡ ⇑ᶜ Γᴿ
      → ⟨ suc Δᴸ , store-bind Σᴸ A , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ suc Δᴿ , store-bind Σᴿ B , Γᴿ⁺ ⟩
```

The current `honestifyʷ`, `lower-leftʷ`, `mix-targetʷ`, and
`mix-renamed-targetʷ` constructors are intentionally absent.  The last three
accept already assembled global invariants and bypass the inductive history.
Honestification, center renaming, and source rebasing should be checked
functions or function graphs over the new structure, not extra constructors.

## Hidden-center projections and type imprecision

Only information absent from the endpoint indices needs projection:

```agda
centerᶜ : ∀ {Cᴸ Cᴿ} → Cᴸ ⊑ᶜ Cᴿ → TyCtx

ηᴸᶜ : ∀ {Cᴸ Cᴿ} (W : Cᴸ ⊑ᶜ Cᴿ)
  → Δᵉ Cᴸ ↪ᵗ centerᶜ W

ηᴿᶜ : ∀ {Cᴸ Cᴿ} (W : Cᴸ ⊑ᶜ Cᴿ)
  → Δᵉ Cᴿ ↪ᵗ centerᶜ W

marksᶜ : ∀ {Cᴸ Cᴿ} (W : Cᴸ ⊑ᶜ Cᴿ)
  → ImpEnv (centerᶜ W)

infix 4 _⊑ᵀ⟨_⟩_

_⊑ᵀ⟨_⟩_ : ∀ {Cᴸ Cᴿ}
  → Ty (Δᵉ Cᴸ)
  → Cᴸ ⊑ᶜ Cᴿ
  → Ty (Δᵉ Cᴿ)
  → Set

A ⊑ᵀ⟨ W ⟩ B =
  marksᶜ W ⊢
    renameᵗ (toRenameᵗ (ηᴸᶜ W)) A
      ⊑ renameᵗ (toRenameᵗ (ηᴿᶜ W)) B

RightBindFreshᶜ : ∀ {Cᴸ Cᴿ}
  → Cᴸ ⊑ᶜ Cᴿ
  → Ty (Δᵉ Cᴿ)
  → Set
RightBindFreshᶜ W B =
  ⇑ᵗ B ≡ ★
    ⊎ Σ[ Yᴿ ∈ TyVar (suc (Δᵉ Cᴿ)) ]
        (⇑ᵗ B ≡ ＇ Yᴿ)
      × (∀ Xᴸ
          → toRenameᵗ (skip (ηᴸᶜ W)) Xᴸ
            ≢ toRenameᵗ (keep (ηᴿᶜ W)) Yᴿ)
```

There should be no public `sourceStore`, `targetStore`, `sourceCtx`, or
`targetCtx` aliases.  The canonical expressions are `Σᵉ Cᴸ`, `Σᵉ Cᴿ`,
`Γᵉ Cᴸ`, and `Γᵉ Cᴿ`.

## Smart functions

The raw equality arguments should be hidden behind the following public
operations.  Their implementations and laws are **schematic and unproved**.

```agda
liftBothᶜ : ∀ {Cᴸ Cᴿ}
  → VarImp
  → Cᴸ ⊑ᶜ Cᴿ
  → ⇑ᵉᵗ Cᴸ ⊑ᶜ ⇑ᵉᵗ Cᴿ

liftLeftᶜ : ∀ {Cᴸ Cᴿ}
  → Cᴸ ⊑ᶜ Cᴿ
  → ⇑ᵉᵗ Cᴸ ⊑ᶜ Cᴿ

bindLeftᶜ : ∀ {Cᴸ Cᴿ}
  → (W : Cᴸ ⊑ᶜ Cᴿ)
  → (A : Ty (Δᵉ Cᴸ))
  → (Cᴸ ,ˢ A) ⊑ᶜ Cᴿ

bindRightᶜ : ∀ {Cᴸ Cᴿ}
  → (W : Cᴸ ⊑ᶜ Cᴿ)
  → (B : Ty (Δᵉ Cᴿ))
  → RightBindFreshᶜ W B
  → Cᴸ ⊑ᶜ (Cᴿ ,ˢ B)

bindBothᶜ : ∀ {Cᴸ Cᴿ}
  → (W : Cᴸ ⊑ᶜ Cᴿ)
  → (A : Ty (Δᵉ Cᴸ))
  → (B : Ty (Δᵉ Cᴿ))
  → A ⊑ᵀ⟨ W ⟩ B
  → (Cᴸ ,ˢ A) ⊑ᶜ (Cᴿ ,ˢ B)

bindBothStarᶜ : ∀ {Cᴸ Cᴿ}
  → (W : Cᴸ ⊑ᶜ Cᴿ)
  → (A : Ty (Δᵉ Cᴸ))
  → (B : Ty (Δᵉ Cᴿ))
  → A ⊑ᵀ⟨ W ⟩ B
  → ⇑ᵗ A ≢ ★
  → (Cᴸ ,ˢ A) ⊑ᶜ (Cᴿ ,ˢ B)
```

## Term-context entries

Term-variable lookup should join the two trusted endpoint lookups with the
type-imprecision proof already indexed by the world:

```agda
infix 4 _∋ᶜ_⦂_

data _∋ᶜ_⦂_ {Cᴸ Cᴿ} (W : Cᴸ ⊑ᶜ Cᴿ) (x : Var) :
    ∀ {A B} → A ⊑ᵀ⟨ W ⟩ B → Set where
  entryᶜ : ∀ {A B} {p : A ⊑ᵀ⟨ W ⟩ B}
    → Cᴸ ∋ᵗ x ⦂ A
    → Cᴿ ∋ᵗ x ⦂ B
    → W ∋ᶜ x ⦂ p
```

The new relation therefore owns the term-context correspondence.  The old
`CtxImpEntry`, `CtxImp`, `srcCtxʷ`, `tgtCtxʷ`, and `_∋ʷ_⦂_` are not
parallel inputs to CTI.

## Direct-representation rebase

Rebase must preserve the endpoint `Ctx` indices.  Consequently the stores and
term contexts are definitionally unchanged.  A source rebase may move its
source pivot, every target pivot remains frozen, and the final pivots are
aligned.

The representation premise must use direct store entries.  The following is
the preferred **schematic and unproved** function-and-graph interface:

```agda
SourceRebasePlan : ∀ {Cᴸ Cᴿ}
  → (W : Cᴸ ⊑ᶜ Cᴿ)
  → TyVar (Δᵉ Cᴸ)
  → TyVar (Δᵉ Cᴿ)
  → Set

rebaseSourceᶜ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ}
  → SourceRebasePlan W Xᴸ Xᴿ
  → Cᴸ ⊑ᶜ Cᴿ

data RebaseSourceᶜ {Cᴸ Cᴿ} (W : Cᴸ ⊑ᶜ Cᴿ) :
    Cᴸ ⊑ᶜ Cᴿ → TyVar (Δᵉ Cᴸ) → TyVar (Δᵉ Cᴿ) → Set where
  rebase-sourceᶜ : ∀ {Xᴸ Xᴿ}
    → (plan : SourceRebasePlan W Xᴸ Xᴿ)
    → lookupStore (Σᵉ Cᴸ) Xᴸ
        ⊑ᵀ⟨ rebaseSourceᶜ plan ⟩
      lookupStore (Σᵉ Cᴿ) Xᴿ
    → RebaseSourceᶜ W (rebaseSourceᶜ plan) Xᴸ Xᴿ

rebaseSource-center : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ}
    (plan : SourceRebasePlan W Xᴸ Xᴿ)
  → centerᶜ (rebaseSourceᶜ plan) ≡ centerᶜ W
rebaseSource-center plan = refl

rebaseSource-ηᴸ-off-pivot :
  ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ Yᴸ}
    (plan : SourceRebasePlan W Xᴸ Xᴿ)
  → Yᴸ ≢ Xᴸ
  → toRenameᵗ (ηᴸᶜ (rebaseSourceᶜ plan)) Yᴸ
      ≡ toRenameᵗ (ηᴸᶜ W) Yᴸ

rebaseSource-ηᴿ-frozen :
  ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ}
    (plan : SourceRebasePlan W Xᴸ Xᴿ)
    (Yᴿ : TyVar (Δᵉ Cᴿ))
  → toRenameᵗ (ηᴿᶜ (rebaseSourceᶜ plan)) Yᴿ
      ≡ toRenameᵗ (ηᴿᶜ W) Yᴿ

rebaseSource-pivot-aligned :
  ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ}
    (plan : SourceRebasePlan W Xᴸ Xᴿ)
  → toRenameᵗ (ηᴸᶜ (rebaseSourceᶜ plan)) Xᴸ
      ≡ toRenameᵗ (ηᴿᶜ (rebaseSourceᶜ plan)) Xᴿ
```

It must not use `resolveVar`, `resolveRep`, or a transitive representation-chain
predicate.  Direct entries are the nominal representation choices made by the
trusted reduction semantics.

`SourceRebasePlan` describes local movement in the inductive history.  The
checked skeleton probe has now chosen and exhausted its constructor cases.
Because the center is hidden behind the world witness, its
`rebaseSource-centerᶜ₀` theorem is proved structurally and the embedding laws
perform the corresponding explicit `Fin` transports.  The displayed live
interface remains schematic, but the function-and-graph alternative is no
longer an untested design choice.

The checked invariant probe confirms that the fallback graph is well typed,
but also makes its cost precise.  Since the center is hidden, two arbitrary
witnesses do not have definitionally equal center indices.  The graph must
transport old embedding points along its explicit center equality before it
can state the off-pivot and frozen-target equations.  The same-world case
reduces by `refl` without extensionality.

Every raw allocation constructor fixes both an endpoint allocation and that
variable's center placement.  Moving a source pivot while preserving the two
endpoint `Ctx` indices therefore requires a checked plan that commutes a source
allocation through the later history.  Adding a function without such local
commutations would merely hide the missing provenance.

The checked `TwoCtxSourceRebasePlanProbe` now supplies the first such
commutation.  In normalized form its local rewrite is

```agda
bind-right-rawᶜ₀ (bind-left-rawᶜ₀ W A) B
  ↦ bind-both-star-rawᶜ₀ (skip-centerᶜ₀ W) represented A≠★
```

The old source-only cell becomes vacant and the source/target pivots occupy a
fresh dynamic paired cell.  The endpoint `Ctx` indices are identical on both
sides of the rewrite.  The plan commutes recursively through every raw history
head: skipped centers, target-only and source-only allocations, both lift
forms, both paired-bind forms, and term binding.  Target-only commutation
deliberately requires a new freshness proof for the rebuilt history.  Term
binding and both paired binds likewise require their type-imprecision proof in
the rebuilt world instead of assuming it is transportable.  The probe proves
center preservation, off-pivot source preservation, frozen target embeddings,
pivot alignment, all four direct invariants, and the direct-store graph
obligation.

This makes `rebaseSourceᶜ₀` total over the checked plan and every constructor
of the raw skeleton.  It does not claim that an arbitrary world and arbitrary
pivot pair admits a plan: identity requires existing direct alignment, while
the moving base case requires the explicit adjacent source-only/target-only
allocation geometry.  That distinction keeps the operational provenance in
the plan rather than turning rebase into an unrestricted world rewrite.

## Boundary-scoped administrative alias focus

The strict Λ trace must preserve three distinct facts:

- the source runtime name `X`;
- the old target name `α` and the fresh target name `β`;
- the one-step target store edge `β := α`.

It must not turn these facts into `X = β`, `β = α`, or `β = ★`.
The stable world therefore leaves `X` and `α` at distinct center points.
The checked probe adds a boundary-local focus:

```agda
record TargetNameFocusᶠ₀ (W : Cᴸ ⊑ᶜ₀ Cᴿ)
    (X : TyVar (Δᵉ Cᴸ)) (α : TyVar (Δᵉ Cᴿ)) : Set where
  field
    stable-points-separated :
      centerᴸ W X ≢ centerᴿ W α
    source-direct-self :
      lookupStore (Σᵉ Cᴸ) X ≡ ＇ X
    stable-direct-representations :
      lookupStore (Σᵉ Cᴸ) X ⊑ᵀ₀⟨ W ⟩ lookupStore (Σᵉ Cᴿ) α
```

The last field is an explicit direct-entry proof; it is not derived by
aligning the stable points.  A constructor-form boundary then records only the
fresh endpoint allocation:

```agda
data TargetAliasBoundaryᶠ₀ (focus : TargetNameFocusᶠ₀ W X α) :
    Ctx → Set where
  target-alias-rawᶠ₀ : ∀ {Γᴿ⁺}
    → Γᴿ⁺ ≡ ⇑ᶜ Γᴿ
    → TargetAliasBoundaryᶠ₀ focus
        ⟨ suc Δᴿ , store-bind Σᴿ (＇ α) , Γᴿ⁺ ⟩
```

`aliasBoundarySubᶠ₀` maps the new target zero to the direct representation
`＇ α` and maps every old target successor back to that old name.
`BoundaryTypeImprecisionᶠ₀` applies this one substitution and then the
single local focus at `α`.  There is no recursive store lookup.  In the checked
concrete world, the endpoint store remains literally

```text
β ↦ α⁺, α⁺ ↦ ★
```

while both the surface name relation `X ⊑ β` and the direct boundary
relation `X ⊑ α⁺` are derivable.  The probe packages the corresponding
paired reveal indices with the exact source and target conversions.

This focus is intentionally not another inhabitant of `_⊑ᶜ_`: it does not
weaken `representationsImprecise`, and ordinary CTI constructors must not be
able to use it outside the matching boundary.  The eventual CTI redesign
therefore needs a premise-only boundary judgment (or an equivalent pending
boundary index) that is introduced and consumed by the exact reveal/conceal
wrapper.  Nested aliases are repeated one-edge boundaries, never a transitive
focus.  The checked mode probe makes this repetition explicit:

```agda
data TargetModeᶠ₁ : Set where
  stable-modeᶠ₁ : TargetModeᶠ₁
  push-focusᶠ₁ : TargetModeᶠ₁ → TyVar Δᴿ → TargetModeᶠ₁
```

The stable mode cannot view the fresh pending `β`.  Crossing the `α := ★`
boundary first pushes an `α` focus; crossing `β := α` then pushes a `β` focus
whose direct representation is checked in the `α` parent mode.  The resulting
mode has depth two and is provably not a single push.  Ordinary variable,
lambda, and application clauses preserve their mode.  Only exact
direct-store-certified target reveal/conceal clauses cross modes.  Thus the
nested target term

```text
((x ↑ unseal β α) ↑ unseal α ★)
```

returns to the stable mode without exposing either pending name to ordinary
term rules.  The typed boundary probe checks the corresponding intermediate
judgments explicitly: `X ⊑ β` at depth two, `X ⊑ α` after the inner reveal,
and `X ⊑ ★` after the outer reveal.  Its atom, lambda, and application clauses
preserve the identical mode and validity witness.  This is not yet a
replacement for live CTI, but it shows that a stack is part of the
compositional interface rather than Λ-specific proof geometry.

## CTI indexing consequence

The CTI judgment loses its separate `CtxImp` argument:

```agda
infix 4 _⊢²_⊑_∶_

data _⊢²_⊑_∶_ {Cᴸ Cᴿ} (W : Cᴸ ⊑ᶜ Cᴿ) :
    Term (Δᵉ Cᴸ) → Term (Δᵉ Cᴿ)
    → {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ Cᴿ)}
    → A ⊑ᵀ⟨ W ⟩ B → Set
```

Representative clauses become:

```agda
x⊑x² : ∀ {x A B} {p : A ⊑ᵀ⟨ W ⟩ B}
  → W ∋ᶜ x ⦂ p
  → W ⊢² ` x ⊑ ` x ∶ p

ƛ⊑ƛ² : ∀ {M M′ A A′ B B′}
    {pA : A ⊑ᵀ⟨ W ⟩ A′} {pB : B ⊑ᵀ⟨ W ⟩ B′}
  → bind-termᶜ W pA ⊢² M ⊑ M′ ∶ pB
  → W ⊢² ƛ M ⊑ ƛ M′ ∶ ⇒⊑⇒ pA pB

Λ⊑Λ² : ∀ {V V′ A B}
    {p : A ⊑ᵀ⟨ liftBothᶜ X⊑X W ⟩ B}
  → Value V
  → Value V′
  → liftBothᶜ X⊑X W ⊢² V ⊑ V′ ∶ p
  → (q : `∀ A ⊑ᵀ⟨ W ⟩ `∀ B)
  → W ⊢² Λ V ⊑ Λ V′ ∶ q

Λ⊑² : ∀ {V M A B}
    {p : A ⊑ᵀ⟨ liftLeftᶜ W ⟩ B}
  → NonVar A
  → Fin.zero ∈ᵗ A
  → Value V
  → Cᴿ ⊢ M ⦂ B
  → liftLeftᶜ W ⊢² V ⊑ M ∶ p
  → (q : `∀ A ⊑ᵀ⟨ W ⟩ B)
  → W ⊢² Λ V ⊑ M ∶ q

blame⊑² : ∀ {M′ A B}
  → Cᴿ ⊢ M′ ⦂ B
  → (p : A ⊑ᵀ⟨ W ⟩ B)
  → W ⊢² blame ⊑ M′ ∶ p
```

For a reveal or conceal premise, `W′` has type `Cᴸ ⊑ᶜ Cᴿ` just like
`W`.  This removes `SameCtx` and `SameRuntime`: equality of both stores and both
term contexts follows from the endpoint indices.  Conversion typing reads
`Σᵉ Cᴸ` or `Σᵉ Cᴿ` directly.

These CTI clauses are **proposed statements only**.  Any live edit still
requires the separate permission process for `CastTermImprecision.agda`.

## Intended deletions

After the migration is complete, delete rather than alias:

- `CtxImpEntry`, `CtxImp`, `srcCtxʷ`, `tgtCtxʷ`, and `_∋ʷ_⦂_`;
- `SameCtx`, `LiftCtx`, `LiftCtxᴸ`, and `SmartLiftCtxᴸ`;
- `SameRuntime`, whose equalities move into the endpoint indices;
- the three-index `World` public surface and its store/context projections;
- `honestifyʷ`, `lower-leftʷ`, `mix-targetʷ`, and `mix-renamed-targetʷ` as
  core constructors;
- `resolveVar`, `resolveRep`, `StoreRepImp`, and any authorization derived from
  transitive representation resolution;
- temporary conversion bridges once all live consumers use `_⊑ᶜ_`.

`RightBindFreshᶜ` remains only as the local guard for constructing an
unmatched target cell.  It must not be fabricated for arbitrary trusted
reductions.  Backward simulation may stop at source blame instead of extending
the world, as the current SimBack result surface now permits.

## Migration order

1. Add `_⊑ᶜ_`, its hidden-center projections, direct invariants, and smart
   functions beside the old relation.  Do not add compatibility re-exports.
2. Rework fixtures as direct proofs of the full-context relation.  Do not remove
   a fixture.
3. Prove direct-entry invariants, type imprecision, center renaming, checked
   rebase, boundary-local alias focus, and world evolution.
4. Add term-entry lookup and prove that relation endpoints supply ordinary
   source and target typing contexts.
5. After explicit user permission, migrate the CTI judgment and its variable,
   lambda, polymorphic, blame, reveal, and conceal clauses as one coherent
   boundary.
6. Migrate compilation preservation and CTI typing, then parked evolution,
   `Sim`/`SimBack`, inversion, source/target stripping, and catch-up.
7. Delete the old world/context representation, temporary bridges, and
   resolved-representation scaffolding.

The highest-impact consumers are `CastTermImprecision.agda`,
`CastTermImprecision2Typing.agda`, `CompilePreservesImprecision2.agda`,
`CenterRename.agda`, `TargetExtend.agda`, `TargetBindLift.agda`,
`Parked/ParkedWorldDef.agda`, `SimProof.agda`, `SimBackProof.agda`, the
target-strip proofs, and the instantiation catch-up and inversion family.

## Open proof obligations

Before this becomes a live design, the remaining probes must establish:

- The checked `TwoCtxWorldInvariantsProbe` establishes that the inductive
  constructors imply all four direct invariants without a general
  invariant-accepting escape constructor.
- Checked source rebase is implemented as a function over an explicit plan.
  Its graph preserves the hidden center and freezes every target embedding.
  The identity and moving base cases and recursion through every raw skeleton
  constructor check.  A separate producer theorem must still show when a
  requested operational pivot move admits such a plan.
- Direct store-entry imprecision is sufficient for every valid reveal and
  conceal square; no proof relies essentially on `resolveVar`.
- The checked boundary-mode stack must be integrated into reveal/conceal CTI
  without making pending names available to ordinary term constructors.
- Store-changing simulation can index evolved endpoint `Ctx` values without
  placing `apply` functions in data-constructor indices.
