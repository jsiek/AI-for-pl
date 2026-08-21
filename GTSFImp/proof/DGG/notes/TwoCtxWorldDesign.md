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

Everything below is **schematic and unproved**.  In particular, the raw
constructors have not been accepted by Agda, the smart functions have not been
implemented, and no preservation theorem has been proved.  This note does not
authorize a change to the live term-imprecision relation.

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

`SourceRebasePlan` must describe local movement in the inductive history; its
constructors remain an open design question.  The crucial requirement is that
`rebaseSource-center` close by `refl`.  A fallback record with an explicit
`centerᶜ W ≡ centerᶜ W′` field is possible, but is expected to create
unnecessary transport obligations.  Both alternatives are **schematic and
unproved**; the function graph should be probed before choosing.

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
   rebase, and world evolution.
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
source/target strip proofs, and the instantiation catch-up and inversion family.

## Open proof obligations

Before this becomes a live design, probes must establish:

- Agda accepts the mutual raw relation and hidden-center projections as
  strictly positive and terminating.
- Every smart operation computes to the expected `CastTerms.Ctx` endpoints.
- The inductive constructors imply the four direct world invariants without a
  general invariant-accepting escape constructor.
- Checked source rebase can be implemented as a function whose graph preserves
  the hidden center and freezes every target embedding.
- Direct store-entry imprecision is sufficient for every valid reveal and
  conceal square; no proof relies essentially on `resolveVar`.
- Store-changing simulation can index evolved endpoint `Ctx` values without
  placing `apply` functions in data-constructor indices.
