# CTI permission packet: anchored crossing frames carried by `γ`

Status: permission request only.  This packet does **not** edit
`proof/DGG/CastTermImprecision.agda`.

## Requested change

Keep the CTI judgment singly indexed,

```agda
γ ⊢² M ⊑ M′ ∶ p
```

but redefine the public relation `_⊑ᶜ_` so that `γ : Γᴸ ⊑ᶜ Γᴿ` carries one
ambient allocation world and a well-bracketed stack of local reveal/conceal
frames.  The superscript `ᵃ` used in an earlier draft meant only "anchored";
it is not a proposed public name.  Replace the ten current reveal/conceal
constructors by six syntax-directed constructors:

- source reveal pushes a source frame;
- target reveal pushes a target frame;
- paired reveal pushes a paired frame;
- source conceal pops the exact source frame;
- target conceal pops the exact target frame;
- paired conceal pops the exact paired frame.

No application, primitive, cast, type-application, lambda, or type-lambda rule
may choose a new world.  Each such constructor gives all immediate children
the same `γ` as its conclusion.  Ambient runtime allocation transports the
entire enriched `γ`; it never pushes or pops a crossing frame.

This supersedes both the historical `OpenFrames`-as-a-second-index design and
the non-syntax-directed `alignment-scope²` proposal.

## Why the live relation must change

The present CTI stores a rebase in the ordinary world.  Consequently, a rebase
needed only inside the reducing child of an application also changes the world
expected by its untouched sibling.  The compiled duplicated-operand example
in `CompiledSiblingFootprintSeparationProbe.agda` reaches exactly that state,
and the sibling cannot be transported through the reducing child's rebase.

Moving the rebase to ordinary application or primitive rules would make CTI
too permissive: unrelated siblings could select conflicting alignments.
Wrapping arbitrary subderivations in `alignment-scope²` avoids that global
effect, but is not syntax directed.

Anchored crossings are the smallest syntax-directed boundary that persists
through the relevant reductions.  Arrow reveal reduction preserves the
parent's full crossing mark on both generated crossings:

```text
((V ↑[X:R] (c ↦↑ d)) · W)
  —→
((V · (W ↓[X:R] c)) ↑[X:R] d)
```

Thus the residual `id↑ ★` does not need an anchor in the conversion.  Its
enclosing reveal occurrence still has the parent's `(X,R)` mark.

## The ambient allocation world

The current `_⊑ᶜ_` datatype mixes four concerns:

1. type-store allocation geometry;
2. term-context imprecision;
3. source pivot rebasing;
4. reveal/conceal balance encoded in rebase history.

The new `AmbientWorldᶜ` is the first concern only.  It relates endpoint type
stores, not complete term contexts:

```agda
record StoreCtx : Set where
  constructor ⟨_,_⟩ˢ
  field
    Δˢ : TyCtx
    Σˢ : TyStore Δˢ

mutual
  data AmbientWorldᶜ : StoreCtx → StoreCtx → Set where
    emptyᵃᶜ :
      AmbientWorldᶜ ⟨ zero , store-empty ⟩ˢ
                     ⟨ zero , store-empty ⟩ˢ

    _▻ᵃᶜ_ : ∀ {Sᴸ Sᴿ Sᴸ′ Sᴿ′}
      → (W : AmbientWorldᶜ Sᴸ Sᴿ)
      → AmbientChangeᶜ W Sᴸ′ Sᴿ′
      → AmbientWorldᶜ Sᴸ′ Sᴿ′

  centerᵃᶜ : AmbientWorldᶜ Sᴸ Sᴿ → TyCtx

  ηᴸᵃᶜ : (W : AmbientWorldᶜ Sᴸ Sᴿ)
    → Injectionᵗ (Δˢ Sᴸ) (centerᵃᶜ W)

  ηᴿᵃᶜ : (W : AmbientWorldᶜ Sᴸ Sᴿ)
    → Injectionᵗ (Δˢ Sᴿ) (centerᵃᶜ W)

  marksᵃᶜ : (W : AmbientWorldᶜ Sᴸ Sᴿ)
    → ImpEnv (centerᵃᶜ W)
```

For `W : AmbientWorldᶜ ⟨ Δᴸ , Σᴸ ⟩ˢ ⟨ Δᴿ , Σᴿ ⟩ˢ`, its complete geometric
change family is:

```agda
data AmbientChangeᶜ : ∀ {Sᴸ Sᴿ}
    → AmbientWorldᶜ Sᴸ Sᴿ → StoreCtx → StoreCtx → Set where

  center-changeᵃᶜ :
    AmbientChangeᶜ W
      ⟨ Δᴸ , Σᴸ ⟩ˢ
      ⟨ Δᴿ , Σᴿ ⟩ˢ

  lift-both-changeᵃᶜ :
    (v : VarImp)
    → AmbientChangeᶜ W
        ⟨ suc Δᴸ , store-lift Σᴸ ⟩ˢ
        ⟨ suc Δᴿ , store-lift Σᴿ ⟩ˢ

  lift-left-changeᵃᶜ :
    AmbientChangeᶜ W
      ⟨ suc Δᴸ , store-lift Σᴸ ⟩ˢ
      ⟨ Δᴿ , Σᴿ ⟩ˢ

  bind-left-changeᵃᶜ :
    (A : Ty Δᴸ)
    → AmbientChangeᶜ W
        ⟨ suc Δᴸ , store-bind Σᴸ A ⟩ˢ
        ⟨ Δᴿ , Σᴿ ⟩ˢ

  bind-right-changeᵃᶜ :
    (B : Ty Δᴿ)
    → AmbientChangeᶜ W
        ⟨ Δᴸ , Σᴸ ⟩ˢ
        ⟨ suc Δᴿ , store-bind Σᴿ B ⟩ˢ

  bind-both-changeᵃᶜ :
    (A : Ty Δᴸ) (B : Ty Δᴿ)
    → AmbientChangeᶜ W
        ⟨ suc Δᴸ , store-bind Σᴸ A ⟩ˢ
        ⟨ suc Δᴿ , store-bind Σᴿ B ⟩ˢ

  bind-both-star-changeᵃᶜ :
    (A : Ty Δᴸ) (B : Ty Δᴿ)
    → ⇑ᵗ A ≢ ★
    → AmbientChangeᶜ W
        ⟨ suc Δᴸ , store-bind Σᴸ A ⟩ˢ
        ⟨ suc Δᴿ , store-bind Σᴿ B ⟩ˢ
```

The derived center data changes as follows:

| ambient change | new mark | new source embedding | new target embedding |
|---|---|---|---|
| `center-changeᵃᶜ` | `X⊑★` | `skipⁱ` | `skipⁱ` |
| `lift-both-changeᵃᶜ v` | `v` | `keepⁱ` | `keepⁱ` |
| `lift-left-changeᵃᶜ` | `X⊑★` | `keepⁱ` | `skipⁱ` |
| `bind-left-changeᵃᶜ A` | `X⊑★` | `keepⁱ` | `skipⁱ` |
| `bind-right-changeᵃᶜ B` | `X⊑★` | `skipⁱ` | `keepⁱ` |
| `bind-both-changeᵃᶜ A B` | `X⊑X` | `keepⁱ` | `keepⁱ` |
| `bind-both-star-changeᵃᶜ A B A≢★` | `X⊑★` | `keepⁱ` | `keepⁱ` |

There is deliberately no ambient term-bind constructor and no ambient rebase
constructor.  Consequently `ηᴸᵃᶜ W` and `ηᴿᵃᶜ W` describe allocation
geometry only.  A frame may derive a different current source view, but it
does not mutate `W`.

The current constructors are factored as follows:

| current `_⊑ᶜ_` component | new formulation |
|---|---|
| `emptyᶜ` and `_▻ᶜ_` | `emptyᵃᶜ` and `_▻ᵃᶜ_` inside `AmbientWorldᶜ` |
| `center-changeᶜ` | `center-changeᵃᶜ` |
| `lift-both-changeᶜ` | `lift-both-changeᵃᶜ` |
| `lift-left-changeᶜ` | `lift-left-changeᵃᶜ` |
| `bind-left-changeᶜ` | `bind-left-changeᵃᶜ` plus an enriched-world safety proof |
| `bind-right-changeᶜ` | `bind-right-changeᵃᶜ` plus current-view freshness |
| `bind-both-changeᶜ` | `bind-both-changeᵃᶜ` plus a current-view allocation certificate |
| `bind-both-star-changeᶜ` | `bind-both-star-changeᵃᶜ` plus a current-view allocation certificate |
| `bind-term-changeᶜ` | `term-contextᶜ` in the enriched public world |
| `rebase-source-changeᶜ` | the checked action of an anchored frame |
| `AlignmentBoundaryᶜ`, `SourceRebaseRoleᶜ`, `openFramesᶜ` | replaced by exact frame keys and `FrameStackᶜ` |

The old public datatype is deleted after migration; it is not retained as a
compatibility alias.  Its allocation spine is the implementation basis for
`AmbientWorldᶜ`, while the canonical public name `_⊑ᶜ_` is reused for the
enriched relation below.

### Allocation evidence is checked at the current view

The semantic premises of the current bind constructors cannot simply be
copied into `AmbientChangeᶜ`.  In particular, this current premise is wrong
for a paired allocation under active frames:

```agda
A ⊑ᵀ⟨ ambientᶜ γ ⟩ B
```

The required premise is:

```agda
A ⊑ᵀ⟨ γ ⟩ B
```

For the concrete alpha scope, `＇X ⊑ ＇Y′` holds in the current alpha view but
is refuted in the ambient view.  Therefore paired allocation is an operation
on the complete enriched world:

```agda
bindBothᶜ :
    (γ : Γᴸ ⊑ᶜ Γᴿ)
  → A ⊑ᵀ⟨ γ ⟩ B
  → (Γᴸ ,ˢ A) ⊑ᶜ (Γᴿ ,ˢ B)
```

It performs five operations together:

1. append `bind-both-changeᵃᶜ A B` to `ambientᶜ γ`;
2. record the representation comparison with the pre-bind
   `source-viewᶜ γ` as its creation view;
3. transport every active frame through the bind;
4. rename `term-contextᶜ` through the bind;
5. re-establish the complete invariant package.

`bindBothStarᶜ` has the analogous current-view premise and additionally
records `⇑ᵗ A ≢ ★`.  `bindRightᶜ` checks freshness against the current view
and every active protected target footprint, rather than only against the
ambient source embedding.  The raw ambient constructors are implementation
details; a valid public `_⊑ᶜ_` can be extended only by these checked enriched
operations.

Each allocation certificate remains tied to the source view at which it was
created.  A later frame may redirect the current source pivot without
retroactively changing an older store-representation obligation.  Ambient
evolution transports these recorded views and their proofs through later
binds.

## The enriched `γ`

The following is the proposed semantic public shape.  Names may be adjusted
to local conventions during implementation, but none of the listed evidence
may be omitted.

```agda
record CrossingMark (Δ : TyCtx) : Set where
  constructor mark
  field
    anchor         : TyVar Δ
    representation : Ty Δ

data FrameKey (Δᴸ Δᴿ : TyCtx) : Set where
  source-frame : CrossingMark Δᴸ
    → FrameKey Δᴸ Δᴿ
  target-frame : CrossingMark Δᴿ
    → FrameKey Δᴸ Δᴿ
  paired-frame : CrossingMark Δᴸ → CrossingMark Δᴿ
    → FrameKey Δᴸ Δᴿ

record AnchoredFrameᶜ ... : Set where
  field
    keyᶜ                    : FrameKey Δᴸ Δᴿ
    source-view-beforeᶜ     : Injectionᵗ Δᴸ center
    source-view-afterᶜ      : Injectionᵗ Δᴸ center
    actionᶜ                 : KeepOrCheckedRebase ...
    endpoint-marks-exactᶜ   : ...
    representation-at-viewᶜ : ...
    occupancy-safeᶜ         : ...

data FrameStackᶜ (ambient : AmbientWorldᶜ Sᴸ Sᴿ) :
    Injectionᵗ (Δˢ Sᴸ) (centerᵃᶜ ambient) → Set where
  []ᶠ : FrameStackᶜ ambient (ηᴸᵃᶜ ambient)
  _∷ᶠ_ : ∀ {before}
    → FrameStackᶜ ambient before
    → (frame : AnchoredFrameᶜ ambient before)
    → FrameStackᶜ ambient (source-view-afterᶜ frame)

record _⊑ᶜ_ (Γᴸ Γᴿ : Ctx) : Set where
  field
    ambientᶜ       : AmbientWorldᶜ
                       ⟨ Δᵉ Γᴸ , Σᵉ Γᴸ ⟩ˢ
                       ⟨ Δᵉ Γᴿ , Σᵉ Γᴿ ⟩ˢ
    source-viewᶜ   : Injectionᵗ (Δᵉ Γᴸ) (centerᵃᶜ ambientᶜ)
    framesᶜ        : FrameStackᶜ ambientᶜ source-viewᶜ
    term-contextᶜ  : ScopedTermContextᶜ ambientᶜ source-viewᶜ
                       (Γᵉ Γᴸ) (Γᵉ Γᴿ)
    invariantsᶜ    : AnchoredWorldInvariantsᶜ
                       ambientᶜ source-viewᶜ framesᶜ
```

`term-contextᶜ` is only the ordinary typing-context relation interpreted in
the current source view.  It is not a term context, AST path, evaluation
context, free-variable footprint, or atlas of alternative worlds stored in
`γ`.

Type imprecision reads the current source view and the ambient target view:

```agda
A ⊑ᵀ⟨ γ ⟩ B =
  marksᵃᶜ (ambientᶜ γ) ⊢
    renameᵗ (toRenameⁱ (source-viewᶜ γ)) A
      ⊑ renameᵗ (toRenameⁱ (ηᴿᵃᶜ (ambientᶜ γ))) B
```

The invariant package contains:

1. allocation certificates, each paired with the source view at which its
   representation or freshness obligation was established;
2. the direct allocation invariants of the ambient geometry;
3. precise-mark alignment in the current view;
4. admissibility of unmatched targets, accounting for targets protected by
   active frames;
5. unoccupancy of a source whose direct entry is `★` at an `X⊑★` center;
6. every frame's representation evidence at the view where it was created.

The checked push operations are deterministic partial functions:

```agda
push-sourceᶜ : ... → γ → CrossingMark (Δᵉ Γᴸ)
  → GeneratorPosition → Maybe (Γᴸ ⊑ᶜ Γᴿ)

push-targetᶜ : ... → γ → CrossingMark (Δᵉ Γᴿ)
  → GeneratorPosition → Maybe (Γᴸ ⊑ᶜ Γᴿ)

push-pairedᶜ : ... → γ
  → CrossingMark (Δᵉ Γᴸ) → CrossingMark (Δᵉ Γᴿ)
  → GeneratorPosition → GeneratorPosition
  → Maybe (Γᴸ ⊑ᶜ Γᴿ)
```

They implement these fixed choices:

- a source-only frame keeps the source view; an active crossing must satisfy
  the present `X⊑★`, target-unoccupied, and `Rᴸ ⊑ ★` checks;
- a paired frame uses its source anchor and target anchor, keeping the view if
  they are already aligned and otherwise performing the unique checked pivot
  update;
- a target-only frame may rebase only the unique source owner determined by
  the target's **full** `(anchor, representation)` mark in the current view;
  if there is no owner, only a generator-absent keep-view frame is permitted;
- every result appends the exact key to the LIFO stack and re-establishes the
  invariant package.

In particular, `push-targetᶜ` does not receive a freely chosen source pivot.
Implementation is gated on proofs that all three push functions are
functional and commute with every ambient allocation transport used by
simulation.

## Complete live crossing rules: before

These are all ten current reveal/conceal constructors, copied in full from
`CastTermImprecision.agda`.

```agda
  ⊑reveal-identity : ∀ {M M′ A B B′ Xᴿ Rᴿ}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
      {c′ : Conv↑ (Δᵉ Γᴿ) B B′}
    → (c′⊢ : Σᵉ Γᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
    → revealGeneratorPosition c′⊢ ≡ generator-absent
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ γ ⟩ B′)
      ---------------------
    → γ ⊢² M ⊑ M′ ↑ c′ ∶ q

  ⊑conceal-identity : ∀ {M M′ A B B′ Xᴿ Rᴿ}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
      {c′ : Conv↓ (Δᵉ Γᴿ) B B′}
    → (c′⊢ : Σᵉ Γᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
    → concealGeneratorPosition c′⊢ ≡ generator-absent
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ γ ⟩ B′)
      ---------------------
    → γ ⊢² M ⊑ M′ ↓ c′ ∶ q

  reveal⊑-identity : ∀ {M M′ A A′ B Xᴸ Rᴸ}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
      {c : Conv↑ (Δᵉ Γᴸ) A A′}
    → (c⊢ : Σᵉ Γᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
    → revealGeneratorPosition c⊢ ≡ generator-absent
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ γ ⟩ B)
      ---------------------
    → γ ⊢² M ↑ c ⊑ M′ ∶ q

  reveal⊑-only² : ∀ {M M′ A A′ B Xᴸ Rᴸ}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
      {c : Conv↑ (Δᵉ Γᴸ) A A′}
    → (c⊢ : Σᵉ Γᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
    → revealGeneratorPosition c⊢ ≢ generator-absent
    → marksᶜ γ (toRenameⁱ (ηᴸᶜ γ) Xᴸ) ≡ X⊑★
    → (∀ Xᴿ → toRenameⁱ (ηᴿᶜ γ) Xᴿ
        ≢ toRenameⁱ (ηᴸᶜ γ) Xᴸ)
    → Rᴸ ⊑ᵀ⟨ γ ⟩ ★
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ γ ⟩ B)
      ---------------------
    → γ ⊢² M ↑ c ⊑ M′ ∶ q

  conceal⊑-identity : ∀ {M M′ A A′ B Xᴸ Rᴸ}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
      {c : Conv↓ (Δᵉ Γᴸ) A A′}
    → (c⊢ : Σᵉ Γᴸ ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
    → concealGeneratorPosition c⊢ ≡ generator-absent
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ γ ⟩ B)
      ---------------------
    → γ ⊢² M ↓ c ⊑ M′ ∶ q

  conceal⊑-only² : ∀ {M M′ A A′ B Xᴸ Rᴸ}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
      {c : Conv↓ (Δᵉ Γᴸ) A A′}
    → (c⊢ : Σᵉ Γᴸ ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
    → concealGeneratorPosition c⊢ ≢ generator-absent
    → marksᶜ γ (toRenameⁱ (ηᴸᶜ γ) Xᴸ) ≡ X⊑★
    → (∀ Xᴿ → toRenameⁱ (ηᴿᶜ γ) Xᴿ
        ≢ toRenameⁱ (ηᴸᶜ γ) Xᴸ)
    → Rᴸ ⊑ᵀ⟨ γ ⟩ ★
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ γ ⟩ B)
      ---------------------
    → γ ⊢² M ↓ c ⊑ M′ ∶ q

  reveal⊑reveal² : ∀ {M M′ A A′ B B′ Xᴸ Xᴿ Rᴸ Rᴿ}
      {c : Conv↑ (Δᵉ Γᴸ) A B}
      {c′ : Conv↑ (Δᵉ Γᴿ) A′ B′}
    → (c⊢ : Σᵉ Γᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
    → (c′⊢ : Σᵉ Γᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
    → revealGeneratorPosition c⊢ ≡ revealGeneratorPosition c′⊢
    → toRenameⁱ (ηᴸᶜ γ) Xᴸ ≡ toRenameⁱ (ηᴿᶜ γ) Xᴿ
    → Rᴸ ⊑ᵀ⟨ γ ⟩ Rᴿ
    → {p : A ⊑ᵀ⟨ γ ⟩ A′}
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : B ⊑ᵀ⟨ γ ⟩ B′)
      ------------------------------
    → γ ⊢² M ↑ c ⊑ M′ ↑ c′ ∶ q

  conceal⊑conceal² : ∀
      {M M′ A A′ B B′ Xᴸ Xᴿ Rᴸ Rᴿ}
      {p : A ⊑ᵀ⟨ γ ⟩ A′}
      {c : Conv↓ (Δᵉ Γᴸ) A B}
      {c′ : Conv↓ (Δᵉ Γᴿ) A′ B′}
    → (c⊢ : Σᵉ Γᴸ ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
    → (c′⊢ : Σᵉ Γᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
    → concealGeneratorPosition c⊢ ≡ concealGeneratorPosition c′⊢
    → toRenameⁱ (ηᴸᶜ γ) Xᴸ ≡ toRenameⁱ (ηᴿᶜ γ) Xᴿ
    → Rᴸ ⊑ᵀ⟨ γ ⟩ Rᴿ
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : B ⊑ᵀ⟨ γ ⟩ B′)
      ------------------------------
    → γ ⊢² M ↓ c ⊑ M′ ↓ c′ ∶ q

  ⊑reveal-rebase² : ∀
      {γᵖ : Γᴸ ⊑ᶜ Γᴿ}
      {M M′ A B B′ Xᴸ Xᴿ Rᴿ}
      {c′ : Conv↑ (Δᵉ Γᴿ) B B′}
    → (c′⊢ : Σᵉ Γᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
    → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
    → {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
    → γᵖ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ γ ⟩ B′)
      ---------------------
    → γ ⊢² M ⊑ M′ ↑ c′ ∶ q

  ⊑conceal-rebase² : ∀
      {γᵖ : Γᴸ ⊑ᶜ Γᴿ}
      {M M′ A B B′ Xᴸ Xᴿ Rᴿ}
      {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
      {c′ : Conv↓ (Δᵉ Γᴿ) B B′}
    → (c′⊢ : Σᵉ Γᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
    → SourceRebaseᶜ γᵖ γ Xᴸ Xᴿ
    → γᵖ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ γ ⟩ B′)
      ---------------------
    → γ ⊢² M ⊑ M′ ↓ c′ ∶ q
```

## Complete proposed crossing rules: after

`reveal-mark c⊢` and `conceal-mark c⊢` are the full `(anchor,
representation)` marks obtained from the anchored term occurrence's typing.
The push equalities both validate the boundary and determine `γ⁺`.  A conceal
can therefore produce `γ⁺` only when its exact key is the new top frame of
`γ`; read outside-in, this is a pop.

```agda
  reveal⊑-push² : ∀ {γ⁺ M M′ A A′ B Xᴸ Rᴸ}
      {c : Conv↑ (Δᵉ Γᴸ) A A′}
    → (c⊢ : Σᵉ Γᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
    → push-sourceᶜ γ (reveal-mark c⊢)
        (revealGeneratorPosition c⊢) ≡ just γ⁺
    → {p : A ⊑ᵀ⟨ γ⁺ ⟩ B}
    → γ⁺ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ γ ⟩ B)
      ---------------------
    → γ ⊢² M ↑ c ⊑ M′ ∶ q

  ⊑reveal-push² : ∀ {γ⁺ M M′ A B B′ Xᴿ Rᴿ}
      {c′ : Conv↑ (Δᵉ Γᴿ) B B′}
    → (c′⊢ : Σᵉ Γᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
    → push-targetᶜ γ (reveal-mark c′⊢)
        (revealGeneratorPosition c′⊢) ≡ just γ⁺
    → {p : A ⊑ᵀ⟨ γ⁺ ⟩ B}
    → γ⁺ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ γ ⟩ B′)
      ---------------------
    → γ ⊢² M ⊑ M′ ↑ c′ ∶ q

  reveal⊑reveal-push² : ∀
      {γ⁺ M M′ A A′ B B′ Xᴸ Xᴿ Rᴸ Rᴿ}
      {c : Conv↑ (Δᵉ Γᴸ) A B}
      {c′ : Conv↑ (Δᵉ Γᴿ) A′ B′}
    → (c⊢ : Σᵉ Γᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
    → (c′⊢ : Σᵉ Γᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
    → revealGeneratorPosition c⊢ ≡ revealGeneratorPosition c′⊢
    → push-pairedᶜ γ (reveal-mark c⊢) (reveal-mark c′⊢)
        (revealGeneratorPosition c⊢)
        (revealGeneratorPosition c′⊢) ≡ just γ⁺
    → Rᴸ ⊑ᵀ⟨ γ⁺ ⟩ Rᴿ
    → {p : A ⊑ᵀ⟨ γ⁺ ⟩ A′}
    → γ⁺ ⊢² M ⊑ M′ ∶ p
    → (q : B ⊑ᵀ⟨ γ ⟩ B′)
      ------------------------------
    → γ ⊢² M ↑ c ⊑ M′ ↑ c′ ∶ q

  conceal⊑-pop² : ∀ {γ⁺ M M′ A A′ B Xᴸ Rᴸ}
      {c : Conv↓ (Δᵉ Γᴸ) A A′}
    → (c⊢ : Σᵉ Γᴸ ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
    → push-sourceᶜ γ (conceal-mark c⊢)
        (concealGeneratorPosition c⊢) ≡ just γ⁺
    → {p : A ⊑ᵀ⟨ γ ⟩ B}
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ γ⁺ ⟩ B)
      ---------------------
    → γ⁺ ⊢² M ↓ c ⊑ M′ ∶ q

  ⊑conceal-pop² : ∀ {γ⁺ M M′ A B B′ Xᴿ Rᴿ}
      {c′ : Conv↓ (Δᵉ Γᴿ) B B′}
    → (c′⊢ : Σᵉ Γᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
    → push-targetᶜ γ (conceal-mark c′⊢)
        (concealGeneratorPosition c′⊢) ≡ just γ⁺
    → {p : A ⊑ᵀ⟨ γ ⟩ B}
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ γ⁺ ⟩ B′)
      ---------------------
    → γ⁺ ⊢² M ⊑ M′ ↓ c′ ∶ q

  conceal⊑conceal-pop² : ∀
      {γ⁺ M M′ A A′ B B′ Xᴸ Xᴿ Rᴸ Rᴿ}
      {c : Conv↓ (Δᵉ Γᴸ) A B}
      {c′ : Conv↓ (Δᵉ Γᴿ) A′ B′}
    → (c⊢ : Σᵉ Γᴸ ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
    → (c′⊢ : Σᵉ Γᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
    → concealGeneratorPosition c⊢ ≡ concealGeneratorPosition c′⊢
    → push-pairedᶜ γ (conceal-mark c⊢) (conceal-mark c′⊢)
        (concealGeneratorPosition c⊢)
        (concealGeneratorPosition c′⊢) ≡ just γ⁺
    → Rᴸ ⊑ᵀ⟨ γ⁺ ⟩ Rᴿ
    → {p : A ⊑ᵀ⟨ γ ⟩ A′}
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : B ⊑ᵀ⟨ γ⁺ ⟩ B′)
      ------------------------------
    → γ⁺ ⊢² M ↓ c ⊑ M′ ↓ c′ ∶ q
```

The ordinary application rule keeps its shape:

```agda
  ·⊑·² : ∀ {L L′ M M′ A A′ B B′}
      {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
    → γ ⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB
    → γ ⊢² M ⊑ M′ ∶ pA
      -----------------------------
    → γ ⊢² L · M ⊑ L′ · M′ ∶ pB
```

This is the compositionality point: a child's reveal may push a frame for its
own premise, but the frame does not change the `γ` at the sibling conclusion.

## Normalized checkpoint 6-to-7 reduction square

The expository notation `↑[X:R] c` and `↓[X:R] c` displays the mark on the
reveal/conceal occurrence; `X` is not a field of `c`.  All binders and free
type variables are named.

```text
M₆ =
  (λx:ℕ. x) ·
    (((
      ((λx:X. (λy:★. y) · (x ⟨ X↦★ ⟩))
        ↑[X:ℕ] (seal X ℕ ↦↑ id↑ ★))
      · 42)
      ⟨ ★↦★ ⟩)
      ⟨ ★↦ℕ ⟩)

N₆ =
  (λx:ℕ. x) ·
    (((
      (((λx:X′. (λy:★. y) · (x ⟨ X′↦★ ⟩))
          ↑[X′:Y′] (seal X′ Y′ ↦↑ id↑ ★))
        ↑[Y′:★] (seal Y′ ★ ↦↑ id↑ ★))
      · (42 ⟨ ℕ↦★ ⟩))
      ⟨ ★↦★ ⟩)
      ⟨ ★↦ℕ ⟩)

M₇ =
  (λx:ℕ. x) ·
    (((
      (((λx:X. (λy:★. y) · (x ⟨ X↦★ ⟩))
        · (42 ↓[X:ℕ] seal X ℕ))
        ↑[X:ℕ] id↑ ★))
      ⟨ ★↦★ ⟩)
      ⟨ ★↦ℕ ⟩)

N₇ =
  (λx:ℕ. x) ·
    (((
      ((((λx:X′. (λy:★. y) · (x ⟨ X′↦★ ⟩))
          ↑[X′:Y′] (seal X′ Y′ ↦↑ id↑ ★))
        · ((42 ⟨ ℕ↦★ ⟩) ↓[Y′:★] seal Y′ ★))
        ↑[Y′:★] id↑ ★))
      ⟨ ★↦★ ⟩)
      ⟨ ★↦ℕ ⟩)
```

Diagram:

    M₆  ⊑[γ₀]  N₆
    │             │
    │ β-reveal-⇒  │ β-reveal-⇒
    │ lifted      │ lifted
    ▼             ▼
    M₇  ⊑[γ₀]  N₇

Both vertical edges are checked whole-term `keep` steps.  On the source,
`β-reveal-⇒` uses the values `λx:X. ...` and `42`.  On the target, it uses the
value `(λx:X′. ...) ↑[X′:Y′] (seal X′ Y′ ↦↑ id↑ ★)` and the value
`42 ⟨ ℕ↦★ ⟩`.  The reduction produces the displayed marked conceal and
residual reveal on each side; no allocation occurs on this step.

The strings without type annotations are computed by
`CTIGammaCarriedFramePacket.checkpoint₆-source-term`,
`checkpoint₆-target-term`, `checkpoint₇-source-term`, and
`checkpoint₇-target-term` using the repository's name-aware `showTerm`.

## Alignments and scopes at each location

These three snapshots are generated by `WorldSnapshot.worldSnapshot` from the
ambient world and the two existing live worlds whose source injections equal
the proposed current views.

    γ₀  stack []
        ⟨X: X↦ℕ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩
          ╲ push paired α; rebase@X; mark (X,ℕ) ↔ (Y′,★)
            γα  stack [α]
                ⟨X: ─ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: X↦ℕ ⊑[X⊑★] Y′↦★⟩
                  ╲ push target β; rebase@X; mark (X′,Y′), owner (X,ℕ)
                    γαβ  stack [β, α]
                         ⟨X: ─ ⊑[X⊑★] ─ │ Y: X↦ℕ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩

The direct alignments are therefore:

| location | stack | source `X` aligned with | target `Y′` aligned with | target `X′` aligned with |
|---|---|---|---|---|
| root / untouched sibling | `[]` | no target | no source | no source |
| inside alpha | `[α]` | `Y′` | `X` | no source |
| inside beta inside alpha | `[β, α]` | `X′` | no source | `X` |

At checkpoint 6:

```text
application root                                      γ₀
├ paired alpha reveal [X:ℕ] / [Y′:★]                 γ₀
│  └ reveal bodies                                    γα
│     └ target beta reveal [X′:Y′]                    γα
│        └ lambda bodies                              γαβ
└ arguments                                            γ₀
```

At checkpoint 7:

```text
paired residual alpha reveal [X:ℕ] / [Y′:★]           γ₀
└ generated application                               γα
   ├ target beta reveal [X′:Y′]                       γα
   │  └ lambda body                                   γαβ
   └ paired alpha conceal [X:ℕ] / [Y′:★]              γα
      └ argument bodies                               γ₀
```

The application at checkpoint 7 is under `γα`, so both immediate children
start under `γα`.  The function's beta reveal changes only its own premise to
`γαβ`.  The argument's alpha conceal checks that `γα` is exactly alpha pushed
on `γ₀`, then relates its premise under `γ₀`.  There is no sibling transport
through beta's alignment.

## Generated live Imp Ladder for the bottom row

This is the exact generated value of
`CTIGammaCarriedFramePacket.checkpoint₇-ladder`; the probe proves it is
definitionally equal to the trusted example's pinned ladder.  It describes
the current live derivation, before the proposed edit.

```text
⟨X: ─ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: X↦ℕ ⊑[X⊑★] Y′↦★⟩
source term      A        ηᴸA      ⊑ costs                          ηᴿB      B         target term
───────────────  ───────  ───────  ───────────────────────────────  ───────  ────────  ────────────────
□₁ · □₂          ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ         □₁ · □₂
├ λx. □          (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                         (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)   ├ λx. □
│ x              ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ         │ x
└ □ ⟨ ★↦ℕ ⟩      ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ         └ □ ⟨ ★↦ℕ ⟩
  □ ⟨ ★↦★ ⟩      ★        ★        ★⊑★                              ★        ★           □ ⟨ ★↦★ ⟩
  □ ↑ id         ★        ★        ★⊑★ + matched reveal partner     ★        ★           □ ↑ id
  □₁ · □₂        ★        ★        ★⊑★                              ★        ★           □₁ · □₂
  ├ ─            (X ⇒ ★)  (Z ⇒ ★)  Z ≈ Z, ★⊑★ + source rebase       (Z ⇒ ★)  (Y′ ⇒ ★)    ├ □ ↑ ⇒-rev
  │ λx. □        (X ⇒ ★)  (Y ⇒ ★)  Y ≈ Y, ★⊑★                       (Y ⇒ ★)  (X′ ⇒ ★)    │ λx. □
  │ □₁ · □₂      ★        ★        ★⊑★                              ★        ★           │ □₁ · □₂
  │ ├ λy. □      (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                         (★ ⇒ ★)  (★ ⇒ ★)     │ ├ λy. □
  │ │ y          ★        ★        ★⊑★                              ★        ★           │ │ y
  │ └ □ ⟨ X↦★ ⟩  ★        ★        ★⊑★                              ★        ★           │ └ □ ⟨ X′↦★ ⟩
  │   x          X        Y        Y ≈ Y                            Y        X′          │   x
  └ □ ↓ seal X   X        Z        Z ≈ Z + matched conceal partner  Z        Y′          └ □ ↓ seal Y′
    ─            ℕ        ℕ        ι⊑★                              ★        ★             □ ⟨ ℕ↦★ ⟩
    42           ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ             42
```

Under the proposed rules, the syntax and seven type columns are unchanged.
The three conversion rows are justified instead as follows:

| ladder row | current justification | proposed justification |
|---|---|---|
| paired `□ ↑ id` | matched reveal in one rebased world | push exact alpha frame: `γ₀ ↦ γα` |
| target-only `□ ↑ ⇒-rev` | global source rebase | push exact beta frame: `γα ↦ γαβ` |
| paired `□ ↓ seal` | matched conceal in one rebased world | pop exact alpha frame: premise `γ₀`, conclusion `γα` |

An after-ladder is intentionally not handwritten: repository policy requires
ladders in notes to be generated by `ImpLadder.impLadder`.  Updating that
generator and pinning the new ladder is part of the authorized implementation,
after the live relation exists.

## Conflicting inject/project combinations remain rejected

Frames are LIFO and keyed by the complete crossing marks, not merely by a
chosen alignment.  In the concrete nested state:

```text
top β = target-frame (X′, Y′)
next α = paired-frame (X, ℕ) (Y′, ★)
```

Therefore:

- `↓[Y′:★] ...` cannot pop beta: `(Y′,★) ≠ (X′,Y′)`;
- `↓[X′:Y′] ...` cannot pop alpha: the side and full mark differ;
- a crossing at anchor `X′` with a different representation cannot reuse
  beta's frame;
- no primitive or application rule can switch to another stored alignment;
  there is no alignment atlas in `γ`.

Only the exact top frame can be removed.  This is the restriction that the
earlier free-scope and context-indexed proposals lacked.

## Checked evidence and implementation gates

The current probes establish:

- `AnchoredCrossingLineageProbe.agda`: parent arrow crossings give their marks
  to generated reveal/conceal occurrences; alpha and beta marks remain
  distinct even when both residual conversions are `id↑ ★`; checkpoint 6 and
  checkpoint 7 have the required push/pop syntax tree.
- `AnchoredCrossingWorldAuthorizationProbe.agda`: the lineage marks match the
  concrete frame's direct store entries; the ambient/alpha/alpha-beta gammas
  satisfy the scoped invariant package; applications preserve `γ`; the beta
  residual reuses the parent beta authorization.
- `ScopedWorldTransportProbe.agda`: arbitrary frame stacks transport through
  the existing source, target, paired-precise, and paired-dynamic ambient bind
  forms.
- `ScopedPairedBindRepresentationProbe.agda`: a paired allocation premise may
  hold in the current framed view while being impossible in the ambient view;
  the resulting representation certificate is preserved by the bind, while
  a later frame correctly prevents it from being reinterpreted as a universal
  current-view invariant.
- `ScopedOneStepSquareProbe.agda`: the whole checkpoint 6-to-7 forward and
  backward reduction squares close with the ambient world unchanged.

Before merging the live replacement, the implementation must additionally
check:

1. total determinism/functionality of the three partial push functions;
2. exact-pop inversion for all three conceal rules;
3. construction of `AmbientWorldᶜ` and its allocation certificates from every
   current world-construction path;
4. transport of ambient allocation certificates, marks, frames, term-context
   evidence, and invariants through every `WorldEvolution` constructor;
5. current-view paired-bind and target-freshness lemmas for nonempty frame
   stacks;
6. endpoint typing projection for all six new rules;
7. CTI preservation for every reduction rule that distributes or removes a
   reveal/conceal;
8. regenerated Imp Ladders and all example gates;
9. forward and backward one-step simulation without `ContextualSim` and
   without a sibling-transport premise.

## Permission requested

Permission is requested to replace exactly the ten live crossing constructors
shown in the **before** section by exactly the six enriched-`γ` constructors
shown in the **after** section, together with the supporting enriched-world,
`AmbientWorldᶜ`, allocation-certificate, push/pop, transport, invariant,
renderer, and proof changes described above.

No permission is requested to add a non-syntax-directed scope constructor, to
change application or primitive rules so that siblings may choose worlds, or
to weaken exact anchor/representation matching.
