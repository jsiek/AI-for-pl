# Strong System F v2 — the conversion-boundary calculus

The informal definition of the calculus mechanized in
`SystemF/agda/strong/`.  It replaces the v1 note (now
`notes/old/notes-v1.md`), whose single combined boundary
`M ⟪ Θ , B₀ ⟫` is refuted: subject reduction is false for it.

Everything below is stated so that it can be read against the Agda.
Section headings say which module carries the definition.  Every example
term in this note was produced by `scripts/render_term.sh` from
`strong/Examples.agda`, so the de Bruijn indices are the machine's, not
mine; the named form uses `X`, `Y`, `Z` for type variables and `x`, `y`,
`z` for term variables, with `V`, `W` reserved for values.


## 1. What "strong" means, and the goal

System F's type abstraction is a *typing* discipline: `ΛX. N` may not
inspect `X`, and parametricity is a metatheorem about the erased
semantics.  **Strong** System F enforces it at *run time*.  When
`(ΛX. N) [A]` fires, the calculus does not substitute `A` into `N`.  It
installs a **boundary** that *binds* `X` to the representation `A` and
lets `N` keep running at the abstract name `X`.  A value only ever
crosses that boundary through a **conversion** that says, leaf by leaf,
which side of it is allowed to see the representation.

The name also records a syntactic property the design maintains:
*weakening with respect to type variables is never used*.  A type
variable that a term may not name is not simply absent from the context —
its entry is **masked in place** (`masked`), so it is still there for a
later re-exposure to point back at, but no type may name it.  Nothing is
dropped and nothing is re-spelled; that is what makes the transports
(`⊢rename`, `⊢retag`) hypothesis-light and what killed v1, where the
representation of a variable was *copied* into every boundary that
mentioned it and the copies drifted apart.

Two consequences shape everything else:

* A variable's representation is stored **exactly once**, at the entry
  that binds it (its *binder*).  Every other mention of that variable —
  in a conversion, in another boundary — carries only the **name**, and
  resolves the representation by looking the name up along the enclosing
  type context (`Δ ∋ X := A`).  This is the *binder-syntactic* ruling
  (`notes/DECISIONS.md`, "Redesign — Q1 realization RULED").
* Because lookup is by slot identity, moving a term across a renaming
  moves its names coherently, and knowledge transport is *definitional*:
  `ren-kn r d = ren∋ r d` in `strong.Ctx`.

### The pre-boundary counterexample (why boundaries carry a context morphism)

Before either v1 or v2 there was a **pre-boundary** design: one wrapper
per revealed or concealed variable, `M ↑[X:=A]` and `M ↓[X:=A]`, with the
rules

    (TyBeta)      (ΛX. V) @B[A]          → V ↑[X:=A]@B
    (WrapReveal)  F ↑[X:=A]@(B₁→B₂) · W  → (F · W↓[X:=A]@B₁) ↑[X:=A]@B₂
    (TyWrapCncl)  F ↓[X:=A]@∀Y.B [C]     → F [C[X:=A]] ↓[X:=A]@B

(the full set is `notes/old/notes-v1.md`, "Old per-variable design").  One
closed program refutes it — Jeremy's trace, verbatim:

    (ΛX. λf:(∀Z.Z→Z). ΛY. f [Y]) [ℕ] · (ΛZ. λz:Z. z)              : ∀Y. Y→Y
    → TyBeta      (λf:(∀Z.Z→Z). ΛY. f [Y]) ↑[X:=ℕ] · (ΛZ. λz:Z. z)
    → WrapReveal  ((λf. ΛY. f [Y]) · (ΛZ. λz:Z. z)↓[X:=ℕ]) ↑[X:=ℕ]
    → Beta        (ΛY. (ΛZ. λz:Z. z)↓[X:=ℕ] [Y]) ↑[X:=ℕ]
    → TyWrapCncl  (ΛY. ((ΛZ. λz:Z. z) [Y]) ↓[X:=ℕ]) ↑[X:=ℕ]              ← ILL-TYPED

**The diagnosis.**  A conceal's interior context was the exterior with `X`
*and every variable bound after `X`* dropped — `X`'s existential scope,
written `Γ ↓ X`.  On the third line the conceal `↓[X:=ℕ]` has come to sit
under the *later* binder `ΛY`, so its exterior is `Γ = Y , X:=ℕ` and its
interior is

    Γ ↓ X  =  (Y , X:=ℕ) ↓ X  =  ∅

because `Y` is shallower than `X` and the prefix drops it.  That is
survivable only while the concealed body never mentions `Y` — and
`TyWrapCncl` is exactly the rule that makes it mention `Y`: it pushes the
type argument **into** the concealed body as a spelled type, so
`(ΛZ. λz:Z. z) [Y]` must type at `∅ ⊢ Y`, which fails.  The last term is
not typeable at any type.

**Two lessons, and together they are what a boundary is.**

1. **Mask, don't drop.**  A `lock X` masks `X` *in place* (`mask`,
   `strong.Ctx`) and retains every other entry, so a variable bound
   between the boundary's creation and its current position stays
   nameable inside.  And the interior is *computed* from the exterior at
   the boundary's **current** position — `interior Θ Δ` is a function of
   the ambient `Δ` — never remembered from the boundary's birth.
2. **A type argument is never pushed into a concealed body.**  `TyPeelR`
   records it as a **new bind** on the boundary (one bind prepended), and
   instantiates the interior at the fresh *name* `` ` 0 `` (§6.4).  So a
   boundary has to carry a bind and a lock at the same time: it is a
   **list** — a context morphism — and not a single reveal-or-conceal.

**The same program today.**  `Examples` §14 runs it, machine-rendered;
`run-E` is the run, `⊢E₅` types the answer by `preservation*`, and
`edet₁ … edet₅` pin every state as the only successor of its predecessor
(`edet-E₅` says `E₅` has none).

Diagram:

    E₀  ((ΛX. (λx:(∀Y. (Y⇒Y)). (ΛY. x [Y]))) [ℕ] · (ΛZ. (λx:Z. x)))
        |
        |  TyBeta: the binder ↑X:=ℕ is minted
        v
    E₁  (((λx:(∀Y. (Y⇒Y)). (ΛY. x [Y]))
           ⟪ ↑X:=ℕ , ((∀Y. (id Y ↦ id Y)) ↦ (∀Y. (id Y ↦ id Y))) ⟫)
          · (ΛZ. (λx:Z. x)))
        |
        |  Peel: the argument crosses and acquires the dual's lock ↓X
        v
    E₂  (((λx:(∀Y. (Y⇒Y)). (ΛY. x [Y]))
           · ((ΛZ. (λx:Z. x)) ⟪ ↓X , (∀Y. (id Y ↦ id Y)) ⟫))
          ⟪ ↑X:=ℕ , (∀Y. (id Y ↦ id Y)) ⟫)
        |
        |  Beta, lifted through ⟪ ↑X:=ℕ , … ⟫ — FRAME-EXACT (§6.2), so
        |  the crossed value acquires ΛY's dual ↓Y as it is planted
        v
    E₃  ((ΛY. (((ΛZ. (λx:Z. x)) ⟪ ↓X , (∀Z. (id Z ↦ id Z)) ⟫)
                 ⟪ ↓Y , (∀Z. (id Z ↦ id Z)) ⟫) [Y])
          ⟪ ↑X:=ℕ , (∀Y. (id Y ↦ id Y)) ⟫)
        |
        |  TyPeelR-⟪⟫ on the Beta-minted wrapper, lifted through
        |  ⟪ ↑X:=ℕ , … ⟫ and ΛY — the moved boundary's change list gains
        |  the new binder's lock, ↓X becomes ↓X , ↓Z (§6.4)
        v
    E₄  ((ΛY. (((ΛX′. (λx:X′. x))
                   ⟪ ↓X , ↓Z , (∀X′. (id X′ ↦ id X′)) ⟫) [Z]
                 ⟪ ↑Z:=Y , ↓Y , (seal Z ↦ unseal Z) ⟫))
          ⟪ ↑X:=ℕ , (∀Y. (id Y ↦ id Y)) ⟫)
        |
        |  TyPeelR-Λ on the value's OWN Peel-minted wrapper — the line
        |  the pre-boundary design died on.  The tower is exhausted, so
        |  the Λ clause fires and instantiates on the spot
        v
    E₅  ((ΛY. (((λx:X′. x)
                   ⟪ ↑X′:=Z , ↓X , ↓Z , (seal X′ ↦ unseal X′) ⟫)
                 ⟪ ↑Z:=Y , ↓Y , (seal Z ↦ unseal Z) ⟫))
          ⟪ ↑X:=ℕ , (∀Y. (id Y ↦ id Y)) ⟫)                    a VALUE

`E₃` *is* the counterexample's third line, and `E₄ → E₅` is where the two
designs part.  Read `E₃` first for the FRAMES.  The planted value sits
inside `↓Y`, whose two type contexts are (`Examples` §14,
`E-dual-int` / `E-dual-ext`, rendered at the trace's own names):

    interior (↓Y) Δ    ⌷[Y Λ-bound] ,   X := ℕ
    convCtx (↓Y) Δ       Y Λ-bound ,    X := ℕ

so the value is read at *its birth frame* `X := ℕ`, one masked entry in:
`Y` is NOT nameable inside it (`E-Y-not-inside`), because the value was
born before `ΛY` existed.  That is frame-exact `Beta` (§6.2); before
2026-09-08 there was no `↓Y` and the value was read at `Y Λ-bound ,
X := ℕ`, one entry wider than its birth frame.  Inside the value's own
Peel-minted wrapper the frames are

    interior (↓X) (interior (↓Y) Δ)   ⌷[Y Λ-bound] , ⌷[X := ℕ]
    convCtx (↓X) (interior (↓Y) Δ)    ⌷[Y Λ-bound] ,   X := ℕ

(`E-int` / `E-ext`), where the old design had `∅`: `X` still is not
nameable (`E-X-hidden`) and nothing was TRUNCATED — lesson 1.  And the
argument `Y` is not written into the sealed body — `↑Z:=Y` binds a fresh
`Z` at the representation `Y`, read in the *exterior* `E-dual-ext` where
it is nameable, and the interior instantiates at `Z`: lesson 2.  The two
contracta type by `preservation-TyPeelR-⟪⟫` and
`preservation-TyPeelR-Λ`.

v1 took lesson 2 only — one combined boundary and a `TyWrap` that recorded
the argument as a reveal representation; that is the "Example 8" entry of
`notes/old/notes-v1.md`, whose `↑Z:=Y , ↓X` residue is `E₅`'s inner frame
here, and it is v1's *copied* representations, not that shape, that
subject reduction later refuted.  The scope move (§6.7) is the same
principle one level up: when a rule would leave a representation outside
the locks that hide it, the locks **move** into the inner frame rather
than being dropped, so nothing that was nameable stops being nameable.


## 2. Syntax

### Types (`strong.Types`)

    A, B ::= X | ℕ | 𝔹 | A ⇒ B | ∀X. A

Ordinary System F types.  In Agda they are de Bruijn (`` `_ ``, `` `ℕ ``,
`` `𝔹 ``, `_⇒_`, `` `∀ ``) with the standard renaming and parallel
substitution.  Nothing in this module knows about boundaries.

### Terms (`strong.Terms`)

    M, N ::= x | n | λx:A. N | L · M | ΛX. N | L [B, A]
           | M ⟪ Θ , c ⟫

`L [B, A]` is type application carrying **both** the instantiated body
type `B` and the argument `A` (`_·[_,_]` in Agda); the annotation is what
lets `TyBeta` mint its conversion without re-deriving the body type.

`M ⟪ Θ , c ⟫` is **the boundary**, and it is the only new form.  It
makes exactly one frame change, described by `Θ`, and carries exactly one
conversion `c`.  Its interior `M` is **term-closed**: `env` types it at
the empty term context.

### Context morphisms (`strong.CtxMorph`)

`Θ : CtxMorph` is Jeremy's *context morphism*: it maps the type context
outside the boundary to the type context inside it.  **It is a PAIR**
(2026-09-06), because its two halves are not the same kind of thing:

```agda
data Change : Set where
  lock unlock : ℕ → Change          -- EXTERIOR indices, name only

record CtxMorph : Set where
  constructor morph
  field
    binds   : List Ty               -- PARALLEL block of binders
    changes : List Change           -- SEQUENTIAL, applied head-LAST
```

| half      | rendered | what it does                                   |
|-----------|----------|------------------------------------------------|
| a `binds` entry `A` | `↑X:=A`  | binds a **fresh** interior slot at rep `A` |
| `lock X`  | `↓X`     | **masks** exterior slot `X`                    |
| `unlock X`| `↥X`     | **unmasks** exterior slot `X`                  |

The renderer prints the pair in its own order — binds first, then
changes, then the conversion:  `⟪ ↑X:=A , ↓Y , ↥Z , c ⟫`.

**The binds are PARALLEL.**  They are one simultaneous event: no bind
sees another, and every rep is read on the same type context — the
exterior with the whole change list's *unmasks* applied and *all* of its
locks lifted (§4.2).  A representation is therefore never blocked by the
frame's own locks (§8, simultaneity).

**The changes are SEQUENTIAL.**  They carry a name and nothing else, and
the list is applied **head-last**: in `↥Y , ↓Y` the `↓Y` acts first.  A
change's index is an *exterior* index, unshifted by the morphism's own
binds.

The old shape was one interleaved `List MorphEnt` with a `bind`
constructor mixed in among `lock`/`unlock`.  It said neither thing: it
made the binds look sequential (a rep was read past its own *tail* only)
and it let a lock sit between two binds, where a lock has no meaning.

One derived number, in `strong.CtxMorph`:

    numBinds : CtxMorph → ℕ            -- numBinds Θ = length (binds Θ)

`numBinds Θ` is the boundary's **frame extension**: the number of binders
it adds.  It is the only list arithmetic that survives from v1.  (The
projection `repsOf` is gone: it *is* the field `binds`.)

### Conversions (`strong.Conversion`)

The grammar and the names are GTSF's (`GTSF/Conversion.agda`), with
GTSF's two mutually defined directions merged into one family:

    s, t ::= id A | seal X | unseal X | s ↦ t | ∀X. s

* `id A` — the identity.  Its payload is restricted to **base types and
  variables** by the typing rules (`conv-id` needs `Base A`, `conv-idv`
  a variable); compound identities are built structurally by `mkId`
  (§4.4).
* `unseal X` — **reveal**: the interior sees the abstract name `X`, the
  exterior sees `X`'s representation.
* `seal X` — **conceal**: the interior sees the representation, the
  exterior sees the abstract name `X`.
* `s ↦ t` — the function conversion; **contravariant in the domain**.
* `∀X. s` — under one abstract binder.

Conversions are **representation-free**: `seal` and `unseal` carry a
name, never a spelling, and the representation is recovered by a binder
lookup on the type context.  That is why the cancel type equation is
definitional (`∋:=-det`) rather than a relation up to unfolding, and why
both conversion transports (`conv-ren`, `conv-⊑`) need no hypotheses.

### Why there is no polarity index

An earlier form of the judgment carried a global index `p` that pinned
`unseal` to reveal positions and `seal` to conceal ones, flipping on
`conv-fun`'s domain.  It is redundant, and it was **dropped**
(`notes/DECISIONS.md`, "RULING: polarity dropped from the conversion
judgment", 2026-09-06).  The discipline `p` summarized is **per type
variable**, not per boundary: each variable's name sits on the side where
it *is* a name — a `bind`'s name on the interior side, a `lock`'s name on
the exterior side — and `env` already enforces exactly that with its two
type contexts.  A locked `X` is masked in the interior context, so it
cannot appear on the interior side of a leaf; a bound `X` is not in the
image of `shiftBy`, so it cannot appear on the exterior side.  A single
global `p` is uniform only for single-kind morphisms, and it breaks the
first time a rule mints a mixed one: `TyPeelR-Λ`'s frame, one bind
prepended to `Θ = morph [] (lock 0 ∷ [])`, produces the conversion
`seal 0 ↦ seal 1`, whose two
leaves cite *different* binders and demand opposite values of one `p`
(`Examples` §13a, `¬seal↦seal` in the record).  Dropping `p` is what
makes `TyPeelR` preservation a theorem at every `∀`-conversion rather
than only at a reveal one (`proof/Preserve.preserve-TyPeelR-Λ`).


## 3. Type contexts and the mask discipline (`strong.Ctx`)

### Entries

An entry is **two layers**: what the slot *binds*, and whether the slot
is *hidden*.  The inner layer carries every type; the outer layer is the
lock, and there is **at most one of it** (Jeremy, 2026-09-08).

    b ::= abst | bind A                       -- Binding
    E ::= unmasked b | masked b               -- Ent

    Δ ::= · | E , Δ            -- Ctxᵗ = List Ent

* `abst` — a `Λ`-bound slot.  No representation, and none can be
  invented.
* `bind A` — the **binder** of an instantiation event; `A` is the
  representation, stored once, as a type over this entry's tail.
* `unmasked b` — the slot may be **named**.
* `masked b` — the slot is **masked** here: it may not be *named*, but its
  binding `b` is **retained**, so a later `unlock` has something to point
  back at.

Splitting the entry this way makes *at most one mask* true **by
construction**: `masked` takes a `Binding`, so `masked (masked …)` is not
a term.  Nothing in the development has to rule a second lock out any
more — see the lemma deltas at the end of this section.

Lookup returns the entry shifted into the ambient context:

    Δ ∋e X , E                   -- slot X has entry E
    Δ ∋tv X    = ∃ E. (Δ ∋e X , E) × Nameable E
    Δ ∋ X := A = Δ ∋e X , unmasked (bind A)

`Nameable` and `Locked` are now the two constructors' own
discriminations — one clause each, **no premise**:

    nameable : Nameable (unmasked b)
    locked   : Locked   (masked b)

so `Locked` is exactly the complement of `Nameable`, and "masked over a
nameable entry" is the only shape a masked entry *has*.  `Nameable` reads
only the lock layer; it never looks at the `Binding`, let alone a bind's
type (`unlock-mentions-no-rep`, `proof/Adversary`).  That is the whole of
the tightness discipline: `` wf-var : Δ ∋tv X → Δ ⊢ᵗ ` X ``, so a masked
slot has no well-formed variable type.  Lookup is a partial *function*
(`∋e-det`, `∋:=-det`), which is what makes every rule that mints an
identity conversion at a looked-up representation deterministic.

Renaming and the instantiation mint both act on the **binding** and are
lifted through the lock layer — a lock carries no spelling:

    renᵇ ρ abst     = abst              renᵉ ρ (unmasked b) = unmasked (renᵇ ρ b)
    renᵇ ρ (bind A) = bind (renameᵗ ρ A)   renᵉ ρ (masked b) = masked (renᵇ ρ b)

(and the same shape for `substᵇ`/`substᵉ` in `proof/Preserve` §2a, and
for `showBinding`/`showEntry` in `strong.Show`, whose rendered strings
are unchanged: `X := A`, `X Λ-bound`, `⌷[…]`).

Note the distinction the mask discipline forces: `↓X` and `↥X` **name**
a possibly masked index — that is an entry, not a type — whereas
`` Δ ⊢ᵗ ` X `` at a masked slot is refused.  Tightness is about *use in a
type*, not about mentioning the index in a context morphism.

### Refinement

Refinement splits along the same two layers.  `b ⊑ᵇ b′` says `b′` knows
at least what `b` knows:

    abst ⊑ᵇ abst          abst ⊑ᵇ bind A          bind A ⊑ᵇ bind A
      le-aa                  le-ab                   le-bb

and `E ⊑ᵉ E′` lifts it through the lock layer:

    b ⊑ᵇ b′ ⇒ unmasked b ⊑ᵉ unmasked b′                        le-uu
    b ⊑ᵇ b′ ⇒ masked b   ⊑ᵉ masked b′                          le-mm
    b ⊑ᵇ b′ ⇒ masked b   ⊑ᵉ unmasked b′                        le-mu

Each constructor's two letters are the two things it relates —
`a` = `abst`, `b` = `bind` at the binding layer; `u` = `unmasked`,
`m` = `masked` at the lock layer (Jeremy, 2026-09-06/08).  There is no
`le-um`: refinement never hides.  With `Δ ⊑ Δ′` pointwise.  There is **no** clause whose source is
`bind A` other than reflexivity: a binder never loses its representation.
That is the deleted v1 demotion, stated as the theorem
`⊑-kn : Δ ⊑ Δ′ → Δ ∋ X := A → Δ′ ∋ X := A`.  Masking only loses
nameability (`mask-⊑`), unmasking only adds it (`unmask-⊑`), and a TYPE
or a CONVERSION transports along `⊑` unchanged (`⊑-wf`, `conv-⊑`).

**A TERM does not.**  A boundary's `unlock X` *claims* that `X` is locked
(§4.2), and `le-mu` is precisely the clause that unmasks — so `⊢retag`
runs along the `le-mu`-free refinement

    b ⊑ᵇ b′ ⇒ unmasked b ⊑ᵃᵉ unmasked b′                  la-uu
    b ⊑ᵇ b′ ⇒ masked b   ⊑ᵃᵉ masked b′                    la-mm

— the *same* `⊑ᵇ` on the binding layer, with the two locks forced to
agree.  With `Δ ⊑ᵃ Δ′` pointwise and `⊑ᵃ→⊑` the embedding.  Its one
content is `⊑ᵃᵉ-Locked : E ⊑ᵃᵉ E′ → Locked E → Locked E′` — *a locked
slot stays locked* — which is what `⊢ˢ-⊑ᵃ` needs at `sw-u`.  Every call
site is covered: `preserve-TyBeta` refines an `abst` to a `bind`
(`la-uu le-ab`), and
the two former `le-mu` sites — the Peel crossing and the scope move — are
now exact identities and use no retagging at all (§6.3, §6.7).

### The three operations a boundary uses

    mask X Δ    = updateAt maskEnt X Δ        -- sets the lock at slot X
    unmask X Δ  = updateAt unmaskEnt X Δ      -- clears the lock at slot X
    pushBinds As Δ                    -- pushes the reps As as binders

    maskEnt (unmasked b) = masked b      unmaskEnt (unmasked b) = unmasked b
    maskEnt (masked b)   = masked b      unmaskEnt (masked b)   = unmasked b

Both are **total** and **idempotent**: there is only one lock to set or
clear.  `maskEnt` is never applied to an already-masked slot in a
well-formed term — `sw-l` (§4.2) admits `lock X` only at a nameable
slot — but the function does not have to know that, and that is the
point.

`updateAt f X` replaces the entry at slot `X` and leaves the rest alone, so
masking is *positional* — which is why the renaming transports carry
`Inj ρ` (`ren-updateAt`), a structural hypothesis about the renaming and about
no representation at all.

`pushBinds` deserves its own line, because it is where **simultaneity** lives:

    pushBinds []       Δ = Δ
    pushBinds (A ∷ As) Δ =
      unmasked (bind (shiftBy (length As) A)) ∷ pushBinds As Δ

The head of the list is interior slot 0.  A representation is a type over
the *exterior*, so it is lifted past exactly the binders **inside** it and
past nothing else — sibling entries of the same boundary never interfere.
As a well-formedness fact:

    wf-shiftBy-pushBinds : Δ ⊢ᵗ A → pushBinds As Δ ⊢ᵗ shiftBy (length As) A

### The two type contexts a boundary induces

Write `Δ` for the **exterior** — the type context in which the whole
term `M ⟪ Θ , c ⟫` is typed.  A boundary induces two more:

    applyChanges S Δ     -- Δ with S's locks AND unlocks applied, in order
    applyUnlocks S Δ     -- Δ with only S's unlocks applied (locks skipped)

    scope         Θ Δ = applyChanges (changes Θ) Δ
    unlockedScope Θ Δ = applyUnlocks (changes Θ) Δ

    interior Θ Δ = pushBinds (binds Θ) (scope Θ Δ)
                                        -- THE INTERIOR context
    convCtx  Θ Δ = pushBinds (binds Θ) (unlockedScope Θ Δ)
                                        -- THE CONVERSION context

`interior Θ Δ` is where `M` is typed: `Θ`'s masks are applied and `Θ`'s
binds are pushed on.  Why the conversion needs a context of its
*own* — why `c : Bᵢ ⇝ Bₑ` can be checked neither inside nor outside — is
the question this section answers, on `Examples` §13a's inner boundary

    ((ΛZ. λx:Z. 3) [Y]) ⟪ ↑Y:=X , ↓X , (seal Y ↦ seal X) ⟫

over the exterior `Δ = X := ℕ`.  The morphism binds a fresh `Y` at the
representation `X` and locks `X`; the conversion is `seal Y ↦ seal X`.

**The exterior cannot check it.**  `seal Y` names `Y` — a slot the
boundary *itself* binds.  `Y` does not exist in `Δ = X := ℕ` at all, so
no judgment over `Δ` can even state the conversion: its leaves live
inside the bind prefix, `numBinds Θ` slots deeper than everything in
`Δ`.

**The interior cannot check it either.**  Every leaf cites its binder by
*lookup*: `conv-seal` and `conv-unseal` need `Δ ∋ X := A`, which does not
hold of a `masked` entry.  Here `seal X : ℕ ⇝ X` must cite `X`'s binder —
and `X` is exactly the slot `↓X` masks, so in `interior Θ Δ` that lookup
fails.  This is not a defect to repair: masking `X` *is* the type
abstraction the boundary enforces, and the interior is supposed not to
name it.

So the conversion needs the binders **and** the locked slots: binds
pushed, locks lifted.  That is `convCtx Θ Δ`, the smallest context in
which both leaves resolve.  It is not a third *construction* but the same
one with the locks skipped: `applyUnlocks` is `applyChanges` minus its
`lock` clause, so **the conversion context is the interior of the same boundary
with its locks removed**.  (As an *operation* on frames, removing the
locks — `dropLocks` — is retired: it cannot be the outer frame of the
scope move, §6.7, and it survives only as a local definition in
`proof/MwUObstruct` §0, where it is refuted.)

The three contexts are ordered by refinement, in one direction only:

    interior⊑convCtx : interior Θ Δ ⊑ convCtx Θ Δ
    Δ⊑unlockedScope  : Δ ⊑ unlockedScope Θ Δ

and each buys one side of `env`'s conversion premise — for the two sides
of `c` live in different contexts.  The source is the interior type `Bᵢ`,
a type of `interior Θ Δ`, read up in the conversion context by the first
refinement (`⊢retag` / `conv-⊑`, types unchanged).  The target is
`shiftBy (numBinds Θ) Bₑ` for the **exterior** type `Bₑ`, a type over
`Δ`; the second refinement with `wf-shiftBy-pushBinds` is what makes that
shifted type well formed in `convCtx Θ Δ` (`wf-convCtx`).

### Diagram: one boundary, two contexts

Here is that same boundary — the inner one of `Examples` §13a's `J₆` —
with its two induced contexts rendered by `showTCtxAt` at the same
names:

Diagram:

    exterior        Δ                          X := ℕ
                    |                            |
       ↑Y:=X , ↓X   |  pushBinds + masks         |  pushBinds, locks SKIPPED
                    v                            v
    interior        interior Θ Δ            Y := X , ⌷[X := ℕ]
                                                 ^
                                                 |  the lock, lifted
    conversion      convCtx Θ Δ             Y := X ,   X := ℕ

`⌷[…]` is the renderer's mark for the lock.  Read the two bottom rows: the
interior may name `Y` but **not** `X` — that is the type abstraction the
lock enforces — while the conversion is checked one row down, where `X`
is live, so `seal X` can cite `X`'s binder.  The conversion typed there is

    Y := X , X := ℕ  ⊢  seal Y ↦ seal X  ∶  (Y ⇒ ℕ)  ⇝  (X ⇒ X)

with `seal Y : X ⇝ Y` (the fresh binder's rep, concealed at its own name)
and `seal X : ℕ ⇝ X` (the crossed boundary's binder).  Each leaf conceals
at *its own* binder: that is the whole content, and it is why no single
polarity index could type the tree.

Indices: everything inside the boundary is `numBinds Θ` slots deeper than
outside, so an exterior type `Bₑ` is read inside as `shiftBy (numBinds Θ) Bₑ`.
`lock X` / `unlock X` name **exterior** slots, and the rules that move a
morphism inward lift those names by the bind count (`shiftScope`, §6.7).

### What the one-mask entry costs, and what it buys

*Bought* (each of these used to be an induction over the mask stack, or a
premise carried only to keep the stack one deep):

| before | after |
|--------|-------|
| `locked : Nameable E → Locked (masked E)` | `locked : Locked (masked b)` — no premise |
| `nameable-a`, `nameable-b` | one `nameable` |
| `⊑ᵉ-trans`, 6 clauses, `le-mu` calling `nameable-mono` | `⊑ᵇ-trans` 3 + `⊑ᵉ-trans` 4, no witness threading |
| `le-mu : E ⊑ᵉ E′ → Nameable E′ → masked E ⊑ᵉ E′` | `le-mu : b ⊑ᵇ b′ → masked b ⊑ᵉ unmasked b′` |
| `unmaskEnt-nameable` (a lemma, only to feed `le-mu`) | **gone** |
| `masked-le`, recursive on the mask stack | `maskEnt-le`, 3 non-recursive clauses |
| `⊑ᵃᵉ-Locked` via `nameable-mono` | `⊑ᵃᵉ-Locked (la-mm l) locked = locked` |
| `maskEnt-unmask (locked v) = refl` | `maskEnt-unmask locked = refl` |
| `core`, `core-ren`, `core-nameable`, `core-masked`, `core-unmaskEnt` (`proof/MaskFacts`) | `core` **is** `unmaskEnt`; the five collapse to three one-line case splits |
| `renᵉ-id`, `renᵉ-comp`, `substᵉ`, `substᵉ-0-⇑`, `substᵉ-⇑`, `showEntry` — all recursive | each is a `Binding` function plus a two-clause lift |
| `renᵉ-Nameable⁻`, `Locked-ren⁻` — 3 clauses each | 2 clauses each |

*Cost* — exactly one place.  `maskEnt` is **idempotent**, so

    unmask-mask : Δ ∋tv X → unmask X (mask X Δ) ≡ Δ

now carries a nameability premise; with a stack of masks the identity
held unconditionally, because a second lock was simply popped.  The
premise is always at hand — `sw-l` admits `lock X` only at a `∋tv` slot
(§4.2), which is the discipline that made double masking unreachable in
the first place — and it is threaded through exactly two lemmas:
`proof/PeelDual.applyUnlocks-dualScope` and
`proof/PeelDual.convCtx-dual`, each of which gains a `Δ ⊢ˢ S` /
`Δ ⊢ˢ changes Θ` argument that its one call site already has (`mwᵥ` in
`preserve-Peel`).  `mask-unmask : Δ ∋lk X → mask X (unmask X Δ) ≡ Δ` is
unchanged, so the two inverses are now symmetric: each holds at the slots
its own direction is applied to, and nowhere else.

`proof/DualTightness.¬⊢ᵐ-double-lock` survives, with a different job: it
is no longer the fact that keeps `Locked` one mask deep — that is by
construction — but the fact that the judgement still refuses a vacuous
re-lock, which is what keeps `unmask-mask`'s premise available.

### Vocabulary

This note uses the Agda names throughout; they are the plain-English ones,
and Appendix A lists them all.  The ones used most here:
`interior` = *interior type context*, `convCtx` = *conversion context,
the one the conversion is checked in*, `scope` = *scope*,
`unlockedScope` = *scope with the locks lifted*, `binds` = *the parallel
block of representations*, `changes` = *the sequential lock/unlock list*,
`pushBinds` = *push the representations on as binders*,
`numBinds` = *number of binds*, `shiftBy` =
*shift past n binders*.


## 4. Typing (`strong.CtxMorph`, `strong.Terms`, `strong.Conversion`)

### 4.1 Well-formed types

    wf-var : Δ ∋tv X → Δ ⊢ᵗ ` X
    wf-ℕ   : Δ ⊢ᵗ ℕ                 wf-𝔹 : Δ ⊢ᵗ 𝔹
    wf-⇒   : Δ ⊢ᵗ A → Δ ⊢ᵗ B → Δ ⊢ᵗ (A ⇒ B)
    wf-∀   : (abst , Δ) ⊢ᵗ A → Δ ⊢ᵗ (∀X. A)

The only interesting clause is `wf-var`: it asks for **visibility**, so a
masked slot is unnameable, and a `∀` pushes `abst`, never a `bind`.

### 4.2 Well-formed context morphisms — `Δ ⊢ᵐ Θ`

Read "the context morphism `Θ` is well formed over `Δ`"; an infix
judgement in the family of `Δ ⊢ᵗ A` and `Δ ⊢ c ∶ A ⇝ B`.  **It is a pair,
because the morphism is** — one judgement per half:

```agda
data _⊢ʳ_ : Ctxᵗ → List Ty → Set where        -- the PARALLEL reps
  rw[] : Δ ⊢ʳ []
  rw-b : Δ ⊢ᵗ A → Δ ⊢ʳ Bs → Δ ⊢ʳ (A ∷ Bs)

data _⊢ˢ_ : Ctxᵗ → List Change → Set where    -- the SEQUENTIAL changes
  sw[] : Δ ⊢ˢ []
  sw-l : applyChanges S Δ ∋tv X → Δ ⊢ˢ S → Δ ⊢ˢ (lock X ∷ S)
  sw-u : applyChanges S Δ ∋lk X → Δ ⊢ˢ S → Δ ⊢ˢ (unlock X ∷ S)

record _⊢ᵐ_ (Δ : Ctxᵗ) (Θ : CtxMorph) : Set where
  constructor mw
  field
    mw-reps    : unlockedScope Θ Δ ⊢ʳ binds Θ
    mw-changes : Δ ⊢ˢ changes Θ
```

The **changes** half is *sequential*: every premise is read on the frame
the change acts on, i.e. on the context the changes to its right (which
`applyChanges` applies first) have already built.  The **reps** half is
*parallel*: every rep is read on ONE context, `unlockedScope Θ Δ` — the
whole change list's unmasks applied, all of its locks lifted.

A `lock` names a slot that is **still visible** where it acts — so a slot
is never masked twice.  (`Locked` is one mask deep by *construction*
now, §3, but the premise still earns its keep: it is what makes
`unmask ∘ mask` the identity at the slot, `unmask-mask`.)  An `unlock`
names a slot that is **LOCKED** there: `Δ ∋lk X` is `∃E. (Δ ∋e X , E) ×
Locked E`, with `Locked (masked b)` for any binding `b`.  It is the
mirror of `Δ ∋tv X`, and it mentions no representation at all — an
`unlock` still claims no knowledge; the knowledge claim lives in the
conversion, where `seal X` must cite a live binder.

**A VACUOUS UNLOCK IS REFUSED** (Jeremy's ruling, 2026-09-06;
`proof/DualTightness` §5).  `↥X` over a slot the frame leaves visible is
not merely useless, it is *wrong*: it is the case on which `dual`'s
restoring `lock` would mask what the exterior left nameable.  The
judgement refuses it, and that refusal is exactly what makes
`mask ∘ unmask` the identity where the dual needs it
(`mask-unmask`, `Locked`).

**A rep is read on `unlockedScope Θ Δ`, not on `scope Θ Δ` and not on the
plain `Δ`.**  This is the surviving half of simultaneity, and it is
forced from both sides:

* not on `scope Θ Δ` — a rep must never be blocked by the frame's *own*
  locks, or `TyPeelR`'s new frame (one bind prepended to `Θ`) would be
  ill formed whenever `Θ` locks a slot the type argument `A` names;
* not on the plain `Δ` — the scope move `_⋉_` (§6.7) merges an inner
  frame's binds with an enclosing frame's changes, and the inner frame's
  reps were read past that enclosing frame's *unlocks*.  With a
  plain-`Δ` rep half the merged frame has no derivation
  (`proof/MwUObstruct` §4, at
  `Θ₁ ⋉ Θ₂ = morph (` 0 ∷ []) (unlock 0 ∷ [])` over an exterior that
  masks slot 0).

**The one semantic move the pair makes.**  The interleaved list read a
rep past *its own tail only*: in `bind A ∷ ↥X ∷ []` the rep `A` saw the
`↥X`, but in `↥X ∷ bind A ∷ []` it did not.  The pair reads **every** rep
past the **whole** change list, which is strictly more permissive — a rep
may now name a slot an unlock to its *left* re-exposes.  That is what
"the binds are a parallel block" means: there is no left and no right
among them, and none of them is nested inside a change.  Nothing in the
development depended on the tighter reading: every `⊢ᵐ` derivation in
`Examples` and in `proof/` goes through unchanged (§9).

**What the strengthened `sw-u` costs, and how it is paid.**  Under it
`sw-l` and `sw-u` are exact complements — a lock names a *nameable* slot,
an unlock a *locked* one — so no *simultaneous* change judgement could
hold of a list that both locks and unlocks one slot, and the scope move
builds exactly such lists.  The sequential reading above is what admits
them.  Two further consequences:

* `⊢retag` no longer runs along `⊑`: `le-mu` *unmasks*, which destroys an
  `unlock`'s claim.  Terms travel along `_⊑ᵃ_`, the `le-mu`-free
  refinement (§3); types and conversions keep the full `⊑`.
* the outer frame of `CancelR`/`IdPush` is `rewind Θ₂`, not
  `dropLocks Θ₂` (§6.7).

### 4.3 Terms

    ⊢`  : Γ ∋ x ⦂ A → Δ ∣ Γ ⊢ x ⦂ A
    ⊢$  : Δ ∣ Γ ⊢ n ⦂ ℕ
    ⊢ƛ  : Δ ⊢ᵗ A → Δ ∣ A , Γ ⊢ N ⦂ B → Δ ∣ Γ ⊢ λx:A. N ⦂ (A ⇒ B)
    ⊢·  : Δ ∣ Γ ⊢ L ⦂ (A ⇒ B) → Δ ∣ Γ ⊢ M ⦂ A → Δ ∣ Γ ⊢ L · M ⦂ B
    ⊢Λ  : (abst , Δ) ∣ ⤊Γ ⊢ N ⦂ C → Δ ∣ Γ ⊢ ΛX. N ⦂ ∀X. C
    ⊢·[]: Δ ∣ Γ ⊢ L ⦂ ∀X. B → Δ ⊢ᵗ A → Δ ∣ Γ ⊢ L [B, A] ⦂ B[X:=A]

and the boundary rule, in full:

    env : Δ ⊢ᵐ Θ
        → interior Θ Δ ∣ [] ⊢ M ⦂ Bᵢ
        → convCtx Θ Δ ⊢ c ∶ Bᵢ ⇝ shiftBy (numBinds Θ) Bₑ
        → Δ ⊢ᵗ Bₑ
          ------------------------------------
        → Δ ∣ Γ ⊢ M ⟪ Θ , c ⟫ ⦂ Bₑ

Premise by premise:

1. **`Δ ⊢ᵐ Θ`** — the morphism is well formed over the exterior
   (§4.2).  This is the only place the morphism's own halves are
   checked: the binds *simultaneously*, against `unlockedScope Θ Δ`; the
   changes *sequentially*, each against the frame it acts on.
2. **`interior Θ Δ ∣ [] ⊢ M ⦂ Bᵢ`** — the interior is typed in the interior
   type context, at the **empty term context**: a boundary is
   term-closed.  `Bᵢ` is the **interior type**, a type of the interior
   context, and it is where the masks bite: if `Θ` locks `X`, then `Bᵢ`
   cannot name `X`.
3. **`convCtx Θ Δ ⊢ c ∶ Bᵢ ⇝ shiftBy (numBinds Θ) Bₑ`** — the conversion is
   checked in the **conversion context**, and it converts the interior
   type `Bᵢ` to the exterior type `Bₑ` *read inside*, i.e. shifted past
   the boundary's own `numBinds Θ` binders.  Both endpoints of `c` therefore
   live at the interior's depth; the conversion context is the interior
   context with `Θ`'s locks lifted, so a `seal X` at a locked `X` is
   typeable here and only here.
4. **`Δ ⊢ᵗ Bₑ`** — the **exterior type** is a type of the exterior.
   This is the premise that the whole preservation endgame turned on
   (§7): a rule whose contractum makes a boundary present a
   representation must present it where this premise can be discharged.

So: `c` converts the **interior type** (the type of `M`, in the interior
type context) to the **exterior type** (in the exterior, shifted
into the interior's frame), and it is typed in neither of those two
contexts but in the third, `convCtx Θ Δ` — the interior with `Θ`'s locks
lifted.

### 4.4 The conversion judgment

    Δ ⊢ c ∶ A ⇝ B

reads: *`c` converts the interior type `A` to the exterior type `B`, both
read in `Δ`*.  In full:

    conv-id     : Base A                  → Δ ⊢ id A      ∶ A   ⇝ A
    conv-idv    : Δ ∋tv X                 → Δ ⊢ id (` X)  ∶ ` X ⇝ ` X
    conv-unseal : Δ ∋ X := A              → Δ ⊢ unseal X  ∶ ` X ⇝ A
    conv-seal   : Δ ∋ X := A              → Δ ⊢ seal X    ∶ A   ⇝ ` X

    conv-fun    : Δ ⊢ s ∶ A′ ⇝ A  →  Δ ⊢ t ∶ B ⇝ B′
                  --------------------------------------
                → Δ ⊢ s ↦ t ∶ (A ⇒ B) ⇝ (A′ ⇒ B′)

    conv-all    : (abst , Δ) ⊢ s ∶ A ⇝ B  → Δ ⊢ ∀X. s ∶ ∀X. A ⇝ ∀X. B

`conv-seal` is **the soundness gate**: a conceal must cite a *live binder*
on its type context.  There is no second premise and no side condition;
`proof/Adversary.agda` shows that this one inversion refutes the
adversaries that v1 needed `Reversal≈ + starOnly + SkelEq` to exclude.
`conv-fun`'s reversed domain is the only trace the retired polarity index
leaves.

Two derived facts used pervasively:

    mkId  : Ty → Conv                 -- the identity at an arbitrary type
    mkId (` X) = id (` X);  mkId ℕ = id ℕ;  mkId 𝔹 = id 𝔹
    mkId (A ⇒ B) = mkId A ↦ mkId B;   mkId (∀X. A) = ∀X. mkId A

    mkId-⊢ : Δ ⊢ᵗ A → Δ ⊢ mkId A ∶ A ⇝ A

and, the one the determinism proof needs:

    conv-types-unique :
      if Δ ⊢ c ∶ A ⇝ B and Δ ⊢ c ∶ A′ ⇝ B′ then A ≡ A′ and B ≡ B′

i.e. a conversion **determines both of its types**, given the context:
`id` carries its own, a `seal`/`unseal` reads its representation by the
binder lookup (`∋:=-det`), and `↦` / `∀` are structural.


## 5. Values, and the active/inert split (`strong.Terms`)

Values:

    V-$  : Value n
    V-ƛ  : Value (λx:A. N)
    V-Λ  : Value N → Value (ΛX. N)
    V-⟪⟫ : Value M → Inert c → Value (M ⟪ Θ , c ⟫)

`V-Λ` carries `Value N` because reduction goes **under `Λ`** (`ξ-Λ`).
Without the premise, `ΛX. N` would be a value for every `N` while `ξ-Λ`
reduced under it, and both "values don't step" and determinism would be
false — machine-checked in the id-layer probe
(`notes/DECISIONS.md`, repair 3).

The split is Siek and Chen's, transplanted:
`notes/ParameterizedCastCalculi.md` digests *Parameterized Cast Calculi
and Reusable Meta-theory for Gradually Typed Lambda Calculi* (JFP 31(e30),
2021).  There, `Inert c` is a cast that forms a value when wrapped around
one, `Active c` is a cast that reduces when it meets one,
`ActiveOrInert` is total, and `Vcast` requires `Inert`.  Here the
classification is by the **conversion constructor** alone — no type is
inspected and no slot arithmetic occurs:

    Inert  = { id (` X) , seal X , s ↦ t , ∀X. s }
    Active = { id A with Base A , unseal X }

    act-or-inert : Δ ⊢ c ∶ A ⇝ B → Active c ⊎ Inert c

Totality holds over *typed* conversions because the payload restriction
on `id` means the untypeable compound identities are never classified at
all.  `act-not-inert` rules out overlap.

Reading the split: an **inert** conversion is a claim the value keeps
carrying (a conceal, a function or `∀` conversion waiting for its
elimination, a transparent variable layer); an **active** one is a
question the value can answer now (reveal a binder's representation, or
drop a base identity over a numeral).


## 6. Reduction (`strong.Reduction`; the minted conversions `reveal`/`conceal`/`instReveal`/`instConceal` are in `strong.Conversion` §4)

The relation is `Δ ⊢ M -→ M′`, indexed by the type context only — there
is no term context, and there cannot be one (§7).  `Δ ⊢ M -→* M′` is its
reflexive-transitive closure.

Three families of derived operators are used by the rules.  All of them
mint **names only**; none copies a representation.

**The canonical conversion at a slot** (mutually recursive):

    reveal X (` Y) = unseal X if X = Y, else id (` Y)
    reveal X ℕ = id ℕ;  reveal X 𝔹 = id 𝔹
    reveal X (A ⇒ B) = conceal X A ↦ reveal X B
    reveal X (∀Y. A) = ∀Y. reveal (X+1) A

    conceal   X (` Y) = seal X if X = Y, else id (` Y)   -- and dually

`reveal X B` reveals `X` wherever `B` runs covariantly and conceals it
where `B` runs contravariantly.  `instReveal` / `instConceal` are the same
mint applied to a **conversion** instead of a type, and on an identity
they agree: `instReveal X (mkId B) ≡ reveal X B`.

**The dual of a crossed boundary**:

    hideBinds n = lock (n-1) , … , lock 0
    dualScope n []             = []
    dualScope n (bind A , Θ)   = dualScope n Θ
    dualScope n (unlock X , Θ) = dualScope n Θ ++ [ lock   (n + X) ]
    dualScope n (lock X , Θ)   = dualScope n Θ ++ [ unlock (n + X) ]

    dual Θ = hideBinds (numBinds Θ) ++ dualScope (numBinds Θ) Θ

so the dual **locks** each of the crossed boundary's own new binders (the
crossing argument may not see them), **unlocks** each of its locks (the
argument came from outside, where those were nameable) and **re-locks**
each of its unlocks (the argument came from outside, where those were
*not* nameable).  Two points of care:

* **it must restore the unlocks.**  Dropping the `unlock` case is the
  tightness defect of §6.3: the crossing argument then gets a frame
  strictly more nameable than the exterior.  Restoring is sound because
  `sw-u` refuses a vacuous unlock, so `mask ∘ unmask` really is the
  identity at the slot;
* **it must run backwards.**  `applyChanges` applies its list head-last,
  so an
  inverse must undo the entries in reverse order — hence the append at
  the end of each clause.  A same-order dual is not an inverse at a frame
  that toggles one slot twice (`↥X , ↓X`, which the judgement admits).

With both, `interior-dual` is an EXACT identity and `convCtx-dual` holds
unconditionally (`proof/PeelDual.agda`).

**The scope move** (§6.7):

    shiftScope n []             = []      -- the CHANGES, indices lifted by n
    shiftScope n (unlock X , S) = unlock (n+X) , shiftScope n S
    shiftScope n (lock X , S)   = lock   (n+X) , shiftScope n S

    rewind Θ = morph (binds Θ)           -- Θ with its own CHANGES undone
                     (dualScope 0 (changes Θ) ++ changes Θ)

    Θ₁ ⋉ Θ₂ = morph (binds Θ₁)
                    (changes Θ₁ ++ shiftScope (numBinds Θ₂) (changes Θ₂))

Note `numBinds (Θ₁ ⋉ Θ₂) ≡ numBinds Θ₁` and
`numBinds (rewind Θ) ≡ numBinds Θ`: neither operation carries a binder.

**The appended lock** (§6.4, `strong.CtxMorph` §5):

    addLock0 Θ = morph (binds Θ) (changes Θ ++ [ lock 0 ])

one `lock 0` at the **tail** of a boundary's own change list, where
`applyChanges` runs it **first** — exactly the position `_⋉_` puts its
travelling changes in.  It carries no binder
(`numBinds (addLock0 Θ) ≡ numBinds Θ`, by reflexivity) and it is
invisible on the conversion context
(`convCtx (addLock0 Θ) Δ ≡ convCtx Θ Δ`, because `applyUnlocks` skips
locks), so a boundary that acquires it re-types its conversion by
`conv-ren` alone.  On the interior it is exactly `mask 0`:
`interior (addLock0 Θ) Δ ≡ interior Θ (mask 0 Δ)`.  `TyPeelR-⟪⟫` is its
only user: it is how a moved boundary masks the new bind slot in its own
frame instead of under a minted wrapper.


### 6.1 `TyBeta` — the boundary is born

    TyBeta : Value N
      → Δ ⊢ (Λ N) ·[ B , A ] -→ N ⟪ morph (A ∷ []) [] , reveal 0 B ⟫

Named:  `(ΛX. N) [B, A]  →  N ⟪ ↑X:=A , reveal X B ⟫`, `N` a value.

**Bookkeeping.** This is the only rule that mints a representation.  It
does *not* substitute: `N` keeps running at the abstract `X`, the new
`bind` becomes `X`'s binder, and the conversion is derived from the body
type `B` by `reveal` — reveal `X` on the way out, conceal it on the way
in.  The `Value N` premise is a determinism repair: this calculus reduces
under `Λ`, so `(Λ N) ·[ B , A ]` with `N` a redex would otherwise have
two distinct steps, this one and `ξ-·[] ⨟ ξ-Λ`.

Example (`Examples` §6, `P₀ → P₁`, under `ξ-·-l`):

    ((ΛX. (λx:X. x)) [ℕ] · 7)
      →  (((λx:X. x) ⟪ ↑X:=ℕ , (seal X ↦ unseal X) ⟫) · 7)

with `reveal 0 (X ⇒ X) ≡ seal 0 ↦ unseal 0`.

### 6.2 `Beta` — and why the substitution carries a type

    Beta : Value W → Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ∶ A ]ᵐ

Named: `(λx:A. N) · W → N[x:=W]`.  The ordinary β step; its preservation
case *is* the substitution lemma (`strong.TermSubst.⊢subst`).  Term
substitution is the identity on boundaries, since a boundary body is
term-closed.

**THE SUBSTITUTION IS FRAME-EXACT** (Jeremy, 2026-09-08).  The old rule
was `N [ W ]ᵐ`, and `substᵐ`'s `Λ` clause moved the substituted value
under the binder by *shifting* it (`⇑ᴹ = renᴹ suc`), which moves the
*names* in its boundaries: in `Examples` §11 the sealed argument
`(7 ⟪ ↓X , seal X ⟫)` becomes, one binder in, `(7 ⟪ ↓X , seal X ⟫)` with
`X` one slot further out.  That is SOUND — the shifted indices cannot
reach slot 0 — but it is not EXACT: the value's frame silently GAINS the
`Λ`'s slot, so at `Examples` §14's `E₃` the crossing wrapper was read at
`Y Λ-bound , ⌷[X := ℕ]`, one entry more than the frame it was born in.
Every other rule in the table is exact (see the frame identities in §7);
`Beta` was the one inexact rule.

**The repair: what crosses a binder is wrapped in the binder's dual.**  A
`Λ` is an `abst` binder occupying slot 0 inside, so its dual is
`morph [] (lock 0 ∷ [])` — no binds, one lock, exactly what
`dual (morph (A ∷ []) [])` is — and the conversion is the identity at the
value's own type, shifted past the binder:

    crossΛ W A = ⇑ᴹ W ⟪ morph [] (lock 0 ∷ []) , mkId (⇑ᵗ A) ⟫

The frame identity is then DEFINITIONAL:

    interior (morph [] (lock 0 ∷ [])) (unmasked abst ∷ Δ) ≡ masked abst ∷ Δ

— the image's BIRTH frame `Δ` with the crossed binder masked: nothing
gained, nothing lost (`Examples.interior-Beta-Λ`).  It is the same shape
`Peel` mints for its crossing argument, so `⊢crossΛ`
(`strong.TermSubst` §6) is proved by the same two moves: `⊢rename` at
`suc` (`Ren-wk`, `Inj-suc`) for the interior, `mkId-⊢` for the
conversion.  A `ƛ` needs no wrapper — a term binder changes no type
frame — and reduction under binders is by the frame-indexed relation
already, so `ξ-Λ`/`ξ-⟪⟫` are untouched.

**Which is why the rule carries `A`.**  `mkId` needs the value's type, and
`env` needs the value TERM-CLOSED (it types an interior at `Γ = []`).
Both live in the substitution's IMAGES (`strong.TermSubst` §5b):

    data Img : Set where
      ivar : ℕ → Img          -- a term variable: never wrapped
      ival : Term → Ty → Img  -- the substituted value, at its type

and `⊢ival : Δ ⊢ᵗ A → Δ ∣ [] ⊢ W ⦂ A → Δ ∣ Γ ⊢ⁱ ival W A ⦂ A` records the
two facts.  `A` is read off the redex (the `ƛ`'s own annotation), so the
contractum is still a function of the redex alone and `det` is unchanged.

**The cost is one step, sometimes.**  `mkId` is INERT at a variable, a
function type and a `∀`, so the wrapper is a value; at a BASE type it is
`id ℕ`, which is ACTIVE, and `7 ⟪ ↓Y , id ℕ ⟫` takes one `Drop$`.  More
generally the layer is walked through by the `IdPush`/`CancelR`/`Drop$`
cascade already in the calculus, which is where the step-count deltas in
`Examples`' header come from (`Q₀` 9 → 11, `D₀` 12 → 16, `E₀` 5 → 6; `P₀`,
`J₀`, `H₀` unchanged).

Example (`Examples` §6, `P₂ → P₃`, under `ξ-⟪⟫`) — no `Λ` is crossed
here, so no wrapper is minted:

    (((λx:X. x) · (7 ⟪ ↓X , seal X ⟫)) ⟪ ↑X:=ℕ , unseal X ⟫)
      →  ((7 ⟪ ↓X , seal X ⟫) ⟪ ↑X:=ℕ , unseal X ⟫)

Example (`Examples` §11, `Q₂ → Q₃`, under `ξ-⟪⟫`) — one `Λ` is crossed,
and the argument acquires `↓Z`:

    (((λx:X. (ΛZ. x) [ℕ]) · (7 ⟪ ↓X , seal X ⟫)) ⟪ ↑X:=ℕ , unseal X ⟫)
      →  ((ΛZ. ((7 ⟪ ↓X , seal X ⟫) ⟪ ↓Z , id X ⟫)) [ℕ])
             ⟪ ↑X:=ℕ , unseal X ⟫

### 6.3 `Peel` — the crossing

    Peel : Value V → Value W
      → Δ ⊢ (V ⟪ Θ , s ↦ t ⟫) · W
          -→ (V · (wkᴹ (numBinds Θ) W ⟪ dual Θ , s ⟫)) ⟪ Θ , t ⟫

Named: `(V ⟪ Θ , s ↦ t ⟫) · W → (V · (W ⟪ dual Θ , s ⟫)) ⟪ Θ , t ⟫`.

**Bookkeeping.** The application is pushed one layer in.  The function
conversion splits: `t` stays on the boundary, and `s` — the domain
component, which `conv-fun` already read contravariantly — becomes the
crossing argument's own conversion, transplanted **verbatim**.  That is
sound because `convCtx (dual Θ) (interior Θ Δ) ≡ convCtx Θ Δ`: the dual's
conversion context *is* the crossed boundary's.  The argument's frame is
the dual: a `↓` for each of `Θ`'s binds (the argument may not name the
new binders) and a `↥` for each of `Θ`'s locks (the argument came from
outside, where they were nameable).  `wkᴹ (numBinds Θ)` re-indexes the
argument one bind frame deeper.

Example (`Examples` §6, `P₁ → P₂`), with
`dual (morph (ℕ ∷ []) []) ≡ morph [] (lock 0 ∷ [])`:

    (((λx:X. x) ⟪ ↑X:=ℕ , (seal X ↦ unseal X) ⟫) · 7)
      →  (((λx:X. x) · (7 ⟪ ↓X , seal X ⟫)) ⟪ ↑X:=ℕ , unseal X ⟫)

The `7` has crossed inward and is now sealed at the new binder, so the
interior sees it at the abstract name `X` — which is exactly what
`λx:X. x` demands.

**TIGHTNESS OF THE CROSSING** (Jeremy's test, 2026-09-06;
`proof/DualTightness.agda`).  The mini-core's `dualScope` **dropped**
`Θ`'s `unlock` entries, so a boundary that unmasks an exterior slot
handed its crossing argument a frame in which that slot was *still*
unmasked: `interior (dual Θ) (interior Θ Δ)` was the masked bind prefix
over `unlockedScope Θ Δ`, strictly more nameable than `Δ`.  The
machine-checked witness — `Δᵤ = ↓U`, `Θᵤ = ↥U`, `W = λy:ℕ. (ΛZ. 3)[U]` —
took an **ill-typed** redex to a **well-typed** contractum: scope was
gained through the boundary.  That is a failure of design law 2 for the
*reduction relation* (not of preservation: the redex is not well typed).

It is repaired, in two coupled halves — the restoring, reversed
`dualScope` above and the `sw-u` that refuses a vacuous unlock (§4.2).
The frame identity is then **exact**:

    (†)  interior (dual Θ) (interior Θ Δ)
           ≡ map maskEnt (pushBinds (binds Θ) []) ++ Δ      given Δ ⊢ᵐ Θ

*the crossing argument's frame IS the exterior*, one (masked) bind prefix
in — so the argument crosses by `⊢rename (wkN (numBinds Θ))` alone, with
no `⊢retag` and no `le-mu` anywhere.  On the witness above the contractum
is now REFUSED (`¬⊢Contractum`), and the positive control still passes:
at a Θ-**locked** slot the dual unlocks it again and the argument keeps
its frame.

### 6.4 `TyPeelR-Λ` / `TyPeelR-⟪⟫` — a `∀` conversion meets a type application

`canon-∀` (`proof/Canonical`) says a closed value at a `∀` type is a `Λ`
over a value **or** a wrapper with a `∀` conversion, and nothing else, so
the rule is **two clauses**, split on the crossed boundary's interior
(2026-09-08, the shift audit; `notes/ShiftAudit.md`).  Together they are
total over canonical `∀`-values, so the pair *replaces* the single rule
rather than supplementing it.

    TyPeelR-Λ : Value N
      → (unmasked abst ∷ convCtx Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ
      → Δ ⊢ ((Λ N) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
          -→ N ⟪ morph (A ∷ binds Θ) (changes Θ) , instReveal 0 s ⟫

    TyPeelR-⟪⟫ : Value W
      → (unmasked abst ∷ convCtx Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ
      → Δ ⊢ ((W ⟪ Θ′ , `∀ s′ ⟫) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
          -→ ((renᴹ (extN (numBinds Θ′) suc) W
                 ⟪ addLock0 (renᴮ suc Θ′)
                 , `∀ (renᶜ (extᵗ (extN (numBinds Θ′) suc)) s′) ⟫)
                ·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ])
               ⟪ morph (A ∷ binds Θ) (changes Θ) , instReveal 0 s ⟫

Named: the `Λ` clause is
`((ΛX. N) ⟪ Θ , ∀X. s ⟫) [B, A] → N ⟪ ↑X:=A , Θ , instReveal X s ⟫`, and
the wrapper clause is
`((W ⟪ Θ′ , ∀X. s′ ⟫) ⟪ Θ , ∀X. s ⟫) [B, A]
   → ((W ⟪ ↓X , Θ′ , ∀X. s′ ⟫) [Bᵢ, X]) ⟪ ↑X:=A , Θ , instReveal X s ⟫`,
where `Bᵢ` is the interior `∀`-body determined by the premise.

**Bookkeeping**, shared by both clauses:

1. **A new binder is prepended.**  The frame becomes
   `morph (A ∷ binds Θ) (changes Θ)` — plain
   `Θ`, not shifted, because `interior` already lifts `Θ`'s representations
   past the prepended binder:
   `interior (morph (A ∷ binds Θ) (changes Θ)) Δ
    ≡ bind (shiftBy (numBinds Θ) A) ∷ interior Θ Δ`.
2. **The conversion is re-minted at the new slot.**  Slot 0 of `s`'s body
   was `abst` and is now the binder this rule introduces, so every leaf
   that reads it must become the instantiation step: `unseal 0` where the
   conversion runs covariantly, `seal 0` where it runs contravariantly —
   that is `instReveal 0 s`.  Keeping `s` is ill-typed: its exterior body
   still mentions `` ` 0 `` where `env` demands the instantiated
   `shiftBy (numBinds Θ + 1) (Bₑ [ A ])` (`Examples` §13a, `¬⊢J-plain`).

**What the `Λ` clause does.**  Nothing moves.  The `Λ`'s `abst` slot
*becomes* the boundary's `bind` slot, so the body's frame move is a
refinement `abst → bind` at a slot it could already name — `la-uu le-ab`,
legal for `_⊑ᵃ_`, which is `TyBeta`'s own step one `∀` inside.  There is
no `wkᴹ`, no `⊢rename`, and the contractum does not mention `Bᵢ` at all,
so it is determined by the redex without `conv-src-unique`.

**What the wrapper clause does.**  The type application is pushed inward
one layer, exactly as the single rule pushed it, and the moved subterm is
shifted by `wkᴹ 1` — which on a boundary renames its interior at
`extN (numBinds Θ′) suc`, its frame by `renᴮ suc` and its conversion body
at `extᵗ (extN (numBinds Θ′) suc)`.  On top of that, `lock 0` is
**appended to the moved boundary's own change list** (`addLock0`, §5's
`_⋉_` position: at the tail, where `applyChanges` runs it first).  The
pushed-in body annotation must be the **interior** `∀`-body `Bᵢ`, which
is what the interior's own `⊢·[]` demands and which differs from the
exterior body at every non-identity leaf.  `Bᵢ` is not syntactically
recoverable from a representation-free conversion (a `seal`'s source is a
binder's representation), so the rule carries the conversion typing as a
**premise**.  `Progress` supplies it for free by inverting the redex's own
`env` (`conv-all-inv`), and determinism is `conv-src-unique`.

**Why the appended lock.**  Without it the moved boundary's interior is
offered the new bind slot **unmasked** — a slot it could not name before
and cannot use after, because `wkᴹ 1` sends every index to ≥ 1.  The tight
frame and the offered one differ by exactly one `le-mu`, the re-exposure
clause, which is precisely the step `_⊑ᵃ_` refuses; that was the audit's
one leak (`notes/ShiftAudit.md` §3).  With the lock the moved boundary's
frame is its **birth frame with the crossed binder masked** —
`proof/ShiftAudit.TyPeelR-⟪⟫-frame`, the same shape `(†)` gives `Peel`'s
crossing argument and `interior-Beta-Λ` gives `Beta`'s.

**Why the wrapper clause terminates.**  Its contractum's inner
application is again a redex, but the `∀`-value's **tower height** — the
number of nested boundaries above the `Λ` — strictly decreases
(`TyPeelR-⟪⟫-height`), because the clause *consumes* a boundary that was
already there.  A tower of height `h` therefore takes `h − 1` wrapper
steps and then exactly one `Λ` step.  The rejected repair — wrap the
moved value in the new binder's dual — *mints* a boundary instead, so its
measure stalls and it loops: an identity conversion at a `∀` is
necessarily a `` `∀ `` conversion, hence inert, hence the wrapped value
under `·[ … ]` is itself a redex (`fixA-height-stalls`, and the run
`T₀ -→ᵃ T₁ -→ᵃ T₂` in `proof/ShiftAudit` §4a).

**Example — both clauses, on a two-deep tower** (`proof/ShiftAudit` §5c₃,
machine-rendered; the outer frame binds `X := ℕ` and the inner one locks
it, so the moved boundary really does carry a change list for the
appended lock to join):

    (((ΛY. 3) ⟪ ↓X , (∀Y. id ℕ) ⟫) ⟪ ↑X:=ℕ , (∀Y. id ℕ) ⟫) [ℕ]
      →  TyPeelR-⟪⟫   (tower height 2 → 1)
    (((ΛZ. 3) ⟪ ↓X , ↓Y , (∀Z. id ℕ) ⟫) [Y] ⟪ ↑Y:=ℕ , ↑X:=ℕ , id ℕ ⟫)
      →  TyPeelR-Λ    (tower exhausted)
    ((3 ⟪ ↑Z:=Y , ↓X , ↓Y , id ℕ ⟫) ⟪ ↑Y:=ℕ , ↑X:=ℕ , id ℕ ⟫)

Read the moved boundary's change list across the first step: `↓X` becomes
`↓X , ↓Y` — the shifted original lock and the new lock, appended at the
tail.  Nothing else about that boundary changes, and no wrapper appears.
The frames confirm it:

    showTCtxAt 9 0 (λ _ → "X") Ξᵈ₁                    =  ⌷[X := ℕ]
    showTCtxAt 9 0 (λ { 0 → "Y" ; _ → "X" }) Ξᵈ₃
      =  ⌷[Y := ℕ] , ⌷[X := ℕ]

`Ξᵈ₁` is `W`'s birth frame and `Ξᵈ₃` its frame in the contractum: the same
frame with the new binder `Y` inserted **masked**.  Exact.

**Example — the mint, at both conversions.**  The **reveal** side
(`Examples` §13b, `H₃ → H₄`):

    ((ΛY. (λx:Y. (7 ⟪ ↓X , seal X ⟫)))
       ⟪ ↑X:=ℕ , (∀Y. (id Y ↦ unseal X)) ⟫) [ℕ]
      →  ((λx:Y. (7 ⟪ ↓X , seal X ⟫))
            ⟪ ↑Y:=ℕ , ↑X:=ℕ , (seal Y ↦ unseal X) ⟫)

with `` instReveal 0 (id (` 0) ↦ unseal 1) ≡ seal 0 ↦ unseal 1 ``: the
inserted `seal Y` conceals the binder this rule introduced, under an
`unseal X` that reveals the crossed boundary's.  The **conceal** side is
`Examples` §13a, `J₅ → J₆`:

    ((((ΛY. (λx:Y. 3)) ⟪ ↓X , (∀Y. (id Y ↦ seal X)) ⟫) [X]
        · (7 ⟪ ↓X , seal X ⟫)) ⟪ ↑X:=ℕ , unseal X ⟫)
      →  ((((λx:Y. 3) ⟪ ↑Y:=X , ↓X , (seal Y ↦ seal X) ⟫)
            · (7 ⟪ ↓X , seal X ⟫)) ⟪ ↑X:=ℕ , unseal X ⟫)

Here `instReveal 0 s ≡ seal 0 ↦ seal 1` — the two-conceal tree of §3's
diagram, the one no single polarity could type.  Both examples reach
their redex from closed, plain System F source, both are `Λ`-clause
steps, and both contracta type by `preservation-TyPeelR-Λ`.  Note that
both contracta are one boundary shallower than the single rule's: the
`Λ` clause performs the instantiation itself, so no
`(Λ …) ·[ … , ` 0 ]` is left behind for `TyBeta` to consume, and one type
instantiation mints **one** binder where the old rule pair minted two.
That is why the `J` run is eleven steps rather than fourteen and the `E`
run of `Examples` §14 is five rather than six.

### 6.5 `Drop$`

    Drop$ : Base A → Δ ⊢ ($ n) ⟪ Θ , id A ⟫ -→ $ n

Named: `n ⟪ Θ , id A ⟫ → n` for base `A`.  A numeral is typeable
anywhere (`⊢$`), so a transparent base layer over one carries no
information and is discarded, frame and all.

Example (`Examples` §6, `P₅ → 7`):  `(7 ⟪ ↑X:=ℕ , id ℕ ⟫)  →  7`.

### 6.6 `CancelR` — a conceal directly under its reveal

    CancelR : Value V → convCtx Θ₂ Δ ∋ Y := A
      → Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
          -→ (V ⟪ Θ₁ ⋉ Θ₂ , mkId (shiftBy (numBinds Θ₁) A) ⟫)
               ⟪ rewind Θ₂ , mkId A ⟫

**Bookkeeping.**  The two conversions cite the *same entry*, so the match
is definitional — there is no second spelling to disagree with the first,
which is the `∋:=-det` fact the whole binder design was chosen for.
Both **frames are kept** and both conversions are **neutralised** to
identities at the looked-up representation; composition happens only on
the conversions, where `unseal ∘ seal = id` is algebra we already trust,
so no context-morphism arithmetic returns.  The two names need no
relating premise: typing already forces `X ≡ numBinds Θ₁ + Y`
(`proof/IdLayer.cancel-name`).  The lookup premise is there because the
rule mints identity conversions *at a looked-up representation*, and
determinism for such rules is exactly `∋:=-det`.  The frames move as in
§6.7.

Example (`Examples` §6, `P₃ → P₄`; here `Θ₂ = ↑X:=ℕ` has no scope at
all, so `Θ₁ ⋉ Θ₂ ≡ Θ₁` and `rewind Θ₂ ≡ Θ₂`):

    ((7 ⟪ ↓X , seal X ⟫) ⟪ ↑X:=ℕ , unseal X ⟫)
      →  ((7 ⟪ ↓X , id ℕ ⟫) ⟪ ↑X:=ℕ , id ℕ ⟫)

Two `Drop$` steps then finish the run to `7`.

### 6.7 `IdPush`, and the scope move

    IdPush : Value V → convCtx Θ₂ Δ ∋ Y := A
      → Δ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫
          -→ (V ⟪ Θ₁ ⋉ Θ₂ , unseal X ⟫) ⟪ rewind Θ₂ , mkId A ⟫

**Bookkeeping.**  A value under a transparent `` id (` X) `` layer, under an
active conversion, is not a value and no other rule fires.  Rather than
*merging* the two frames — the retired `IdAbsorb`'s `⊳`, which failed
the no-composition test by regrowing representation arithmetic — the two
**conversions are swapped**: the transparent layer becomes the revealing
one and the outer becomes transparent.  Each step moves the active
conversion one layer inward toward the seal, so the process terminates.
The pushed name is already written in the id-conversion:
`X ≡ numBinds Θ₁ + Y` (`proof/IdLayer.idpush-name`).  `unseal` is the only
active conversion this left-hand side can meet
(`proof/IdLayer.outer-id-base-untypeable`).

**Why the frames move.**  Both `IdPush` and `CancelR` make the *inner*
boundary stop presenting the abstract name and start presenting `Y`'s
**representation** `A`.  A representation is a type over the
exterior, so `env`'s last premise now asks for `A` to be well formed
*inside* the outer frame — and `Θ₂`'s own locks may have masked the very
slot `A` names.  That was **the wall**, and the whole invariant hunt was a
search for a side condition to ground it.  Every candidate was refuted;
the record is in `notes/DECISIONS.md` (2026-09-06 entries), and its two
surviving artifacts are `proof/MaskFacts.mask-only` and `Examples` §12/§12b.

The repair is not a side condition but a **frame move** (Jeremy,
2026-09-06).  The outer frame's whole **scope** — locks *and* unlocks, in
order, lifted past its own binders — travels into the inner frame's tail
(`Θ₁ ⋉ Θ₂`), where `scope` applies it **first**, exactly where it applied
before; and what stays outside is the frame with its own scope **rewound**
(`rewind Θ₂`, its changes prefixed by their inverse), whose net effect is
its bind prefix alone:

    scope    (rewind Θ₂) Δ ≡ Δ                      given Δ ⊢ᵐ Θ₂
    interior (rewind Θ₂) Δ ≡ pushBinds (binds Θ₂) Δ

The representation is then presented outside the locks, where it is
nameable, and the locks still stand between the value and the world.

**Why `rewind`, and not the two cheaper frames.**  All three of
`rewind Θ₂`, `dropLocks Θ₂` and `morph (binds Θ₂) []` (delete the changes
outright) leave the same type context.  Only `rewind` keeps its own
`_⊢ᵐ_`, and both alternatives are refuted on ONE configuration
(`proof/MwUObstruct`): `Δ₆ = ↓U`, `Θ₂ = ↥U`, `Θ₁ = ↑V:=U`, so that
`Θ₁ ⋉ Θ₂ = ↑V:=U , ↥U`.

* `dropLocks Θ₂` KEEPS `Θ₂`'s unlocks, so the *moved copy* of the same
  unlock lands where the slot is already nameable — a vacuous unlock,
  which `sw-u` refuses (`¬⊢ᵐ-dropLocks`);
* `morph (binds Θ₂) []` DELETES them, and then `Θ₂`'s *own* bind representation
  — read on `unlockedScope Θ₂ Δ`, i.e. past that very unlock — is
  stranded on the plain exterior (`¬⊢ᵐ-bindsOnly`);
* `rewind Θ₂` keeps every entry and rewinds it, so every premise is read
  exactly where the redex read it (`⊢ᵐ-rewind`).

Example — the wall witness itself (`Examples` §12b, over
`Δi = X := Y , Y := ℕ`, so `X`'s representation *names* `Y` and the outer
boundary *locks* `Y`):

Diagram:

    R₀   ((((7 ⟪ seal Y ⟫) ⟪ ↥Y , seal X ⟫) ⟪ id X ⟫) ⟪ ↓Y , unseal X ⟫)
      |
      |  IdPush  (Θ₁ = [] , Θ₂ = ↓Y ; Θ₁ ⋉ Θ₂ = ↓Y , rewind Θ₂ = ↥Y , ↓Y)
      v
    R₁′  ((((7 ⟪ seal Y ⟫) ⟪ ↥Y , seal X ⟫) ⟪ ↓Y , unseal X ⟫)
                                                        ⟪ ↥Y , ↓Y , id Y ⟫)
      |
      |  CancelR  lifted through the outer boundary (ξ-⟪⟫)
      v
    R₂   ((((7 ⟪ seal Y ⟫) ⟪ ↥Y , ↓Y , id Y ⟫) ⟪ ↥Y , ↓Y , id Y ⟫)
                                                        ⟪ ↥Y , ↓Y , id Y ⟫)

Read `R₀` and `R₁′` side by side: `↓Y` has moved from the outer boundary
to the inner one, and the reveal `unseal X` went with it.  The
representation `Y` that the reveal hands back is now presented on the
outer boundary's own type context, where `Y` is live, instead of inside
the lock, which is what `env`'s last premise refused.  The value's frame
is unchanged (`interior ([] ⋉ Θi) (interior (rewind Θi) Δi)
≡ interior [] (interior Θi Δi)` is `refl`), so `V` retypes where it was —
by `subst`, not by `⊢retag` — and `R₂` is a **value**.  The `↥Y , ↓Y`
riding on the outer frames is the rewind: inert on the type context, and
carrying the premises its own reps were read under.  Under
the old rule `R₀`'s contractum was untypeable — that refutation was the
content of `proof/PreserveObstruct` §4, which now records the positive
fact on the same witness.

**Why the unlocks travel too, and are also retained.**  `scope` applies its
list head-last, so moving only the *locks* past a same-slot `unlock`
reorders a mask/unmask pair, and the value's frame is then not refined
but **corrupted** — a slot it may name in the redex is masked in the
contractum.  The refutation is in tree
(`proof/MoveScope` §4b, `¬frame-locksOnly`) at the `_⊢ᵐ_`-legal witness
`Θ✗ = morph [] (unlock 0 ∷ lock 0 ∷ [])` over `Δ✗ = unmasked (bind ℕ) ∷ []`,
where `interior Θ✗ Δ✗ ≡ unmasked (bind ℕ) ∷ []` but the lock-only
contractum's interior is `masked (bind ℕ) ∷ []`.  Moving the whole scope keeps the order, and then
the value's frame is preserved **on the nose**: with `rewind` outside,
both frame lemmas are equalities,

    interior (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ) ≡ interior Θ₁ (interior Θ₂ Δ)
    convCtx  (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ) ≡ convCtx  Θ₁ (convCtx  Θ₂ Δ)

(both given `Δ ⊢ᵐ Θ₂`), so neither case uses `⊢retag` at all — no premise
about `Θ₂`'s shape, and no side condition for `Progress` to supply.

A second example, from closed plain source (`Examples` §11,
`Q = ((ΛY. λx:Y. ((ΛZ. x) [ℕ])) [ℕ]) · 7`, nine steps to `7`).  The
inner, *vacuous* `Λ` is instantiated at a body type that is an **outer**
variable, and `` reveal 0 (` k) ≡ id (` k) `` for `k ≠ 0` — so `TyBeta`
mints an identity layer, and that two-wrapper stack is the `IdPush`
redex:

    Q₃  ((ΛY. (7 ⟪ ↓X , seal X ⟫)) [ℕ] ⟪ ↑X:=ℕ , unseal X ⟫)
    Q₄  (((7 ⟪ ↓X , seal X ⟫) ⟪ ↑Y:=ℕ , id X ⟫) ⟪ ↑X:=ℕ , unseal X ⟫)
    Q₅  (((7 ⟪ ↓X , seal X ⟫) ⟪ ↑Y:=ℕ , unseal X ⟫) ⟪ ↑X:=ℕ , id ℕ ⟫)

`Q₃ → Q₄` is the inner `TyBeta` (the id-layer is born); `Q₄ → Q₅` is
`IdPush`.  Here `Θ₂ = ↑X:=ℕ` locks nothing, so the move is the identity
and only the two conversions swap.  `CancelR` then fires under `ξ-⟪⟫`
and three `Drop$` steps finish.

### 6.8 The congruence rules

    ξ-·-l : Δ ⊢ L -→ L′            → Δ ⊢ L · M -→ L′ · M
    ξ-·-r : Value V → Δ ⊢ M -→ M′  → Δ ⊢ V · M -→ V · M′
    ξ-·[] : Δ ⊢ L -→ L′            → Δ ⊢ L ·[ B , A ] -→ L′ ·[ B , A ]
    ξ-Λ   : (unmasked abst ∷ Δ) ⊢ N -→ N′   → Δ ⊢ Λ N -→ Λ N′
    ξ-⟪⟫  : interior Θ Δ ⊢ M -→ M′     → Δ ⊢ M ⟪ Θ , c ⟫ -→ M′ ⟪ Θ , c ⟫

Left-to-right, call-by-value, and **under `Λ`** — which is why `V-Λ` and
`TyBeta` both carry `Value N`.  Note the two index changes: `ξ-Λ` steps
in `unmasked abst ∷ Δ`, and `ξ-⟪⟫` steps in the *interior* type context
`interior Θ Δ`.  A boundary is not a barrier to reduction; it is a barrier to
*naming*.

Example of `ξ-Λ` and `ξ-·[]` together (`Examples` §3, `run-Ωt` — the
witness for `TyBeta`'s `Value` premise):

    (ΛX. ((λx:ℕ. 1) · 2)) [ℕ]  →  (ΛX. 1) [ℕ]  →  (1 ⟪ ↑X:=ℕ , id ℕ ⟫)

The first step is `ξ-·[] ⨟ ξ-Λ ⨟ Beta`; only then is the now-valuable
package instantiated.  `ξ-·-l` is `P₀ → P₁` (§6.1) and `ξ-⟪⟫` is
`P₂ → P₃` (§6.2); `ξ-·-r` is the mirror of `ξ-·-l` and has no instance in
the corpus, because every argument in it is already a value.


## 7. Metatheory (`strong.TypeSafety`)

The public surface, verbatim, all parameter-free and `--safe`:

    progress     : Δ ∣ [] ⊢ M ⦂ A → Value M ⊎ ∃ M′. (Δ ⊢ M -→ M′)
    preservation : Δ ∣ [] ⊢ M ⦂ A → Δ ⊢ M -→ M′  → Δ ∣ [] ⊢ M′ ⦂ A
    preservation*: Δ ∣ [] ⊢ M ⦂ A → Δ ⊢ M -→* M′ → Δ ∣ [] ⊢ M′ ⦂ A
    type-safety  : Δ ∣ [] ⊢ M ⦂ A → Δ ⊢ M -→* N
                 → Value N ⊎ ∃ N′. (Δ ⊢ N -→ N′)
    det          : Δ ⊢ M -→ M₁ → Δ ⊢ M -→ M₂ → M₁ ≡ M₂
    value-¬step  : Value M → Δ ⊢ M -→ M′ → ⊥

Two structural facts about the statements.  **The term context is
empty**, and it has to be: `_⊢_-→_` carries no term context, and
`TyBeta`'s contractum is a boundary, whose body `env` types at `Γ = []`.
At a non-empty `Γ` the theorem is already false — `Λ (λx:ℕ. y)` is a
value at `Γ = ℕ , ·`, `TyBeta` fires, and the contractum's interior would
have to mention a term variable that a boundary body may not have.  And
**there is no context well-formedness premise** (`⊢ᶜ Δ`, the store-typing
pattern the v1 endgame expected).  It is unnecessary: every site that
reads a representation back also has the `env` node that put it there,
whose last premise is `Δ ⊢ᵗ Bₑ`, and `⊢ᵗ-of` recovers the
well-formedness of any typed term's type from the derivation alone.

### `progress`

Stated in `strong.Progress` (and again in `strong.TypeSafety`), proven in
`proof/Progress` — the same public/proof split the other theorems have.

Induction on the typing derivation.  The three ordinary cases are decided
by the canonical-forms suite (`proof/Canonical`): `canon-⇒` gives `λ` or
a `↦`-converted boundary, `canon-∀` gives `Λ` (with its body a value, so
`TyBeta`'s premise is `V-Λ`'s premise) or a `∀`-converted boundary, and
`canon-base` gives a numeral.  The boundary case is the content, and it
is two steps.  First run the induction hypothesis on the **interior**, at
`interior Θ Δ`, where `env`'s second premise types it; an interior step lifts
by `ξ-⟪⟫`.  Then classify the conversion by `act-or-inert`, keeping the
active branches' premises:

* **inert** — the boundary is a value, `V-⟪⟫`;
* **`conv-id b`** — the exterior type is base, so the interior value is a
  numeral (`canon-base`) and `Drop$` fires with `b` as its own `Base`
  premise;
* **`conv-unseal d`** — the interior value sits at a *variable* type, so
  by `canon-var` it is a `seal`-converted or an `` id (` Y) ``-converted
  boundary — precisely `CancelR`'s and `IdPush`'s left-hand sides.  Both
  rules ask for `convCtx Θ Δ ∋ Y := A`, which **is** `conv-unseal`'s own
  premise `d`: the lookup is free, never re-derived.

The historically hard case — a value at an abstract type — costs one
two-way split, because the only conversions with a variable exterior are
exactly the two that the id-layer rules consume.

### `preservation`

Induction on the step, with the rule cases distributed:

* **`TyBeta`** (`proof/Preserve.preserve-TyBeta`) — the mint.  The new
  binder is the `unmasked abst ⊑ᵃᵉ unmasked (bind A)` refinement of the
  `Λ`'s own slot (`la-uu le-ab`), so the interior retypes by `⊢retag`; the minted conversion
  types by `⊢reveal`/`⊢conceal`, and its exterior type is the
  instantiated body by `subst-at-0`.  The exterior premise is `⊢·[]`'s
  own two premises through `wf-[]ᵗ`, and `interior (morph (A ∷ []) []) Δ` is
  definitional.
* **`Beta`** — `⊢subst` (`strong.TermSubst`).
* **`Peel`** (`proof/PeelDual.preserve-Peel`) — the two context
  identities are what carries it: (†)
  `interior (dual Θ) (interior Θ Δ)
  ≡ map maskEnt (pushBinds (binds Θ) []) ++ Δ` (given `Δ ⊢ᵐ Θ`)
  and `convCtx (dual Θ) (interior Θ Δ) ≡ convCtx Θ Δ`.  The crossing
  argument, typed in `Δ`, retypes one bind frame deeper by
  `⊢rename (wkN (numBinds Θ))` and **nothing else** — the tail is `Δ`
  itself, so no `⊢retag` and no `le-mu` — and the conversion `s`
  transplants verbatim through the second identity.
* **`TyPeelR-Λ`** (`proof/Preserve.preserve-TyPeelR-Λ`) — at **every**
  `∀`-conversion, once polarity is gone.  The body is `⊢retag`ged along
  `la∷ (la-uu le-ab) (⊑ᵃ-refl _)` — the `Λ`'s slot becoming the
  boundary's binder — and the minted `instReveal 0 s` types leaf by leaf,
  each leaf citing its own binder.  Nothing is renamed.
* **`TyPeelR-⟪⟫`** (`proof/Preserve.preserve-TyPeelR-⟪⟫`) — the same
  outer `env`, with the moved boundary crossing by `⊢addLock0-cross`
  (`strong.TermSubst`): its reps by `⊢ʳ-ren`, its changes by `⊢ˢ-++`
  (`⊢ˢ-ren` plus `sw-l` for the appended lock, whose slot **is**
  nameable), its interior by `⊢rename` at `Ren-addLock0` **alone**, and
  its conversion by `conv-ren` — the appended lock is lifted on the
  conversion context (`convCtx-addLock0`), so nothing about the
  conversion changes.  The interior instantiation lands at the fresh
  binder's name and `ren-suc-[0]` undoes the annotation shift.
* **`Drop$`** — one inversion: `conv-id-refl` plus `shiftBy-ℕ⁻` force the
  exterior type to be the base type.
* **`CancelR`, `IdPush`** (`proof/MoveScope`) — the scope move, §6.7.
  Four moves each, one per premise of the contractum's inner `env`:
  the frame is `Θ₁ ⋉ Θ₂`, well formed by `⊢ᵐ-⋉`; the interior is `V`,
  moved by `subst` along the frame **equality**; the conversion cites the
  binder that `move-∋` transports; and the exterior premise is
  `moved-scoped`, the one the wall used to deny — which is now just
  `wf-shiftBy-pushBinds` on the redex's own exterior type, because
  `interior (rewind Θ₂) Δ ≡ pushBinds (binds Θ₂) Δ`
  and `A ≡ shiftBy (numBinds Θ₂) C` for the redex's `C`.
  The two frame lemmas are **equalities** (§6.7), so neither case uses
  `⊢retag`.  `⊢ᵐ-⋉` is where the sequential judgement pays for itself:
  `⊢ˢ-++` splits the merged change list at the move, `⊢ˢ-shiftScope`
  re-reads `Θ₂`'s
  entries one bind prefix in, and `Θ₁` is then read over exactly
  `interior Θ₂ Δ` — its own exterior in the redex.
* the five `ξ` rules — structural, using the same `env` node.

The three transports the induction rests on are `⊢rename` (along a
context renaming, with `Inj ρ`), `⊢retag` (along `⊑ᵃ`, types unchanged),
and `⊢subst`.  After the repairs `⊢retag` has exactly one call site in
the whole preservation proof — `TyBeta`'s `abst ⊑ᵃᵉ bind A`.

### `det` and `value-¬step`

`value-¬step` holds on the nose once `V-Λ` carries `Value N`.  `det` is a
case analysis on the two steps; the interesting entries are the rules
whose contracta are not syntactically determined by the redex:

* `TyPeelR-⟪⟫`'s pushed-in annotation is premise-determined, and the two
  premises give the same annotation by `conv-src-unique` (§4.4).
  `TyPeelR-Λ` needs no such appeal: its contractum does not mention the
  annotation at all, so it is determined by the redex outright.  The two
  clauses' patterns are disjoint (a `Λ` is not a boundary), so no cross
  case arises;
* `CancelR` and `IdPush` mint identity conversions at a looked-up
  representation, and the two lookups agree by `∋:=-det`.

Everything else is either `refl` or an appeal to `value-¬step` at an
overlapping `ξ`.

### Tightness

The six theorems above say nothing about **ill-typed** terms, and design
law 2 (§8) is a claim about exactly those: reduction must never take a
term the exterior refuses to one it accepts.  That is a property of the
*relation*, so it is checked the way Jeremy proposed — by exhibiting it
(`proof/DualTightness`, `Examples` §15).  Build an ill-typed redex whose
fault is one localized `wf-var` premise: a subterm names a type variable
the frame at its position masks, or has no entry for at all.  Take the
step.  The rule moves that subterm into a new frame.  The rule is
**tight** iff the contractum is refused for the same reason.

It is a theorem rather than five anecdotes because each rule's new frame
is a known function of the old one:

| rule | the moved subterm's new frame |
|------|-------------------------------|
| `TyBeta` | `interior (morph (A ∷ []) []) Δ ≡ unmasked (bind A) ∷ Δ` — `Δ` on the nose, one refinement (`unmasked abst ⊑ᵃᵉ unmasked (bind A)`, i.e. `la-uu le-ab`) at the slot the rule reveals |
| `TyPeelR-Λ` | `interior (morph (A ∷ binds Θ) (changes Θ)) Δ ≡ bind (shiftBy (numBinds Θ) A) ∷ interior Θ Δ` — the redex's frame, one binder in, and the body is **not moved**: its slot 0 was `unmasked abst` and is now `unmasked (bind …)`, the same `la-uu le-ab` refinement `TyBeta` performs, at a slot it could already name.  No shift at all (`proof/ShiftAudit.TyPeelR-Λ-refinement`, `TyPeelR-Λ-no-shift`) |
| `TyPeelR-⟪⟫` | `interior (addLock0 (renᴮ suc Θ′)) (interior (morph (A ∷ binds Θ) (changes Θ)) Δ) ≡ pushBinds (map ⇑ᵗ (binds Θ′)) (masked (bind (shiftBy (numBinds Θ) A)) ∷ scope Θ′ (interior Θ Δ))` — the moved boundary's **birth frame** with the new binder inserted **masked** below its bind prefix, the same shape `(†)` gives `Peel` and `interior-Beta-Λ` gives `Beta` (`proof/ShiftAudit.TyPeelR-⟪⟫-frame` and `-slot-locked`, from `strong.TermSubst.interior-addLock0-cross`); it crosses by `⊢rename` alone, at `Ren-addLock0` |
| `Peel` | (†) `interior (dual Θ) (interior Θ Δ) ≡ map maskEnt (pushBinds (binds Θ) []) ++ Δ`, given `Δ ⊢ᵐ Θ` (`proof/PeelDual.interior-dual`) |
| `CancelR`, `IdPush` | `interior (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ) ≡ interior Θ₁ (interior Θ₂ Δ)`, given `Δ ⊢ᵐ Θ₂` (`proof/MoveScope.interior-⋉-rewind`) |
| `Beta` | `Δ` where no binder is crossed — no frame changes |
| `Beta`, under a `Λ` | `interior (morph [] (lock 0 ∷ [])) (unmasked abst ∷ Δ) ≡ masked abst ∷ Δ` — the image's BIRTH frame with the crossed `Λ`'s slot masked (`Examples.interior-Beta-Λ`) |

The `Beta` row used to read `Δ` and nothing else, and it was the one
INEXACT row: `substᵐ` shifted the image under the `Λ` without recording
that the new slot is not the image's, so the image's frame was
`unmasked abst ∷ Δ` — one entry wider than its birth frame, sound but not
exact.  The dual wrapper of §6.2 closes it, and `Examples` §15d₂ runs the
test on the closed case.

The first two rows and the last are `refl` (`Examples.interior-TyBeta`,
`interior-TyPeelR`, `interior-Beta-Λ`); the `TyPeelR-⟪⟫` row is
`applyChanges-++` plus `applyChanges-shiftScope1` (`strong.CtxMorph` §5,
`strong.TermSubst`), and the `Peel` and scope-move rows are the theorems
whose `Δ ⊢ᵐ Θ` premise is where the sequential judgement pays for itself
(§4.2).  `Drop$` and the five congruences move nothing into a new frame.

Every rule passes.  **The one exception is recorded and is not a scope
gain**: `Beta` at an erasing body — `(λx:ℕ⇒ℕ. 3) · W` with `W` ill typed
steps to `3`, which types.  Substitution may *drop* its argument, and a
dropped subterm crosses nowhere; what is left was already typed inside
the redex (`Examples` §15d).

**The shift audit (2026-09-08)** re-read the table against the stronger
question Jeremy asked after #199 — not "does the relation gain scope?"
but "**does the frame say the truth about what the moved subterm may
name?**" — and found **one** offending row, the old single `TyPeelR`.  It
was the only rule that put a moved subterm under an **unmasked** new
binder: the identity above held, but the new slot 0 arrived unmasked, so
the frame offered `V` a slot `V` could not name before and cannot use
after (`wkᴹ 1` sends every index to ≥ 1).  Machine-checked in
`proof/ShiftAudit` §3 — `TyPeelR-slot0-nameable` (the frame has it),
`TyPeelR-V-tight` (`V`'s own `⊢rename` goes through at the **masked**
entry), `TyPeelR-node-needs-slot0` (the pushed-in `·[ … , ` 0 ]` is what
needs it, and it shares `V`'s frame) and `TyPeelR-leak-¬⊑ᵃ` (the
difference is exactly one `le-mu`, the step a **term** may not travel).
It was never a scope gain — the frame simply did not say the truth.

**That row is now closed.**  The split of §6.4 is installed, and the two
clauses give the two exact rows above: `Peel` masks its whole bind prefix
((†)), frame-exact `Beta` masks the crossed `Λ`, `TyBeta` introduces no
new slot at all, `TyPeelR-Λ` moves nothing, and `TyPeelR-⟪⟫` masks the
new binder in the moved boundary's own change list.  **Every rule that
moves a subterm masks what it introduces, and the table has no
exceptions.**  `Drop$` moves a numeral into a strictly *more* nameable
frame, which is vacuous because a numeral names no type variable and no
other term can take the step (`proof/ShiftAudit` §9).  The full
site-by-site table, the witness of what the leak was, and the candidate
fixes with their hazards — the wrap repair **loops** (`proof/ShiftAudit`
§4/§4a, still recorded as a refutation), the resolve variant trades a
scope leak for a **knowledge** leak — are in `notes/ShiftAudit.md`.

### `type-safety`

`progress ∘ preservation*` (`proof/TypeSafety`): a well-typed closed term
never gets stuck along a run.

### The evaluator (`strong.Eval`)

**The step function is progress.**  There is no second, type-blind
transcription of the rule table (v1 needed one, because progress was
false for v1 as it stood):

    step ⊢M  =  progress ⊢M
      : Value M ⊎ ∃ M′. (Δ ⊢ M -→ M′)

decides "value or redex" and, in the redex case, returns the contractum
*together with its derivation*.  `eval k ⊢M` iterates it with fuel `k`,
retyping each contractum by `preservation` so the next step has a
derivation to run on, and returns a `Trace`: the steps taken, each with
its `_⊢_-→_` derivation, ending in the status of the state they arrive
at (`value v`, or `out-of-fuel`).  So

    trace-sound  : (tr : Trace Δ M) → Δ ⊢ M -→* traceEnd tr
    traceFinal   : (tr : Trace Δ M) → Final (traceEnd tr)
    trace-unique : (tr₁ tr₂ : Trace Δ M) → traceLen tr₁ ≡ traceLen tr₂
                 → traceTerms tr₁ ≡ traceTerms tr₂

are, in order: soundness *by construction* — the steps are literally
stored, so the run is assembled by `done`/`_then_` and nothing is
re-checked; the status is a status of the *last* state; and, by `det`,
two runs of the same length from the same term have the same states.
`eval-⦂` closes the loop: the endpoint still has the type it started
with.

Two uses.  `evalTerms k ⊢M` (the states, as a list) regenerates the
hand-composed `-→*` chains of `Examples.agda`, and seven of them — §6
`P₀`, §11 `Q₀`, §12 `L₀`, §12b `Ri`, §13a `J₀`, §13b `H₀`, §14 `E₀` — are
pinned against it by `refl`.  And `showTrace n tr` renders a whole run
through `Show.agda`, one state per line, each arrow labelled by
`ruleName` — the *redex* rule, found by descending through the
congruences of the stored derivation.  §6's run, rendered:

    ((ΛX. (λx:X. x)) [ℕ] · 7)
      --[TyBeta]-->
    (((λx:X. x) ⟪ ↑X:=ℕ , (seal X ↦ unseal X) ⟫) · 7)
      --[Peel]-->
    (((λx:X. x) · (7 ⟪ ↓X , seal X ⟫)) ⟪ ↑X:=ℕ , unseal X ⟫)
      --[Beta]-->
    ((7 ⟪ ↓X , seal X ⟫) ⟪ ↑X:=ℕ , unseal X ⟫)
      --[CancelR]-->
    ((7 ⟪ ↓X , id ℕ ⟫) ⟪ ↑X:=ℕ , id ℕ ⟫)
      --[Drop$]-->
    (7 ⟪ ↑X:=ℕ , id ℕ ⟫)
      --[Drop$]-->
    7
      -- VALUE


## 8. Design laws

These are the standing constraints the design is held to; each has a
machine-checked consequence in tree.

1. **Grounded invariants.**  No external companion predicate.  Every
   invariant lives *in the relation*, is minted by the rules and
   preserved by reduction.  The scope move is this law winning: instead
   of grounding `interior Θ₂ Δ ⊢ᵗ A` with a side condition, the rule was
   changed so that the fact follows from `env`'s own last premise.
2. **Tightness, for terms and for scope.**  A masked slot may not be
   named in any type; `Nameable` and `wf-var` are the whole enforcement.
   *Mentioning* a masked index in a morphism entry (`↓X`, `↥X`) is not a
   use, and `_⊢ᵐ_` permits it — but it must be TRUE: `↓X` needs `X`
   nameable and `↥X` needs `X` LOCKED, where the entry acts.  The law
   held for typing all along and was **broken for the reduction
   relation** by a `dual` that dropped `unlock` entries; it is repaired
   (§4.2, §6.3) and the witness that broke it is now refused
   (`proof/DualTightness.¬⊢Contractum`).  The frame identity (†) is the
   law in one line: *the crossing frame IS the exterior*.  The law is now
   tested at **every** rule that moves a subterm into a new frame
   (`Examples` §15, and the frame-identity table in §7), with one
   recorded exception that is not a scope gain — `Beta` may *erase* its
   argument.
3. **No term type-shifts, and the shifts that remain are AT BINDERS.**
   Shift types, not terms.  The only index arithmetic in the design is
   ordinary de Bruijn binder offsets: `numBinds Θ`, `shiftBy`, and the
   `n + X` lift in `shiftScope` and `dualScope`.  `cmax`, `dropN`,
   `swapᵇ`, `shiftReps` have no analogue.

   Frame-exact `Beta` (§6.2) does not change this: the shift a substituted
   image undergoes when it crosses a `Λ` is still `⇑ᴹ = renᴹ suc`, one
   binder, applied AT that binder — what the repair adds is a WRAPPER
   beside the shift, not more arithmetic.  The wrapper's morphism
   `morph [] (lock 0 ∷ [])` names slot 0 and carries no representation,
   and its conversion `mkId (⇑ᵗ A)` is derived from the type the redex
   already carries.  The rule of thumb survives: every shift in the
   development sits at a binder, and no shift is ever applied to a
   representation twice.
4. **Simultaneity, as far as it goes — and the pair says which far.**
   `pushBinds` lifts a representation past exactly the binders inside it
   and past nothing else — that half is untouched, and the telescopic
   variant stays reverted (`notes/DECISIONS.md`, "RULING … telescopic
   (mwf-↑) REVERTED").  The other half — *every* premise read on the
   plain exterior — did not survive the tightness repair, and could not:
   with an `sw-u` that refuses a vacuous unlock, `sw-l` and `sw-u` are
   exact complements, so a simultaneous judgement cannot hold of a change
   list that both locks and unlocks one slot, and the scope move builds
   exactly such lists (§4.2).  The PAIR is what makes the surviving
   statement exact: the BINDS are simultaneous — one block, every rep
   read on the same `unlockedScope Θ Δ`, never blocked by the frame's OWN
   locks — while the CHANGES are sequential, each read on
   `applyChanges S′ Δ`, the frame it actually acts on.  The interleaved
   list could only approximate this by reading a rep past its own tail;
   the pair drops the tail dependence outright (§4.2, "the one semantic
   move").
5. **Determinism.**  Reduction is a partial function.  This is what forces
   `Value` premises on `V-Λ`, `TyBeta` and `Beta`, and what forces every
   rule that mints an identity at a looked-up representation to carry the
   lookup as a premise.
6. **Towers, not merges.**  Boundaries pile up; they are never merged.
   The merging rule `IdAbsorb` with its frame operator `⊳` was retired
   for failing the no-composition test — its merge equations could only
   be repaired by substituting representations into representations,
   which is v1's disease one level out.  Instead, an inert `↦` or `∀`
   conversion is **eliminated at its use** (`Peel`, `TyPeelR`), and a
   transparent layer is dissolved by pushing the active conversion inward
   (`IdPush`) until it meets its seal (`CancelR`) or a numeral (`Drop$`).
   The towers stay bounded because every such step moves the active
   conversion strictly inward.


## 9. How we got here

The design log is `notes/DECISIONS.md`, in order; this is only a map.
Do not read the sections below for content — read them there.  The
*graphical* map — fifty design points, with the evidence on every edge —
is `notes/DesignSpace.md`, with `notes/DesignPoints.md` as its glossary.

* **The pre-boundary design refuted.**  One wrapper per variable, with an
  interior that *dropped* the shallower context and a rule that pushed
  the type argument inward.  The counterexample, the diagnosis and the
  same program run in v2 are in §1, "The pre-boundary counterexample";
  the historical record is `notes/old/notes-v1.md`, "Old per-variable
  design" and "Example 8, historical".
* **v1 refuted.**  "THE PRESERVATION VERDICT (2026-09-05) — SUBJECT
  REDUCTION IS FALSE".  Every failure was a failed representation *copy*.
* **The survey.**  "REDESIGN SURVEY ORDERED (Jeremy, 2026-09-05)" and
  `notes/BoundarySurvey.md`: the critical examples re-run with an event
  log and a bookkeeping-independent requirements extractor.
* **The redesign advice.**  "REDESIGN ADVICE (2026-09-05)" and
  `notes/RedesignAdvice.md`: central representation storage (yes),
  simultaneity (keep), Conversion as the conversion half of a split
  boundary (yes), the cancel match becomes definitional (yes).  Then
  "Redesign — Q1 realization RULED": *binder-syntactic*.
* **The probe and the restructure.**  "THE REDESIGN PROBE VERDICT
  (2026-09-05) — GREEN", then the rule repairs:
  "THE ID-LAYER PROBE VERDICT", "Id-layer RULING", "v2 vocabulary +
  repair (5) CONFIRMED", and `notes/RuleRepairs-TyPeelR-CancelR.md`.
* **Polarity dropped.**  "RULING: polarity dropped from the conversion
  judgment (Jeremy, 2026-09-06)" — with the trace artifact *Two
  Polarities, One Rule* built on `Examples` §13.
* **The scope move.**  "PRESERVATION PROVEN, PARAMETER-FREE — Jeremy's
  lock-moving contractum (2026-09-06)", with the artifact *The Wall*;
  the invariant hunt it retired is "Rule repairs LANDED; the invariant
  hunt; …".  The hunt's four record modules were **deleted** on Jeremy's
  ruling (2026-09-06); `notes/DECISIONS.md` is the whole record, and its
  two surviving artifacts are `proof/MaskFacts.mask-only` and `Examples`
  §12/§12b.
* **The tightness episode.**  The last thing that moved the design, and
  the one that reshaped `_⊢ᵐ_`, `dual`, `⊢retag` and the scope move at
  once.  In order:
  * *the leak* — "Peel's dual is NOT tight for `unlock` entries
    (Jeremy's test, 2026-09-06)".  Jeremy asked for a `Peel` step whose
    argument is ill formed before and after; `proof/DualTightness`
    produced one where the contractum **typed**.  Design law 2 was false
    for the reduction relation.
  * *the refuted package* — same section, "PROBED FIX, REFUTED"
    (`proof/MwUObstruct`): masked-only `sw-u` + unconditional
    `unlock ↦ lock` + `bindsOnly` as the outer frame.  Under a
    **simultaneous** `_⊢ᵐ_` it kills `⊢retag` (`le-mu` unmasks a slot an
    `unlock` cites) and `⊢ᵐ-⋉` (the merged list both locks and unlocks
    one slot).
  * *the Δ-dependent dual* — the `(δ)` candidate of the same section and
    of "RULING: vacuous unlocks are wrong and unreachable (Jeremy,
    2026-09-06)": let `dual` read the exterior and re-lock only
    non-vacuous unlocks.  It closes the leak while leaving `_⊢ᵐ_` alone,
    and is **superseded** — branch `dual-relock`.
  * *the principled package* — the second probe of that ruling, and what
    landed: **sequential** `Δ ⊢ᵐ Θ` (no vacuous unlocks, no double
    locks), the restoring and **reversed** `dualScope`, `rewind Θ₂` as
    the scope move's outer frame, `⊢retag` over `⊑ᵃ`.  The two frame
    lemmas become equalities and (†) becomes exact.
  * *the ratification* — "RATIFIED: representations read past the tail's
    unlocks; PR #193 merged (Jeremy, 2026-09-06)".  A representation is
    read past the unlocks, and design **law 4 is reduced to its
    surviving half** (§8): no interference from the frame's own entries;
    the "every premise on the plain exterior" half is retired.
* **The pair** (Jeremy, 2026-09-06; PR #195, `3f080fdb`).  The
  ratification left `_⊢ᵐ_` reading a rep past its own TAIL's unlocks,
  which is a sequential statement about something that is not sequential.
  The morphism became a PAIR — `morph (binds : List Ty)
  (changes : List Change)` — so the type says what is true: the binds are
  a parallel block, the changes a sequential list.  The rep reading loses
  its tail dependence (every rep past the WHOLE change list); no
  derivation in the development needed the tighter reading.  What the
  pair buys, mechanically: `repsOf` and every filtering lemma about it
  vanish (`numBinds (Θ₁ ⋉ Θ₂) ≡ numBinds Θ₁`, `numBinds (rewind Θ) ≡
  numBinds Θ`, `numBinds (dual Θ) ≡ 0` all become `refl`), the bind cases
  disappear from the change inductions and the change cases from the rep
  inductions, and `⊢ᵐ-++` splits into a rep-free `⊢ˢ-++`.

  The tests that came out of it are `proof/DualTightness` (the `unlock`
  half) and `Examples` §15 (every other rule that moves a subterm), with
  the frame-identity table in §7.
* **The shift audit, and the `TyPeelR` split** (Jeremy, 2026-09-08; this
  PR).  "Frame exactness is the main point of Strong System F" — so after
  #199 made `Beta` exact Jeremy asked for an audit of *every* place a
  rule moves a subterm, against the stronger question: does the frame say
  the truth about what the moved subterm may name?  `proof/ShiftAudit`
  answers it site by site (§7's table), and found **one** leak: the
  single `TyPeelR` moved its value into a frame with a new **unmasked**
  bind slot.  The candidates and their fates are in
  `notes/ShiftAudit.md` — wrapping the moved value in the new binder's
  dual **loops** (machine-refuted, `proof/ShiftAudit` §4/§4a, kept as a
  record), and the resolve variant trades a scope leak for a *knowledge*
  leak, which the binder-syntactic design exists to forbid.  What landed
  is the `canon-∀` **split**: `TyPeelR-Λ` instantiates a `Λ` interior on
  the spot (no shift at all; the `Λ`'s slot becomes the boundary's
  binder, `TyBeta`'s own refinement one `∀` inside) and `TyPeelR-⟪⟫`
  pushes inward past a boundary interior, masking the new binder in the
  moved boundary's **own** change list (`addLock0`, `strong.CtxMorph`
  §5).  No premise was added; the pair is total over canonical
  `∀`-values, so it replaces the single rule.  Its descent terminates on
  the `∀`-value's tower height, the measure the wrap repair leaves fixed.
  Side effect: one type instantiation now mints **one** binder where the
  old rule pair minted two, so runs get shorter (`Examples` §13a's `J`
  eleven steps rather than fourteen, §14's `E` five rather than six).


## Appendix A. Names

Jeremy ruled on the helper names on 2026-09-06 and the Agda now spells
them out in full.  Names ruled on earlier and kept as they were:
`Θ` = *context morphism*; the change constructors `lock` / `unlock`;
the type-context entries `abst` / `bind` / `masked`; `dual`; `Inj`.
The morphism's `bind` entry became the `binds` field on 2026-09-06.

| name | reading |
|------|---------|
| `interior Θ Δ` | the interior type context |
| `convCtx Θ Δ` | the conversion context: where the conversion is checked |
| `scope Θ Δ` | `Δ` with `Θ`'s masks and unmasks applied |
| `unlockedScope Θ Δ` | `Δ` with only `Θ`'s unmasks applied |
| `pushBinds As Δ` | push the representations on as binders |
| `binds Θ` | the parallel block of representations (a record field) |
| `changes Θ` | the sequential lock/unlock list (a record field) |
| `numBinds Θ` | how many binders the boundary adds |
| `shiftBy n A` | shift a type past `n` binders |
| `shiftBodyBy n B` | the same, read under one binder |
| `updateAt f X Δ` | one-slot entry update |
| `Binding` | what a slot binds: `abst` or `bind A` — no lock |
| `unmasked b` | the nameable entry at binding `b` |
| `masked b` | the retained, unnameable entry at binding `b` |
| `renᵇ ρ b` | rename inside a binding (the lock carries no spelling) |
| `maskEnt E` | set the lock (total, idempotent) |
| `unmaskEnt E` | clear the lock (total, idempotent) |
| `Nameable E` | the entry is `unmasked` — may be named in a type |
| `b ⊑ᵇ b′` | refinement at the BINDING layer (`le-aa`/`le-ab`/`le-bb`) |
| `Δ ⊢ᵐ Θ` | the morphism is well formed over Δ — a PAIR of halves |
| `Δ ⊢ʳ Bs` | the parallel rep half: every rep well formed on ONE Δ |
| `Δ ⊢ˢ S` | the sequential change half |
| `mkId A` | the identity conversion at any type |
| `reveal X A` | mint: reveal `X` through `A` |
| `conceal X A` | mint: conceal `X` through `A` |
| `instReveal X s` | the same mint, on a conversion |
| `instConceal X s` | its contravariant partner |
| `dual Θ` | the frame a crossing argument acquires |
| `dualScope n S` | the change list `S`, inverted and reversed |
| `hideBinds n` | lock the crossed boundary's own binders |
| `shiftScope n S` | the change list `S`, indices lifted by `n` |
| `applyChanges S Δ` | `Δ` with `S`'s locks and unlocks applied, head-last |
| `applyUnlocks S Δ` | `Δ` with only `S`'s unlocks applied |
| `rewind Θ` | `Θ` with its own changes undone |
| `Θ₁ ⋉ Θ₂` | `Θ₁` with `Θ₂`'s changes moved into its tail |
| `Locked E` | the entry is `masked` — the complement of `Nameable` |
| `Δ ∋lk X` | slot `X` is LOCKED at `Δ` — what an `unlock` cites |
| `Δ ⊑ᵃ Δ′` | refinement WITHOUT `le-mu`: the transport a TERM travels |
| `Inj ρ` | the renaming does not confuse two slots |

The `_⊑ᵉ_` constructors were relettered on the same ruling so that each
name spells the two entries it relates (§3, *Refinement*):
`le-ao` → `le-ab`, `le-oo` → `le-bb`, `le-bb` → `le-mm`,
`le-bu` → `le-mu`; `le-aa` unchanged.  With the two-layer entry
(2026-09-08) the letters split by layer: `le-aa`/`le-ab`/`le-bb` are the
`_⊑ᵇ_` constructors, and `le-uu`/`le-mm`/`le-mu` (and `la-uu`/`la-mm`)
lift them through the lock; `la-aa`/`la-ab`/`la-bb` are gone, subsumed by
`la-uu` over `_⊑ᵇ_`.

Two identities worth stating, because they are what the names are meant
to make obvious:

    interior (rewind Θ) Δ ≡ pushBinds (binds Θ) Δ       given Δ ⊢ᵐ Θ
    interior (dual Θ) (interior Θ Δ)
      ≡ map maskEnt (pushBinds (binds Θ) []) ++ Δ       given Δ ⊢ᵐ Θ

The first is `proof/MoveScope.interior-rewind` — *a rewound frame leaves
its bind prefix and nothing else* — and it is the identity that retired
the wall.  The second is (†), `proof/PeelDual.interior-dual`: *the
crossing frame is the exterior*, which is tightness for `Peel`.  Both
appear in the frame-identity table of `Examples` §15f, alongside
`interior-⋉-rewind` and the two `refl` identities for `TyBeta` and
`TyPeelR`.
