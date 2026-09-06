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
  that binds it (its *owner*).  Every other mention of that variable —
  in a conversion, in another boundary — carries only the **name**, and
  resolves the representation by looking the name up along the enclosing
  type context (`Δ ∋ X := A`).  This is the *owner-syntactic* ruling
  (`notes/DECISIONS.md`, "Redesign — Q1 realization RULED").
* Because lookup is by slot identity, moving a term across a renaming
  moves its names coherently, and knowledge transport is *definitional*:
  `ren-kn r d = ren∋ r d` in `strong.Ctx`.


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

### Context morphisms (`strong.Terms`)

`Θ : CtxMorph` is a list of **morphism entries**, Jeremy's *context
morphism*: it maps the type context outside the boundary to the type
context inside it.  There are three entries, written here in the form
the renderer prints:

| entry     | rendered | what it does                                   |
|-----------|----------|------------------------------------------------|
| `bind A`  | `↑X:=A`  | binds a **fresh** interior slot at rep `A`     |
| `lock X`  | `↓X`     | **masks** exterior slot `X`                    |
| `unlock X`| `↥X`     | **unmasks** exterior slot `X`                  |

Only `bind` carries a type, and that type — the *representation* — is
read in the **plain exterior**, never through `Θ`'s other entries
(§8, simultaneity).  `lock` and `unlock` carry a name and nothing else.
The list is applied **head-last**: in `↥Y , ↓Y` the `↓Y` acts first.

Two derived numbers, both in `strong.Terms`:

    repsOf   : CtxMorph → List Ty     -- the bind entries' reps, in order
    numBinds : CtxMorph → ℕ            -- numBinds Θ = length (repsOf Θ)

`numBinds Θ` is the boundary's **frame extension**: the number of binders
it adds.  It is the only list arithmetic that survives from v1.

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
name, never a spelling, and the representation is recovered by an owner
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
first time a rule mints a mixed one: `TyPeelR`'s frame `bind A ∷ Θ` at
`Θ = lock 0 ∷ []` produces the conversion `seal 0 ↦ seal 1`, whose two
leaves cite *different* owners and demand opposite values of one `p`
(`Examples` §13a, `¬seal↦seal` in the record).  Dropping `p` is what
makes `TyPeelR` preservation a theorem at every `∀`-conversion rather
than only at a reveal one (`proof/Preserve.preserve-TyPeelR`).


## 3. Type contexts and the mask discipline (`strong.Ctx`)

### Entries

    E ::= abst | bind A | masked E

    Δ ::= · | E , Δ            -- Ctxᵗ = List Ent

* `abst` — a `Λ`-bound slot.  No representation, and none can be
  invented.
* `bind A` — the **owner** of an instantiation event; `A` is the
  representation, stored once, as a type over this entry's tail.
* `masked E` — the slot is **masked** here: it may not be *named*, but its
  entry `E` is **retained**, so a later `unlock` has something to point
  back at.

Lookup returns the entry shifted into the ambient context:

    Δ ∋e X , E                   -- slot X has entry E
    Δ ∋tv X    = ∃ E. (Δ ∋e X , E) × Nameable E
    Δ ∋ X := A = Δ ∋e X , bind A

`Nameable` holds of `abst` and of `bind A`, and never of `masked E`.  That
is the whole of the tightness discipline: `` wf-var : Δ ∋tv X → Δ ⊢ᵗ ` X ``, so
a masked slot has no well-formed variable type.  Lookup is a partial
*function* (`∋e-det`, `∋:=-det`), which is what makes every rule that
mints an identity conversion at a looked-up representation deterministic.

Note the distinction the mask discipline forces: `↓X` and `↥X` **name**
a possibly masked index — that is an entry, not a type — whereas
`` Δ ⊢ᵗ ` X `` at a masked slot is refused.  Tightness is about *use in a
type*, not about mentioning the index in a context morphism.

### Refinement

`E ⊑ᵉ E′` says `E′` knows at least what `E` knows:

    abst ⊑ᵉ abst          abst ⊑ᵉ bind A          bind A ⊑ᵉ bind A
    E ⊑ᵉ E′ ⇒ masked E ⊑ᵉ masked E′
    E ⊑ᵉ E′ and Nameable E′ ⇒ masked E ⊑ᵉ E′

with `Δ ⊑ Δ′` pointwise.  There is **no** clause whose source is
`bind A` other than reflexivity: an owner never loses its representation.
That is the deleted v1 demotion, stated as the theorem
`⊑-kn : Δ ⊑ Δ′ → Δ ∋ X := A → Δ′ ∋ X := A`.  Masking only loses
nameability (`mask-⊑`), unmasking only adds it (`unmask-⊑`), and typing
transports along `⊑` with the types unchanged (`⊢retag`, `conv-⊑`).

### The three operations a boundary uses

    mask X Δ    = updateAt masked X Δ         -- masks slot X in place
    unmask X Δ  = updateAt unmaskEnt X Δ       -- peels one masked at slot X
    pushBinds As Δ                    -- pushes the reps As as binders

`updateAt f X` replaces the entry at slot `X` and leaves the rest alone, so
masking is *positional* — which is why the renaming transports carry
`Inj ρ` (`ren-updateAt`), a structural hypothesis about the renaming and about
no representation at all.

`pushBinds` deserves its own line, because it is where **simultaneity** lives:

    pushBinds []       Δ = Δ
    pushBinds (A ∷ As) Δ = bind (shiftBy (length As) A) ∷ pushBinds As Δ

The head of the list is interior slot 0.  A representation is a type over
the *plain exterior*, so it is lifted past exactly the owners bound
**inside** it and past nothing else — sibling entries of the same
boundary never interfere.  As a well-formedness fact:

    wf-shiftBy-pushBinds : Δ ⊢ᵗ A → pushBinds As Δ ⊢ᵗ shiftBy (length As) A

### The two type contexts a boundary induces

This is the heart of the design, so it gets its own definitions.  Write
the *plain exterior* `Δ` for the type context in which the whole term
`M ⟪ Θ , c ⟫` is typed.  Then:

    scope  Θ Δ    -- Δ with Θ's locks AND unlocks applied, in order
    unlockedScope Θ Δ    -- Δ with only Θ's unlocks applied (locks skipped)

    interior Θ Δ = pushBinds (repsOf Θ) (scope Θ Δ)
                                        -- THE INTERIOR context
    exterior Θ Δ = pushBinds (repsOf Θ) (unlockedScope Θ Δ)
                                        -- the CONVERSION context

`interior Θ Δ` is the context the interior `M` is typed in: `Θ`'s masks are
applied, and `Θ`'s owners are pushed on as fresh binders.  `exterior Θ Δ` is
the same thing **with `Θ`'s locks lifted** — it is the context the
conversion `c` is checked in, and it is exactly where a `seal X` can
still resolve `X` at its owner even though the interior may not name it.
The relation between them is a refinement in one direction only:

    interior⊑exterior : interior Θ Δ ⊑ exterior Θ Δ
    Δ⊑unlockedScope    : Δ ⊑ unlockedScope Θ Δ

`exterior` has a second, sharper reading, which is the identity that closes
the whole preservation proof (`proof/MoveScope.interior-dropLocks`):

    interior (dropLocks Θ) Δ ≡ exterior Θ Δ

where `dropLocks Θ` is `Θ` with its locks removed.  So **the conversion
context is the interior of the dropLocks boundary** — not a third kind of
context, just the same construction on a smaller morphism.

### Diagram: one boundary, two contexts

Here is the inner boundary of `Examples` §13a's `J₆`, machine-rendered.
The whole term is

    ((ΛZ. (λx:Z. 3)) [Y] ⟪ ↑Y:=X , ↓X , (seal Y ↦ seal X) ⟫)

sitting over the plain exterior `Δ = X := ℕ`.  The morphism binds a fresh
`Y` at rep `X` and locks `X`.  Its two induced contexts, rendered by
`showTCtxAt` at the same names:

Diagram:

    plain exterior  Δ                          X := ℕ
                    |                            |
       ↑Y:=X , ↓X   |  pushBinds + masks         |  pushBinds, locks SKIPPED
                    v                            v
    interior        interior Θ Δ            Y := X , ⌷[X := ℕ]
                                                 ^
                                                 |  the lock, lifted
    conversion      exterior Θ Δ            Y := X ,   X := ℕ

`⌷[…]` is the renderer's mark for `masked`.  Read the two bottom rows: the
interior may name `Y` but **not** `X` — that is the type abstraction the
lock enforces — while the conversion is checked one row down, where `X`
is live, so `seal X` can cite `X`'s owner.  The conversion typed there is

    Y := X , X := ℕ  ⊢  seal Y ↦ seal X  ∶  (Y ⇒ ℕ)  ⇝  (X ⇒ X)

with `seal Y : X ⇝ Y` (the fresh owner's rep, concealed at its own name)
and `seal X : ℕ ⇝ X` (the crossed boundary's owner).  Each leaf conceals
at *its own* owner: that is the whole content, and it is why no single
polarity index could type the tree.

Indices: everything inside the boundary is `numBinds Θ` slots deeper than
outside, so an exterior type `Bₑ` is read inside as `shiftBy (numBinds Θ) Bₑ`.
`lock X` / `unlock X` name **exterior** slots, and the rules that move a
morphism inward lift those names by the owner count (`scopeOf`, §6.7).

### Vocabulary

This note uses the Agda names throughout; they are the plain-English ones,
and Appendix A lists them all.  The ones used most here:
`interior` = *interior type context*, `exterior` = *the type context the
conversion is checked in*, `scope` = *scope*, `unlockedScope` = *scope with
the locks lifted*, `pushBinds` = *push the owners on as binders*,
`numBinds` = *number of binds*, `shiftBy` = *shift past n binders*.


## 4. Typing (`strong.Terms`, `strong.Conversion`)

### 4.1 Well-formed types

    wf-var : Δ ∋tv X → Δ ⊢ᵗ ` X
    wf-ℕ   : Δ ⊢ᵗ ℕ                 wf-𝔹 : Δ ⊢ᵗ 𝔹
    wf-⇒   : Δ ⊢ᵗ A → Δ ⊢ᵗ B → Δ ⊢ᵗ (A ⇒ B)
    wf-∀   : (abst , Δ) ⊢ᵗ A → Δ ⊢ᵗ (∀X. A)

The only interesting clause is `wf-var`: it asks for **visibility**, so a
masked slot is unnameable, and a `∀` pushes `abst`, never a `bind`.

### 4.2 Well-formed context morphisms — `MorphWf Δ Θ`

Every premise is read on the **plain exterior** `Δ` (simultaneity),
never on the context the earlier entries build:

    mw[] : MorphWf Δ []
    mw-b : Δ ⊢ᵗ A     → MorphWf Δ Θ → MorphWf Δ (bind A ∷ Θ)
    mw-l : Δ ∋tv X    → MorphWf Δ Θ → MorphWf Δ (lock X ∷ Θ)
    mw-u : Δ ∋e X , E → MorphWf Δ Θ → MorphWf Δ (unlock X ∷ Θ)

A `bind` checks its representation in the plain exterior.  A `lock` names
a **visible** slot.  An `unlock` asks only that the slot **exist** — it
cannot ask that the slot be masked and stay masked under refinement (a
cancel may already have unmasked it), and it need not: `unmask` is total
and an unlock at an unmasked slot is a no-op.  An `unlock` claims nothing
and a `lock` claims nothing either; the claim lives in the conversion,
where `seal X` must cite a live owner.

### 4.3 Terms

    ⊢`  : Γ ∋ x ⦂ A → Δ ∣ Γ ⊢ x ⦂ A
    ⊢$  : Δ ∣ Γ ⊢ n ⦂ ℕ
    ⊢ƛ  : Δ ⊢ᵗ A → Δ ∣ A , Γ ⊢ N ⦂ B → Δ ∣ Γ ⊢ λx:A. N ⦂ (A ⇒ B)
    ⊢·  : Δ ∣ Γ ⊢ L ⦂ (A ⇒ B) → Δ ∣ Γ ⊢ M ⦂ A → Δ ∣ Γ ⊢ L · M ⦂ B
    ⊢Λ  : (abst , Δ) ∣ ⤊Γ ⊢ N ⦂ C → Δ ∣ Γ ⊢ ΛX. N ⦂ ∀X. C
    ⊢·[]: Δ ∣ Γ ⊢ L ⦂ ∀X. B → Δ ⊢ᵗ A → Δ ∣ Γ ⊢ L [B, A] ⦂ B[X:=A]

and the boundary rule, in full:

    env : MorphWf Δ Θ
        → interior Θ Δ ∣ [] ⊢ M ⦂ Bᵢ
        → exterior Θ Δ ⊢ c ∶ Bᵢ ⇝ shiftBy (numBinds Θ) Bₑ
        → Δ ⊢ᵗ Bₑ
          ------------------------------------
        → Δ ∣ Γ ⊢ M ⟪ Θ , c ⟫ ⦂ Bₑ

Premise by premise:

1. **`MorphWf Δ Θ`** — the morphism is well formed in the plain exterior
   (§4.2).  This is the only place the morphism's own entries are
   checked, and they are all checked *simultaneously*, against `Δ`.
2. **`interior Θ Δ ∣ [] ⊢ M ⦂ Bᵢ`** — the interior is typed in the interior
   type context, at the **empty term context**: a boundary is
   term-closed.  `Bᵢ` is the **interior type**, a type of the interior
   context, and it is where the masks bite: if `Θ` locks `X`, then `Bᵢ`
   cannot name `X`.
3. **`exterior Θ Δ ⊢ c ∶ Bᵢ ⇝ shiftBy (numBinds Θ) Bₑ`** — the conversion is
   checked in the **conversion context**, and it converts the interior
   type `Bᵢ` to the exterior type `Bₑ` *read inside*, i.e. shifted past
   the boundary's own `numBinds Θ` binders.  Both endpoints of `c` therefore
   live at the interior's depth; the conversion context is the interior
   context with `Θ`'s locks lifted, so a `seal X` at a locked `X` is
   typeable here and only here.
4. **`Δ ⊢ᵗ Bₑ`** — the **exterior type** is a type of the plain
   exterior.  This is the premise that the whole preservation endgame
   turned on (§7): a rule whose contractum makes a boundary present a
   representation must present it where this premise can be discharged.

So: `c` converts the **interior type** (the type of `M`, in the interior
type context) to the **exterior type** (in the plain exterior, shifted
into the interior's frame), and it is typed in neither of those two
contexts but in the third, `exterior Θ Δ` — the interior with `Θ`'s locks
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

`conv-seal` is **the soundness gate**: a conceal must cite a *live owner*
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

    conv-faces-unique :
      if Δ ⊢ c ∶ A ⇝ B and Δ ⊢ c ∶ A′ ⇝ B′ then A ≡ A′ and B ≡ B′

i.e. a conversion **determines both of its types**, given the context:
`id` carries its own, a `seal`/`unseal` reads its representation by the
owner lookup (`∋:=-det`), and `↦` / `∀` are structural.


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
question the value can answer now (reveal an owner's representation, or
drop a base identity over a numeral).


## 6. Reduction (`strong.Reduction`)

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
    dualScope n []           = []
    dualScope n (bind A , Θ) = dualScope n Θ
    dualScope n (unlock X , Θ) = dualScope n Θ
    dualScope n (lock X , Θ) = unlock (n + X) , dualScope n Θ

    dual Θ = hideBinds (numBinds Θ) ++ dualScope (numBinds Θ) Θ

so the dual **locks** each of the crossed boundary's own new binders (the
crossing argument may not see them) and **unlocks** each of its locks
(the argument came from outside, where those were nameable).  The
`unlock` case of `dualScope` is deliberately dropped: mapping
`unlock X ↦ lock (n+X)` would re-block a no-op unlock and would make a
same-slot mask/unmask pair fail to cancel.  With it dropped,
`interior-dual` and `exterior-dual` hold in general (`proof/PeelDual.agda`).

**The scope move** (§6.7):

    scopeOf n []           = []           -- Θ's SCOPE, indices lifted by n
    scopeOf n (bind A , Θ) = scopeOf n Θ
    scopeOf n (unlock X , Θ) = unlock (n+X) , scopeOf n Θ
    scopeOf n (lock X , Θ)   = lock   (n+X) , scopeOf n Θ

    dropLocks []           = []          -- Θ with its LOCKS removed
    dropLocks (bind A , Θ) = bind A , dropLocks Θ
    dropLocks (unlock X , Θ) = unlock X , dropLocks Θ
    dropLocks (lock X , Θ)   = dropLocks Θ

    Θ₁ ⋉ Θ₂ = Θ₁ ++ scopeOf (numBinds Θ₂) Θ₂

Note `numBinds (Θ₁ ⋉ Θ₂) ≡ numBinds Θ₁`: the move carries no binder.


### 6.1 `TyBeta` — the boundary is born

    TyBeta : Value N
      → Δ ⊢ (Λ N) ·[ B , A ] -→ N ⟪ bind A ∷ [] , reveal 0 B ⟫

Named:  `(ΛX. N) [B, A]  →  N ⟪ ↑X:=A , reveal X B ⟫`, `N` a value.

**Bookkeeping.** This is the only rule that mints a representation.  It
does *not* substitute: `N` keeps running at the abstract `X`, the new
`bind` becomes `X`'s owner, and the conversion is derived from the body
type `B` by `reveal` — reveal `X` on the way out, conceal it on the way
in.  The `Value N` premise is a determinism repair: this calculus reduces
under `Λ`, so `(Λ N) ·[ B , A ]` with `N` a redex would otherwise have
two distinct steps, this one and `ξ-·[] ⨟ ξ-Λ`.

Example (`Examples` §6, `P₀ → P₁`, under `ξ-·-l`):

    ((ΛX. (λx:X. x)) [ℕ] · 7)
      →  (((λx:X. x) ⟪ ↑X:=ℕ , (seal X ↦ unseal X) ⟫) · 7)

with `reveal 0 (X ⇒ X) ≡ seal 0 ↦ unseal 0`.

### 6.2 `Beta`

    Beta : Value W → Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ]ᵐ

Named: `(λx:A. N) · W → N[x:=W]`.  The ordinary β step; its preservation
case *is* the substitution lemma (`strong.TermSubst.⊢subst`).  Term
substitution is the identity on boundaries, since a boundary body is
term-closed.

**Bookkeeping.** None at the boundary level, but `substᵐ`'s `Λ` clause
shifts the substituted value past the new type binder, and that moves the
*names* in its boundaries: in `Examples` §11 the sealed argument
`(7 ⟪ ↓X , seal X ⟫)` becomes, one binder in, `(7 ⟪ ↓Y , seal Y ⟫)` —
the lock name and the conversion name move together, and nothing else
changes.

Example (`Examples` §6, `P₂ → P₃`, under `ξ-⟪⟫`):

    (((λx:X. x) · (7 ⟪ ↓X , seal X ⟫)) ⟪ ↑X:=ℕ , unseal X ⟫)
      →  ((7 ⟪ ↓X , seal X ⟫) ⟪ ↑X:=ℕ , unseal X ⟫)

### 6.3 `Peel` — the crossing

    Peel : Value V → Value W
      → Δ ⊢ (V ⟪ Θ , s ↦ t ⟫) · W
          -→ (V · (wkᴹ (numBinds Θ) W ⟪ dual Θ , s ⟫)) ⟪ Θ , t ⟫

Named: `(V ⟪ Θ , s ↦ t ⟫) · W → (V · (W ⟪ dual Θ , s ⟫)) ⟪ Θ , t ⟫`.

**Bookkeeping.** The application is pushed one layer in.  The function
conversion splits: `t` stays on the boundary, and `s` — the domain
component, which `conv-fun` already read contravariantly — becomes the
crossing argument's own conversion, transplanted **verbatim**.  That is
sound because `exterior (dual Θ) (interior Θ Δ) ≡ exterior Θ Δ`: the dual's
conversion context *is* the crossed boundary's.  The argument's frame is
the dual: a `↓` for each of `Θ`'s binds (the argument may not name the
new owners) and a `↥` for each of `Θ`'s locks (the argument came from
outside, where they were nameable).  `wkᴹ (numBinds Θ)` re-indexes the
argument one owner-frame deeper.

Example (`Examples` §6, `P₁ → P₂`), with
`dual (bind ℕ ∷ []) ≡ lock 0 ∷ []`:

    (((λx:X. x) ⟪ ↑X:=ℕ , (seal X ↦ unseal X) ⟫) · 7)
      →  (((λx:X. x) · (7 ⟪ ↓X , seal X ⟫)) ⟪ ↑X:=ℕ , unseal X ⟫)

The `7` has crossed inward and is now sealed at the new owner, so the
interior sees it at the abstract name `X` — which is exactly what
`λx:X. x` demands.

### 6.4 `TyPeelR` — a `∀` conversion meets a type application

    TyPeelR : Value V
      → (abst ∷ exterior Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ
      → Δ ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ]
          -→ (wkᴹ 1 V ·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ])
               ⟪ bind A ∷ Θ , instReveal 0 s ⟫

Named: `(V ⟪ Θ , ∀X. s ⟫) [B, A] → (V [Bᵢ, X]) ⟪ ↑X:=A , Θ , instReveal X s ⟫`
where `Bᵢ` is the interior `∀`-body determined by the premise.

**Bookkeeping**, three moves:

1. **A new owner is prepended.**  The frame becomes `bind A ∷ Θ` — plain
   `Θ`, not shifted, because `interior` already lifts `Θ`'s representations
   past the prepended owner:
   `interior (bind A ∷ Θ) Δ ≡ bind (shiftBy (numBinds Θ) A) ∷ interior Θ Δ`.
2. **The interior is instantiated at the new owner's name**, `` ` 0 ``,
   not at `A`.  The pushed-in body annotation must be the **interior**
   `∀`-body `Bᵢ`, which is what the interior's own `⊢·[]` demands and
   which differs from the exterior body at every non-identity leaf.  `Bᵢ`
   is not syntactically recoverable from a representation-free conversion
   (a `seal`'s source is an owner's representation), so the rule carries
   the conversion typing as a **premise**.  `Progress` supplies it for
   free by inverting the redex's own `env` (`conv-all-inv`), and
   determinism is `conv-faces-unique`.
3. **The conversion is re-minted at the new slot.**  Slot 0 of `s`'s body
   was `abst` and is now the owner this rule binds, so every leaf that
   reads it must become the instantiation step: `unseal 0` where the
   conversion runs covariantly, `seal 0` where it runs contravariantly —
   that is `instReveal 0 s`.  Keeping `s` is ill-typed: its exterior body
   still mentions `` ` 0 `` where `env` demands the instantiated
   `shiftBy (numBinds Θ + 1) (Bₑ [ A ])` (`Examples` §13a, `¬⊢J-plain`).

Example, the **reveal** side (`Examples` §13b, `H₃ → H₄`):

    ((ΛY. (λx:Y. (7 ⟪ ↓X , seal X ⟫)))
       ⟪ ↑X:=ℕ , (∀Y. (id Y ↦ unseal X)) ⟫) [ℕ]
      →  ((ΛZ. (λx:Z. (7 ⟪ ↓X , seal X ⟫))) [Y]
            ⟪ ↑Y:=ℕ , ↑X:=ℕ , (seal Y ↦ unseal X) ⟫)

with `` instReveal 0 (id (` 0) ↦ unseal 1) ≡ seal 0 ↦ unseal 1 ``: the
inserted `seal Y` conceals the owner this rule bound, under an
`unseal X` that reveals the crossed boundary's.  The **conceal** side is
`Examples` §13a, `J₅ → J₆`:

    ((((ΛY. (λx:Y. 3)) ⟪ ↓X , (∀Y. (id Y ↦ seal X)) ⟫) [X]
        · (7 ⟪ ↓X , seal X ⟫)) ⟪ ↑X:=ℕ , unseal X ⟫)
      →  ((((ΛZ. (λx:Z. 3)) [Y] ⟪ ↑Y:=X , ↓X , (seal Y ↦ seal X) ⟫)
            · (7 ⟪ ↓X , seal X ⟫)) ⟪ ↑X:=ℕ , unseal X ⟫)

Here `instReveal 0 s ≡ seal 0 ↦ seal 1` — the two-conceal tree of §3's
diagram, the one no single polarity could type.  Both examples reach
their redex from closed, plain System F source, and both contracta type
by `preservation-TyPeelR`.

### 6.5 `Drop$`

    Drop$ : Base A → Δ ⊢ ($ n) ⟪ Θ , id A ⟫ -→ $ n

Named: `n ⟪ Θ , id A ⟫ → n` for base `A`.  A numeral is typeable
anywhere (`⊢$`), so a transparent base layer over one carries no
information and is discarded, frame and all.

Example (`Examples` §6, `P₅ → 7`):  `(7 ⟪ ↑X:=ℕ , id ℕ ⟫)  →  7`.

### 6.6 `CancelR` — a conceal directly under its reveal

    CancelR : Value V → exterior Θ₂ Δ ∋ Y := A
      → Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
          -→ (V ⟪ Θ₁ ⋉ Θ₂ , mkId (shiftBy (numBinds Θ₁) A) ⟫)
               ⟪ dropLocks Θ₂ , mkId A ⟫

**Bookkeeping.**  The two conversions cite the *same entry*, so the match
is definitional — there is no second spelling to disagree with the first,
which is the `∋:=-det` fact the whole ownership design was chosen for.
Both **frames are kept** and both conversions are **neutralised** to
identities at the looked-up representation; composition happens only on
the conversions, where `unseal ∘ seal = id` is algebra we already trust,
so no context-morphism arithmetic returns.  The two names need no
relating premise: typing already forces `X ≡ numBinds Θ₁ + Y`
(`proof/IdLayer.cancel-name`).  The lookup premise is there because the
rule mints identity conversions *at a looked-up representation*, and
determinism for such rules is exactly `∋:=-det`.  The frames move as in
§6.7.

Example (`Examples` §6, `P₃ → P₄`; here `Θ₂ = ↑X:=ℕ` locks nothing, so
`Θ₁ ⋉ Θ₂ ≡ Θ₁` and `dropLocks Θ₂ ≡ Θ₂`):

    ((7 ⟪ ↓X , seal X ⟫) ⟪ ↑X:=ℕ , unseal X ⟫)
      →  ((7 ⟪ ↓X , id ℕ ⟫) ⟪ ↑X:=ℕ , id ℕ ⟫)

Two `Drop$` steps then finish the run to `7`.

### 6.7 `IdPush`, and the scope move

    IdPush : Value V → exterior Θ₂ Δ ∋ Y := A
      → Δ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫
          -→ (V ⟪ Θ₁ ⋉ Θ₂ , unseal X ⟫) ⟪ dropLocks Θ₂ , mkId A ⟫

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
**representation** `A`.  A representation is a type over the plain
exterior, so `env`'s last premise now asks for `A` to be well formed
*inside* the outer frame — and `Θ₂`'s own locks may have masked the very
slot `A` names.  That was **the wall**, and the whole invariant hunt
(`proof/WallReach`, `proof/WallGrounding`, `proof/ChainScoped`,
`proof/IdPushReach`) was a search for a side condition to ground it.

The repair is not a side condition but a **frame move** (Jeremy,
2026-09-06).  The outer frame keeps only what binds and what unmasks
(`dropLocks Θ₂`); its whole **scope** — locks *and* unlocks, in order,
lifted past its own owners — travels into the inner frame's tail
(`Θ₁ ⋉ Θ₂`), where `scope` applies it **first**, exactly where it applied
before.  The representation is then presented outside the locks, where it
is nameable, and the locks still stand between the value and the world.

Example — the wall witness itself (`Examples` §12b, over
`Δi = X := Y , Y := ℕ`, so `X`'s representation *names* `Y` and the outer
boundary *locks* `Y`):

Diagram:

    R₀   ((((7 ⟪ seal Y ⟫) ⟪ ↥Y , seal X ⟫) ⟪ id X ⟫) ⟪ ↓Y , unseal X ⟫)
      |
      |  IdPush   (Θ₁ = [] , Θ₂ = ↓Y ;  Θ₁ ⋉ Θ₂ = ↓Y , dropLocks Θ₂ = [])
      v
    R₁′  ((((7 ⟪ seal Y ⟫) ⟪ ↥Y , seal X ⟫) ⟪ ↓Y , unseal X ⟫) ⟪ id Y ⟫)
      |
      |  CancelR  lifted through the outer boundary (ξ-⟪⟫)
      v
    R₂   ((((7 ⟪ seal Y ⟫) ⟪ ↥Y , ↓Y , id Y ⟫) ⟪ id Y ⟫) ⟪ id Y ⟫)

Read `R₀` and `R₁′` side by side: `↓Y` has moved from the outer boundary
to the inner one, and the reveal `unseal X` went with it.  The
representation `Y` that the reveal hands back is now presented on the
outer boundary's own type context, where `Y` is live, instead of inside
the lock, which is what `env`'s last premise refused.  The value's frame
is unchanged (`interior ([] ⋉ Θi) (interior (dropLocks Θi) Δi)
≡ interior [] (interior Θi Δi)` is `refl`), so `V` retypes where it was,
and `R₂` is a **value**.  Under
the old rule `R₀`'s contractum was untypeable — that refutation was the
content of `proof/PreserveObstruct` §4, which now records the positive
fact on the same witness.

**Why the unlocks travel too, and are also retained.**  `scope` applies its
list head-last, so moving only the *locks* past a same-slot `unlock`
reorders a mask/unmask pair, and the value's frame is then not refined
but **corrupted** — a slot it may name in the redex is masked in the
contractum.  The refutation is in tree
(`proof/MoveScope` §4b, `¬frame-locksOnly`) at the `MorphWf`-legal witness
`Θ✗ = unlock 0 ∷ lock 0 ∷ []` over `Δ✗ = bind ℕ ∷ []`, where
`interior Θ✗ Δ✗ ≡ bind ℕ ∷ []` but the lock-only contractum's interior is
`masked (bind ℕ) ∷ []`.  Moving the whole scope keeps the order, and the
retained unmasks are harmless: unmasking only *adds* nameability, so the
value's frame is **refined** and `⊢retag` carries it.  With that, the
frame lemma is unconditional — no premise about `Θ₂`'s shape, and no side
condition for `Progress` to supply.

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
    ξ-Λ   : (abst ∷ Δ) ⊢ N -→ N′   → Δ ⊢ Λ N -→ Λ N′
    ξ-⟪⟫  : interior Θ Δ ⊢ M -→ M′     → Δ ⊢ M ⟪ Θ , c ⟫ -→ M′ ⟪ Θ , c ⟫

Left-to-right, call-by-value, and **under `Λ`** — which is why `V-Λ` and
`TyBeta` both carry `Value N`.  Note the two index changes: `ξ-Λ` steps
in `abst ∷ Δ`, and `ξ-⟪⟫` steps in the *interior* type context
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
  rules ask for `exterior Θ Δ ∋ Y := A`, which **is** `conv-unseal`'s own
  premise `d`: the lookup is free, never re-derived.

The historically hard case — a value at an abstract type — costs one
two-way split, because the only conversions with a variable exterior are
exactly the two that the id-layer rules consume.

### `preservation`

Induction on the step, with the rule cases distributed:

* **`TyBeta`** (`proof/Preserve.preserve-TyBeta`) — the mint.  The new
  owner is the `abst ⊑ᵉ bind A` refinement of the `Λ`'s own slot
  (`le-ao`), so the interior retypes by `⊢retag`; the minted conversion
  types by `⊢reveal`/`⊢conceal`, and its exterior type is the
  instantiated body by `subst-at-0`.  The exterior premise is `⊢·[]`'s
  own two premises through `wf-[]ᵗ`, and `interior (bind A ∷ []) Δ` is
  definitional.
* **`Beta`** — `⊢subst` (`strong.TermSubst`).
* **`Peel`** (`proof/PeelDual.preserve-Peel`) — the two context
  identities are what carries it:
  `interior (dual Θ) (interior Θ Δ)
  ≡ map masked (pushBinds (repsOf Θ) []) ++ unlockedScope Θ Δ`
  and `exterior (dual Θ) (interior Θ Δ) ≡ exterior Θ Δ`.  The crossing
  argument, typed in `Δ`, retypes one owner-frame deeper by
  `⊢rename (wkN (numBinds Θ))` and then `⊢retag` (the tail relaxes along
  `Δ ⊑ unlockedScope Θ Δ`), and the conversion `s` transplants verbatim
  through the second identity.
* **`TyPeelR`** (`proof/Preserve.preserve-TyPeelR`) — at **every**
  `∀`-conversion, once polarity is gone.  The interior instantiation
  lands at the fresh owner's name, `ren-suc-[0]` undoes the annotation
  shift, and the minted `instReveal 0 s` types leaf by leaf, each leaf
  citing its own owner.
* **`Drop$`** — one inversion: `conv-id-refl` plus `shiftBy-ℕ⁻` force the
  exterior type to be the base type.
* **`CancelR`, `IdPush`** (`proof/MoveScope`) — the scope move, §6.7.
  Four moves each, one per premise of the contractum's inner `env`:
  the frame is `Θ₁ ⋉ Θ₂`, well formed by `MorphWf-⋉`; the interior is `V`,
  retagged along `frame-move`; the conversion cites the owner that
  `move-∋` transports; and the exterior premise is `moved-scoped`, the
  one the wall used to deny — which is now just `wf-shiftBy-pushBinds` on
  the redex's own exterior type, because
  `interior (dropLocks Θ₂) Δ ≡ exterior Θ₂ Δ`
  and `A ≡ shiftBy (numBinds Θ₂) C` for the redex's `C`.
  The two frame lemmas are **refinements**, not equalities —
  `interior Θ₁ (interior Θ₂ Δ)
  ⊑ interior (Θ₁ ⋉ Θ₂) (interior (dropLocks Θ₂) Δ)` and the
  same for `exterior` — because the retained unmasks apply twice; `⊢retag`
  and `conv-⊑` carry that.
* the five `ξ` rules — structural, using the same `env` node.

The three transports the induction rests on are `⊢rename` (along a
context renaming, with `Inj ρ`), `⊢retag` (along `⊑`, types unchanged),
and `⊢subst`.

### `det` and `value-¬step`

`value-¬step` holds on the nose once `V-Λ` carries `Value N`.  `det` is a
case analysis on the two steps; the interesting entries are the rules
whose contracta are not syntactically determined by the redex:

* `TyPeelR`'s pushed-in annotation is premise-determined, and the two
  premises give the same annotation by `conv-faces-unique` (§4.4);
* `CancelR` and `IdPush` mint identity conversions at a looked-up
  representation, and the two lookups agree by `∋:=-det`.

Everything else is either `refl` or an appeal to `value-¬step` at an
overlapping `ξ`.

### `type-safety`

`progress ∘ preservation*` (`proof/TypeSafety`): a well-typed closed term
never gets stuck along a run.


## 8. Design laws

These are the standing constraints the design is held to; each has a
machine-checked consequence in tree.

1. **Grounded invariants.**  No external companion predicate.  Every
   invariant lives *in the relation*, is minted by the rules and
   preserved by reduction.  The scope move is this law winning: instead
   of grounding `interior Θ₂ Δ ⊢ᵗ A` with a side condition, the rule was
   changed so that the fact follows from `env`'s own last premise.
2. **Tightness, for terms and for scope.**  A masked slot may not be
   named in any type; `Nameable` and `wf-var` are the whole enforcement.  But
   *mentioning* a masked index in a morphism entry (`↓X`, `↥X`) is not a
   use, and `MorphWf` permits it.
3. **No term type-shifts.**  Shift types, not terms.  The only index
   arithmetic in the design is ordinary de Bruijn binder offsets:
   `numBinds Θ`, `shiftBy`, and the `n + X` lift in `scopeOf` and `dualScope`.
   `cmax`, `dropN`, `swapᵇ`, `shiftReps` have no analogue.
4. **Simultaneity.**  A boundary's entries never interfere: every `MorphWf`
   premise, and every representation, is read in the **plain exterior**,
   and `pushBinds` lifts a representation past exactly the owners bound inside
   it.  The telescopic variant was landed and reverted
   (`notes/DECISIONS.md`, "RULING … telescopic (mwf-↑) REVERTED").
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
Do not read the sections below for content — read them there.

* **v1 refuted.**  "THE PRESERVATION VERDICT (2026-09-05) — SUBJECT
  REDUCTION IS FALSE".  Every failure was a failed representation *copy*.
* **The survey.**  "REDESIGN SURVEY ORDERED (Jeremy, 2026-09-05)" and
  `notes/BoundarySurvey.md`: the critical examples re-run with an event
  log and a bookkeeping-independent requirements extractor.
* **The redesign advice.**  "REDESIGN ADVICE (2026-09-05)" and
  `notes/RedesignAdvice.md`: central representation storage (yes),
  simultaneity (keep), Conversion as the conversion half of a split
  boundary (yes), the cancel match becomes definitional (yes).  Then
  "Redesign — Q1 realization RULED": *owner-syntactic*.
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
  hunt; …".


## Appendix A. Names

Jeremy ruled on the helper names on 2026-09-06 and the Agda now spells
them out in full.  Names ruled on earlier and kept as they were:
`Θ` = *context morphism*; the morphism entries `bind` / `lock` / `unlock`;
the type-context entries `abst` / `bind` / `masked`; `dual`; `Inj`.

| name | reading |
|------|---------|
| `interior Θ Δ` | the interior type context |
| `exterior Θ Δ` | the type context the conversion is checked in |
| `scope Θ Δ` | `Δ` with `Θ`'s masks and unmasks applied |
| `unlockedScope Θ Δ` | `Δ` with only `Θ`'s unmasks applied |
| `pushBinds As Δ` | push the representations on as binders |
| `repsOf Θ` | the `bind` entries' representations |
| `numBinds Θ` | how many binders the boundary adds |
| `shiftBy n A` | shift a type past `n` binders |
| `shiftBodyBy n B` | the same, read under one binder |
| `updateAt f X Δ` | one-slot entry update |
| `masked E` | the retained, unnameable entry |
| `unmaskEnt E` | peel one mask |
| `Nameable E` | the entry may be named in a type |
| `MorphWf Δ Θ` | the morphism is well formed |
| `mkId A` | the identity conversion at any type |
| `reveal X A` | mint: reveal `X` through `A` |
| `conceal X A` | mint: conceal `X` through `A` |
| `instReveal X s` | the same mint, on a conversion |
| `instConceal X s` | its contravariant partner |
| `dual Θ` | the frame a crossing argument acquires |
| `dualScope n Θ` | its scope half |
| `hideBinds n` | lock the crossed boundary's own owners |
| `scopeOf n Θ` | `Θ`'s scope, indices lifted by `n` |
| `dropLocks Θ` | `Θ` with its locks removed |
| `Θ₁ ⋉ Θ₂` | `Θ₁` with `Θ₂`'s scope moved into its tail |
| `Inj ρ` | the renaming does not confuse two slots |

Two identities worth stating, because they are what the names are meant to
make obvious:

    scope (dropLocks Θ) Δ ≡ unlockedScope Θ Δ
    interior (dropLocks Θ) Δ ≡ exterior Θ Δ

The second is `proof/MoveScope.interior-dropLocks` — *the exterior is the
interior of the dropLocks boundary* — and it is the identity that retired
the wall.
