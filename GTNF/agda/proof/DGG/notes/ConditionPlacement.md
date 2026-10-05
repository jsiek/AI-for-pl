# Where the relation reads what it knows

Status: design note, 2026-10-05 (supervisor; requested by Jeremy).
No Agda.  It inventories the information `⊑` has about the two
kinds of variables, says where the relation reads each piece, and
traces each `SimBackBlame` counterexample, from its source programs,
to the place it gets through.  It ends with candidate placements and
open questions, not decisions.  LEFT is the more precise side.  All
terms are `scripts/render_gtnf.sh` renders taken from the cited notes.

## 1. Inventory

| information | how the two sides relate today | where it is read |
|---|---|---|
| type variables (names X) | lexical: the center `μʷ` (each name with a mark `X⊑X` or `X⊑★`), the embeddings `ηᴸʷ`, `ηᴿʷ` (joined, or one-sided), the pending names `πʷ` (D27) | type indices `_⊑ᵂ⟨_⟩_`; `Interior`; the ★ clauses of `ConvImp` |
| rep. vars (α) | global: `ϱᵍʷ` (matched TyBetas), `ϱˡʷ` (Λ, ν, boundary binders), any agreeing relation (D16, D25); payloads by `RepImp` (D23), `α ⊑ ★` unconditional | `Interior` (a `+X^α` rejoins the name that ϱ pairs with α); `WfWorld` (`Agree`) |
| the link name ↔ rep. var | a boundary entry: `+X^α` binds name X to α, `−X^α` unbinds it | `Interior` only |
| how a boundary exits a name | its conversion: `+X` unseals, `−X` seals, `id(★)` leaves the value as it is | `ConvImp`, only at **matched** boundaries (`ν⊑ν`, `⟪⟫⊑⟪⟫`, D17); the one-sided rules `⟪⟫⊑`, `⊑⟪⟫` (including D27's push) compare none (D18) |
| how a cast uses a name | its coercion (`X!`, `X?`) and its mode (`★∼X` from `gen`, `★∼X∼★` from compilation, …) | the coercion only through its type index (`CastTy`); the mode nowhere |

The marks are the only knob that decides whether a left name may face
`★`.  They are chosen at the binder (D11), kept across a right
unbind/rebind (D15), and fixed at `X⊑★` for a pending name (D27,
`PendingOK`).  Every repair tried so far adjusted the marks: sidedness
(SidedMarks), modes (ModeCondition), hidden names (HiddenNames).

## 2. What a mark licenses at run time

`X⊑★` at a name that both sides have lets a right value tagged with
the right's X face a left value of type X that carries no tag:

```
⊑cast   x ⊑ x⟨X!⟩     at  X ⊑ ★
```

The tag `X!` names X, which the right's boundary `+X^α` binds to its
rep. var αᴿ.  Whether relating it is safe depends on what happens when
the value leaves the right's boundary: if the right **unseals or
checks** X on the way out, the tag never escapes; if it exits X with
`id(★)`, the X-tagged value escapes and a later `G?` blames.  That is
a fact about the right's conversion for αᴿ.  The mark is a fact about
the name.  The relation never connects the two.

## 3. The counterexamples, from their source programs

None of them is a DGG counterexample: every initial pair is unrelated.
Each refutes `SimBackBlame` (M22), which must hold for every related
pair, because the relation **gains** a pair during the run that no
related predecessor justifies.

### C1 and C4 (one source pair)

```
L   ((ΛX. λx:X. x) : ★→★) 5 : ℕ
R   ((ΛX. λx:X. (x : ★)) : ★→★) 5 : ℕ
```

Unrelated at the source: the two Λs need `∀X.X→X ⊑ ∀X.X→★`, which is
empty (`ModeCondition.esc-source-unrelated`).  Compiled:

```
L₀  ((ΛX. λx:X. x)⟨inst Y.(Y?ℓ0 → Y!)⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
R₀  ((ΛX. λx:X. x⟨X!⟩^[X:★∼X∼★])⟨inst Y.(Y?ℓ0 → id(★))⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
```

Unrelated as cast terms (`PendingOpenings.Probes.initial-unrelated`).
Both sides run `Inst`, `TyBeta` (α:=★).  The exits differ:

```
L  ([+X^α] (λx:X. x) ⟨−X → +X⟩) …                 -- exit +X
R  ([+X^α] (λx:X. x⟨X!⟩) ⟨−X → id(★)⟩) …          -- exit id(★)
```

L reaches `5`; R reaches
`([+X^α] ([−X^α] 5⟨ℕ!⟩ ⟨−X⟩)⟨X!⟩ ⟨id(★)⟩)⟨ℕ?ℓ0⟩` and blames
(`TagUntagBad-⟪⟫`).

**C4** relates L₀ (left not yet run) to R₂ (right after `Inst`,
`TyBeta`):

```
⊑⟪⟫   push X                      -- one-sided: no conversion compared
  Λ⊑  pop X at X⊑★                -- PendingOK fixes the mark
    ƛ⊑ƛ, ⊑cast  x ⊑ x⟨X!⟩ at X ⊑ ★
```

**C1** relates the two states after both sides' `Inst`, `TyBeta`, by
three routes (HiddenNames §2):

```
matched      ⟪⟫⊑⟪⟫ with  +X ⊑ id(★)   (conv-unseal⊑id★, joined X at X⊑★, D11)
left-first   ⟪⟫⊑ (left +X, X left-only), then ⊑⟪⟫ (right +X rejoins, keeps X⊑★, D15)
right-first  ⊑⟪⟫ (right +X, X right-only at a chosen X⊑★), then ⟪⟫⊑ (left +X rejoins, keeps it)
```

### C2 and C3 (one source pair)

```
L   (((ΛY. λx:Y. x) [ℕ]) 5 : ★) : ℕ
R   ((((λx:★. x) : ∀Y. Y→★) [ℕ]) 5) : ℕ
```

Unrelated at the source, by the same empty index `∀Y.Y→Y ⊑ ∀Y.Y→★`.
Compiled (ModeCondition `Esc`):

```
LE  ((ν X:=ℕ. ((ΛY. λx:Y. x) X) ⟨−X → +X⟩) 5)⟨ℕ!⟩⟨ℕ?ℓ0⟩
RE  ((ν X:=ℕ. ((λx:★. x)⟨gen Y. (Y! → id(★))⟩ X) ⟨−X → id(★)⟩) 5)⟨ℕ?ℓ0⟩
```

Again the exits differ (`−X → +X` against `−X → id(★)`).  LE reaches
`5`; RE's gen tag `X!^[X:X∼★]` escapes through `id(★)` and blames.

- **C3** (both after `TyBeta`): matched `⟪⟫⊑⟪⟫` with `+X ⊑ id(★)` on
  the joined X at X⊑★.
- **C2** (left state 3, right state 5): the left's one-sided `+X` makes
  X left-only, the right's `+X` rejoins and keeps X⊑★ (D15), and the
  premise underneath is P4 B4's own pair `S⊑J`.

### C4g

Source: L as in C4; `R = (((λx:★. x) : ∀X. X→★) : ★→★) 5 : ℕ`.
Unrelated by the same empty index.  Like C4 (push, pop at X⊑★), with a
`gen`-mode tag, so the mode condition does not reject it.

### The pair that must stay related: P4

```
L   (λx:∀X.X→X. x [ℕ] 5) (ΛY. λx:Y. x)
R   (λx:∀X.X→X. x [ℕ] 5) (λx:★. x)
```

Related at the source and as cast terms (the argument by `Λ⊑`,
`∀Y.Y→Y ⊑ ★→★`).  After both `TyBeta`s:

```
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
R  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩) 5)
```

The right's `gen` wrapper tags with X on the way in and **checks**
`X?` on the way out, and both boundaries exit with `−X → +X`.  The
shared X needs `X⊑★` across the wrapper.

## 4. The gaps

| | route | what the relation should have read |
|---|---|---|
| C1 matched, C3 | `+X ⊑ id(★)` justified by the mark | the right exits αᴿ with `id(★)` while its scope holds X-tagged values |
| C1 left-first/right-first, C2 | a one-sided `+X` and a rejoin that keeps `X⊑★` | the two sides' exits for the same rep. var pair, which no one-sided rule compares |
| C4, C4g | a push and a pop at `X⊑★` | the right's ∀ type before its `Inst` (`∀X.X→★`), equivalently its exit `−X → id(★)` |

P4 and C2 reach the same inner pair, in worlds of the same shape, with
the same payloads (`ν X:=ℕ` on both sides).  They differ only in the
right's exit for its rep. var:

```
P4  right exit  −X → +X
C2  right exit  −X → id(★)
```

So the distinguishing information exists, on the boundary, as a
conversion.  The relation reads it only at matched boundaries, and even
there the ★ clause lets the mark override it.

## 5. Candidate placements (not decisions)

1. **Read exits at every boundary.**  One-sided boundary rules take a
   condition on their own conversion: a right boundary that exits a
   name with `id(★)` may only enclose terms where that name is not
   related at `X⊑★` (equivalently: `X⊑★` at a shared name is
   available only under a right exit that unseals or checks it).  The
   mark stays, but it is justified by the conversion that closes its
   scope.  Open: a boundary's conversion is outside its interior, so
   the condition is read where the scope closes, not where `⊑cast` uses
   the mark.  The world would carry "this name's right exit unseals"
   from the boundary down to `⊑cast` (a fact about the rep. var pair,
   set by `Interior`).

2. **Attach the mark to the rep. var pair.**  `ϱ` entries record
   whether the pair may relate a left value to a right ★ value, set at
   the binder from the two exits (the ν's or boundary's conversions),
   and a joined name's mark is read through its rep. vars.  This puts
   the knob next to the information D17 already compares.  Open: how
   it interacts with `gen` wrappers (P4's `[−X^α]` inside the right),
   whose own `−X`/`+X` exits are internal to the right.

3. **Pushes take the pre-`Inst` type** (`∀A ⊑ ∀A′ᵢ`, being checked in
   `PushTypePremise`).  Covers C4 and C4g only.  It is an instance of
   (1) or (2) for the boundary that `Inst` creates, since the right's
   exit `−X → id(★)` is computed from the same codomain `★`.

The shared idea of (1) and (2): a name may face `★` only where the
side that holds the tag also closes its scope in a way that removes
the tag (unseal or check).  Today that is decided by a mark chosen at
the binder, with no reference to the closing conversion.

## 6. Open questions

- Is "the right's exit unseals or checks X" a property of a single
  boundary, or of the path from the tag to the exit (P4 checks with
  `X?` inside the right, before the exit)?
- Does placement (1) or (2) let the marks become a plain function of
  sidedness again (SidedMarks), with P4 handled by the exit condition?
- What do Sim and SimBack need to preserve the new information across
  `Merge` (which concatenates two boundaries' entries and composes
  their conversions) and `exitEnv`?

## 7. Invariants on rep. vars instead of names (Jeremy, 2026-10-05)

Rep. vars live longer than names.  A name exists between a boundary's
`+X^α` and the `−X^α` (or the boundary's exit); `Merge` concatenates
entries and `exitEnv` renames, so a fact about a name must be carried
through every such step (this is where InteriorMerge broke under
HiddenNames).  A rep. var is allocated once by `TyBeta` and never
renamed or freed.

**What holds of rep. vars along a run** (all directly from the
reduction rules; none uses the relation):

1. A rep. var's payload never changes after `TyBeta` allocates it.
2. The store only grows; rep. var numbering only shifts under the
   allocations `↑ᴹ[ δ ]` of siblings (no rebase, Evolve's charter).
3. Every name in a term is bound by some boundary entry to exactly one
   rep. var, so "the rep. var of a name occurrence" is well defined
   from the enclosing entries.
4. A seal `−X` and a tag `X!` act on the rep. var of X; `Merge` and
   `exitEnv` change the names and the entry lists but not which
   rep. var a seal or tag refers to.

**Where P4 and C2 really differ.**  Right after `CastFun`, the two
right terms are identical except for two coercions:

```
P4  ([+X^α] (([−X^α] (λx:★. x) ⟨…⟩) ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★])⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
C2  ([+X^α] (([−X^α] (λx:★. x) ⟨…⟩) ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★])⟨id(★)⟩^[X:★∼X] ⟨id(★)⟩)
```

Both relate the left's untagged `[−X^α] 5 ⟨−X⟩` to the right's tagged
`(…)⟨X!⟩` at `X ⊑ ★`, in the same world.  In P4 that tagged value sits
under a right check `⟨X?⟩` of the **same rep. var**, so it cannot
leave untagged-against-tagged; in C2 it sits under `⟨id(★)⟩` and then
a boundary exit `id(★)`, so it escapes.  C1 and C4 are like C2 (the
tag `x⟨X!⟩` is under no check).  So the distinguishing fact is not a
static property of the rep. var pair (P4 and C2 have the same pair,
`ν X:=ℕ` on both sides): it is whether **an αᴿ-tagged right value that
faces an untagged left value is still under a right check of αᴿ (or a
right hiding `−X^αᴿ`)**.

**A candidate invariant, stated on rep. vars:**

```
a right value tagged by αᴿ faces an untagged left value
  only under a right check of αᴿ, or inside a right hiding of αᴿ
```

It mentions names only through the rep. var they denote, so `Merge`
and `exitEnv` (fact 4) preserve it without re-proving anything about
marks.  In the relation it would be read top-down: a right check
`⟨X?⟩` (or a right `−X^α`) grants, to its premise, permission for
αᴿ-tagged right values to face untagged left ones; `⊑cast` of a right
tag `X!` at `X ⊑ ★` requires that permission.  Then the marks of
shared names need not license anything by themselves, which is the
sidedness rule (SidedMarks) with P4's need supplied by the check.

**Name relation from the rep. var relation.**  A shared name X is bound
by entries `+X^αᴸ` and `+X^αᴿ`.  Its mark could be read from the pair
`(αᴸ, αᴿ)` in `ϱ` plus the permission above, instead of being stored on
the name and chosen at the binder (D11) or kept on a rejoin (D15).
D23 decided "rep. vars carry no marks; marks belong to names" (Jeremy,
2026-10-03); this would revisit it: the information moves to `ϱ` (and
to permissions granted by checks), and names read it.

Open:
- Function casts: in P4 before `CastFun`, the wrapper `⟨X! → X?⟩` is one
  arrow coercion; the permission for its domain tag comes from its own
  codomain check.  The rule for a right arrow cast must grant it
  per position (a contravariant `X!` is covered by a covariant `X?` of
  the same rep. var).  C2's `⟨X! → id(★)⟩` grants nothing.
- Whether "under a check" must also account for a check that may never
  run (the right diverges first): that only helps SimBackBlame.
- How the permission interacts with D27 pushes (C4's push has no check
  above the tag, so C4 dies; does every corpus push have one?).

## 8. Sources

`PendingOpenings.agda` (`Probes`), `SidedMarks.{agda,md}`,
`ModeCondition.{agda,md}` (`Esc`), `HiddenNames.{agda,md}` (§2, §5),
design.md §10 D11, D15, D16–D18, D23, D25, D27, and §12.4 (P4).
