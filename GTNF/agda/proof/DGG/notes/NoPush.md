# With claim-rep, can pushes go?

Status: 2026-10-06.  Agda: `NoPush.agda` (this directory).  From
`GTNF/agda` it checks with

```
agda --safe -v0 proof/DGG/notes/NoPush.agda
```

The file has no holes, no postulates and no pragmas.  It imports the
real relation (D29, `claim-rep` included), and All.agda does not
import it.  It removes nothing from the real relation.  LEFT is the
more precise side.

## Verdict

**Not entirely.**  Every push that a left `Λ` pops can be replaced by
`claim-rep`: the `Λ` claims the right's still-unnamed `★` rep. var
above the right boundary, and the boundary rejoins it.  A push that a
left GEN cast pops (`cc-gen`) cannot be replaced.  The gen binder
scopes over no left term, so the left context stays closed down to
the right's `Inst` boundary.  At a world with no pending name, no
closed left type is `⊑ X → X` at a right name `X`.  So C2 X0 and R2c
are lost, and so is G1, a DGG part 1 pair from related sources (§3).

## 1. The push-free relation

`_∣_⊢_⊑ⁿ_∶_` is the real relation's 15 rules with every world at
`πʷ = []`:

- 11 rules are verbatim.
- `Λ⊑` takes `ClaimN`, which is `claim-fresh` or `claim-rep` (no pop).
- `cast⊑` has no `CastClaim`, `⟪⟫⊑` has no `BdyClaim`, and `⊑⟪⟫` has
  no `Push`.

Two maps connect it to the real relation:

- `toReal` embeds it into the real relation.  So every
  non-derivability result of the real relation holds here (`Dead.c1`
  … `Dead.c5`, `Dead.c4g`).
- `lift refl d _` carries a real derivation `d` with no push, pop or
  pass over to this relation.  The side condition `NoPend d`
  normalizes to `⊤` on push-free derivations.

## 2. The corpus without pushes

| block | without pushes | Agda (`NoPush.Corpus`, `C2X0`) |
|---|---|---|
| P3 = Ch X0 | **derives**: `ΛX` claims `αᴿ`, `+X^αᴿ` rejoins | `p3-inst` (generic `coreN`) |
| Cg X0 | **derives**: claim, rejoin, then the gen wrapper's grant | `cg-x0` |
| C12 X0 | **derives**: `ν⊑ν` around `coreN` | `c12-x0` |
| L3c pre / post | **derives**: each copy of the duplicated Inst boundary is claimed separately (at `W₁`, `αᴿ` has two left partners: `αᴸ` unnamed, the binder named) | `l3c-pre`, `l3c-post` |
| L3d before | **derives** (`coreN` at `W₁`) | `l3d-before` |
| K `VL⊑RF`, `lk₁⊑rk₄` | **derives**: `⟪⟫⊑` FIRST (left Y left-only), `ΛX` claims β, the merged `(+Y^β, +X^αᴿ)` rejoins both | `VL⊑RF`, `lk₁⊑rk₄` |
| K `lk₁⊑rk₃` | **derives**: `+Y^β` rejoins X, then `+X^αᴿ` rejoins Y | `lk₁⊑rk₃` |
| K `lk⊑rk`, `lk₁⊑rk₁`; `dgg1-K` | **derive** (lift; `dgg1-K` on the new `VL⊑RF`) | `lk⊑rk`, `lk₁⊑rk₁`, `dgg1-K` |
| H1 state 2 | **derives**: claim α above both right casts | `h1-st2` |
| H1 final; init | **derive** (`final-no-push` and `init` lift) | `h1-final`, `h1-init` |
| P4 B1, B1′, B2–B6; P4c R7–R10; Cg B1; C18b B7 | **derive** (push-free, lift) | `p4-B*`, `p4-R*`, `cg-b1`, `c18b-b7` |
| P1, P2, P6, Ch B0/B1, Cg B0, C2 B0/B6/B7, C12 B0/B1, C13 B1, C14 B1 | **derive** (push-free, lift) | `p1-init` … `c14-b1` |
| **C2 X0** | **not derivable**, in any world, at any index, in any term context | `C2X0.c2-x0-unrelated` |
| **G1** (new, §3) | **not derivable**.  The real relation relates it, so DGG part 1 fails without pushes | `C2X0.g1-final-unrelated`, `g1-final-real`, `g1-dgg1-real` |
| R2c pre / post | argued not derivable: its only push is C2 X0's (a left gen-cast value against the outer Inst boundary).  Its terms live in ForallBoundaryFixes, which no longer checks | — |
| C1, C2 (late), C3, C4, C4g, C5 | **still dead** (sub-relation) | `Dead.*` |

## 3. Why the gen case fails

Take C2 X0.  The left is

```
(ν X:=ℕ. ((λx:★. x)⟨gen Y. (Y! → Y?ℓ0)⟩^[] X) ⟨−X → +X⟩) 5
```

The right is

```
([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[]
```

- The left never binds a name.  `ν⊑` and the gen `cast⊑` keep the
  left context `empty`.
- So the right's `+X^α` is entered with a closed left term `M`: the
  `ν`, the gen value, or `λx:★.x`.
- Its interior `([−X^α] …)⟨X! → X?ℓ0⟩` has type `X → X`.
- With no pending name the index is plain.  `not⊑var⇒` shows that no
  closed type `A` has `A ⊑ X → X`: the domain would have to be a left
  name.  The left context is closed (`⊢ᵗ-of`), and the right type comes
  from `coercion-trg`.  So `no-at-I★gen` holds for EVERY left term, and
  `walk` covers every order of `ν⊑`, `cast⊑`, `cast⊑cast`, `⊑cast` and
  `⊑⟪⟫`.

A claim-rep analogue at the gen cast cannot help.  The claim must
happen below the right's check `X! → X?` (which the real derivation
uses to grant) and inside `+X^α`, where X is NAMED.  Above it, the
left gen cast is unpeeled and the index fails just as well.  Only an
index opened at X relates the pair, and that is a pending name.

**G1.**  The same obstacle as a DGG part 1 pair.  Sources (RELATED:
the same term, and `∀X.X→X ⊑ ★→★`, `g1-src`):

```
L:  ((λx:★. x) : ∀X.X→X)
R:  (((λx:★. x) : ∀X.X→X) : ★→★)
```

Initial cast terms (rendered; related in both relations, `g1-init`):

```
L₀ = (λx:★. x)⟨gen X. (X! → X?ℓ0)⟩^[]
R₀ = (λx:★. x)⟨gen X. (X! → X?ℓ0)⟩^[]⟨inst Y. (Y?ℓ0 → Y!)⟩^[]
```

The left is a value.  The right's run (`G-R-states`, pinned to
`evalTerms`):

```
  (λx:★. x)⟨gen X. (X! → X?ℓ0)⟩^[]⟨inst Y. (Y?ℓ0 → Y!)⟩^[]
⟶ (Inst)
  (ν X:=★. ((λx:★. x)⟨gen Y. (Y! → Y?ℓ0)⟩^[] X) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[]
⟶ (TyBeta, ⊣ α:=★)
  ([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[]
```

Its only value is the last state (`G-R-nv`, `G-R₁-nv`).  The real
relation relates the final pair (`g1-final-real`: push X, grant, then
`cc-gen` pop) and meets DGG part 1 (`g1-dgg1-real`).  The push-free
relation relates the final pair in no world (`g1-final-unrelated`).

## 4. Cost and gain of full removal (if the gen case were solved)

| | real (D29) | push-free |
|---|---|---|
| relation rules | 15 | 15 (4 lose a premise) |
| side relations | `Claim` (3), `CastClaim` (3), `BdyClaim` (2), `ForallConv` (2), `Carried` (2), `Push` (1); `push-none` | `Claim` (2) |
| world fields | 7 (`πʷ`) | 6 |
| index | `OpenImp`, `_⊳_` (opens one ∀ per pending name) | plain `marksʷ W ⊢ embᴸ W A ⊑ embᴿ W A′` |
| world operations | `Join↪` (2), `Open1`, `open-⊕`, `_⊕⁺^_`; π shifts in every op | none of these |
| `WfWorld` fields | 7 (`wf-pending`, `wf-distinct`; `PendingOK`, `RightOnly`) | 5 |
| `cast⊑` premise world | `record W { πʷ = πₚ }` | `W` |
| corpus lost | — | C2 X0, R2c, G1 (gen values) |

STATEMENTS-CORE lemmas whose pending-name part would go:

- `PushInstR`.  For a `Λ` value it becomes the re-association to
  `claim-rep` above the new boundary.
- `RightMergePending` becomes a plain RightMerge, and its INLINE
  `PushCompose` goes: two rejoining boundaries merge with no pending
  bookkeeping.
- `WfPop` becomes INLINE `WfWorld (W ⊕ᴸ⇔ β)`.
- `PendingMor` goes.
- `PopInstX` becomes the claim case of InstXImpL (`allocᴸ⇔`, as for a
  pop).
- `CatchupRightπ` is CatchupRight at `πʷ = []`.
- `pending-¬⊑blame` (SimBack) goes.

## 5. What a partial removal would keep

The gen case uses only these:

- a push of NEW names with nothing carried;
- `⊑cast` carrying `π` (the grant sits between the push and the pop);
- the `cc-gen` pop.

K's carry (`ca-∷`), the pass into a left ∀-boundary (`bc-∀`,
`ForallConv`), the `∀ᵖ` pass (`cc-∀`) and `claim-pop` all have
claim-rep replacements in the corpus.  A gen-only pending list would
keep `πʷ`, `OpenImp`, `Push` (without `Carried`) and `cc-gen`.  Not
checked:

- whether a left value with TWO gen layers, against two nested right
  Inst boundaries (H1's gen analogue), is related at all.  `cc-gen`
  pops exactly one name, and the order problem of PushOrder §2 would
  reappear for gen binders;
- whether a SimBack schedule could avoid C2 X0 by letting the left
  take its own `TyBeta` first.  G1 has no such escape: its left is a
  value.

## 6. Names

- **Relation**: `ClaimN` (`n-fresh`, `n-rep`), `_∣_⊢_⊑ⁿ_∶_`, `⊑cast₀`,
  `toReal`, `NoPend`, `NoPush′`, `lift`.
- **Corpus**: `Corpus.{Wo, Wiₒ, claimₒ, Intₒ, coreN, Wiₒ-W₃-wf,
  Wiₒ-W₁-wf, p3-inst, c12-x0, cg-inner, cg-x0, copy2, l3c-pre,
  l3c-post, l3d-before, Wl, IntL, claimK, WX2, IntΘ₂, VL⊑Bm, VL⊑RF,
  lk₁⊑rk₄, WY, IntY, IntX, VL⊑Rarg₃, lk₁⊑rk₃, dgg1-K, h1-st2,
  h1-final, …}`.
- **Gen case**: `C2X0.{not⊑var, not⊑var⇒, πN, plainN, no-at-I★gen,
  walk, c2-x0-unrelated, g1-src, G-R-states, g1-init, g1-final-real,
  g1-final-unrelated, g1-dgg1-real}`.
- **Dead**: `Dead.{c1, c2, c3, c4, c4g, c5}`.
