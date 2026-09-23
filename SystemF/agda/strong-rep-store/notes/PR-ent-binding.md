# Split `Ent` into `Binding` + one unbind

Branch `ent-binding`.  `make -C SystemF/agda/strong check` passes cold
(exit 0, `postulate-check: OK`).

## What changed

`strong-rep-store.Ctx`'s entry type was recursive in its mask:

```agda
data Ent : Set where
  abst   : Ent
  bind   : Ty → Ent
  masked : Ent → Ent        -- masked (masked (bind A)) is a term
```

It is now two layers — what the slot **binds**, and whether the slot is
**hidden** — with **at most one unbind**:

```agda
data Binding : Set where          -- what a slot binds
  abst : Binding                  -- Λ-bound, no representation
  bind : Ty → Binding             -- bound by a boundary, rep A

data Ent : Set where              -- a type-context entry
  unmasked : Binding → Ent        -- nameable
  masked   : Binding → Ent        -- hidden by an unbind
```

`masked` no longer takes an `Ent`, so `masked (masked …)` is not a term:
**"at most one mask" is true by construction**, not by a premise, not by
an invariant, and not by an induction over a stack.

Everything else follows.  `Nameable`/`Unbound` become the two
constructors' own discriminations — one clause each, **no premise**:

```agda
data Nameable : Ent → Set where
  nameable : Nameable (unmasked b)

data Unbound : Ent → Set where
  unbound : Unbound (masked b)      -- was: unbound : Nameable E → Unbound (masked E)
```

`Nameable` was kept as a predicate (rather than inlined as
`E ≡ unmasked b`) because `_∋tv_`, `_∋lk_` and their transports read as
before and the several hundred lookup triples in `Examples.agda` keep
their arity; the whole content of the old two-constructor version was the
`abst`/`bind` split, which now lives one layer down where it belongs.

Setting and clearing the unbind are total and idempotent:

```agda
maskEnt : Ent → Ent               unmaskEnt : Ent → Ent
maskEnt (unmasked b) = masked b   unmaskEnt (unmasked b) = unmasked b
maskEnt (masked b)   = masked b   unmaskEnt (masked b)   = unmasked b

mask   = updateAt maskEnt         unmask = updateAt unmaskEnt
```

(`maskEnt` is never applied to an already-masked slot in a well-formed
term — `sw-l` demands a nameable slot — but the function does not have to
know that, and that is the point.)

Renaming, the instantiation mint and the renderer all become a `Binding`
operation lifted through the unbind layer, with no recursion:

```agda
renᵇ ρ abst     = abst                 renᵉ ρ (unmasked b) = unmasked (renᵇ ρ b)
renᵇ ρ (bind A) = bind (renameᵗ ρ A)   renᵉ ρ (masked b)   = masked (renᵇ ρ b)
```

and likewise `substᵇ`/`substᵉ` (`proof/Preserve` §2a),
`renᵇ-id`/`renᵉ-id`, `renᵇ-comp`/`renᵉ-comp` (`proof/PeelDual` §3a),
`showBinding`/`showEntry` (`strong-rep-store.Show`).

Refinement splits the same way.  `_⊑ᵇ_` carries the knowledge order and
`_⊑ᵉ_`/`_⊑ᵃᵉ_` lift it through the unbind:

```agda
data _⊑ᵇ_ : Binding → Binding → Set where
  le-aa : abst ⊑ᵇ abst
  le-ab : abst ⊑ᵇ bind A
  le-bb : bind A ⊑ᵇ bind A

data _⊑ᵉ_ : Ent → Ent → Set where
  le-uu : b ⊑ᵇ b′ → unmasked b ⊑ᵉ unmasked b′
  le-mm : b ⊑ᵇ b′ → masked b   ⊑ᵉ masked b′
  le-mu : b ⊑ᵇ b′ → masked b   ⊑ᵉ unmasked b′     -- no Nameable premise

data _⊑ᵃᵉ_ : Ent → Ent → Set where               -- the TERM transport
  la-uu : b ⊑ᵇ b′ → unmasked b ⊑ᵃᵉ unmasked b′
  la-mm : b ⊑ᵇ b′ → masked b   ⊑ᵃᵉ masked b′
```

`_⊑ᵃᵉ_` reuses `_⊑ᵇ_` verbatim — the `abst → bind` step is legal for
both relations; only the unbinds differ — so `la-aa`/`la-ab`/`la-bb` are
gone, subsumed by `la-uu`.

## Lemma deltas

Gone:

* `unmaskEnt-nameable : E ⊑ᵉ E′ → Nameable E′ → E ⊑ᵉ unmaskEnt E′` — it
  existed only to manufacture the `Nameable` argument `le-mu` used to
  demand.
* `la-aa`, `la-ab`, `la-bb` — replaced by `la-uu` over `_⊑ᵇ_`.
* `core`, `core-ren`, `core-nameable`, `core-masked`, `core-unmaskEnt`
  (`proof/MaskFacts`) — with one unbind per entry the "core" of an entry
  **is** `unmaskEnt`.  The five are replaced by three one-line case
  splits (`unmaskEnt-nameable`, `unmaskEnt-maskEnt-core`,
  `unmaskEnt-idem`), and `core-ren`'s induction becomes
  `sym (unmaskEnt-comm suc E)`.

Shrunk (no recursion, no witness threading):

| lemma | before | after |
|-------|--------|-------|
| `⊑ᵉ-trans` | 6 clauses; `le-mu` calls `nameable-mono` | `⊑ᵇ-trans` 3 + `⊑ᵉ-trans` 4 |
| `nameable-mono` | 5 clauses | 3 |
| `masked-le` → `maskEnt-le` | recursive over the stack | 3 clauses |
| `unmaskEnt-mono` | 5 clauses, one calling a helper | 3 clauses |
| `⊑ᵉ-refl`, `⊑ᵃᵉ-refl`, `⊑ᵉ-⇑`, `⊑ᵃᵉ-⇑` | recursive | `⊑ᵇ-refl`/`⊑ᵇ-⇑` + 2-clause lift |
| `⊑ᵃᵉ-Unbound` | rebuilds via `nameable-mono` | `(la-mm l) unbound = unbound` |
| `maskEnt-unmask` | `(unbound v) = refl` | `unbound = refl` |
| `renᵉ-Nameable⁻`, `Unbound-ren⁻` | 3 clauses each | 2 each |
| `⊑ᵉ-unmaskEnt` | `masked` case via `masked-le` | 2 clauses, `le-uu`/`le-mu` |
| `renᵉ-⇑-comm`, `renᵉ-Nameable`, `renᵉ-Unbound` | recursive / 2 clauses | 2 / 1 / 1 |

Grew — **one** place, and it is the honest cost of an idempotent mask:

```agda
-- was: unmask-mask : (X : ℕ) (Δ : Ctxᵗ) → unmask X (mask X Δ) ≡ Δ
unmask-mask : Δ ∋tv X → unmask X (mask X Δ) ≡ Δ
```

With a stack of masks, `mask` at an already-masked slot pushed a second
unbind which `unmask` popped, so the identity held everywhere.  With one
unbind, `maskEnt` is idempotent, so at an already-masked slot `unmask (mask
X Δ)` *exposes* what `Δ` had hidden.  Counterexample:
`Δ = masked abst ∷ []`, `X = 0` — `mask 0 Δ ≡ Δ` and
`unmask 0 (mask 0 Δ) ≡ unmasked abst ∷ [] ≢ Δ`.

The premise is always at hand: `sw-l` admits `unbind X` only at a `∋tv`
slot, which is exactly the discipline that made double masking
unreachable before.  It is threaded through two lemmas, each of which
gains an argument its single call site already has:

* `proof/PeelDual.applyUnlocks-dualScope` gains `Δ ⊢ˢ S`;
* `proof/PeelDual.convCtx-dual` gains `Δ ⊢ˢ changes Θ`, supplied at its
  one use site by `mw-changes mwᵥ` in `preserve-Peel`.

No theorem statement was weakened otherwise; `mask-unmask : Δ ∋lk X →
mask X (unmask X Δ) ≡ Δ` is unchanged, so the two inverses are now
**symmetric** — each holds exactly at the slots its own direction is
applied to.

`proof/DualTightness.¬⊢ᵐ-double-unbind` survives with a different job: it
is no longer what keeps `Unbound` one mask deep (that is by construction),
but the fact that the judgement still refuses a vacuous re-unbind — which
is what keeps `unmask-mask`'s premise available.

## Rendering deltas

None.  `showEntry` was split into `showBinding` (the slot) and
`showEntry` (the `⌷[…]` wrap), and the strings are byte-identical:
`X := A`, `X Λ-bound`, `⌷[X := A]`.  Every `Examples.agda` rendering
example still checks by `refl`.

## Mechanical rewrite

Every pattern match on an entry across the development was rewritten:
`abst` → `unmasked abst`, `bind A` → `unmasked (bind A)` in `Ent`
position, `masked (bind A)` unchanged (its argument is now a `Binding`),
`masked` in function position → `maskEnt`, `nameable-a`/`nameable-b` →
`nameable`, `unbound v` → `unbound`.  `Examples.agda` carries the bulk:
about 290 lines mentioning an entry constructor, most of them lookup
triples of the form `(unmasked (bind ℕ) , ez , nameable)`; ~30 of them
then had to be re-wrapped to stay under 80 columns.  Files touched: `Ctx`,
`Conversion`, `Boundary`, `Terms`, `TermSubst`, `Reduction`, `Progress`,
`Preservation`, `Show`, `Examples`, and `proof/{Adversary, DualTightness,
IdLayer, MaskFacts, MoveScope, MwUObstruct, PeelDual, Preserve,
PreserveObstruct, Progress}`.

## Docs

`Design.md` §3 (*Entries*, *Refinement*, *The three operations*, plus a
new *What the one-mask entry costs, and what it buys*), §4.2 (the `unbind`
premise's new job), Appendix A (`Binding`, `unmasked`, `maskEnt`, `⊑ᵇ`,
the reletter note); `README.md`'s `Ctx.agda` row.
