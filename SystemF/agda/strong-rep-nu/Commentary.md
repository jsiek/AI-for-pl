# Commentary on the Strong System F sources

This is the design, history and rationale commentary that used to live
inline in the `.agda` files of `SystemF/agda/strong-rep-nu/`, moved
out on 2026-09-22 so that the Agda reads as Agda.  It is keyed by
MODULE and, within a module, by DEFINITION or section, in source order;
each file keeps a short charter at its top and a one-line
`-- Commentary.md § <Module> / <definition>` pointer wherever the
explanation moved.  The top-level modules appear below in `All.agda`'s
import order, then the `proof/` modules bottom-up.  `Examples.agda` is
not covered: its comments ARE its content.  Everything here describes
the CURRENT design; where a rule's SHAPE is only explicable by what it
used to be, the historical remark is kept and marked as history in one
clause, and each module section ends with a short "Retired" list naming
what was dropped and why.  The mathematical presentation in
named-variable notation is `notes/notes.md`, the dated design log is
`notes/DECISIONS.md`, and the module map is `README.md`.

The calculus is System F with type abstraction enforced at run time.
Instantiating `(ΛX. N) [A]` does not substitute `A` into `N`; it
installs a BOUNDARY `M ⟪ Θ , c ⟫` whose boundary scope `Θ` says which
ordinary type variables are live on each side and whose conversion `c`
says, leaf by leaf, which side may see the representation behind a
name.  The two jobs the old type-variable slot did at once are split
into two de Bruijn universes: a REPRESENTATION variable α is runtime
storage, held in a representation context `Ξ`, and an ORDINARY type
variable `X` is lexical, held in a name map that says which α it
denotes — a type context being the pair `Ctxᵗ = Ξ ∣ names`.  Since
experiment 2 (2026-09-22, `notes/RepStoreSketch.md`) the representation
a ∀-elimination mints is NOT carried by the boundary: it is allocated
in the AMBIENT store at index 0 by `allocate`, every existing
representation variable moves up by one, and a step therefore RETURNS
the change it made (`Alloc`, `apply`), with the congruences shifting
the redex's siblings.  A boundary scope is consequently nothing but its
change list — `Boundary = List Change`, `unbind X α` and `bind X α` —
so merging frames is `_++_`, the dual is `dual`, rewinding is `rewind`,
instantiating is `inst`, and the two contexts a boundary induces are
RELATIONS (`_⊢ⁱ_⇒_`, `_⊢ᶜ_⇒_`), not functions of the exterior.  The
one-paragraph map of the files this commentary follows is `README.md`;
the store sketch that ruled the current shape is
`notes/RepStoreSketch.md`.

Since 2026-09-24 (strong-rep-nu, `notes/NuSketch.md`) the run-time
language has NO TYPE APPLICATION.  Its ∀-elimination is the term
`ν A · L ⟨ c ⟩`, which carries the conversion `c` the compiler wrote
(`reveal 0 C` for `L : ∀ C`); plain System F with `L [ A ]` is a
separate source language (`Source.agda`) that `Compile.agda` elaborates
into it.  The four rules that changed were renamed, and the dated
history below keeps the name a rule had at the time:

```
  TyBeta       ⟶  Nu-Λ       the reveal moved to compile time
  TyPeelR-Λ    ⟶  Nu-⟪Λ⟫     STACKS s under ν's c instead of fusing
                             them into `instReveal 0 s`
  TyPeelR-⟪⟫   ⟶  Nu-⟪⟫      pushes a `ν`, not a type application
  ξ-·[]        ⟶  ξ-ν
```

## Ctx.agda

The two de Bruijn universes and every relation over them.  §1 declares
`RVar`, `RepBinding` (`abstR`/`bindR`), `RepCtx`, `TyCtx` and the pair
`Ctxᵗ = reps ∣ names`.  §2 is the lookup family — `_∋ˡ_:=_`, `_∋ᵗ_:=_`,
`_∋tv_`, `_∋ʳ_:=_`, `_∋rep_:=_`, `_∋_:=ᴿ_`, `_∋ʳ_`, `_∋ᵅ_`, `_⊆ᵃ_`.
§3 is ordinary type formation `_⊢ᵗ_` with `underΛ` and `Base`; §4
representation payloads `_⊢ref[_]_`, `_⊢ᴿ[_]_`, `WfRepCtx`; §5 the two
readings of `Ty` — `_⊢_~_`, `_⊢ᶜ_~_`, `_⊢_≈_⊣_` — and the lookup square
`_∋_:=_`; §6 well-formedness `_∌ʳ_`, `Unique`, `ValidNames`, `WfCtx`.
§§8–11 are the representation universe's machinery: `extN`/`Injᵗ`,
`shiftBy`, THE STORE (`allocate`, `Alloc`, `apply`), the insert/delete
relations `_⊢+_at_⇒_` / `_⊢-_at_⇒_`, and the renaming interface
`RepWk`.

DEFINITIONS ONLY.  Every lemma about the above lives in
`proof/Ctx.agda` (`notes/DECISIONS.md`, 2026-09-20).  Anything
mentioning `Change` or `Boundary` — the boundary scope, its two induced
contexts, `BoundaryWf` — is `Boundary.agda`; terms and the typing
judgement are `Terms.agda`; conversions are `Conversion.agda`.

### The two universes

The two uses the old single type-variable slot was put to are split
into distinct de Bruijn universes.

* `names Γ` contains EXACTLY the ordinary type variables currently in
  scope.  An entry is the representation variable named by that
  ordinary variable.  A CONCEALED ordinary variable has no entry at all.
* `reps Γ` contains abstract and represented representation variables.
  A represented payload is a `Ty` whose FREE indices range over this
  representation-variable universe.  A `∀` inside the payload binds an
  ordinary local type variable in the usual way.

A term-level `Λ` extends both universes: it binds an abstract
representation variable and an ordinary type variable that names it
(`underΛ`).  Boundary scopes change the ordinary name map; those
operations live in `Boundary.agda`.

### The two invariants to know before touching anything here

1. `names Γ` holds exactly the ordinary type variables currently in
   scope, and an entry is the representation variable named at that
   position — so a concealed ordinary variable has no entry, and a
   represented payload's free indices live in the OTHER universe.
2. A REPRESENTATION-ONLY renaming leaves every ordinary POSITION where
   it was (§8, §11): it renames `reps` and acts on the name map by
   `map ρ`, so no ordinary spelling in any type, conversion or change
   moves.  `RepWk` is exactly what such a move must supply — three
   fields for `WfCtx`'s three obligations one universe down, plus
   injectivity, which is what an `unbind`'s freshness record needs — and
   it is what makes `renᴹᴿ` (`TermSubst.agda`) type-preserving.

### `renNameCtx`

View one context's ordinary names after a representation renaming,
using a SECOND context's representation store.  Crossings use this when
the same ordinary spelling is carried across an inserted representation
binder: the positions stay fixed, but the representation indices they
denote move.  `Nu-⟪⟫`'s `SameConv` premise is stated through it.

### `_∋ʳ_:=_`

A representation payload is stored OUTSIDE its own binder.  Looking it
up shifts it through that binder and every newer representation binder
— that is what the `renRepBinding suc` in every clause does.

### `_∋_:=ᴿ_`, `_∋_:=_`

`_∋_:=ᴿ_` is the composite lookup used by conversions: ordinary `X`
names α, whose representation is `R`.  `_∋_:=_` is the full conversion
lookup SQUARE: ordinary `X` names α; α is represented by `R`; and
ordinary `A` is `R` read back through the current ordinary-name
assignment.

### `_⊢ref[_]_`, `_⊢ᴿ[_]_`

A payload has a MIXED de Bruijn interpretation.  The first `n` indices
are ordinary variables bound by enclosing payload `∀`s.  Index `n + α`
is the free representation variable α.  `WfRepCtx` then checks a
concrete representation OUTSIDE its own binder.

### `_⊢_~_`, `_⊢_≈_⊣_`

`_⊢_~_` translates free ordinary variables through the name map.  A `∀`
extends only the LOCAL binder prefix on both sides; it does not
allocate a free representation variable.

`_⊢_≈_⊣_` says two ordinary types at the same representation depth
denote the same representation-universe type.  `unbind` and `bind` may
give that type different ordinary de Bruijn spellings, which is exactly
why the reduction rules carry `≈` premises rather than renamings — see
§ Reduction.agda / The crossing-spelling law.

### `extN`, `Injᵗ` (§8, the name-map half of representation renaming)

A REPRESENTATION-ONLY renaming moves representation variables and
leaves every ordinary POSITION exactly where it was.  On a name map
that is `map ρ`: a lookup keeps its ordinary index and changes only the
representation variable it names.  §8 is everything that transport
needs from the name map alone; the representation-CONTEXT half — where
a payload must move too — is §11.

`extN n ρ` renames underneath `n` binders.  The depth it is used at is
the `n` local `∀`s inside a representation payload: a reference at
depth `m` is either local (untouched) or free (renamed), which is
exactly what `extN m ρ` does (`wk-ref`, `proof/Ctx.agda`).

`Injᵗ ρ` — an INJECTIVE renaming is what a name map needs: `unbind`
records that the name it deleted is now fresh, and freshness is not
preserved by a map that identifies two representation variables.

### THE STORE — `allocate`, `Alloc`, `apply`

Experiment 2, 2026-09-22; `notes/RepStoreSketch.md`.  A boundary no
longer carries a bind block: the representation a ∀-elimination mints
is pushed onto the AMBIENT representation context at index 0, and every
existing representation variable — in the context's name map and in
every sibling term — moves up by one.  `Alloc` is what one reduction
step did to the store (nothing, or one cell) and `apply` performs it.

Fresh = 0 rather than append-at-the-end, because under `Λ N` the body
is already typed with the binder at index 0: if the cell `Nu-Λ` mints
is also index 0, the body's indices already line up and `N` moves into
the contractum VERBATIM, its re-typing being the in-place refinement
`abstR → bindR R`.  The price is that a step GROWS the context, which
is why a step returns its change and the congruences shift siblings.

### `RepWk` (§11, the context half)

A representation-only renaming ρ acts on a context by renaming the
representation context and renaming the name map POINTWISE (`map ρ`).
Ordinary positions never move, so the ordinary spelling of every type,
conversion and change is untouched — which is the whole point of
`renᴹᴿ`.  `RepWk ρ Ξ Ξ′` is what such a move must supply, and it is
exactly what the two induced readings, the conversion typing and the
typing judgement all consume.  Three fields are the three `WfCtx`
obligations one universe down; the fourth, injectivity, is what a
`unbind`'s freshness record needs.

The base instances insert ONE fresh binding at the head: `repwk-abst₀`
(abstract, for `crossΛᴹ`) and `repwk-cons₀ (bindR R)` (represented, at
an allocation) — both `proof/Ctx.agda`.  `repwk-abst` closes either
instance under the one way the typing induction goes deeper: a `Λ`.

### Retired

* "the `n` parallel representation binders a boundary scope's bind
  block introduces" as `extN`'s second use, and "`repwk-push`, which
  closed `RepWk` under a bind block" — the bind block is gone, and with
  it `pushRepBinds`, `shiftRVars`, `extendReps`, `_⊢ᴮ_`, `shiftByᵇ`,
  `shiftRep` and `SameTyExt` (experiment 2, 2026-09-22).
* "`repwk-wkN`, `proof/RepWeaken.agda`, at the allocation" — that
  instance went with the bind block; the allocation now uses
  `repwk-cons₀ (bindR R)`.

## Boundary.agda

The boundary scope and its two induced contexts.  §2 is `Change`
(`unbind`/`bind`), its two running judgements `_∣_⊢δ_⇒_` and
`_∣_⊢χ_⇒_`, the dual (`dualChange`, `dual`, `dual-step`) and the
representation-only renaming `renᶠᴿ`.  §3 is `Boundary = List Change`
with `renᴮᴿ`, the constructions `rewind` and `inst`, and the two
readings — `_⊢ⁱ_⇒_`, which PERFORMS every change, and `_⊢ᶜ_⇒_` (via
`_∣_⊢χᶜ_⇒_`), which SKIPS unbinds — with `interior-functional` and
`conversion-functional`.  §§3a–3d are transport:
`interior-wf`/`conversion-wf`, the name-set invariant (Q) that `Peel`
needs, `dual-conversion-exists`, `conv-weaken`,
`merged-conversion-exists`, and the representation-renaming lemmas
(`changes-ren`, `interior-ren`, `conversion-ren`,
`snoc-unbind0-conversion-ren`, `snoc-unbind0-interior-ren`).  The witness
`BoundaryWf` and its derived `bw-interior-wf`/`bw-conversion-wf` close
§3d; §4 is the concrete shapes `TyBetaBoundary`, `TyBeta-bw`,
`crossΛ`/`uncrossΛ`.

EVERYTHING HERE MENTIONS `Change` OR `Boundary`.  The context material
it stands on — the store (`allocate`/`Alloc`/`apply`), the
insert/delete relations, `RepWk` — is `Ctx.agda`, and the lemmas about
that material are `proof/Ctx.agda`; that split
(`notes/DECISIONS.md`, 2026-09-20) is why the sections here begin at 2.
Other modules cite these numbers, so do not renumber them.  The
renamings that pair the two universes (`renᴮ²`, `renᴹ²`, `renᴹᴿ`) are
`TermSubst.agda`, one layer UP: §3d is stated over `renᶠᴿ`/`renᴮᴿ`
precisely so that it need not import that module.  Conversions are
`Conversion.agda`.

### The two laws a reader must know

**(1) THE CONVERSION CONTEXT IS A UNION OF NAMES.**  This law is used
in `Boundary.agda`, `Conversion.agda`, `Terms.agda`, `Reduction.agda`
and `TypeCheck.agda`; it is stated here once.

The conversion context performs `bind`s but SKIPS `unbind`s, so both a
concealed ordinary variable and its representation stay available to
the conversion.  It is therefore the UNION of the names live anywhere
along the boundary scope, not the name map at any one point of the run.
A conversion reading only ADDS names (`conversion-live`).

**(2) BOTH READINGS ARE FUNCTIONS OF THE CHANGE LIST.**  The two bind
clauses are mutually exclusive (`fresh-not-lookup`), so
`conv-changes-functional` / `conversion-functional` hold, and they are
exactly what determinism for `CancelR`, `IdPush` and `Nu-⟪⟫`
consumes.

`BoundaryWf` stores only what cannot be recovered — the exterior's
`WfCtx` and the two readings.  Output well-formedness is DERIVED, not
stored (`notes/DECISIONS.md`, 2026-09-18).

### `Boundary = List Change`

A boundary scope IS a list of changes, which sequentially bind and
anti-bind ordinary type variables.  Every change carries both the
ordinary de Bruijn position and the representation variable named at
that position.  The representation binders a scope used to carry are
allocated in the ambient representation context instead (`allocate`,
`Ctx.agda`): a boundary changes NAMES only.

`Boundary` is an ALIAS since 2026-09-22 (experiment 2,
`notes/RepStoreSketch.md`): the bind block it used to carry lives in the
ambient store, and the one-field record that briefly survived that
experiment is gone too.  So a scope is written as the list it is,
merging is `_++_`, and the rewind / dual / unbind-0 constructions are
plain list expressions.

Changes retain the head-LAST order: the tail acts first.

### `_∣_⊢δ_⇒_` — `unbind` and `bind`

`unbind` records FRESHNESS OF THE RESULT and `bind` demands FRESHNESS
OF ITS INPUT.  Thus one representation variable never has two
simultaneous ordinary names, and the two changes are exact inverses.
The `Ξ` index makes the carried representation-variable occurrence well
scoped.

### `renᶠᴿ`, `renᴮᴿ`

A REPRESENTATION-ONLY renaming of a change, and of a scope.  The
ordinary position is untouched, which is what makes a rep-only
weakening leave every ordinary de Bruijn spelling in a term exactly
where it was.  There is no bind prefix to skip.

### `rewind`, `_++_`, the snoc unbind, `inst`, `liftᴮ`

* `rewind Θ = dual Θ ++ Θ` — the changes, then their exact inverse.
  NO RULE BUILDS ONE since the one-layer contractum (2026-09-23); it
  survives as a `Boundary.agda` construction with its two transports,
  `rewind-interior` and `rewind-conversion`.
* Merging two scopes is `_++_`: the OUTER scope's changes sit at the
  TAIL, so they run first (head-last order, §2).  Nothing shifts — both
  were spelled at the same store.
* Appending `unbind 0 0` — `Θ ++ (unbind 0 0 ∷ [])` — makes it act FIRST:
  the NEW ordinary name 0, which names the NEW cell 0, is deleted
  before the scope's own changes run.
* `inst Θ` is a scope read at `allocate R Γ`: the fresh cell is
  representation index 0, the appended `bind 0 0` (acting first)
  gives it ordinary name 0, and the old changes — spelled at `Γ` — run
  underneath both, hence one shift in each universe.
* `liftᴮ Θ = map shiftChange Θ` is that shift alone, so
  `inst Θ = liftᴮ Θ ++ (bind 0 0 ∷ [])` (2026-09-24).  The `Nu` rules
  write the two halves as two STACKED layers — `inst []` outside, the
  crossed frame `liftᴮ Θ` in the middle — and `liftᴮ-interior` /
  `liftᴮ-conversion` are the halves of `inst-interior` /
  `inst-conversion` that read the middle layer at the outer layer's
  interior.  No rule builds a whole `inst Θ` any more; `Nu-⟪⟫` still
  reads one (`allocate R Δ ⊢ⁱ inst Θ ⇒ Δᵢ⁺`), because the stacked
  layers' combined interior is exactly that reading.

### `_⊢ⁱ_⇒_`

The interior reading PERFORMS every change on the name map.  The
representation context is untouched: a boundary changes NAMES only
(`interior-reps`).

### `_∣_⊢χᶜ_⇒_`, `_⊢ᶜ_⇒_` — and the re-bind clause

The conversion reading is the union described in law (1).

THE RE-BIND CLAUSE (2026-09-17).  Reading the conversion context as a
union FORCES a third clause.  Skipping an `unbind X α` leaves α live, so a
LATER `bind` of that same α — the shape every `dual`/`rewind`
composite has, since a dual inverts each unbind with a bind — meets a
name that is already there and the freshness premise of `conv-bind`
fails.  Without this clause `rewind Θ` and `Θ′ ++ Θ` have NO conversion
context whenever Θ unbinds, so `CancelR`'s and `IdPush`'s contracta were
untypeable: that is the wall the tower example walked into
(`Examples.agda` §5a, `no-rewind-conv` / `no-cancel-inner-conv`; the
refutation module is `notes/ReUnlockWall.agda`).  The rewind half of
that is history since 2026-09-23 — no rule builds one — but the merge
`Θ₁ ++ Θ₂` both rules do build has the same shape whenever `Θ₂` unbinds
what `Θ₁` binds.

The clause does not widen the judgement where the old one applied: the
two bind clauses are mutually exclusive (`fresh-not-lookup`), so the
conversion context stays a FUNCTION of the change list.  In
`conv-changes-functional` the mixed pairs are impossible: one says α is
FRESH in the tail's output, the other says α is LOOKED UP there.

WHY THE POSITION IS DROPPED.  `conv-unbind` already ignores its position:
skipping the unbind keeps α exactly where it was.  The paired bind must
therefore keep it there too — re-inserting it at the interior position
`X` would move a name the conversion context never moved.  The
positions of a conversion context are the interior's positions with the
unbound names left in place, and this clause is what makes that reading
hold through a dual.

### §3a — transport across a boundary scope

The two induced contexts are WELL FORMED whenever the exterior is.
Each of `WfCtx`'s three fields transports separately, and none of them
needs the term or the conversion.

* (i) `name-fn` (`int-unique`, `conv-unique`).  An unbind deletes and an
  bind inserts a name its own premise says is fresh, so both readings
  preserve uniqueness.  The conversion reading preserves it for the
  same reasons: it skips unbinds, and a bind either inserts a fresh
  name or does nothing at all.
* (ii) `wf-names` (`int-valid`).  Every name a reading leaves live is
  one the exterior already had, or one a `bind` brought in — and an
  bind carries its own `Ξ ∋ʳ α` premise.
* `conversion-live`.  A conversion reading only adds ordinary names.
  Preservation uses this to re-spell an exterior type in the conversion
  context selected by the relational reading.
* `interior-unique` / `dual-unique`.  The lifted readings preserve
  name-map functionality independently of the other two `WfCtx` fields.
  `dual-unique` is the instance needed when a crossed argument is
  wrapped in a boundary scope's dual.

`rewind-interior : Γ ⊢ⁱ Θ ⇒ Γᵢ → Γ ⊢ⁱ rewind Θ ⇒ Γ`.  A rewound
boundary scope performs the original changes and then their exact
inverse, so ITS INTERIOR IS THE EXTERIOR ITSELF.  Its conversion
context is the original conversion context: unbinds are skipped in both
halves, and each inverse bind is a no-op because the corresponding
unbound name is live in that union context.  The interior reading is the
evidence for that last fact — a conversion reading alone permits a
`conv-unbind` even when its name is absent.

`dual-interior : Γ ⊢ⁱ Θ ⇒ Γᵢ → Γᵢ ⊢ⁱ dual Θ ⇒ Γ`.  The dual runs the
same changes backwards, so it returns a crossing argument to the
ordinary name map the boundary was read on.  This is `Peel`'s
counterpart of `rewind-interior`, and it needs no `BoundaryWf` either.

`merged-interior`.  Merging two scopes: the outer's changes run first,
then the inner's, on one and the same store.

`interior-wf` / `conversion-wf` are THE TWO TRANSPORT THEOREMS — what
`BoundaryWf` used to take as explicit obligations.  `bw-interior-wf`
and `bw-conversion-wf` are the two former fields, now theorems; they
keep the names they had, so every USE site reads the same and only the
construction sites shrink.

### §3b — the name-set invariant (Q)

`Peel` reads its domain conversion at a boundary scope's conversion
context, then uses a re-spelling of it at the DUAL's conversion
context.  Those contexts need not have the same name LIST, but they
name the same representation variables.  That is (Q):

> the two conversion contexts straddled by `Peel` name the same
> representation variables, although their ordinary positions may
> differ.

The development was proved first in `notes/PeelPremise.agda`; it lives
here because progress needs the general theorem, not just the note's
concrete witness.

### §3c — `conv-weaken`, `dual-conversion-exists`, `merged-conversion-exists`

A conversion reading is MONOTONE in its starting name set.  Unbinds are
skipped; a bind either finds its name already live in the larger set
or inserts it at the same position.  The old output therefore remains
available, although its ordinary positions may change.  This is the
unbind-skipping transport needed when the appended `unbind 0 0` carries a
boundary across a newly inserted name.  (`conv-snoc-unbind`: appending a
unbind makes it run first, and a conversion reading skips it.)

`merged-conversion-exists`.  The MERGED frame's conversion reading
exists and retains every name available at the inner frame's conversion
context.  The lifted outer conversion runs first; its output contains
the lifted outer interior, so `conv-weaken` restarts the inner
conversion from that larger map and retains the inner output in the
merged output.  This is the last module parameter progress and type
safety shed, on 2026-09-21 (`notes/DECISIONS.md`).

### §3d — renaming the representation universe

The change run and both readings.  An `unbind` deletes at the same
ordinary position and records freshness of the RENAMED name; an
`bind` inserts at the same position.  Nothing here is arithmetic on
ordinary positions, which is why the ordinary spelling survives.  Under
a representation renaming the scope is renamed by `renᴮᴿ ρ`, the name
maps by `map ρ`, and the store is whatever the `RepWk` says — no bind
prefix, no `extN` offset.

`snoc-unbind0-conversion-ren`.  The snoc `Θ ++ (unbind 0 0 ∷ [])` carries a
scope past one fresh cell and one fresh ordinary name (`Nu-⟪⟫`).
The conversion reading: representation renaming transports the old
reading, the appended unbind is skipped, and `conv-weaken` restarts the
transported run in the map that also holds the fresh name; it retains
the REPRESENTATION-RENAMED old names.
`snoc-unbind0-interior-ren`: the interior reading, where the appended
unbind acts first and deletes the fresh name, after which the renamed old
changes run as before.

### §4 — `TyBetaBoundary`

`inst []`, the outer scope of every `Nu` contractum, and the scope
`⊢ν` reads its conversion under.  At `empty` it is `Nu-Λ` on
`ν ℕ · (Λ N) ⟨ c ⟩`: the cell is allocated and the scope binds name 0
for it.  (The name is from the retired `TyBeta`, whose boundary this
was.)

### Retired

* "whenever the exterior is and THE BIND BLOCK CHECKS" (§3a), "its
  interior is just the exterior UNDER THE ORIGINAL BIND BLOCK"
  (`rewind-interior`, `dual-interior`), "shifted past the bind block"
  (`int-valid`), "the bind block, the two readings" (`BoundaryWf`'s
  stored fields), and "the parallel-bind lifting this used to need —
  `underRepBinds`, `shiftRVars`" (`merged-interior`) — a boundary has
  no bind block, so each of these clauses is simply deleted and the
  statements are the plainer ones above.

## Conversion.agda

Conversions — the `c` of a boundary `M ⟪ Θ , c ⟫`.  §1 the grammar; §2
the typing judgement `Δ ⊢ c ∶ A ⇝ B`; §2b the re-spelling relation
`SameConv` and its uniqueness; §2c re-spelling across a crossing;
§2d representation renaming; §3 `mkId`; §4 the canonical mints at a
slot (`reveal`/`conceal`, `instReveal`/`instConceal`); §5 the
inversions; §6 `conv-types-unique`; §7 concrete lookup-square checks.

### Where the grammar comes from

The grammar and the names are GTSF's (see `GTSF/Conversion.agda`,
`GTSF/Coercions.agda`): `id` / `seal` / `unseal` / `_↦_` / `` `∀ ``.
The echo is deliberate — Jeremy's Q3 answer was "use Conversion for
relating the interior type to the exterior type", and this is that
judgement, with GTSF's two mutually defined directions merged into ONE
family.

### NO POLARITY (Jeremy's ruling, 2026-09-06)

The judgement carried a global index `p` that fixed `unseal` to a
REVEAL position and `seal` to a CONCEAL one, flipping on `conv-fun`'s
domain.  It is REDUNDANT: the discipline it enforced is PER TYPE
VARIABLE, and `env` already enforces it with the FRAMES — a UNBOUND `X`
is DELETED from the interior reading, so it cannot sit on the interior
side of a leaf, and a name the scope itself BINDS has no entry in the
exterior name map, so it cannot sit on the exterior side.  Dropping `p`
is what makes the `Nu` boundary rules' preservation cases theorems at
every `∀` conversion rather than only at a reveal one
(`proof/Preserve.agda`, `preserve-Nu-⟪Λ⟫`, `preserve-Nu-⟪⟫`).

### Conversions are REP-FREE

`seal` and `unseal` carry an ordinary type-variable NAME, never a
representation spelling.  The lookup square `Δ ∋ X := A` follows that
name to its representation variable and relates the stored
representation payload back to the ordinary type `A`.  This is why a
representation-only renaming leaves a conversion and both of its types
UNCHANGED — see §2d below.

### §1 — `id`

`id A` is restricted to BASE TYPES AND VARIABLES by the typing
judgement (`conv-id` / `conv-idv`) and by the classification in
`Terms.agda` (`A-idb` needs `Base A`, `I-idv` needs a variable
payload); compound identities stay structural (`mkId`, §3).

### §2 — `Δ ⊢ c ∶ A ⇝ B`

`c` converts the SOURCE type `A` to the TARGET type `B`, both read on
the type context `Δ` — the CONVERSION CONTEXT, the type context at
which the boundary's binders are live (§ Boundary.agda, law (1)).
Every representation is read by NAME from `Δ`.  `conv-fun` is
CONTRAVARIANT in its domain — that is the only trace the retired
polarity index leaves.

* `conv-unseal` is the REVEAL: the interior sees the abstract name, the
  exterior its representation.
* `conv-seal` is the CONCEAL: the interior sees the representation, the
  exterior the abstract name.  THE SOUNDNESS GATE: a seal must cite a
  LIVE BINDER on its type context (`proof/Adversary.agda`).

### §2b — `SameConv`, two spellings of one conversion

`_⊢_≈_⊣_` (`Ctx.agda` §5) relates two ordinary spellings of ONE
representation-universe type.  `SameConv` is the same thing for a
CONVERSION, and it exists for the same reason: a rule that carries a
conversion from one name map to another cannot reuse the spelling,
because the two maps can reorder relative to each other (§ Reduction.agda
/ The crossing-spelling law).

A conversion mentions ordinary names at exactly three leaves — `seal`,
`unseal`, and the type under `id` — so the judgement is `_⊢_~_` one
universe up, structural everywhere else.  `sameᶜ-rep-unique` determines
the spelling, so a rule carrying it stays a function;
`sameConv-src-unique` is `Peel`'s determinism case, in the shape
`sameTy-src-unique` has.

### §2c — re-spelling across a crossing

These facts were proved first in `notes/PeelPremise.agda`.  They are
core infrastructure now because progress must construct every premise
carried by `Peel`.  `Q` and `dual-conversion-exists` live with the
relational context readings in `Boundary.agda` §3b–3c; this section
transports the actual type and conversion spellings.

### §2d — renaming the representation universe

A conversion is REP-FREE: every name it carries is ORDINARY, and a
representation-only renaming moves no ordinary name.  So a conversion
and both of its types survive the move UNCHANGED; what moves is the
CONTEXT it is read on — the lookup square follows the same ordinary
name to a renamed representation variable with a renamed payload
(`∋:=-ren`, `proof/Ctx.agda` §3).

### §4 — the canonical mints at a slot

`reveal` / `conceal`: unseal every occurrence of `X` where the
conversion runs covariantly, seal it back where it runs
contravariantly.  These are what the boundary rules mint at a fresh
binder; they are DERIVED FROM THE TYPE, not from stored knowledge, and
they carry only the NAME `X`.

`instReveal` / `instConceal` — THE SAME MINT, APPLIED TO A CONVERSION
(the `TyPeelR` repair, `notes/RuleRepairs-TyPeelR-CancelR.md` §1).  When
a boundary whose conversion is a `` `∀ `` is instantiated, the
boundary's frame gains a BINDER at slot 0 — the slot the conversion's
`` `∀ `` had left ABSTRACT.  Every leaf of the conversion that reads
that slot is an identity (`id (` 0)`, because an abstract slot has no
binder to seal or unseal at), and each such leaf must become the
instantiation step: `unseal 0` where the conversion runs covariantly,
`seal 0` where it runs contravariantly.  That is exactly
`reveal`/`conceal` pushed through a CONVERSION instead of through a
type — and on an identity conversion the two agree
(`instReveal-mkId`).

NO RULE MINTS `instReveal` SINCE 2026-09-24.  The retired `TyPeelR-Λ`
and `TyPeelR-⟪⟫` minted `instReveal 0 s`, fusing the crossed conversion
with the instantiation.  Their `ν` successors STACK instead: `s` moves
verbatim into a middle layer and `ν`'s own conversion — the compiler's
`reveal 0 C`, or `Nu-⟪⟫`'s run-time `reveal 0 (⇑Bᵢ′)` — sits outside it
(§ Reduction.agda / Nu-⟪Λ⟫, Nu-⟪⟫).  `reveal` is the only mint that
survives, and the compiler writes it.  `instReveal`/`instConceal` stay
here with `instReveal-mkId`, and `proof/Canonicity.agda` keeps the
refuted `CanonTyPeelR` about them as a record.

### §5 — the inversions

`seal-source-is-rep`: every representation a conversion mentions IS the
binder's representation — there is no second spelling, which is why the
≡/≈ gap of the gauntlet's stuck term cannot arise here
(`notes/BoundarySurvey.md` §9m, `notes/DesignPoints.md` §9m).

`conv-all-inv`: a `∀` conversion's body, as an inversion that returns
the two `∀` shapes AS EQUATIONS.  At the use sites the conversion's
source and target are variables that `env` constrains only
RELATIONALLY, so matching `conv-all` directly does not unify; the
`Nu-⟪Λ⟫`/`Nu-⟪⟫` premise `underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ` is recovered by this
lemma instead.  (History: the
lemma was introduced when `env` pinned the target type to a
`shiftBy`-headed stuck term, which could not be seen through either.)

### §6 — `conv-types-unique`

Its premise is the exact invariant used at `seal` and `unseal`: one
representation variable has at most one ordinary name.  All contexts
produced by well-formed boundary scopes preserve this invariant
(`Boundary.agda` §3a).

### Retired

* "a UNBOUND X is masked in `interior`" / "a BOUND X is not in the image
  of `shiftBy`" (the no-polarity argument) — there is no masking and no
  bind block; the same argument is made above with deletion from the
  interior reading and absence from the exterior name map.
* "`env` pins the target type to `shiftBy (numBinds Θ) Bₑ`, which is a
  stuck term" (`conv-all-inv`) — `env`'s exterior premise is the
  relation `Δ ⊢ Bₑ ≈ Cₑ ⊣ Δᶜ`; the lemma is still needed, for the
  reason given above.

## Terms.agda

The term syntax, the typing judgement, and values.  §1 is `Var` (= ℕ)
and `Term` — with `ν_·_⟨_⟩` in place of type application since
2026-09-24 — whose last constructor is the boundary `_⟪_,_⟫`, together
with the ordinary term context `Ctx`, its lookup `_∋_⦂_` and the
type-binder lift `⤊`.  §2 classifies a conversion as `Inert` or
`Active`, with `act-or-inert` and `act-not-inert`.  §3 is `Value`,
which comes BEFORE the typing judgement because `⊢Λ` reads it.  §4 is
`_∣_⊢_⦂_`, whose boundary rule is `env`, whose `⊢Λ` carries the
VALUE RESTRICTION and whose `⊢ν` types the ∀-elimination, plus
`value-var-visible`.  §5 is the concrete `β-seven` / `β-seven-⊢`.

NO OPERATIONS AND NO METATHEORY.  Renaming and substitution on terms
are `TermSubst.agda`; reduction is `Reduction.agda`; the decision
procedures that BUILD these derivations are `TypeCheck.agda`; canonical
forms, preservation and progress are under `proof/`, with the public
theorem statements in `Preservation.agda`, `Progress.agda` and
`TypeSafety.agda`.

### The four laws a reader must know

1. `env` never COMPUTES the two contexts a boundary scope induces: it
   takes `BoundaryWf Δ Θ Δᵢ Δᶜ` (`Boundary.agda`) and the two contexts
   are its OUTPUTS.  The retired `interior` / `convCtx` functions are
   gone.
2. The three sides can spell the same semantic type differently, so
   `env` compares them by the REPRESENTATION each denotes, by one and
   the same relation on both sides: `Δᵢ ⊢ Bᵢ ≈ Cᵢ ⊣ Δᶜ` inside and
   `Δ ⊢ Bₑ ≈ Cₑ ⊣ Δᶜ` outside (`Ctx.agda` §5).  A boundary's interior
   is TERM-CLOSED — `Δᵢ ∣ [] ⊢ M ⦂ Bᵢ` — which is what lets
   `TermSubst.agda` leave wrappers alone.
3. Classification in §2 is by the CONVERSION CONSTRUCTOR alone: no
   source or target type is inspected and no slot arithmetic occurs, so
   `id` at a variable is inert and `id` at a base type is active.
4. THE VALUE RESTRICTION: `⊢Λ` requires `Value N`, and there is NO
   `ξ-Λ` — reduction never goes under a `Λ`.  This is where
   `strong-rep-nu` departs from `strong-rep-var`, whose `⊢Λ`
   accepted any body and whose `ξ-Λ` reduced under the binder (the
   reason `V-Λ` carries `Value N` there; `notes/DECISIONS.md`,
   repair 3).

### The shape of a boundary

```
  M ⟪ Θ , c ⟫   with ONE frame change:

    Θ : Boundary   a sequential list of ordinary-variable binders and
                   anti-binders — `Boundary = List Change`, nothing
                   else since the representation binders moved to the
                   ambient store.  `BoundaryWf Δ Θ Δᵢ Δᶜ` produces the
                   interior context Δᵢ and conversion context Δᶜ.

    c : Conv       the conversion checked on Δᶜ.  Its source is related
                   to the interior term's type through `_⊢_≈_⊣_`; its
                   target is related to the exterior type the same way.
```

### §2 — `Inert` / `Active`

```
  Inert  = { s ↦ t , `∀ s , seal X , id-at-a-variable }
  Active = { unseal X , id-at-base }
```

`act-or-inert` is totality over TYPED conversions: the payload
restriction on `id` makes classification a match on the TYPING
derivation, so the untypeable compound identities are never classified
at all.

### §3 — `Value`, and `V-Λ`'s premise

`V-Λ` carries `Value N`.  In `strong-rep-var` it was FORCED: reduction
went under `Λ` (`ξ-Λ`), so without the premise `Λ N` was a value for
every `N` and both "values don't step" and determinism failed
(`notes/DECISIONS.md`, repair 3).  `strong-rep-nu` has no `ξ-Λ` and
its `⊢Λ` rule demands `Value N` OUTRIGHT, so on well-typed terms the
premise is automatic; it is kept so that `Value` stays the
`strong-rep-var` relation VERBATIM and so that `Nu-Λ`'s premise keeps
meaning the same thing on untyped terms.

### §4 — `⊢Λ`

THE VALUE RESTRICTION (`strong-rep-nu`'s first experiment).  A type
abstraction's body must ALREADY be a value: there is no `ξ-Λ` rule, so
a `Λ` over a redex would be stuck.  With the premise, `Λ N` is a value
the moment it is well typed (`V-Λ`), and `Nu-Λ`'s own `Value N`
premise is discharged by the typing derivation.

### §4 — `⊢ν`

THE ∀-ELIMINATION (2026-09-24, `notes/NuSketch.md`).  `ν A · L ⟨ c ⟩`
instantiates `L : ∀ C` at a fresh cell holding `A`'s representation `R`
and converts the result with `c`.  The premises are the `env` pattern,
read at the context the `Nu` rules leave:

```
  Δ ⊢ᵗ A,  Δ ⊢ᶜ A ~ R                  the argument and its representation
  Δ ∣ Γ ⊢ L ⦂ ∀ C                      the operator
  BoundaryWf (allocate R Δ) TyBetaBoundary Δᵢ Δᶜ
                                       the scope `inst []` over the cell
  Δᶜ ⊢ c ∶ C ⇝ Cₑ                      c, read on its conversion context
  allocate R Δ ⊢ B ≈ Cₑ ⊣ Δᶜ,  Δ ⊢ᵗ B  the result, compared by
                                       representation as `env` does
```

ANY `c` WHOSE TYPES LINE UP IS ACCEPTED (Jeremy, 2026-09-24, as GTPLC's
`⊢ν` does).  The compiler always writes `reveal 0 C`
(`Compile.agda`; its typing is `compile-ν`, `proof/Compile.agda`), but
the generality is used at run time: `Nu-⟪⟫` pushes a `ν` whose
conversion is the reveal of an INNER body, and the typing rule must not
care who wrote it.

WHY `c` IS READ AT `Δᶜ` AND NOT AT `underΛ Δ`.  `c`'s ordinary variable
0 is the name `inst []` binds for the new cell, so its source `C` reads
that name as REPRESENTED — the same `abstR → bindR R` refinement the
contractum's body undergoes.  Every `Nu` contractum's outer layer is
`⟪ inst [] , c ⟫`, and `preserve-Nu-*` retype it by reusing these
premises verbatim (`nu-outer`, `proof/Preserve.agda` §3).

WHY `⊢ν` CARRIES A `BoundaryWf`.  It is what `nu-outer` needs, and it
has a consequence for the metatheory: a `ν` cannot be typed at a
context whose allocation is ill formed, so the old `TyBeta`
counterexample to premise-free preservation no longer exists in
well-typed form (§ Preservation.agda / Why `WfCtx Δ` is part of the
statement).

### §4 — `env`

The boundary scope witness supplies both contexts.  Since ordinary
variables may be inserted and removed, the same semantic type can have
different ordinary de Bruijn spellings on the three sides; `_⊢_≈_⊣_`
compares them by the representation each denotes.  Since experiment 2 a
boundary carries no bind block, so the exterior and the conversion
context share ONE store and the exterior comparison is the SAME
relation as the interior one.

### §4 — `value-var-visible`

A value's variable type is VISIBLE on the value's own type context,
because `env`'s last conjunct checks it there.  So a boundary can never
conceal the slot its conversion names.

### §5 — `β-seven`

The term `Nu-Λ` produces on `ν ℕ · (Λ ($ 7)) ⟨ id ℕ ⟩` (`Nu-ℕ`,
`Reduction.agda`), typed at the context `Nu-Λ` LEAVES: the cell for `ℕ`
has been allocated.

### Retired

* "the bind-prefix crossing `SameTyExt`" in law (2) and "`SameTyExt` is
  gone" at `env` — stated once above as "one store, the same relation
  on both sides".
* "on the value's BIND type context" (`value-var-visible`) — there is
  no bind block; the context is the value's own.

## TermSubst.agda

Renaming and substitution on terms — THE PUBLIC HALF.  §1 is the PAIRED
type-level renaming `TyRename = ren² ordinary represent` with `idᵗ`,
`renᶠ²`, the scope-level `renᴮ² ρ Θ = map (renᶠ² …) Θ` (a boundary IS
its change list, `Boundary.agda` §3) and `underΛ-ren`.  §2 is `renᴹ²`
on terms, the REPRESENTATION-ONLY traversal `renᴹᴿ`, and the sibling
shifts `↑ᴹ[_]` / `↑ᴮ[_]`.  §5 is substitution — `Img`, `imgTm`,
`shiftᴵ`, `crossΛᴹ`, `⇑ᴵ`, `extᴵ`, `substᵐ`, `betaEnv` and `_[_∶_]ᵐ`,
the substitution `Beta` performs.

ONLY WHAT A PUBLIC FILE NEEDS IS HERE (2026-09-22, the AGENTS.md
public/private mandate).  Every lemma about these operations, and every
definition no top-level module mentions — the derived
`renᴹ`/`wkN`/`wkᴹ`/`⇑ᴹ`/`id²`/`renᶠ`, the value-preservation and
ordinary-identity families, TERM-VARIABLE renaming `extⁿ`/`renⁿ`/
`shiftᵐ` with `⊢renⁿ`/`⊢weakenⁿ`, the `⤊` transports, and the typed
images `_∣_⊢ⁱ_⦂_` — is `proof/TermSubst.agda`.  That file KEEPS the
section numbers its material had here (§1–§6), and the numbers here are
unchanged for the same reason: other modules cite them, so do not
renumber either file.

WHAT IS DELIBERATELY ONE LAYER DOWN.  `extN` is `Ctx.agda` §8 and the
representation-only `renᶠᴿ` / `renᴮᴿ` are `Boundary.agda` §2/§3, beside
the syntax they act on, because the representation-renaming metatheory
of `Boundary.agda` §3d is stated over them and cannot import this
module.  Reduction is `Reduction.agda`; the typing transport for
`renᴹᴿ` and `crossΛᴹ` is `proof/RepWeaken.agda` (`rep-weaken-⊢`,
`cross-Λ-⊢`).

### The two laws a reader must know

1. Boundaries are TERM-CLOSED (`Terms.agda`, `env`), so `substᵐ` does
   NOT descend into `_⟪_,_⟫`.
2. `Beta` is FRAME-EXACT: a closed value image crossing a `Λ` is
   wrapped in that binder's DUAL with an identity conversion at the
   argument's type (`crossΛᴹ`, used by `⇑ᴵ`), which is why `_[_∶_]ᵐ`
   carries the `ƛ`'s own annotation instead of shifting.

### §1 — why type renaming carries two maps

Ordinary type variables and representation variables have distinct de
Bruijn universes.  Consequently a syntax-level type renaming carries
two maps:

* the ORDINARY map renames term annotations, type arguments, conversion
  names, and the positions carried by `unbind` and `bind`;
* the REPRESENTATION map renames boundary scope payloads and the
  representation-variable occurrence carried by every change.

### §2 — `↑ᴹ[_]`, `↑ᴮ[_]`, the sibling shift

Experiment 2.  When a step allocates a cell, every representation
variable of the redex's SIBLINGS — terms and boundary scopes alike —
moves up by one; when it does not, nothing moves.  So `↑ᴹ[ new R ]` is
`renᴹᴿ suc` and `↑ᴹ[ none ]` is the identity.

### §5 — `crossΛᴹ`, `⇑ᴵ`

A value crossing `Λ` is weakened only in the free representation
universe and wrapped in the binder's DUAL.  The unbind removes the fresh
ordinary variable, so the surviving ordinary indices retain their old
positions; representation occurrences move past the new abstract
binder.

`⇑ᴵ`: variables cross a type binder unchanged.  Closed value images
acquire the frame-exact wrapper above, and their ordinary type spelling
is weakened.

### §5 — `betaEnv`

The substitution `Beta` performs: the argument, carrying the `ƛ`'s
annotation, for variable zero; every other variable steps down.  It is
a NAMED function, not a pattern lambda, so that `Residual.agda` can
cite the very same substitution when it follows a position through
`Beta`.

## Reduction.agda

The rule set.  §1 is `_⊢_-→_∣_` with fourteen rules — `Nu-Λ`, `Beta`,
`Peel`, `Nu-⟪Λ⟫`, `Nu-⟪⟫`, `CancelR`, `Drop$`, `Drop-true`,
`Drop-false`, `IdPush` and the four congruences `ξ-·-l`, `ξ-·-r`,
`ξ-ν`, `ξ-⟪⟫` — plus the concrete check `Nu-ℕ`, the multi-step
`_⊢_-→*_` and `runCtx`.  §2 is `value-¬step`.  (`det` is
`proof/Determinism.agda`.)

What is *not* here: the typing judgement is `Terms.agda`; the decision
procedures that DISCHARGE these rules' side conditions are
`TypeCheck.agda`, and the redex search that assembles them is
`Eval.agda`.  Preservation, progress and canonical forms live under
`proof/` with their public statements in `Preservation.agda`,
`Progress.agda` and `TypeSafety.agda`.

### The crossing-spelling law

This is the one law a reader of the rules must know, and it is the
reason five rules carry a premise that looks redundant.

> When a rule MOVES a subterm between two name maps, the moved spelling
> is CARRIED by the rule as a named premise and PINNED by a `Same…`
> relation — `SameConv` (`Conversion.agda`) for a conversion,
> `_⊢_≈_⊣_` (`Ctx.agda` §5) for a type or a bare name — and is NEVER
> computed by a fixed renaming.  The crossing is by the
> REPRESENTATION a name denotes, never by arithmetic on its position,
> because the two contexts can reorder relative to each other.

Five such spellings are carried today, and each was installed only
after a machine-checked defect:

| spelling | rule | pinned by | date | wall |
|---|---|---|---|---|
| `s′`  | `Peel`       | `SameConv Δᵈ s′ Δᶜ s`        | 2026-09-18 | `notes/CrossingAudit.agda`, `notes/PeelPremise.agda` |
| `Bᵢ′` | `Nu-⟪⟫`      | `≈` at the interior          | 2026-09-18 | `notes/ForallPayloadWall.agda` |
| `X′`  | `IdPush`     | `≈` at the merged frame      | 2026-09-18 | `notes/ForallPayloadWall.agda` |
| `A′`  | `CancelR`    | `≈` at Θ₁'s OWN conv. ctx    | 2026-09-19 | `notes/CancelRShiftWall.agda`, `notes/CancelRReachabilityWitness.agda`† |
| `s″`  | `Nu-⟪⟫`      | `SameConv` at `underΛ Δ″ᶜ`   | 2026-09-20 | `notes/AddLock0Wall.agda`† |

(The dates are those of the pre-`ν` rules, `TyPeelR-⟪⟫` for the `Nu-⟪⟫`
rows; both spellings moved to `Nu-⟪⟫` unchanged on 2026-09-24.  † kept
unported and no longer gated by `notes/All.agda` since 2026-09-24:
their checked content is exact states of runs through the retired
rules, and strong-rep-store holds their checked versions.)

A sixth defect of the same reading discipline hit the CONVERSION
CONTEXT itself rather than a spelling: a conversion reading skips
unbinds, so a later `bind` can meet a name that is already live.  That
is the clause `conv-bind-live` (2026-09-17, `notes/ReUnlockWall.agda`,
`Boundary.agda` §3; see § Boundary.agda / `_∣_⊢χᶜ_⇒_`).

Determinism for the carried premises is `sameConv-src-unique`,
`sameTy-src-unique`, `conv-src-unique` and `same-rep-unique`; for the
lookup-carrying rules it is `∋:=-det`.

### The repairs the rule set carries (history)

The conversion-boundary design was repaired five times before the fork,
with the repairs ruled in `notes/DECISIONS.md` ("Id-layer RULING",
2026-09-05).  Each repair is still visible in a rule's shape.

1. `V-Λ` carries `Value N` (in `Terms.agda`).  In `strong-rep-var` that
   was because reduction went under `Λ`; here `⊢Λ` itself demands
   `Value N` and `ξ-Λ` is gone.
2. `TyPeelR` shifts its type annotation, and is SPLIT IN TWO —
   `TyPeelR-Λ` and `TyPeelR-⟪⟫`, today `Nu-⟪Λ⟫` and `Nu-⟪⟫` — by the
   shift audit (`notes/ShiftAudit.md`, 2026-09-08), so that no moved
   subterm is offered a slot it could not name before.
3. `CancelR` drops the residue its mini-core ancestor appended, carries
   the BINDER-LOOKUP premise that determines its `mkId` conversion, and
   names its two conversions separately.
4. `IdPush` replaces `IdAbsorb`: the two conversions are SWAPPED
   instead of the two frames being merged, so no boundary-scope
   arithmetic is needed and the no-⊕ test is passed by construction.
5. `TyBeta`, today `Nu-Λ`, carries `Value N`.  In `strong-rep-var` that
   closed the `TyBeta` / `ξ-·[] ⨟ ξ-Λ` overlap; here it is implied by
   `⊢Λ`.

The principle behind (3)/(4): EVERY rule that mints an identity
conversion at a looked-up representation carries the binder-lookup
premise, and determinism for that lookup is exactly `∋:=-det`.  Since
2026-09-23 `CancelR`'s `mkId A′` is the only such mint left — `IdPush`
mints no identity at all — so `CancelR` carries one lookup,
`Δ₁ᶜ ∋ X := Aᵢ`, and `IdPush` carries none.

### The two-universe / store port

A `ν` carries an ordinary type `A`, but a ∀-elimination mints a
representation payload `R`.  The three `Nu` rules therefore carry
`Δ ⊢ᶜ A ~ R`, return the store change `new R` — the cell is pushed onto
the AMBIENT representation context at index 0 (`allocate`, experiment
2, `notes/RepStoreSketch.md`) — and build the outer layer `inst []`,
which binds ordinary name 0 for that cell; the two boundary rules put
the crossed frame under it as `liftᴮ Θ`, which shifts the old changes in
both universes.

A boundary scope IS its change list (`Boundary = List Change`), so the
frames the rules build are plain list expressions: `Θ₁ ++ Θ₂` where
`CancelR` and `IdPush` merge, and `renᴮᴿ suc Θ′ ++ (unbind 0 0 ∷ [])`
where `Nu-⟪⟫` moves a boundary past the cell it just minted.
Congruence rules carry the relational interior/conversion-context
witnesses rather than computing those contexts, and shift the redex's
SIBLINGS by the store change.

### `_⊢_-→_∣_` — the store change

A step returns the CHANGE it made to the store: `none`, or `new R` when
a ∀-elimination allocated the cell for `R`.  The contractum therefore
lives at `apply δ Δ`, not at `Δ`, and the congruences shift the redex's
siblings by `↑ᴹ[ δ ]` / `↑ᴮ[ δ ]` (`TermSubst.agda` §2).

### `Nu-Λ`

A boundary is BORN: the ∀-elimination mints THE BINDER of the event.
The contractum is `N ⟪ inst [] , c ⟫` at change `new R`, and `c` is the
conversion `ν` carries, moved verbatim.

THE REVEAL MOVED TO COMPILE TIME (2026-09-24, `notes/NuSketch.md`,
rule 1).  The rule's predecessor `TyBeta` reduced `(Λ N) ·[ B , A ]`
and MINTED `reveal 0 B` from the annotation `B`.  The compiler now
writes that reveal into the `ν` (`Compile.agda`), so a compiled program
takes exactly the step it took before and reaches the same contractum;
only the origin of the conversion changed, and `B` is gone from the
run-time term.  Since `⊢ν` accepts any `c` whose types line up, the rule
does not look at `c` at all.

THE VALUE PREMISE (repair (5), history).  In `strong-rep-var` reduction
went under `Λ`, and the premise kept `TyBeta` from overlapping
`ξ-·[] ⨟ ξ-Λ`.  `strong-rep-nu` has no `ξ-Λ`, and `⊢Λ` demands
`Value N`, so on a well-typed redex the premise is supplied by the
typing derivation.  It is kept verbatim so that the untyped relation is
unchanged.

### `Beta`

FRAME-EXACT (2026-09-08).  The substitution CARRIES THE ARGUMENT'S TYPE
— the `ƛ`'s own annotation `A` — because every image that crosses a `Λ`
in the body is wrapped in that binder's DUAL with an IDENTITY
conversion at the argument's type (`crossΛᴹ`, `TermSubst.agda` §5).

Shifting alone (the old `N [ W ]ᵐ`) was sound but not frame-exact: the
argument's frame silently gained the `Λ`'s slot.  Determinism is
unaffected — `A` is read off the redex, so the contractum is still a
function of the redex alone.

### `Peel`

THE CROSSING.  The application is pushed in one layer and the argument
acquires the DUAL.  `s`/`t` are `↦`'s components: the crossing
argument's conversion is RE-BASED by the repointing.

IT CARRIES THE DUAL'S SPELLING (2026-09-18, the crossing audit).  `s`
is read at Θ's conversion context and is used at the DUAL's, which is
taken at the interior — a different name map, and not merely a
renumbering of the same one: the invariant that would have made the two
agree, `conv(dual Θ, int(Θ,Δ)) ≡ conv(Θ,Δ)`, is FALSE here, and `_++_`
is what breaks it (`notes/CrossingAudit.agda` §§4–6).  So the rule
NAMES the dual's spelling `s′` and carries a `SameConv` relating it to
`s`, exactly as `Nu-⟪⟫`, `IdPush` and `CancelR` carry `_⊢_≈_⊣_`.

The premise never blocks a reduction.  The two contexts name the same
representation variables — that is (Q), `notes/PeelPremise.agda` §5 —
and a well-typed conversion always has a reading to transport, so a
witness always exists (`peel-premises-env`, `Conversion.agda` §2c).
`t` needs no premise: it stays on the same boundary, at `Δᶜ`, where it
was read.

Since experiment 2 the argument crosses VERBATIM: no representation
renaming is applied to `W` at all (see § Residual.agda).

### `Nu-⟪Λ⟫`, `Nu-⟪⟫`

`ν` OVER A BOUNDARY — the ∀-conversion analogue of `Peel`.  IT IS TWO
CLAUSES, split on the crossed boundary's INTERIOR (2026-09-08, the
shift audit, `notes/ShiftAudit.md`, when the rules were `TyPeelR-Λ` and
`TyPeelR-⟪⟫`).

`canon-∀` (`proof/Canonical.agda`) says a closed value at a `∀` type is
a `Λ` over a value or a WRAPPER with a `∀` conversion, and nothing
else.  So:

```
  Nu-⟪Λ⟫   the interior is `Λ N`: INSTANTIATE AT ONCE.  N moves
           nowhere, gains no shift, and the boundary is born on
           the spot.
  Nu-⟪⟫    the interior is a boundary: PUSH A `ν` AT THE NEW NAME
           INWARD one layer, and mask that name in the MOVED
           BOUNDARY'S OWN change list (the snoc `++ (unbind 0 0 ∷ [])`).
```

Together they are TOTAL over canonical `∀`-values (`progress`,
`proof/Progress.agda`; `nuRedex`, `Eval.agda`).

STACK, DON'T FUSE (Jeremy, 2026-09-24, `notes/NuSketch.md` candidate
N1).  Both contracta have the same two outer layers:

```
    (… ⟪ liftᴮ Θ , s ⟫) ⟪ inst [] , c ⟫
```

`ν`'s own conversion `c` is the OUTER layer, on the scope `⊢ν` read it
at, and the crossed conversion `s` is the MIDDLE layer, moved VERBATIM,
on the crossed frame read under the new name (`liftᴮ Θ`, Θ shifted one
step in both universes).  The retired rules wrote ONE layer,
`N ⟪ inst Θ , instReveal 0 s ⟫`: they FUSED `s` with the reveal
`TyBeta` would have minted.  With `c` written by the compiler there is
nothing to fuse with — the alternative, a run-time conversion
composition `s ⨟ c` (N2), would put back the run-time work the
compile-time reveal removed.  So NO RULE COMPUTES A CONVERSION FROM `c`,
and none mints `instReveal`.  Read inside out the two scopes act as the
old fused one: `inst Θ = liftᴮ Θ ++ inst []`, by `refl`
(`Nu-⟪Λ⟫-stacks-to-inst`, `proof/ShiftAudit.agda` §3).  The cost is one
more layer per crossing, which a later `Peel` passes and an `IdPush` or
a `Drop` consumes: every run in `Examples.agda` that crosses a boundary
got longer (K 9→11 … V 24→49; `notes/DECISIONS.md`, 2026-09-24).

WHY THE MOVED VALUE'S FRAME MUST NOT GAIN AN UNMASKED SLOT.  In the
store design `W` moves by the representation-only renaming `renᴹᴿ suc`
— past the cell this rule allocates — while the new ORDINARY name 0 is
removed from the moved boundary's interior reading by the appended
`unbind 0 0`.  `W` is therefore offered exactly the ordinary scope it
already had.  (History, and the reason the split exists: in the
masked-entry ancestor the single rule moved `V` by `wkᴹ 1` into its old
frame with ONE NEW SLOT, offered UNMASKED.  `V` neither had that slot
nor could use it — `wkᴹ 1` sends every index to ≥ 1 — so the frame said
more than the truth: the tight frame and the live one differed by
exactly one re-exposure step, which `_⊑ᵃ_`, the refinement a TERM may
travel along, REFUSES.  See `notes/ShiftAudit.md`, "The TyPeelR leak";
the surviving Agda half is `proof/ShiftAudit.agda` §3.)  Every other
rule masks what it introduces — `Peel` by the dual, `Beta` by `crossΛ`
— so this was the one exception, and the audit closed it.

WHY THE `Λ` CLAUSE NEEDS NO SHIFT.  The `Λ`'s abstract slot BECOMES the
cell the outer layer binds: `N` already lives one `abst` binder in
(`⊢Λ`, `underΛ`), and the cell is allocated at index 0, exactly where
`N`'s own abstract variable already sits, so `N` moves into the
contractum VERBATIM and its re-typing is the in-place refinement
`abstR → bindR R`.  Hence no renaming of `N`, and the contractum does
not mention `Bᵢ` at all.

WHY THE WRAPPER CLAUSE TERMINATES.  Its contractum's pushed `ν` is again
a redex (reached by `ξ-⟪⟫` through the two stacked layers), but the
`∀`-value's TOWER HEIGHT — the number of nested boundaries above the `Λ`
— strictly DECREASES (`Nu-⟪⟫-height`, `proof/ShiftAudit.agda` §4),
because the clause CONSUMES a boundary that was already there.  The
rejected repair (wrap the moved value in the new binder's dual) MINTS
one instead, so its measure stalls and it loops: an identity conversion
at a `∀` is necessarily a `` `∀ `` conversion, hence inert, hence the
wrapped value under a `ν` is itself a redex (`fixA-height-stalls`,
`proof/ShiftAudit.agda` §4; the looping run is written out in
`notes/ShiftAudit.md`, candidate fix (a)).  A tower of height `h`
therefore takes `h − 1` `Nu-⟪⟫` steps and then exactly one `Nu-⟪Λ⟫`
step.

THE BODY PREMISE (2a).  Both clauses carry the typing
`underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ` of the crossed conversion's body.  The
interior body `Bᵢ` is not syntactic (a `seal`'s source is a binder's
representation, which the representation-free conversion does not
carry) but it IS DETERMINED by the conversion typing, so the rules carry
that typing as a PREMISE — the same move already ruled for the `mkId`
conversions.  It is read at the ∀-body, i.e. under one `abst`, and
progress derives it for free by inverting the redex's own `env`
(`conv-all-inv`).  `Nu-⟪Λ⟫`'s contractum does not use it; `Nu-⟪⟫`'s
writes it, re-spelled as `Bᵢ′`, into the pushed `ν`'s conversion.
Determinism is `conv-src-unique` for the wrapper clause; the `Λ` clause
needs nothing.

### `Nu-⟪Λ⟫`

THE SHIFT.  The middle layer's frame is `liftᴮ Θ = map shiftChange Θ`
(`Boundary.agda` §4): the cell is allocated in the AMBIENT context at
index 0, so every one of Θ's changes moves up in BOTH universes.  The
outer layer's `inst [] = bind 0 0 ∷ []` makes ordinary name 0 denote the
new cell, and it acts FIRST, so the middle layer is read at a context
where name 0 is the new cell and Θ's old names sit one step up.  (In the
bind-block ancestor the boundary's own changes were left UNSHIFTED,
because the interior reading itself lifted the boundary's binds past the
prepended binder — history.)

THE CONVERSION.  `s` is moved VERBATIM.  Its body's slot 0 was the
`` `∀ ``'s abstract variable; in the middle layer it reads as ordinary
name 0, which the outer layer binds to the new cell, so `s` is typed at
exactly the conversion context `liftᴮ-conversion` produces from the
crossed one, and `preserve-Nu-⟪Λ⟫` retypes the middle layer from the
crossed `env`'s premises, refined at the new cell (`liftᴮ-interior`,
`liftᴮ-conversion`).  The leaves of `s` that read slot 0 are
identities, and they STAY identities: the instantiation step is `c`'s
job, one layer out.  (The retired `TyPeelR-Λ` had to turn them into
`instReveal 0 s`, because it had only one layer.)

### `Nu-⟪⟫`

The moved boundary crosses a binder that its appended `unbind 0 0`
removes from the INTERIOR reading.  Its ordinary term indices therefore
retain their positions after deletion; only representation occurrences
move past the new representation binder.  Thus the interior term and
frame use paired, representation-only renamings (`renᴹᴿ suc`,
`renᴮᴿ suc`), and the pushed `ν`'s body type is re-spelled separately
at the outer frame's interior.

THE PUSHED `ν` AND THE ONE RUN-TIME REVEAL.  The pushed term is

```
    ν (` 0) · (renᴹᴿ suc W ⟪ renᴮᴿ suc Θ′ ++ (unbind 0 0 ∷ []) , ∀ s″ ⟫)
            ⟨ reveal 0 (renameᵗ (extᵗ suc) Bᵢ′) ⟩
```

Its argument is the new name, so when it fires it allocates an ALIAS
cell whose payload is this step's cell — as the retired rule's pushed
type application did (NuSketch nested case (a), Jeremy, 2026-09-24).
Its conversion is the reveal of the inner body `Bᵢ′`, lifted past the
new name with the body's own variable kept at 0; its target is `Bᵢ`
read through the alias, which is the source of the middle layer's `s`.
This is the only conversion any rule mints from a type, and the reason
`⊢ν` must accept any `c` whose types line up.  (The retired
`TyPeelR-⟪⟫` pushed in `·[ ⇑Bᵢ′ , 0 ]`, and the next `TyBeta` or
`TyPeelR` minted the same reveal from that annotation.)

THE CONVERSION WALL AND REPAIR (2026-09-20, on `TyPeelR-⟪⟫`).  The
conversion reading SKIPS unbinds.  Hence the new ordinary name survives
there while every `bind X α` in `Θ′` inserts around it; where that name
ends up depends on `Θ′`.  In the closed witness of
`notes/AddLock0Wall.agda`, one `bind 0 0` displaces it to position one,
so the old fixed `renᶜ (extᵗ suc) s′` points at the wrong representation
and the third state loses its type.  No fixed renaming can be right for
all `Θ′`.  (That witness runs through the retired rules; the module is
kept as the record, ungated since 2026-09-24.)

The rule therefore NAMES the carried spelling `s″`, carries both the
old and the moved conversion readings, and pins the spellings with
`SameConv`, in the same pattern as `Peel`.  The old context is viewed
through the representation renaming made by the insertion
(`renNameCtx suc Δ″ᶜ Δ′ᶜ`): without that view, §6b of `Examples.agda`
loses its type, because a free representation index is compared to the
newly inserted binder.  `Nu-⟪⟫` inherited the repair unchanged: same
snoc-unbind frame, same carried `s″`.

THE RE-BASED BODY (2026-09-18).  `Bᵢ` is read at the CONVERSION
context, because that is where the crossed boundary's conversion is
typed; the pushed `ν` is typed at the INTERIOR.  Those are two
different name maps, and they can even reorder relative to each other
(`notes/ForallPayloadWall.agda` §3), so the rule carries the interior
spelling `Bᵢ′` and a `_⊢_≈_⊣_` relating the two.  Determinism for it is
`sameTy-src-unique`; `det` reads the interior's `Unique` name map from
the redex typing derivation.

### `CancelR`

A conceal directly under the binder it names.  The conversion match is
DEFINITIONAL: `seal X` and `unseal Y` cite the SAME entry, so there is
no second spelling to disagree with the first.

THE RESIDUE REPAIR (3a), AS RE-RULED (2026-09-05).  The mini-core
appended a masking residue over the inner boundary's binds, which
masked EXTERIOR slots that need not exist (refuted by the retired
`¬⊢ᵐ-cancel-residue`); dropping the residue was not enough either,
because rebuilding the inner frame from Θ₂'s binds alone DISCARDED Θ₁'s
whole frame, and a `V` that names one of Θ₁'s own binders lost it (the
old `proof/PreserveObstruct.agda` §1 witness).  The honest form keeps
BOTH FRAMES, MERGED as `Θ₁ ++ Θ₂`, and neutralises the matched PAIR to
one conversion: composition happens only on the conversions, where
`unseal ∘ seal = id` is the algebra we already trust, so no
boundary-scope arithmetic returns.  `V` retypes exactly where it was
(`merged-interior`), and the `mkId` layer is transparent at a variable
and finished by `Drop$` at a base type.

ONE LAYER (2026-09-23).  The contractum used to carry a SECOND,
OUTER boundary `⟪ rewind Θ₂ , mkId A ⟫` with `Δᶜ ∋ Y := A`.  A rewind's
interior is the exterior it sits at (`rewind-interior`) and the
conversion was an identity, so the layer converted nothing:
`preserve-CancelR` already typed the surviving layer at the redex's own
exterior type `C` and wrapped it only to re-spell a type it already
had.  The layer is gone, and with it the two premises that existed only
to mint it, `Δ ⊢ᶜ Θ₂ ⇒ Δᶜ` and `Δᶜ ∋ Y := A`.  `Y` is still pinned to
`X`'s representation by the redex's typing (`cancel-name`), which is
all the metatheory used those premises for.

THE SINGLE-NAME PRESUMPTION, EXAMINED (3b).  The mini-core wrote ONE
name `X` on both conversions.  That presumed the two conversions are
read at the same name map, and they are not: the inner conversion is
read at Θ₁'s OWN conversion context `Δ₁ᶜ`, which is Θ₂'s interior
reading further changed by Θ₁, while the outer one is read at Θ₂'s
conversion context `Δᶜ`.  The honest general form carries TWO names —
and needs no extra premise to relate them, because typing already
FORCES both to denote ONE representation variable α
(`proof/IdLayer.agda`, `cancel-name`), exactly as it does for `IdPush`
(`idpush-name`).

THE LOOKUP PREMISE (3c).  `mkId A` is an identity conversion minted at
a looked-up representation, so the rule carries the binder lookup;
determinism for it is `∋:=-det`.

THE SCOPE MOVE (3d, 2026-09-06).  The residue's INNER boundary now
presents `Y`'s representation where it presented the abstract name, so
Θ₂'s changes must travel into the inner frame — which is precisely what
the merge `Θ₁ ++ Θ₂` does, Θ₂ first and then Θ₁ — otherwise `env`'s
last premise reads that representation INSIDE Θ₂'s unbinds.

THE RE-BASED IDENTITY (2026-09-18), REPAIRED (2026-09-19, repair (a),
approved by Jeremy).  `A` is the looked-up type at the OUTER conversion
context `Δᶜ`, which is where the outer layer's `mkId A` is checked;
that half was always right.  The INNER layer is checked at the merged
frame's conversion context `Δ⋉ᶜ`, which lies inside `Δᶜ` — so
re-spelling `A` FROM `Δᶜ` asserted that `A′` denotes the same
representation as `A`, while the inner reading demands the spelling
that has already crossed Θ₁.  The two agree only when Θ₁ changes
nothing or the representation is closed, and NEITHER holds at a
reachable redex.

The premise is therefore read where that crossing already lives: at
Θ₁'s OWN conversion context `Δ₁ᶜ`, on the cancelled `seal X`'s own
source `Aᵢ`.  That makes this premise block premise-isomorphic to
`IdPush`'s — the same interior reading, the same inner conversion
reading, the same lookup, the same re-spelling target.

The wall is `notes/CancelRShiftWall.agda` (the incompatibility, and the
OLD statement refuted against a local copy); the reachable closed
witness and the measured before/after run are
`notes/CancelRReachabilityWitness.agda`.  See `notes/DECISIONS.md`,
2026-09-19.

### `Drop$`, `Drop-true`, `Drop-false`

An identity boundary at a base type, over a literal.  (`⊢$` types a
numeral anywhere, which is why `Drop$` needs no context premise.)

### `IdPush`

Repair (4) — the transparent-layer rule, as ruled.  An inert
`id (` X)` layer under an ACTIVE conversion is not a value and no other
rule fires; instead of merging the two frames with boundary arithmetic
(`IdAbsorb`, retired for failing the no-⊕ test) the reveal is RE-READ
on the merge `Θ₁ ++ Θ₂` and the transparent layer is CONSUMED.
`unseal` is the only active conversion this left-hand side can meet
(`proof/IdLayer.agda`, `outer-id-base-untypeable`), and the pushed name
is already written in the identity conversion (`idpush-name`).

THE SCOPE MOVE (2026-09-06).  The surviving boundary is the revealing
one, so its exterior type becomes `Y`'s representation.  Θ₂'s changes
travel into that frame — the merge `Θ₁ ++ Θ₂` — so that the
representation is presented OUTSIDE Θ₂'s unbinds, at the plain exterior
`Δ`, where it is nameable.  With no bind block there is no shift left
to get wrong.  That is what retires the wall — the case needs no
scoping invariant at all (`proof/MoveScope.agda`, `preserve-IdPush`).

ONE LAYER (2026-09-23).  As for `CancelR`: the outer
`⟪ rewind Θ₂ , mkId A ⟫` was an identity over a frame whose interior is
its own exterior, `preserve-IdPush` already typed the surviving layer at
`C`, and the layer and its two minting premises are gone.  `Y` now
appears only in the redex; typing pins it to `X`'s representation
(`idpush-name`).  A stack of transparent layers therefore SHRINKS by one
boundary per step (`Examples.agda` §9c).

THE RE-BASED NAME (2026-09-18).  `X` is read at the INNER frame's
conversion context; the swap moves it into the MERGED frame's, which is
a different name map.  So the rule carries the merged spelling `X′` and
a `_⊢_≈_⊣_` relating the two, exactly as `Nu-⟪⟫` does for its
pushed body type.

### The congruences, and the absent `ξ-Λ`

THE CONGRUENCES pass the store change up and shift the SIBLINGS by it:
after an allocation the whole program lives under one more
representation binder.  Type annotations are ordinary and do not move;
neither does a boundary's conversion (`renᴹᴿ` leaves it alone).  `ξ-ν`
reduces the operator of a `ν` and has no sibling: `A` and `c` are
ordinary, so it passes `δ` up and shifts nothing.

There is NO `ξ-Λ`.  `strong-rep-nu` does not reduce under a type
binder: `⊢Λ` (`Terms.agda`) requires the body to be a value, so a
well-typed `Λ N` is already a value (`V-Λ`) and there is nothing for a
congruence to do.  `strong-rep-var` had `ξ-Λ`.

### `_⊢_-→*_`, `runCtx`

A run needs no store index: each step's change is applied to the
context the tail runs at.  `runCtx` is the context a run ENDS at —
every step's change applied in order.

### `value-¬step`

Nothing reduces under `Λ` (there is no `ξ-Λ`), so the `V-Λ` case is
absurd outright; the boundary case recurses through `ξ-⟪⟫`.

### `det` (moved to proof/Determinism.agda)

`det` takes the redex's TYPING DERIVATION (`notes/DECISIONS.md`,
2026-09-18: uniqueness comes from typing, not reduction) and reads the
name-map `Unique`ness off it through `bw-exterior`, `bw-interior-wf`
and `bw-conversion-wf`; NO rule carries a `Unique` premise any more.
It concludes `M₁ ≡ M₂ × δ₁ ≡ δ₂`.

* `Peel`: the dual's spelling is pinned by `sameConv-src-unique`, once
  the three readings have been identified.
* `Nu-Λ`: determined by the redex outright (`same-rep-unique` for the
  cell).  The three `Nu` rules' patterns are DISJOINT (a `Λ` is not a
  boundary, and a `Λ` under a boundary is not a tower), and each is
  disjoint from `ξ-ν` because its operator is a value (`value-¬step`).
* `Nu-⟪Λ⟫`: determined by the redex OUTRIGHT — its contractum does not
  mention `Bᵢ`, so `conv-src-unique` is not needed at all.
* `Nu-⟪⟫`: the two contracta agree after all five carried readings have
  been identified: the SOURCE type determines the pushed `ν`'s reveal,
  the type argument determines the instantiated frame, and the moved
  conversion
  spelling is pinned by `sameConv-src-unique`, whose `Unique` map is
  recovered from the redex typing's exterior and the carried
  instantiated interior / moved-conversion readings, just as `Peel`
  recovers the dual map.
* `CancelR`: the cancelled binder's lookup and the re-spelling are
  functional.  The repaired rule reads that lookup at Θ₁'s own
  conversion context, so determinism inverts the redex typing to BOTH
  boundaries' `BoundaryWf`s.  `IdPush` is determined by its re-spelling
  `X′` alone (`sameTy-src-unique`): with the outer layer gone it looks
  nothing up.
* The congruences: the sibling shift is a function of the store change,
  so once the two steps agree on the contractum AND the change, the two
  shifted siblings agree too.

### Retired

Dropped from the inline text, with the reason:

* `TyBeta`, `TyPeelR-Λ`, `TyPeelR-⟪⟫`, `ξ-·[]` and the check
  `TyBeta-ℕ` (2026-09-24) — replaced by `Nu-Λ`, `Nu-⟪Λ⟫`, `Nu-⟪⟫`, `ξ-ν`
  and `Nu-ℕ` when type application left the run-time language.  What
  the old rules' sections argued is restated above against `ν`; the
  one thing that did NOT survive is the fused `instReveal 0 s` mint.
* "`hideBinds (numBinds Θ₂)`", "`repsOf→bind (binds Θ₂)`",
  "`numBinds (Θ₁ ⋉ Θ₂) ≡ numBinds Θ₁`", "`shiftBy (numBinds Θ₁) A`",
  "`interior (rewind Θ₂) Δ` IS `pushBinds (binds Θ₂) Δ`",
  "`A ≡ shiftBy (numBinds Θ₂) C`", "`renᴮ suc Θ` would double-count",
  "`interior (boundary (A ∷ binds Θ) (changes Θ)) Δ ≡ bind (shiftBy
  (numBinds Θ) A) ∷ interior Θ Δ`", "`shiftBy (numBinds Θ + 1)
  (Bₑ [ A ])`", "`SameTyExt (numBinds Θ₁)`", "`X ≡ numBinds Θ₁ + Y`",
  "the `unmasked (bind …) ∷ interior Θ Δ` frame", "`le-mu`",
  "`la-uu le-ab`", "Θ₂'s UNBINDS travel into the inner frame (§2b)" — all
  name the BIND BLOCK and the MASKED-ENTRY contexts, neither of which
  exists.  The claims they made are restated above against
  `Boundary = List Change`, `_++_`, `rewind`, `inst` and `allocate`.
* The rule-by-rule repetition of "the conversion context is the union
  of the names the changes leave live" — stated once, in
  § Boundary.agda / `_∣_⊢χᶜ_⇒_`.
* `proof/MaskFacts.agda` and `proof/PreserveObstruct.agda` are named
  only as the modules that held the refutations; both went with the
  masked-entry design and no longer exist.

## TypeCheck.agda

An executable, DERIVATION-PRODUCING type checker for the whole
development.  §1 `_≟Ty_`; §2–§3 the atoms a change carries and the two
change-list readings (`runδ`, `runχ`, `runχᶜ`); §4 representation
payloads and context well-formedness (`wfᴿ?`, `wfRepCtx?`,
`validNames?`, `unique?`, `wfCtx?`); §5 the two induced contexts
`interior?` / `conversion?` and the complete witness `boundaryWf?`;
§6 the readings between the universes (`read?`, `sameTy?`, `rebase?`,
`respell?`); §7 the lookup square `∋:=?`, type formation `wfTy?` and
conversion typing `convTy?`; §8 `infer`; §9 the checking forms
`check⊢`, `checkConv`, `check~`; §10 the forcing family `IsJ`/`force`
with the goal-directed `tc`, `tk`, `tu`, `tf`, `tr` and the inferring
`int!`, `conv!`, `mw!`, `sq!`, `tv!`, `cv!`, `ty!`, `wf!`.

NOTHING HERE IS ASSUMED AND NOTHING IS TRUSTED.  Every checker returns
a `Maybe` of the ORDINARY derivation, built from the constructors of
the judgements in `Ctx.agda`, `Boundary.agda`, `Conversion.agda` and
`Terms.agda` — never a bit, never a postulate, so there is no soundness
theorem to owe.  The caller states the answer it expects and §10 forces
the checker at it, so a failure or a different answer is a type error
rather than a silently accepted witness.  The rules and judgements
themselves belong in those modules; the redex search that consumes
these checkers is `Eval.agda`; the metatheory is under `proof/`.  This
module depends on none of it, which is why `All.agda` checks it before
the theorems.

### Three things to know before using it (`notes/PLAN.md`)

1. It must INFER, not merely CHECK.  `⊢·` and `⊢ν` need the head's
   type, and a head can be a boundary; inferring a boundary's exterior
   type means re-spelling the conversion target at the ambient name
   map.  `rebase?` (§6) supplies that spelling through the common
   representation.
2. A goal-directed form discharges a premise only when the goal fixes
   every input.  The lookup premise of `CancelR` and `IdPush` does not:
   both contracta mention the looked-up type only under `mkId`, which
   the unifier cannot invert, so the inferring `sq!` must be used there
   — and likewise wherever a rule mints a conversion from a looked-up
   type, including those two rules' preservation cases.
3. A FAILURE IS A REJECTION, NOT AN ACCEPTANCE.  The hidden argument's
   type becomes `⊥` and Agda reports an unsolved meta at the call site,
   which `--no-allow-unsolved-metas` and `make check` turn into an
   error.  It does not say why; `proj₂ (ty! Δ Γ M)` reports the type
   the checker did infer.

### Usage

`tc` IS a typing derivation — it reads its four arguments off the goal,
so

```agda
    P₀-⊢ : empty ∣ [] ⊢ P₀ ⦂ `ℕ
    P₀-⊢ = tc
```

is the whole thing.  `tk`, `tu`, `tf` and `tr` do the same for the
conversion, uniqueness, type-formation and representation-reading
judgements.  Where the answer is an OUTPUT the goal does not fix — a
boundary scope's two induced contexts, a lookup's type — the `!` family
is used instead and the input is written out.

### Why it exists (2026-09-17)

A boundary `M ⟪ Θ , c ⟫` is typed by `env`, whose six premises are of
two very different kinds.  Three of them say something about the
PROGRAM: which conversion applies, which `_⊢_≈_⊣_` reading relates the
three sides, what the interior term's type is.  The other three are
MECHANICAL: the two contexts Θ induces, and the well-formedness of
each.  A derivation of `Ξ ∣ Δ ⊢χ Θ ⇒ Δ′` is one line per change and
contains nothing the change list does not already determine.

That became unworkable when the fourth reduction example was finished.
`CancelR` and `IdPush` replace their frames by the COMPOSITE
`Θ₁ ++ Θ₂`, whose change list is the concatenation of its arguments',
so unwinding an n-deep tower of boundaries reaches
frames carrying tens of changes each.  The checker removes that
transcription entirely, and — since it decides the term judgement too —
an example's typing derivation becomes a statement of the type and
nothing else.

### §2 — `find?`

Where a representation variable currently sits, if it is live at all.
This is what the re-bind clause of `_∣_⊢χᶜ_⇒_` needs
(§ Boundary.agda).

### §3 — `runχ`, `runχᶜ`

The tail acts first (head-LAST order, `Boundary.agda` §2).  In the
conversion reading an `unbind` is skipped, and a `bind` of a name the
skipped unbinds left live is a no-op (`Boundary.agda` §3).

### §4 — `ref?`

A payload index below the local binder depth is a payload-local
variable; otherwise it is `n + α` for a free representation variable α,
and the subtraction has to be PROVED to put the index back in
constructor form.

### §6 — `read?` / `unread?` / `rebase?` / `respell?`

Forward (`read?`): replace each live ordinary name by the
representation variable it names.  A `∀` extends only the LOCAL binder
prefix on both sides.  Backward (`unread?`): the ordinary spelling a
representation type has under a given name map, if it has one.

RE-BASING (`rebase?`) is the one genuinely non-obvious checker, and it
is also the reason `infer` is an inference and not a check: `env`
exposes the conversion target at the CONVERSION context, while the
result type must be spelled at the AMBIENT context.  `A` is read on the
name map `η`; `rebase?` finds its spelling on `η′` together with the
`_⊢_≈_⊣_` that relates them.  It goes through the REPRESENTATION, which
is the only route there is: the two maps can reorder relative to each
other, so no arithmetic on positions would do
(`notes/ForallPayloadWall.agda` §3).  It is PARTIAL, because `η′` need
not name everything `η` does — which is why the rules that cross carry
this as a premise rather than computing it.

`readᶜ?` is the same thing for a CONVERSION, which is what `Peel`
needs: a conversion mentions ordinary names at three leaves only, so
both directions are `read?`/`unread?` with those three cases added.
`respell? η η′ s` is `rebase?` one universe up.

### §7 — `ConvResult`

A conversion determines BOTH its types: every representation it
mentions is read by name from the conversion context
(`Conversion.agda` §5).

### §8 — `inert?`, `value?`, and the boundary case of `infer`

Deciding the classifications `Value` guards on.  `V-Λ` carries
`Value N` and `V-⟪⟫` carries `Inert c`, so this is a RECURSION, not a
shape test.  `infer` needs `value?` for `⊢Λ`'s value restriction;
`Eval.agda` reuses both for the rules' side conditions.

The boundary case: `env`'s mechanical premises come from §5; its three
informative ones are the interior term's type, the conversion's two
types, and the two readings that relate them.

### §10 — forcing a checker

`IsJ m` is the unit RECORD when the checker succeeded, so Agda solves a
hidden argument of that type by eta on its own.  A checker whose inputs
are all determined by the goal therefore needs no arguments written at
all: `tc` IS a typing derivation.

HOW A FAILURE LOOKS.  When the checker says `nothing` the hidden
argument's type is `⊥`, which nothing solves, so Agda reports an
UNSOLVED META at the `tc`.  That is a rejection, not an acceptance —
`--no-allow-unsolved-metas` (and `make check`) turn it into an error —
but it does not say WHY.  To see why, replace `tc` by
`proj₂ (ty! Δ Γ M)`, which reports the type the checker did infer, or
call the failing sub-checker directly.

The goal-directed family: `tc` a term's typing derivation, `tk` a
conversion's, `tf` a type's well-formedness, `tr` the reading that
relates an ordinary type to its representation (what the three `Nu`
rules and `⊢ν` carry as `Δ ⊢ᶜ A ~ R`), and `tu` name-uniqueness of a
name map.  No REDUCTION rule carries `tu`'s judgement any more — since
2026-09-18 `det` recovers it from the redex's typing derivation
(`notes/DECISIONS.md`) — but `WfCtx`'s `name-fn` field and the lemmas
stated over `Unique` still ask for it.

The inferring family: `from-just` turns a checker into what it found;
the caller's type signature is what pins the answer, because a
different one does not typecheck.  These are used where the answer is
an OUTPUT the goal does not already fix.  `sq!` in particular is the
lookup square that `CancelR` and `IdPush` need in inferring form, per
point (2) above.

## Eval.agda

The step function and the evaluator built on it.  §1 decides the
classifications the rules guard on (`base?`, `inert?`, `value?`); §2
assembles each boundary rule's side conditions (`peelPremises?`,
`crossPremises?`, `bdyPremises?`, `mergedPremises?`,
`pushPremises?`); §3 is the redex search by head shape (`appRedex`,
`tyAppRedex`, `bdyRedex`); §4 is `step`, leftmost-outermost, returning
the contractum, allocation and step derivation; §5 forgets the
derivation (`stepTo`, `Steps`); §6–§7 are `Trace` and `eval`; §8–§9
read a trace (`traceEnd`, `traceTerms`, `traceLen`, `evalTerms`,
`trace-sound`, `Checked`, `trace-⦂`); §10 is `Report`/`report` and
`Reaches` with `reaches-end`, `reaches-checked`, `reaches-run`,
`reaches-⦂`.

### No metatheory is needed and none is claimed

`step` takes no typing derivation and RETURNS THE DERIVATION, so
soundness is its type: there is no second rule table to transcribe and
no `step-sound` theorem to prove.  What it does NOT give is the other
half — that a well-typed term is a value or steps — so a `nothing`
means only that this search found no redex; that is `progress`, and it
lives in `Progress.agda` / `proof/`.  The rules are `Reduction.agda`;
the checkers every premise here comes from are `TypeCheck.agda`; the
recorded runs are `Examples.agda`.

WHY THIS IS NOT A SECOND RULE TABLE.  v2's evaluator WAS progress
(`step = progress`), on the argument that a `Maybe`-returning step
function is a type-blind transcription of the rules that then needs a
`step-sound` theorem tying it back to the relation.  That argument does
not apply here: `step` returns the derivation, not the term, so
soundness is the type and there is nothing to transcribe.

On a well-typed term, determinism (`det`, `Reduction.agda`) is what
makes "no soundness theorem" enough in practice.  Any redex `step`
finds is THE redex, so a run it produces is THE run, and an example has
only to say where that run ends (`Reaches`, §10).

WHERE THE PREMISES COME FROM.  The boundary rules carry side conditions
not read off the redex — induced contexts, conversion typing, lookup
squares, re-spellings and the representation reading of a type
argument.  Those are decided by `TypeCheck.agda`, which returns the
ordinary derivations, so this module assumes nothing either.  Name
uniqueness is no longer a reduction premise and is not decided here.

### What a run asserts, and the one way it can lose the type

`eval` is `step ⨟ check⊢` iterated with fuel: preservation is not used
to retype a contractum, the contractum is CHECKED instead, at the type
the run started with and the context after that step's allocation.  A
step whose contractum the checker rejected is recorded as `illtyped`,
and that constructor is the ONLY way a type is lost along a `Trace`.
`Checked tr` is the unit record exactly when no `illtyped` occurs, so
Agda discharges it by eta at a concrete run.  That is subject reduction
FOR THAT RUN, checked rather than proved.

That is not preservation and does not pretend to be — it says nothing
about runs it was not pointed at.  What it is, is the executable form
of subject reduction, and it is the check that would have caught the
`rewind` defect by itself: the eleventh state of the fourth example was
the first one `check⊢` would have rejected (`notes/DECISIONS.md`,
2026-09-17).

### §1–§2 — the side conditions

`inert?` and `value?` live in `TypeCheck.agda` now, because `infer`
needs `value?` to discharge `⊢Λ`'s value restriction; they are
re-exported here.

* `PeelPremises` (the name is from the `TyPeelR` rules) — `Nu-⟪Λ⟫`
  asks for three things of the crossed frame and the type argument:
  the frame's conversion reading, the crossed body's conversion typing
  and the argument's representation.  `Nu-⟪⟫` asks for those and, since
  2026-09-18, for the interior spelling of the body type its pushed `ν`
  reveals.
* `BdyPremises` — the wrapper clause's remaining premises.  Besides
  re-spelling the pushed body type, it reads the old inner
  boundary, the instantiated outer frame and the moved inner boundary,
  then re-spells the inner conversion between those two conversion
  contexts.  In particular, NO arithmetic renaming is used for the
  carried conversion.
* `PushPremises` — `IdPush` re-bases the name it pushes into the merged
  frame, the same way `Nu-⟪⟫` re-bases its pushed body type.
* `MergedPremises` — `CancelR`'s inner layer is checked at the MERGED
  frame's conversion context, so its `mkId` needs a type spelled there.
  Repaired 2026-09-19: the type re-spelled is the cancelled `seal X`'s
  OWN source, read at Θ₁'s conversion context — the same
  context-reading block `pushPremises?` builds for `IdPush`.
* `CrossPremises` — `Peel`'s crossing premises (2026-09-18): the
  boundary scope's two readings, the DUAL's conversion context (which
  the redex typing does not supply, so it is built here) and the dual's
  spelling of the domain half.  The redex fixes only Δ, Θ and `s`.

(`CancelPremises` / `cancelPremises?` — the reading of Θ₂ and the lookup
of `Y` — went with the outer layer on 2026-09-23: no rule asks for them
any more.)

### §3 — the redexes, by the shape of the head

* `appRedex`: an application whose two sides are values.  Matching on
  the head's VALUE derivation is what refines its shape — and, at a
  boundary, its conversion, since `Peel` fires only under a `_↦_`.
* `nuRedex`: a `ν` whose operator is a value.  `canon-∀` says the
  operator is a `Λ`, a `Λ` under one `∀`-conversion boundary, or a
  tower of them; the three clauses are `Nu-Λ`, `Nu-⟪Λ⟫` and `Nu-⟪⟫` in
  that order.  None of them looks at `ν`'s conversion.
* `bdyRedex`: a boundary.  `Drop` fires at a literal under an identity
  at a base type; `CancelR` and `IdPush` fire at a REVEALING boundary
  over an inert one, and are told apart by the inner conversion.
  Everything else is either a congruence or stuck, which is the
  caller's business.

### §4–§5 — `step`, `stepTo`, `Steps`

Leftmost-outermost, with the rules' own `Value` premises deciding where
a congruence stops: at each node the head is tried first, and a redex
is reported only once every subterm the rule demands to be a value is
one.  Values do not step (`value-¬step`), so the two never both apply.

`stepTo` is the contractum alone, for stating what a recorded trace
expects; the derivation is still what `step` returns, this only forgets
it.  `Steps Δ M N` is what a regression check asserts, and `refl`
proves it; `stepDeriv` hands back the derivation when a caller wants
that instead of the equation.

### §6 — `Final`, `Trace`

`Final` is why the run stopped, said of the state it stopped at.
`no-redex` is the honest one: it is where progress would say something
and cannot yet, so the evaluator reports "this search found nothing"
rather than claiming the term is stuck.

A `Trace` is a run from `M` that is supposed to keep the type `A`.
Each step stores its own derivation AND a typing derivation for the
contractum, because `eval` re-checks after every step; `illtyped`
records a step whose contractum the checker REJECTED.

### §8–§9 — reading a trace

`traceCtx` is the context in which the final state lives; allocating
steps change this index even though the trace itself remains a run from
its initial context.  `traceTerms` is the states, the first one
included.

`trace-sound`: the states really are a run — the `_⊢_-→_` derivations
are stored, so this only reassembles them.  `trace-⦂` is SUBJECT
REDUCTION FOR THIS RUN: not proved, checked state by state by the
derivations the trace stores.  `illtyped-unchecked` shows that
`Checked` really bites: an `illtyped` trace has no such proof, so the
`_` a caller writes for it is a proof only because every state the run
passed through was checked.

### §10 — `Report`, `Reaches`

ONE PASS OVER THE RUN.  Agda shares nothing between the occurrences of
a term, so a statement that mentions `eval k M ⊢M` three times RUNS THE
PROGRAM THREE TIMES — measured, on the 25-step example, at about 0.12 s
an occurrence.  `report` therefore walks the trace once and returns
everything an example asserts about it: where the run ended, how many
steps it took, and whether every state kept its type.  `Reaches` then
mentions the run ONCE.

`bump` matches on the triple rather than projecting out of it, which is
what keeps that one pass one pass: projections would put three copies
of the recursive call back in.  The price is that `report` is stuck on
a variable trace, so the two lemmas below it have to `with` their way
past it; that is paid once, there, and not per example.

`Report` is A DATA TYPE, not a triple: a triple has eta, so comparing
one against a literal splits into three independent projections and
walks the run three times anyway (measured).  Forcing a datatype to
weak head normal form walks it once and leaves the three components
computed.

`Reaches k n ⊢M V` is one statement per example: with fuel `k` the
evaluator reaches `V` in exactly `n` steps, no state along the way lost
the type, and `V` is a value.  Only the first component mentions the
run.  The intermediate states are deliberately NOT part of this — they
are what `eval` type-checked on the way (the `true` is the record of
that), and `evalTerms` hands them back whenever a reader wants to see
one.  It is A RECORD, not a product, so that `k`, `n` and `⊢M` are
recoverable from the type: the accessors are applied to an example's
`Reaches` and have to read them off it.

The accessors — `reaches-end`, `reaches-checked`, `reaches-run`,
`reaches-⦂` — do not re-run the program: they are equational, so the
trace stays unevaluated.  `eval-run` is the multi-step run with the
endpoint NAMED (`eval-sound` already gives
`Δ ⊢ M -→* traceEnd …`; this is that, with the endpoint read off an
equation), and `reaches-⦂` is the endpoint's typing — subject reduction
for this run, checked.

The fuller sharing-and-measurement story behind `Report`, `bump` and
the datatype-rather-than-triple choice is in `notes/PLAN.md`.

## Preservation.agda

The public preservation surface, and nothing else.  §1 states
`Preservation`, `PreservationWf` and `Preservation*` explicitly; §2
proves them as `preservation`, `preservation-wf` and `preservation*`.
All three are UNCONDITIONAL THEOREMS — no `Stage1` module, no
parameter.  Each takes `WfCtx Δ`, a typing `Δ ∣ [] ⊢ M ⦂ A` and a step
(respectively a `-→*` run).

A STEP RETURNS THE CHANGE IT MADE TO THE STORE (experiment 2,
`notes/RepStoreSketch.md`).  So the contractum is typed at
`apply δ Δ`, not at `Δ`: a ∀-elimination ALLOCATES the cell for the
type argument's representation at index 0 and pushes every existing
representation variable up by one.  `PreservationWf` is the companion
that keeps the context well formed, and it is what `preservation*`
threads along a run; the run's final context is read off the derivation
by `runCtx` (`Reduction.agda`).

NO PROOF SCRIPT LIVES HERE.  The theorems are thin wrappers around
`proof/Preserve.agda`'s `Impl` and `preserve-wf`, instantiated with
`RepWeaken.cross-Λ-⊢`, `AddUnbind0.addUnbind0-⊢`, `RepWeaken.shift-⊢` (THE
SIBLING SHIFT), `PeelDual.preserve-Peel`, `MoveScope.preserve-CancelR`
and `MoveScope.preserve-IdPush`.  Progress is `Progress.agda`, their
composition is `TypeSafety.agda`, and the refuted statements that
shaped these rules are the wall modules under `notes/`.

### Why `WfCtx Δ` is part of the statement

The premise-free form is FALSE here (`notes/DECISIONS.md`,
2026-09-18).  The reduction relation is indexed by the type context `Δ`
alone, the term context being empty; but a contractum can MINT a
`BoundaryWf`, whose exterior field demands `WfCtx Δ`, from a redex that
mentioned no ordinary type variable at all.

For example, let `reps Δ` be `bindR ℕ ∷ []` and `names Δ` be
`0 ∷ 0 ∷ []`.  The redex (rendered)

```
    ((λx:ℕ. (ΛX. (λy:ℕ. x))) · 0)
```

can be typed because it mentions no ordinary type variable.  `Beta`
substitutes the value `0` under the `Λ`, so frame-exact substitution
wraps it in the binder's dual, and the contractum is

```
    (ΛX. (λx:ℕ. (0 ⟪ ↓X , id ℕ ⟫)))
```

That boundary's `BoundaryWf` is read at `underΛ Δ`, whose `WfCtx`
fails: uniqueness fails for the duplicate name map.  (Checked with the
derivation-producing checker on 2026-09-24: `infer` succeeds on the
redex and fails on the contractum.)

UNTIL 2026-09-24 the example was the type application
`(Λ ($ 0)) ·[ ℕ , ℕ ]`, whose `TyBeta` contractum minted the
`BoundaryWf`.  Its `ν` counterpart `ν ℕ · (Λ ($ 0)) ⟨ id ℕ ⟩` is not
typeable at that `Δ` at all: `⊢ν` carries
`BoundaryWf (allocate R Δ) TyBetaBoundary …` itself (§ Terms.agda / §4
— ⊢ν).

`progress` needs no such premise, because every boundary typing node
carries its own `BoundaryWf`.

### What the store changed in the proof (2026-09-22)

One lemma is new and several are gone.

* NEW: the SIBLING SHIFT `ShiftTyping`, today's representation
  weakening at `ρ = suc` (`proof/RepWeaken.agda`, `shift-⊢`), applied
  in the four congruences to the sibling the redex leaves behind; and
  `step-alloc`, which reads off a step what it did to the store.
* GONE: the `RepWeakenTyping` parameter `Peel` used to consume —
  `dual-interior` now lands the crossing argument at the exterior
  ITSELF, so it moves verbatim — and every `shiftBy` / `shiftRep` /
  `numBinds` occurrence in `TyBeta`, both `TyPeelR` clauses (today the
  three `Nu` rules), `CancelR` and `IdPush`.

### How the three crossing cases landed

Stage 2 (2026-09-19) discharged all three: `IdPush` and, after the
`CancelR` rule repair of the same day, `CancelR` are proved outright
(`proof/MoveScope.agda`), and `Peel` is proved in
`proof/PeelDual.agda`.  NOTHING REMAINS A PARAMETER (2026-09-20): the
last one, `AddUnbind0Typing`, is proved by `proof/AddUnbind0.agda`'s
`addUnbind0-⊢`.

### The wall of 2026-09-20, and its repair

`notes/AddLock0Wall.agda` refuted the OLD `AddUnbind0Typing` and, at the
same instance, `Preservation` and `Preservation*`: a closed, plain
System F program — no hand-written boundary — lost its type three steps
in, at `TyPeelR-⟪⟫` (today `Nu-⟪⟫`, which inherited the repair; the
witness module is kept as a record and ungated since 2026-09-24).  That
rule re-spelled the moved boundary's
conversion with `renᶜ suc`, the renaming that is correct for the
INTERIOR reading (where the appended unbind, acting first, deletes the
new ordinary name) and wrong for the CONVERSION reading (which SKIPS
unbinds, so the new name survives and the moved boundary scope's own
binds displace it).  No premise repairs a contractum, so the RULE was
repaired, with Jeremy's approval and in the pattern `Peel` got on
2026-09-18: the moved conversion is NAMED and pinned by a `SameConv`,
against the old conversion context viewed through the representation
renaming the allocation makes.

`CancelRCase` WAS refuted too — the old rule re-spelled the inner
layer's identity type in the OUTER conversion context and so dropped a
shift `env` demanded, at a redex reachable from a closed plain source
program.  Repair (a) was approved by Jeremy on 2026-09-19 and installed
in `Reduction.agda`: the premise now reads the cancelled seal's own
source at Θ₁'s conversion context.  With the store there is no shift
left to drop, but the premise STAYS — it is a different NAME MAP, which
is what `_⊢_≈_⊣_` is for.

## Progress.agda

The public progress surface, and nothing else.  §1 states `Progress`
explicitly: from `Δ ∣ [] ⊢ M ⦂ A` alone, `M` is a `Value` or there are
an `M′` and a store change `δ` with `Δ ⊢ M -→ M′ ∣ δ`.  §2 supplies the
theorem outright, `progress = proof.Progress.Impl.progress`.

The statement is PREMISE-FREE — no `WfCtx Δ`, unlike preservation —
because every boundary typing node carries its own `BoundaryWf`, so the
induction never needs a global one.  It is UNCONDITIONAL as of
2026-09-21: the merged-frame reading is proved by
`Boundary.merged-conversion-exists`.

THE CHANGE IS EXISTENTIALLY QUANTIFIED.  A step returns what it did to
the store (experiment 2, `notes/RepStoreSketch.md`), and progress does
not say which: `det` (`Reduction.agda`) says the pair `(M′ , δ)` is
unique, and `preservation` says the contractum types at `apply δ Δ`.

NO PROOF SCRIPT AND NO CANONICAL-FORMS SUITE HERE.  Those are
`proof/Progress.agda` and `proof/Canonical.agda`.

## TypeSafety.agda

The whole public theorem surface, stated explicitly in one place.
`Progress`, `Preservation`, `PreservationWf`, `Preservation*` and
`TypeSafety` are written out here rather than re-exported, and
`TypeSafety` is the COMPOSITION of progress and preservation: from
`WfCtx Δ`, `Δ ∣ [] ⊢ M ⦂ A` and a run `r : Δ ⊢ M -→* N`, `N` is a
`Value` or `N` steps — at `runCtx r`, the context the run ENDS at.
`det` and `value-¬step` are re-stated here and delegate to
`Reduction.agda`.

NO PROOFS AND NO DEFINITIONS.  Every right-hand side is a delegation:
`Preservation.agda`, `Progress.agda`, `proof/TypeSafety.agda` and
`Reduction.agda`.  The refutations that shaped these statements are the
wall modules under `notes/`, and the dated record is
`notes/DECISIONS.md`.

### The whole surface holds outright

```
  det              reduction is deterministic on well-typed terms —
                   contractum AND store change
  value-¬step      values do not step
  preservation     a well-typed term stays well typed, at `apply δ Δ`
  preservation-wf  and that context stays well formed
  preservation*    and along a whole run, at `runCtx r`
  progress         a well-typed closed term is a value or steps
  type-safety      every state reached is a value or steps
```

### The premises are not uniform, and that is the point

`preservation` (and everything built on it, `type-safety` included)
takes `WfCtx Δ`; the premise-free form is FALSE here, because at a
duplicate name map a `Beta` contractum must mint a `BoundaryWf` that
`Unique` refuses (§ Preservation.agda, and `notes/DECISIONS.md`,
2026-09-18).  `progress` takes NO such premise — a boundary case reads
well-formedness off its own `env`.  `det` takes the REDEX'S TYPING
DERIVATION, from which it recovers the name-map uniqueness the rules
used to carry as premises (same entry).  The reduction relation is
indexed by the type context `Δ` only; the term context is empty, as it
must be.

### How the surface became unconditional

PRESERVATION BECAME UNCONDITIONAL ON 2026-09-20, in three steps of the
same day: `RepWeakenTyping` was proved, making `PeelCase`
unconditional; `CrossΛTyping` was proved, making `Beta` unconditional;
and `AddUnbind0Typing`, which `notes/AddLock0Wall.agda` had REFUTED that
morning, was answered by the RULE repair Jeremy approved (the moved
conversion is NAMED and pinned by `SameConv`) and then PROVED on the
reshaped statement.  That was the second rule defect of the shape
`CancelRCase`'s had (refuted by `notes/CancelRShiftWall.agda`, reached
from source by `notes/CancelRReachabilityWitness.agda`, repaired by
Jeremy's repair (a) on 2026-09-19 and proved).  The final progress
obligation, `MergedReading`, was proved on 2026-09-21.

THE STORE EXPERIMENT (2026-09-22) kept every one of those statements
and retired one of the lemmas behind them: `Peel` no longer moves its
argument at all, so `RepWeakenTyping` is gone, replaced by the SIBLING
SHIFT `ShiftTyping` that the four congruences consume.

## Residual.agda

One-hole term contexts, the scope map at a hole, and residuals.  This
is the layer the COLOR PRESERVATION theorem
(`ColorPreservation.agda`) is stated in.  §1 is `TermCtx` with `plug`;
§2 is `_⊢C_⊣_`, the type context AT THE HOLE — the hole's SCOPE MAP is
its `names`; §3 renames a context in the REPRESENTATION UNIVERSE
exactly as `renᴹᴿ` renames a term, and reads off the renaming that
reaches the hole; §4 pushes `Beta`'s substitution through a context;
§5 is `Residual`, ONE STEP, and §6 `Residuals`, a whole run.

THIS MODULE PROVES NOTHING.  The sanity lemma that `plug D N` is the
step's contractum is `proof/Residual.agda`, and the theorem is
`proof/ColorPreservation.agda`.

### What a residual records (2026-09-21, the v7 restatement)

A position is a pair `(C , M)`, the hole and the node in it.  A step
moves a retained node to a new position `(D , N)`, and every move in
this calculus except the `Nu` rules' refinement is REPRESENTATION-ONLY
(`proof/ShiftAudit.agda` §3): the node is `M` renamed by some
`renᴹᴿ ρ`, so the residual relation carries that `ρ` — the
representation renaming that reaches the hole — as an INDEX.
`Residuals` composes them along a run.  The theorem then says the scope
map at `D` is the scope map at `C` under `ρ`.

### What the store changed (experiment 2, 2026-09-22)

A boundary no longer carries a bind block, so NO rule moves a subterm
past one: the only representation move left is the UNIFORM SIBLING
SHIFT a step's allocation imposes — `suc` when the step returns
`new R`, the identity when it returns `none`
(`↑ᶜ[_]` / `↑ᴴ[_]` / `↑ʳ[_]`, §3).

`Peel`'s argument therefore moves VERBATIM (`dual-interior` lands it at
the exterior itself), and the redex's own contractum keeps `idᵗ`:
`Nu-Λ`'s and `Nu-⟪Λ⟫`'s body sits under the `Λ` binder that
BECOMES the allocated cell, so its indices are already right.  The one
position that still moves inside a redex is `Nu-⟪⟫`'s inner
boundary, a SIBLING of that `Λ`, which gets exactly `suc`.

What went with the bind block: the paired `renCtx²` / `holeRen²`, whose
boundary clause stepped past `numBinds Θ` representation binders, and
the `moveᴿ` wrapper — §3 is now the representation-only `renCtxᴿ` /
`holeᴿ`.

### Which nodes have residuals

The nodes of the REDEX ITSELF are CONSUMED — the application node
`Peel` pushes through a boundary, the `Λ` and `ν` nodes `Nu-Λ`
eliminates, the `ƛ` and `·` nodes of `Beta`, the boundary nodes every
boundary rule re-mints.  Every node strictly inside a retained subterm
has exactly one residual, except that a term variable `Beta`
substitutes is replaced by a COPY of the argument (`CopyResidual`), and
`Drop$` / `Drop-true` / `Drop-false` consume their literal with its
boundary — a literal has no scope to preserve
(`proof/ShiftAudit.agda` §7, "vacuous").

### §2 — `_⊢C_⊣_`, the type context at the hole

Its `names` is the hole's SCOPE MAP: which ordinary type variables are
live there (the positions) and which representation variable each
denotes (the entries).  `ƛ`, `·` and `ν` frames bind no type
variable (a `ν` frame's hole is its operator, read at the `ν`'s own
context); `Λ` binds one in both universes; a boundary frame moves to
the INTERIOR its boundary scope relates the frame's context to.

### §3 — `renCtxᴿ`, `holeᴿ`, and the sibling shift

Renaming a context in the REPRESENTATION universe, clause for clause
with `renᴹᴿ`, and the renaming that reaches its hole: only a `Λ` frame
changes it, and a boundary frame does not — crossing a boundary no
longer crosses a bind block.

THE SIBLING SHIFT AT A POSITION.  A step returns the change `δ` it made
to the store and the congruences shift the redex's siblings by
`↑ᴹ[ δ ]` (`TermSubst.agda` §2).  A position inside such a sibling
therefore moves by the same shift, split into its three halves: the
context around it, the node in it, and the renaming that reaches the
hole.  At `none` all three are the identity ON THE NOSE, which is what
keeps the `_-→_∣ none` rules' residuals `idᵗ`.

### §4 — `substCtx`, `holeEnv`, `Stable`

`Beta`'s substitution through a context, clause for clause with
`substᵐ`: a boundary frame is TERM-CLOSED, so the substitution stops
there.  `holeEnv` is the substitution that reaches the hole, and
`Stable` says the node in the hole SURVIVES it — every node but a
substituted variable.

### `ImageResidual` — a copy of the argument

A copy of the argument, at one substituted occurrence.  Each `Λ` the
occurrence sits under wraps the copy in that binder's dual (`crossΛᴹ`,
`TermSubst.agda` §5): the position moves inside one more boundary frame
and one more representation-only `suc`.

THE DEPTH INDEX (2026-09-21, restored from v7 during the proof).  The
ℕ counts the `Λ`s the copy walk has descended, and `image-here` demands
it be ZERO.  Without it the relation admits a WRONG-POSITION
derivation: when the β-redex's argument is itself a `crossΛᴹ`-shaped
wrapper, `⇑ᴵ (ival V A)` is again an `ival`, so a depth-1 occurrence
could match `image-here` and claim the UNWRAPPED source position at the
ambient one `Λ` in — and for that derivation the color equation is
FALSE.  The index pins the leaf to the walk's actual depth.

`CopyResidual`: positions inside a copy of the argument, followed
through the body to the occurrence that receives it.  The body's
binders extend the substitution exactly as `substᵐ` does; a boundary in
the body receives no copy.

### §5 — `Residual`, one step

`Residual r C M ρ D N`: the step `r` moves the node `M` in hole `C` to
hole `D` as `N`, and the representation renaming that reaches the hole
is `ρ`.  The site-by-site moves are `proof/ShiftAudit.agda` §1's table;
`ρ` is that table's third column, and since the store it is `idᵗ`
everywhere but in `Nu-⟪⟫`'s moved boundary and in a sibling the
allocating step shifted.

* `residual-Nu-Λ` — the body stays where it is; its `Λ` slot BECOMES
  the allocated cell (refinement `abstR → bindR R`, no move), and the
  scope `inst []` re-binds the body's own name for it, so the body's
  indices are already right and ρ is `idᵗ`.
* `residual-Beta-body` — a node the substitution does not replace;
  `residual-Beta-arg` — one residual per occurrence that receives it.
* `residual-Peel-fun` — the function keeps its frame.
  `residual-Peel-arg` — the argument crosses into the dual VERBATIM:
  there is no bind block to cross any more, and `dual-interior` lands
  the dual's interior at the exterior itself, so ρ is `idᵗ`.
* `residual-Nu-⟪Λ⟫` — as `Nu-Λ`, one boundary in: the body's `Λ`
  slot becomes the allocated cell the outer scope `inst []` binds, and
  the crossed boundary is the middle layer.
* `residual-Nu-⟪⟫` — the inner boundary is a SIBLING of the `Λ`
  slot the allocation consumes, so its interior gets exactly the
  sibling shift `suc` — the one non-identity ρ a redex still produces.
* `residual-CancelR` / `residual-IdPush` — the value keeps its frame
  under the merged scope, the one layer the contractum has
  (`proof/ShiftAudit.agda` §6).
* `Drop$` / `Drop-true` / `Drop-false` — NO residual: the literal is
  consumed with its boundary.
* the ξ rules — the position is inside the stepping subterm, or in the
  SIBLING that stands still, and a sibling moves by the step's own
  store change, `↑ᶜ[ δ ]` / `↑ᴴ[ δ ]` / `↑ʳ[ δ ]`.

### §6 — `Residuals`, a whole run

The renamings compose, and each step's store change is applied to the
context its tail runs at.

## ColorPreservation.agda

The color-preservation theorem and the stronger scope-map form it is a
corollary of (statement approved by Jeremy and proved 2026-09-21; the
proof is `proof/ColorPreservation.agda`).

### Two theorems (Jeremy's ruling, 2026-09-21)

Color is about TYPE variables only — which ordinary names are live at a
hole — not about the representation variables they denote.  So the
COLOR THEOREM proper, `ColorPreservation`, concludes

```
    length (names Δ₂) ≡ length (names Δ₁)
```

and it is a corollary of the stronger `ScopeMapPreservation`, which
pins the whole scope map:

```
    names Δ₂ ≡ map ρ (names Δ₁)
```

— same positions, each denoting the same representation variable read
through the run's renaming ρ.

### The design law (Jeremy, 2026-09-04, `notes/DECISIONS.md`)

> the color of a non-boundary term should never change during
> reduction

— reduction never changes which type variables a subterm can see; only
boundary syntax moves.  The v7 theorem (`strong-v3-design`, commit
31fa0918) said it as `scopeᵗ Δ₁ ≡ scopeᵗ Δ₂` for the contexts at a hole
and at its residual.

### The restatement

A hole's COLOR is its SCOPE MAP, `names Δ` at that hole
(`Residual.agda` §2): which ordinary type variables are live there and
which representation variable each denotes.  A move can rename the
representation universe — an allocating step shifts the redex's
siblings by one, `Nu-⟪⟫` shifts the boundary it pushes in, `Beta`
sends a copy past a `Λ`'s dual — so the scope map is transported along
the representation renaming `ρ` the run delivered to the hole, which
`Residuals` records.  Everything else is EQUAL: no ordinary position is
added, removed or moved, and a name denotes the same representation
variable, read through `ρ`.  `Nu-Λ` / `Nu-⟪Λ⟫`'s refinement of an
`abstR` slot to `bindR R` changes what a representation variable IS
BOUND TO, not which one a name denotes, so it is invisible to the scope
map (and `ρ` is `idᵗ`).

In the named presentation (`notes/notes.md`): a residual position sees
exactly the type variables `X` it saw before, each standing for the
same α — up to the α-renaming of the representation universe that the
crossed binders impose.

### The target is read at the run's own context (experiment 2, 2026-09-22)

A step returns the change it made to the store, so the run's positions
live at `runCtx rs` (`Reduction.agda`), not at `Δ`: allocating a cell
renumbers the ambient name map, which is exactly the `map ρ` the
equation already reports.

### The well-formedness premise (2026-09-21)

Added with the proof; the one delta against the reviewed statement.
The run's intermediate terms are re-typed by `preservation`, which is
conditional on `WfCtx Δ` — so a run under an arbitrary ambient `Δ`
inherits that premise.  It is the price of decision 5 (stating over any
`Δ` rather than `empty`); `ColorPreservationClosed` and
`ScopeMapPreservationClosed` are the v7-faithful closed forms at the
empty ambient, premise-free beyond the typing.

## Show.agda

de Bruijn → NAMED rendering for the two-universe Strong System F:
terms, ordinary types, representation payloads, conversions, boundary
scopes, type contexts, and whole evaluator traces.  DISPLAY ONLY —
there is no theorem here, and nothing in the development depends on it.

WHY IT EXISTS (Jeremy, 2026-09-05): a hand-transcription error read an
interior `` ` 0 `` in the exterior frame.  Nothing in this development
should ever be transcribed by hand; it should be rendered.

### The two universes are rendered differently

That is the point of the 2026-09-19 port.

* a REPRESENTATION variable prints as a Greek letter — α, β, γ, then
  α′, β′, γ′, …;
* the ORDINARY type variable that NAMES it prints as the Latin letter
  at the same position — X, Y, Z, then X′, Y′, Z′, ….

So `X` is by construction the ordinary name of α, `Y` of β, and a
boundary that binds cell α at ordinary position 0 prints as
`⟪ ↥X , … ⟫`.  Reading a change's letter therefore says which
representation it is about; if a rendered `↓` shows a letter other than
the one its representation was allocated with, the name map and the
representation it is supposed to denote have COME APART, which is the
defect class the 2026-09-18 repairs were about.

### What a boundary `M ⟪ Θ , c ⟫` renders as

Under an exterior environment:

* `Θ`'s CHANGES appear IN THE ORDER THEY ACT — that is, the list is
  walked head-LAST, which is the order `_∣_⊢χ_⇒_` uses.  An `unbind`
  prints as `↓X` naming the ordinary variable it deletes, a `bind`
  as `↥X` naming the ordinary variable it inserts.
* the CONVERSION comes last and is read on the CONVERSION context —
  binds performed, unbinds SKIPPED, a re-bind of a live name a no-op
  — which is a different name map from the interior's whenever the
  boundary scope unbinds.  `showBnd` computes both; the body is rendered
  on the interior, `c` on the conversion context.

### How it is driven

USED AS A TOOL non-interactively via `scripts/render_term.sh`, which
exploits the type-error trick: `oops : e ≡ ""; oops = refl` makes Agda
print `e`'s normal form in the mismatch error.  The entry points it
calls are at the bottom: `showTyIn`, `showRepIn`, `showTmIn`,
`showConvIn`, `showBndIn`, `showTCtx`, `showTermsIn`, and `showRun`,
which renders a whole evaluator run with the store and the rule that
fired at each step.

### §3 — the rendering environment

`eReps` is the representation context, de Bruijn indexed, each entry
carrying BOTH names allocated for that representation variable: the
Greek one it prints as, and the Latin one any ordinary variable naming
it prints as.  `eNames` is the ordinary name map itself — exactly
`names Γ`, a list of representation-variable indices — so an ordinary
variable's rendered name is a TWO-STEP lookup, which is what the design
says it is.

### §4 — `showRep`

A PAYLOAD is read in the representation universe, with a LOCAL prefix:
`Ξ ⊢ref[ n ] i` says index `i < n` is bound by an enclosing payload `∀`
and index `n + α` is the free representation variable α.  The locals
are ordinary variables, so they print with Latin letters and the free
ones with Greek.

### §6 — binder names are globally unique

Jeremy, 2026-09-06: two sibling `Λ`s must not both print as `ΛX`.  The
type/representation counter `f` is threaded left to right through the
whole term; the term-binder counter is the λ-depth, restored after each
body, because term names are stable across steps and sibling λs may
share one.

A `ν` takes a name from the same counter `f` (2026-09-24): it prints as
`(ν X:=A · L ⟨ c ⟩)`, where `X` is the name of the cell it WILL
allocate, and `c` is shown under that name — the conversion context of
`TyBetaBoundary` at the allocated context is `underΛE`'s shape with a
bound cell.  Because the operator `L` draws later names, a `Λ` inside it
prints with a different letter than the `ν` (`ν X:=ℕ · (ΛY. …)`), and the
two denote the same variable once `Nu-Λ` fires.

### §7 — `showRepEntries`

A representation payload is stored OUTSIDE its own binder (`∋ʳ` shifts
it on lookup), so the entry at index `i` is read on the names from
`i+1` on.  `ctxEnv` builds the renderer from the actual state context:
cell `i` is always named by the `i`-th Greek name, and the ordinary
names are exactly the state's name map.

### §9 — the ambient environment

`n` representation variables, ordinary name `i` denoting representation
`i`, so ordinary slot 0 prints as X and names α.  New names start at
`n`, so term binders cannot collide with them.

## proof/Types.agda

THE LEMMAS ABOUT `renameᵗ` AND `substᵗ` that the two-universe layer
needs: `substᵗ-cong`, `extsᵗ-renᵗ`, and the agreement of renaming with
substitution, `substᵗ-renᵗ`.

NOT THE DEFINITIONS (`Types.agda`), and not the full algebraic theory —
composition, `sub-sub`, `substitution`, the `_[_]ᵗ` commutation laws —
which is `proof/TypeSubst.agda`.  This module is the private half of
`Types.agda` under the repo's public/private split
(`notes/DECISIONS.md`, 2026-09-20).

IT IS THE BOTTOM OF THE HIERARCHY.  It imports `Types.agda` and the
standard library and NOTHING else, which is what lets `Ctx.agda`,
`proof/Ctx.agda` and `Boundary.agda` stand on it.  Keep that import
list closed when adding a lemma.

## proof/TypeSubst.agda

THE ALGEBRAIC THEORY OF TYPE SUBSTITUTION.  Composition `_⨟ᵗ_` and
`cons-sub`; the congruences `rename-cong` / `subst-cong`; the fusion
laws `rename-rename-commute`, `rename-subst-commute`, `rename-subst`,
`exts-seq`, `sub-sub`, `subst-id`; and the two laws the metatheory uses
pervasively, `substitution` and `exts-sub-cons`, together with
`rename-[]ᵗ-commute` and `subst-[]ᵗ-commute`.  `substitution` is

```
  (a [ b ]ᵗ) [ c ]ᵗ ≡ (subst-one-at-one a c) [ (b [ c ]ᵗ) ]ᵗ
```

NO DEFINITIONS.  `Ty`, `Substᵗ`, `renameᵗ`, `substᵗ`, `extsᵗ`,
`singleTyEnv` and `_[_]ᵗ` are `Types.agda`.  The few single-index facts
the two-universe layer needs — `substᵗ-cong`, `extsᵗ-renᵗ`,
`substᵗ-renᵗ` — are `proof/Types.agda`, kept apart so that `Ctx.agda`
and everything above it can stand on a module that imports nothing but
`Types.agda`.  Nothing here mentions a context, a universe, a
conversion or a term.

IT IS A MIRROR, DELIBERATELY.  Same names and same statements as
`SystemF/agda/extrinsic/TypeSubst.agda`, so the two developments can be
diffed line for line; keep it that way when adding a law.  Its only
client inside this development is `proof/Preserve.agda`, so a law added
here is not automatically reachable from the rest of the tree.

## proof/Ctx.agda

EVERY FACT ABOUT THE TWO DE BRUIJN UNIVERSES.

§1 is the determinacy and uniqueness suite the reduction rules' `det`
consumes — `∋ˡ-det`, `∋ʳ-det`, `same-rep-unique`, `same-target-unique`,
`sameTy-src-unique`, `∋:=-det`, `unique-lookup`, `unique-underΛ`,
`wf-empty`.  §2 is the NAME-MAP half of representation renaming
(`renameᵗ-fuse`, `∋ˡ-ren`, `fresh-ren`).  §3 is the insert/delete
relations (`lookup→del`, `ins-exists`, `pigeon`, `live?`) and `RepWk` —
its base instances `repwk-abst₀` / `repwk-cons₀` and the closure lemma
`repwk-abst`, with `wfctx-ren` and `∋:=-ren`.

NOT THE DEFINITIONS.  Every judgement and relation named above is
declared in `Ctx.agda`, which holds definitions only.  Anything
mentioning `Change` or `Boundary` belongs in `Boundary.agda`.

### Why the split is by subject, not by layer (`notes/DECISIONS.md`, 2026-09-20)

The second half is the context material that used to sit in
`Boundary.agda` §1; moving it here is what lets `Ctx.agda` stay
definition-only and lets `Boundary.agda` begin at its §2.  The import
list is `Types`, `proof/Types` and `Ctx` — keep it that way, since
`Boundary.agda` imports this module and a cycle is one careless import
away.

### §1 — the uniqueness suite

`same-target-unique`: for a unique name map, a representation-universe
type has at most one ordinary reading.

`sameTy-src-unique`: a spelling CROSSES between the interior and the
conversion context by the REPRESENTATION it denotes, never by
arithmetic on its position — the two name maps can reorder relative to
each other (`notes/ForallPayloadWall.agda` §3).  `_⊢_≈_⊣_` is that
crossing, and on a unique name map it is a FUNCTION, which is what
determinism needs from the rules that carry it.  It is stated on NAME
MAPS, because `_⊢_≈_⊣_`'s contexts reach the judgement only through
`names`, a projection, and so are not determined by it.

### §2 — the name-map half of renaming

Renaming is a congruence, composes, and commutes with a shift.
`same-cast` / `same-ren`: the representation READING of an ordinary
type moves with the map — the ordinary spelling is untouched and the
representation it denotes is renamed.  `tv-ren`: ordinary type
formation reads the name map for POSITIONS only, so it transports along
ANY representation renaming whatever; it too is stated on the name map,
since the source representation context plays no part in `∋tv` and
naming it would leave an unsolvable implicit.

### §3 — insert/delete and `RepWk`

`∋ˡ-cons` — inserting ONE FRESH BINDING at the head, abstract or
represented.  Three of the four `RepWk` fields do not look at the
binding at all — a name lookup only moves one place further in, and
injectivity is `suc`'s — so the only thing the insertion has to supply
is the WEAKEST form of its own well-formedness: the step
`WfRepCtx Ξ → WfRepCtx (b₀ ∷ Ξ)`, which is `wf-abstR` for an abstract
binder and `wf-bindR w` for a represented one whose payload checks over
`Ξ`.  This is the base move made by a term crossing `Λ` (at `abstR`)
and by one crossing a new representation binder (at `bindR R`);
`repwk-abst` is the recursion-closure move when an existing renaming
itself goes under `Λ`.

`wk-ref`: a payload is checked at a local-binder depth `m`, so it moves
by `extN m ρ`; a reference at depth `m` is either local (untouched) or
free (renamed), which is exactly what `extN m ρ` does.

### Retired

* "including `repwk-wkN`, whose home is `proof/RepWeaken.agda`" — that
  instance went with the bind block; the live instances are
  `repwk-abst₀`, `repwk-cons₀` and `repwk-abst`, all here.
* "(iii) `wf-reps` … all that is needed is that the BIND BLOCK itself
  is well formed where it lands — each payload weakened past the
  block's own tail" — there is no bind block; both readings leave the
  representation context alone, so `wf-reps` transports unchanged.
* The bind-block lemmas themselves — `wfᴿ-push`, `wfRepCtx-push`,
  `∋ʳ-push`, `⊆ᵃ-shiftRVars`, `repwk-push` and the `shiftRVars` family
  — went on 2026-09-22 with experiment 2.

## proof/TermSubst.agda

THE PROOF HALF OF `TermSubst.agda` (2026-09-22, the AGENTS.md
public/private mandate): every renaming/substitution definition and
lemma that NO top-level module mentions.  The section numbers are the
ones this material had in the public file, because other modules cite
them.

§1 is `id²` and the single-map `renᶠ`; §2 is values under a type
renaming (`inert-renᶜ`, `value-renᴹ²`, `value-renᴹᴿ`), the
ordinary-identity agreement `renᴹ²-ord-id` with its `-pointwise-id` /
`-ord-id` helpers, and the derived `renᴹ`, `wkN`, `wkᴹ`, `⇑ᴹ`; §3 is
TERM-VARIABLE renaming `extⁿ` / `renⁿ` / `shiftᵐ` with `value-renⁿ` and
`∋-extⁿ`; §4 the `⤊` transports and the typing lemmas `⊢renⁿ`,
`renⁿ-id`, `⊢weakenⁿ`; §5 `value-substᵐ`; §6 the typed images
`_∣_⊢ⁱ_⦂_` with `⊢imgTm`, `shiftᴵ-⊢`, `extᴵ-⊢`.

WHAT IS PUBLIC AND WHY.  `TermSubst.agda` keeps exactly what a
top-level module names: `TyRename` / `idᵗ` / `renᴮ²` / `renᴹ²` and
`renᴹᴿ` (Reduction, Residual), `↑ᴹ[_]` / `↑ᴮ[_]` (Eval, Reduction,
Residual), and the substitution `Img`, `crossΛᴹ`, `⇑ᴵ`, `extᴵ`,
`substᵐ`, `betaEnv`, `_[_∶_]ᵐ` (Reduction, Residual, Examples).
Nothing here may be cited from a top-level file: the audit principle is
that the top level plus the theorem statements can be read alone.

### The two laws a reader must know

1. Boundaries are TERM-CLOSED (`Terms.agda`, `env`), so `renⁿ` does NOT
   descend into `_⟪_,_⟫` and `⊢renⁿ` reuses the boundary's derivation
   unchanged.
2. A type renaming carries TWO independent maps, and the ordinary one
   never moves a representation occurrence: `renᴹ²-ord-id` is the
   general statement that an ordinary-identity `renᴹ²` IS `renᴹᴿ`
   (`notes/DECISIONS.md`, 2026-09-20 — representation-only renaming is
   its own traversal).

### §2 — values survive every renaming and substitution

Needed because `⊢Λ` carries `Value N` (the value restriction,
`Terms.agda` §4): each typing-transport lemma must rebuild that
premise.  Inertness is by conversion constructor, which no renaming
changes.  `⇑ᴹ`: crossing a term-level type binder weakens both free
universes — the newly bound ordinary variable names the newly bound
abstract representation.

### §3, §5 — values under the other two operations

`value-renⁿ`: ordinary-variable renaming never enters a boundary and a
variable is never a value, so values are preserved on the nose.
`value-substᵐ`: likewise for substitution — a value contains no free
ordinary variable at a value position, and boundaries are left alone.

## proof/Canonical.agda

CANONICAL FORMS for the conversion-boundary calculus.

A closed value is one of five shapes, and its EXTERIOR TYPE decides
which.  The whole suite is driven by ONE observation: for a wrapper
value `V ⟪ Θ , c ⟫` the `env` rule relates the EXTERIOR TYPE and the
TARGET TYPE of `c` by `_⊢_≈_⊣_` — two ordinary spellings of ONE
representation type — and an INERT `c` determines that target type's
head constructor outright:

```
  id (` X)  ⇝  ` X          I-idv
  seal X    ⇝  ` X          I-seal
  s ↦ t     ⇝  A′ ⇒ B′      I-fun
  `∀ s      ⇝  `∀ B         I-all
```

Neither ACTIVE conversion can occur under `V-⟪⟫`, so no inert
conversion has a BASE target at all — which is why `canon-base` returns
a literal OUTRIGHT (§3), with no wrapper escape hatch.  Dually, the two
conversions with a VARIABLE target are exactly `seal` and the
id-at-a-variable — the two left-hand sides of `CancelR` and `IdPush`
(§3, `canon-var`).  This is the v1 "canon-var nightmare", dissolved: it
is a two-way case split on a conversion constructor, with no
representation comparison anywhere.

### §1 — `≈` preserves the exterior type's head constructor

History: the old `env` exposed `shiftBy (numBinds Θ) Bₑ` directly, and
the relational rule that replaced it factored both spellings through a
representation type and applied `shiftRep` on the conversion side.
With the store design (experiment 2) there is no bind prefix to cross,
so `Δ ⊢ Bₑ ≈ Cₑ ⊣ Δᶜ` relates the two spellings at EQUAL
representation depth, and the head-constructor inversions simplify
accordingly.

`conv-tgt≡` retypes a conversion along an equality of its target type;
`⊢ty≡` retypes a term along an equality of its type — used to move an
interior derivation along the conversion inversions of
`Conversion.agda` (which name the SOURCE type of an `id`/`unseal`), so
that the canonical-forms lemmas can be applied to it.

### §2 — what an INERT conversion can look like, read off its target

* `inert-¬base`: no inert conversion has a base target.  `id A` at a
  base type is the one conversion with a base target, and it is ACTIVE
  (`A-idb`), so `V-⟪⟫` can never build a value at a base type.
* `inert-fun-conv`: an ARROW target forces a function conversion —
  `id`/`seal` have variable targets and `` `∀ `` has a `∀` target.
* `inert-all-conv`: a `∀` target forces a `∀` conversion.
* `inert-var-conv`: a VARIABLE target admits exactly TWO conversions,
  and the variable is literally the name they carry — there is no
  second spelling to compare.  These two are the left-hand sides of
  `CancelR` and `IdPush`.

### §3 — canonical forms

* BASE.  A closed value at a base type is a numeral or Boolean literal,
  OUTRIGHT — no wrapper survives (§2, `inert-¬base`).
* ARROW.  A closed value at an arrow type is a λ or a wrapper with a
  FUNCTION CONVERSION — the two left-hand sides of `Beta` and `Peel`.
  The wrapper's interior is itself a value, which is exactly `Peel`'s
  first premise.
* ∀.  A closed value at a `∀` type is a `Λ` over a VALUE (`V-Λ`'s
  premise, and exactly `Nu-Λ`'s premise) or a wrapper with a `∀`
  CONVERSION (`Nu-⟪Λ⟫`'s and `Nu-⟪⟫`'s).
* VARIABLE.  A closed value at an abstract type is a wrapper whose
  conversion is `seal Y` or `id (` Y)`, nothing else: the two left-hand
  sides of `CancelR` and `IdPush`.  (`value-var-visible` is NOT needed
  here — the conversion inversion already decides the shape; visibility
  of the named slot is a separate, and independently available, fact.)

### Retired

* "`env` relates the exterior type and the target type of `c` through
  `SameTyExt`, its common representation type shifted past Θ's
  representation binders on the conversion side" — `env`'s exterior
  premise is `_⊢_≈_⊣_` at equal depth, as stated above.

## proof/Preserve.agda

Preservation for the two-universe representation-variable design, on
the GLOBAL REPRESENTATION STORE (experiment 2,
`notes/RepStoreSketch.md`).

§1 recovers type well-formedness from typing and supplies the ordinary
type-substitution facts used by elimination.  §1b is `RepRefines` — the
`abstR → bindR R` refinement a ∀-elimination performs in place.  §2 is
`alloc-wf` / `repwk-alloc` / `inst-boundarywf`, everything the
ALLOCATION of a cell needs, and the minted-conversion typings
`⊢reveal`/`⊢conceal` — which `compile-ν` and `Nu-⟪⟫`'s pushed `ν` use —
with `⊢instReveal`/`⊢instConceal` (§2b), which no rule needs since
2026-09-24.  §3 opens with `nu-outer`, the outer layer every `Nu`
contractum shares, typed from `⊢ν`'s own premises.  §3 proves the local reduction cases.  §4 states the
transports that are proved downstream — `CrossΛTyping`,
`AddUnbind0Typing`, `ShiftTyping` and the three crossing cases (§4b) —
and supplies the `AllocWf` / `env-apply` machinery the congruences
consume.  §5 reads off a step what it did to the store (`step-alloc`),
proves `preserve-wf`, and assembles `preserve` / `preserve*` in `Impl`.

A STEP RETURNS THE CHANGE IT MADE, so the contractum is typed at
`apply δ Δ` and the congruences must SHIFT THE REDEX'S SIBLINGS by
`↑ᴹ[ δ ]`.  That shift, `ShiftTyping`, is the one lemma the store
experiment added; it is today's representation weakening at `ρ = suc`
(`proof/RepWeaken.agda`, `shift-⊢`).  What it replaced —
`RepWeakenTyping`, the bind-block weakening `Peel` used to need — is
gone: the dual's interior is now the exterior itself, so `Peel` moves
its argument verbatim.

ALL FOUR TRANSPORTS have implementations, the last being
`AddUnbind0Typing` — reshaped with the 2026-09-20 `TyPeelR-⟪⟫` (today
`Nu-⟪⟫`) repair and
proved the same day in `proof/AddUnbind0.agda` — so `Preservation.agda`
exposes no parameter at all.

### §1 — `WfRen`, `SubWf`, `same-wf`

A well-formedness renaming only needs to preserve the EXISTENCE of an
ordinary name; the representation variable denoted by that name is not
part of the ordinary type-formation judgement.  A type substitution is
well formed when it sends every live ordinary variable to a well-formed
type.  And back: a type that HAS a representation reading is well
formed, because every leaf of a reading is a live ordinary name.

### §1b — `RepRefines`, `⊢refine`

The two-universe transcription of the old retagging relation.  Concrete
bindings and payloads are preserved; an ABSTRACT representation
variable may become represented.

In `⊢refine` the target well-formedness is EXPLICIT: the only
refinement that creates a concrete binding is supplied by the caller
together with its payload proof.  All output well-formedness is then
derived by `BoundaryWf`.

### §2 — the allocation, and the conversion a reveal mints

`alloc-wf` — ALLOCATING A CELL.  The store grows at index 0 and every
existing representation variable — in the name map and in every sibling
term — moves up by one (`allocate`, `Ctx.agda` §9).  The payload is
well formed because `same-wfᴿ` reads it off the argument's `~`.

`repwk-alloc` — the representation weakening the allocation induces;
`repwk-cons₀` needs exactly the payload's well-formedness.

`inst-boundarywf` — THE INSTANTIATED SCOPE IS AGAIN A BOUNDARY SCOPE
WITNESS, read at the ALLOCATED context.  The three `Nu` rules mint the
cell for the type argument's representation at index 0 and bind it by
`bind 0 0`; the old changes run underneath, in both universes.  The
two readings are `inst-interior` and `inst-conversion`
(`Boundary.agda` §3a).  `preserve-Nu-⟪⟫` uses it for the moved
boundary's exterior;
`proof/Progress.agda`'s `addUnbind0-reading` uses it for the `RepWk suc`
that the same allocation induces.

`SameSub` — eliminating an ordinary `∀` binder COMMUTES with the
representation reading: both sides substitute the readings of the same
argument.  `underNames-shift-free` shifts only the FREE representation
names while leaving the ordinary spelling in place; the depth parameter
accounts for local `∀` names.  `abstract-rep-avoid` — looking up a
represented payload past an abstract prefix always weakens it past the
distinguished abstract binder, so the returned payload avoids the
distinguished representation index.

### §3 — the local cases

`sameTy-ℕ`: the exterior comparison is now at EQUAL DEPTH — a boundary
carries no bind block — so a base conversion type pins the exterior
type outright.

### §4 — the transports

THREE TRANSPORTS, all PROVED downstream, all internal staging
interfaces only: `Preservation.agda` instantiates each with its proof,
so preservation has no parameter.  The first two need a BINDER
(`underΛ`, the appended `unbind 0 0`) on top of the renaming; the third,
the SIBLING SHIFT, is pure renaming.

```
  CrossΛTyping    PROVED 2026-09-20, `proof/RepWeaken.cross-Λ-⊢`, as one
                  `env` around `⊢renᴿ` at `repwk-abst₀`.
  AddUnbind0Typing  REFUTED, RESHAPED and PROVED, all on 2026-09-20, and
                  reshaped again by the store, which removed its
                  `numBinds` arithmetic.
  ShiftTyping     NEW with the store (2026-09-22),
                  `proof/RepWeaken.shift-⊢`.  It REPLACES
                  `RepWeakenTyping`, the bind-block weakening `Peel`
                  used to consume: `Peel` moves its argument verbatim
                  now, and what needs a shift instead is every
                  congruence's SIBLING.
```

`AddUnbind0Typing`, RESHAPED WITH THE RULE (2026-09-20) AND AGAIN WITH
THE STORE (2026-09-22).  The moved boundary crosses ONE fresh cell and
ONE fresh ordinary name for it, so its interior term and its scope get
exactly the SIBLING SHIFT — `renᴹᴿ suc` and `renᴮᴿ suc`, with no
bind-block offset to compute, since a boundary carries no binds any
more.  The moved conversion is still NAMED (`s′`) and pinned by a
`SameConv` against the old conversion context viewed through the
representation renaming the allocation makes (`renNameCtx suc`) — that
was the 2026-09-20 repair (`notes/AddLock0Wall.agda`), and it stays.

PROVED in `proof/AddUnbind0.agda`'s `addUnbind0-⊢`: the `env`-to-`env`
transport across one allocated cell and one fresh ordinary name.  The
interior reading is `Boundary.snoc-unbind0-interior-ren` (the appended
unbind DELETES the fresh name, so what is left is `interior-ren`), the
interior term is `proof/RepWeaken.⊢renᴿ` at `repwk-alloc`, and the
conversion is `conv-ren` (`Conversion.agda` §2d) followed by
`proof/PeelDual.respell-⊢` — whose `reps Γ′ ≡ reps Γ` premise is
exactly what `renNameCtx` arranges.  It stays a PARAMETER of `Impl`
here only because its proof imports this module.

`ShiftTyping` — THE SIBLING SHIFT, the one new lemma of the store
experiment (`notes/RepStoreSketch.md` §2).  When a step allocates a
cell, the whole program lives under one more representation binder, so
every SIBLING of the redex moves up by one.  `renᴹᴿ` is
representation-only by construction, so the sibling's TYPE and every
ordinary spelling are unchanged.  It is today's rep-weakening at
`ρ = suc`, PROVED in `proof/RepWeaken.shift-⊢` as
`⊢renᴿ (repwk-alloc wR)`.

THE PAYLOAD MUST BE WELL FORMED.  Without `reps Δ ⊢ᴿ R` the statement
is FALSE: a boundary's `env` stores a `BoundaryWf` whose `bw-exterior`
demands a `WfCtx` of the allocated context, and
`WfRepCtx (bindR R ∷ Ξ)` holds only when `R` checks over `Ξ`.  At every
call site it is `same-wfᴿ` of the rule's own `Δ ⊢ᶜ A ~ R` premise
(`step-alloc`).

`AllocWf` — what a step's change did to the store, as a PROPOSITION:
nothing, or one well-formed cell.  Everything the theorems need about
`apply` and `↑ᴹ[_]` is stated once at `none` (identity) and once at
`new R`.  `aw-reps`: a boundary changes NAMES only, so a reading
transports an `AllocWf`.

`env-apply` — THE BOUNDARY CASE OF THE CONGRUENCE.  The interior
stepped at `Δᵢ` and its contractum lives at `apply δ Δᵢ`; the new
boundary is read at `apply δ Δ` by `interior-ren` / `conversion-ren` at
`suc`, and that reading's interior IS `apply δ Δᵢ` — a boundary keeps
the store, so `reps Δᵢ ≡ reps Δ`.  Everything else transports by
representation weakening.

### §4b — the crossing cases

The downstream crossing cases and transports stay module parameters
HERE because their proofs import this module.  `Preservation.agda`
plugs in every implementation and exposes NO public parameter at all.
Until 2026-09-20 `AddUnbind0Typing` was REFUTED and `Impl.preserve` a
conditional theorem with a false hypothesis; the `TyPeelR-⟪⟫` repair
installed that day reshaped it (`notes/AddLock0Wall.agda`), and
`proof/AddUnbind0.addUnbind0-⊢` proved the reshaped statement, which made
preservation UNCONDITIONAL.

```
  CrossΛTyping   PROVED (2026-09-20) — `proof/RepWeaken.cross-Λ-⊢`.
  AddUnbind0Typing PROVED (2026-09-20), on the statement RESHAPED with
                 the `TyPeelR-⟪⟫` (today `Nu-⟪⟫`) repair of the same day —
                 `proof/AddUnbind0.addUnbind0-⊢`.  The old statement fixed
                 the moved conversion at `renᶜ (extᵗ suc) s` and was
                 REFUTED from a closed, plain source program
                 (`notes/AddLock0Wall.agda`, which keeps that statement
                 locally and still refutes it).
  PeelCase       PROVED UNCONDITIONALLY (2026-09-20), and SHRUNK by the
                 store (2026-09-22) — `proof/PeelDual.agda`.  The
                 dual's interior IS the exterior (`dual-interior`), so
                 the crossing argument moves VERBATIM and the rule's
                 old `renᴹ² (wkN (numBinds Θ))` is gone with the binds.
  IdPushCase     PROVED outright — `proof/MoveScope.preserve-IdPush`.
  CancelRCase    PROVED outright, on the rule REPAIRED 2026-09-19 —
                 `proof/MoveScope.preserve-CancelR`.
```

### §5 — what a step did to the store

`step-alloc`: ONLY THE THREE ∀-ELIMINATIONS ALLOCATE, and each carries
the reading `Δ ⊢ᶜ A ~ R` that makes the minted cell well formed
(`same-wfᴿ`).  The congruences pass the change up; `ξ-⟪⟫` passes it
across a boundary, which keeps the store (`interior-reps`).  NO TYPING
DERIVATION IS NEEDED — the rule premises and `WfCtx Δ` are enough.

`preserve-wf` — PRESERVATION OF WELL-FORMEDNESS.  The typing derivation
is not read: it is part of the statement only so that the two
preservation theorems read the same.

`preserve*` — ALONG A WHOLE RUN.  The endpoint's context is read off
the derivation (`runCtx`): each step's change is applied to the context
the tail runs at.

## proof/RepWeaken.agda

REPRESENTATION-ONLY MOVES OF A TYPING DERIVATION.  This module proves
the two transports whose movers have an IDENTITY ORDINARY COMPONENT:

* `ShiftTyping` — THE SIBLING SHIFT of the store experiment
  (`notes/RepStoreSketch.md`), which every congruence of `preserve`
  consumes;
* `CrossΛTyping` — which term substitution consumes when an image
  crosses `Λ` (`proof/Preserve.agda` §3).

When a step allocates a cell the whole program lives under one more
representation binder, so the redex's SIBLINGS move up by one:
`allocate R Δ` only RENUMBERS the ordinary name map — every ordinary
position survives — so a sibling's type does not change and no ordinary
spelling inside it moves.  What moves is every representation
occurrence: the payloads its own boundary scopes cite and the
representation variable each of their changes carries.  `renᴹᴿ` is
exactly that traversal.

### The workhorse is the cut

Not the statement itself but its generalisation.  The induction goes
under `Λ`, which pushes one `abstR`, so the inserted cell stops being
at the head of the representation context and the name map stops being
the exterior's.  Both are absorbed by abstracting the insertion into an
arbitrary representation renaming ρ together with the four facts it
must supply — `RepWk ρ Ξ Ξ′`, `Ctx.agda` §11 — and renaming the name
map POINTWISE, as `map ρ`:

```agda
  ⊢renᴿ : RepWk ρ Ξ Ξ′ → (Ξ ∣ η) ∣ Γ ⊢ M ⦂ A
        → (Ξ′ ∣ map ρ η) ∣ Γ ⊢ renᴹᴿ ρ M ⦂ A
```

The term context `Γ` passes through UNCHANGED: `⊢`'s variable rule does
not read the type context at all, and an ordinary type spelling is
untouched by a representation renaming.  Under `Λ` the renaming becomes
`extᵗ ρ` (`repwk-abst`), which is precisely how `renᴹᴿ` recurses.
CROSSING A BOUNDARY CHANGES NOTHING any more: since the store
experiment a boundary scope carries no bind block, so the SAME ρ runs
inside it (`interior-ren` / `conversion-ren` at ρ, no `extN` offset).

### The hard case is `env`

Every one of its premises transports by a lemma of `proof/Ctx.agda` §3,
`Boundary.agda` §3d or `Conversion.agda` §2d: the exterior
well-formedness by `wfctx-ren`, the two readings by `interior-ren` /
`conversion-ren`, the conversion's TYPING by `conv-ren` (the conversion
and both of its types are unchanged — a conversion is rep-free — but
the lookup square it cites now reads a renamed payload), the two
alignment premises by `same-ren`, and the exterior type's
well-formedness by `wf-ren-rep`.  The two alignment premises are now
the SAME relation at the same depth, which is what retired the old
`shiftRep` bookkeeping here.

### The payload must be well formed

`repwk-alloc` (`proof/Preserve.agda` §2) demands `Ξ ⊢ᴿ R`, and without
it the shift is FALSE: `env` stores a `BoundaryWf` whose `bw-exterior`
is a `WfCtx`, so the ALLOCATED context must be well formed, and
`WfRepCtx (bindR R ∷ Ξ)` holds only when `R` checks over `Ξ`.  At every
call site it is `same-wfᴿ` of the allocating rule's own reading premise
(`step-alloc`).

### §2 — `shift-⊢`, the instance the store runs at

Allocating a cell pushes `bindR R` onto the head of the representation
context and moves every existing representation variable — and every
name-map entry — up by one; that is `RepWk suc` (`repwk-alloc`), and
`map suc` IS `shiftReps`, so `allocate R (Ξ ∣ η)` is literally
`(bindR R ∷ Ξ) ∣ map suc η`.  Hence THE ONE NEW LEMMA of the store
experiment is `⊢renᴿ` at that instance, with no cast at all.

### §3 — `cross-Λ-⊢`

The same induction at the base instance
`repwk-abst₀ : RepWk suc Ξ (abstR ∷ Ξ)`.  The moved term lands under
the new abstract representation binder but OUTSIDE its ordinary name.
One `env` with `(unbind 0 0 ∷ [])` then supplies exactly that missing
ordinary boundary: its interior DELETES name zero, while its conversion
reading RETAINS it for `mkId (⇑ᵗ A)`.

## proof/AddUnbind0.agda

THE MOVED BOUNDARY'S TYPING — `AddUnbind0Typing`, preservation's last
parameter, on the statement the 2026-09-20 `TyPeelR-⟪⟫` repair gave it
and the 2026-09-22 store experiment simplified.  The statement is
unchanged by `ν`: `Nu-⟪⟫` moves the inner boundary exactly as
`TyPeelR-⟪⟫` did, and only what surrounds it changed.

`Nu-⟪⟫` moves the inner boundary out across ONE freshly allocated
cell (the type argument's representation, minted by `inst`) and ONE
fresh ordinary name for it, and appends `unbind 0 0` to the scope.  The
move is the plain SIBLING SHIFT on the TERM — `renᴹᴿ suc` — because the
appended unbind acts FIRST in the interior reading and deletes the fresh
ordinary name before any of Θ's own changes run.  It is NOT
representation-only on the CONVERSION, because a conversion reading
SKIPS unbinds: the fresh name survives there and Θ's own binds displace
it.  That is the content of `notes/AddLock0Wall.agda`, and it is why
the rule carries the moved spelling `s′` with a `SameConv` instead of
renaming for it.

### How the `env` premises transport

```
  bw-exterior    the statement's own `WfCtx` premise
  bw-interior    `snoc-unbind0-interior-ren` — the unbind deletes the fresh
                 name, leaving `interior-ren` at `suc`
  bw-conversion  the rule's own premise
  the interior   `proof/RepWeaken.⊢renᴿ` at `repwk-cons₀ (bindR P) …`:
                 purely representation
  the conversion `conv-ren` to move the OLD typing onto the new
                 representation context, then `proof/PeelDual.respell-⊢`
                 to move it onto the new NAME map.  `respell-⊢` demands
                 `reps Γ′ ≡ reps Γ`, which is exactly why the rule's
                 `SameConv` reads the old context through
                 `renNameCtx`: that keeps the old ordinary positions
                 and takes the representation context from the moved
                 side.
  the two ≈      come back FROM `respell-⊢`, paired with the old
                 readings; `same-ren` supplies the moved side and
                 `same-rep-unique` identifies the two representations.
  the exterior   `same-weaken` for the fresh ordinary name.  There is
                 no bind-block shift left to commute with: the exterior
                 comparison is `≈` at equal depth.
```

The retention `respell-⊢` consumes is NOT a new assumption: it is the
`keep` component of `Boundary.snoc-unbind0-conversion-ren`, transported
onto the rule's own `Δ⁺ᶜ` by `conversion-functional`.  Nothing is
postulated.

### The pieces

* §1 `same-∀⁻`: the exterior reading of a `` `∀ `` splits, and the
  caller needs the split BEFORE it knows the representation is a
  `` `∀ `` — which is why this is an inversion and not a pattern match.
* §2 `moved-keep`: the retention the moved conversion is re-spelled
  along.  `Δ⁺ᶜ` is the rule's own reading, so the transport's output
  context is identified with it by `conversion-functional`.
  `moved-conv`: the moved conversion's TYPING, with both of its types
  paired back to the old ones — two moves, in this order: `conv-ren`
  changes the representation context, `respell-⊢` changes the name map
  (`moved-conv′` is the same on the premises the rule actually
  carries).  `moved-sameᵢ`: the interior alignment — the moved side is
  the old reading renamed, the conversion side is `respell-⊢`'s, and
  the two representations are identified because a reading determines
  its representation.  `moved-sameₑ`: the exterior alignment — the new
  ordinary name weakens the exterior reading, and that is all.
* §3 `moved-env`, the assembled `env`; §4 `addUnbind0-⊢`, the theorem.

## proof/PeelDual.agda

THE PEEL CROSSING — the dual is an INVERSE, and both of its readings
are theorems of `Boundary.agda` §3a.

```
  Δ ⊢ⁱ Θ ⇒ Δᵢ  →  Δᵢ ⊢ⁱ dual Θ ⇒ Δ
```

is `dual-interior`: the crossing argument's frame IS THE EXTERIOR.
Since the store experiment (2026-09-22) a boundary scope carries no
bind block, so that is the exterior ON THE NOSE — the argument, typed
at `Δ`, crosses VERBATIM and gains neither ordinary scope nor a
representation binder.  The rule's old
`renᴹ² (ren² idᵗ (wkN (numBinds Θ)))`, and with it this module's
`RepWeakenTyping` parameter and the `renᴹ²-ord-id` bridge, are gone.

### The dual's conversion context is the one thing not free

It is not `convCtx Θ Δ` renumbered: (P), the identity
`conv(dual Θ, int(Θ, Δ)) ≡ conv(Θ, Δ)`, is a theorem on `main` and is
FALSE here, because deleting a name from a SEQUENCE renumbers the rest
(`notes/CrossingAudit.agda` §§4–6).  What survives is (Q) — the two
contexts name the same representation VARIABLES (`Q`, `Boundary.agda`
§3b) — and `Peel` therefore carries the dual's own spelling `s′`
together with a `SameConv` relating it to `s`.  §1 is what turns that
premise into the dual boundary's conversion typing.

```
  §1  re-spelling a TYPED conversion across the crossing
  §2  the ⇒-splitting the redex's `env` premises need
  §3  the crossing, and `preserve-Peel`
```

### §1 — `respell-⊢`

`respell` (`Conversion.agda` §2c) produces a conversion's other
spelling; this produces its TYPING.  The two contexts share a
representation context and differ only in their ordinary name map, so
every leaf transports: a `seal`/`unseal` cites the SAME binder and only
its ordinary spelling changes, and an identity's payload is re-spelled
by `respell-ty`.  The source and target types come back paired with
`_⊢_≈_⊣_`s, which is what the crossing boundary's `env` consumes.

### §2 — splitting at the arrow

The interior type of a boundary whose conversion is a `_↦_` is an
arrow, because its reading is.  Since the store experiment the EXTERIOR
comparison is the same relation at the same depth, so this one
inversion (`sameTy-⇒⁻`) serves BOTH `env` premises.

### §3 — the crossing

THE ARGUMENT DOES NOT MOVE ANY MORE.  `W` is typed on the exterior `Δ`,
and the dual's interior IS `Δ` (`dual-interior`): since the store
experiment a boundary scope carries no bind block, so there is nothing
for the crossing argument to be shifted past.  `⊢W` is reused verbatim.
In the `where` block, `mwD` is the dual's frame (the exterior itself)
and `sameᵢ-d` says the crossing argument's own exterior reading is the
source spelling the dual's conversion wants.

WHAT WAS DELETED (2026-09-19).  The whole masked-entry development:
`applyChanges-dualScope`, `⊢ˢ-dualScope`, `applyUnlocks-dualScope` and
their `updateAt` commutations (old §2); `interior-dual`, `convCtx-dual`
— which was (P) — and `applyUnlocks-hideBinds` (old §3); and the
`Ren`/`wkN` crossing machinery `⊢ᵐ-dual`, `Ren-wkN`, `crossing` (old
§4).  None of them has a two-universe counterpart: there is no computed
context to state an equality between, (P) is refuted, and the frame
identity is `dual-interior`.  AND (2026-09-22) `shiftRep-⇒` and
`sameTyExt-⇒⁻`: the exterior comparison is now the same relation at the
same depth, so `sameTy-⇒⁻` serves both `env` premises.

## proof/MoveScope.agda

THE SCOPE MOVE — the ONE-LAYER contractum `CancelR` and `IdPush` build,
and the preservation cases they owe.

### The move

Both rules neutralise the OUTER conversion of a two-layer wrapper, so
the surviving boundary stops presenting the abstract name `` ` Y `` and
starts presenting `Y`'s REPRESENTATION.  A representation is a type over
the exterior; inside Θ₂'s UNBINDS it need not be nameable at all, and
`env`'s last premise would then fail.  So the two frames merge:

```
  (V ⟪ Θ₁ , c ⟫) ⟪ Θ₂ , unseal Y ⟫  -→  V ⟪ Θ₁ ++ Θ₂ , c′ ⟫
```

In the two-universe design the frame algebra is RELATIONAL, and the
reading the contractum needs is a theorem of `Boundary.agda` §3a:

```
  merged-interior    the merged frame's interior IS the inner frame's.
```

The merged frame's CONVERSION context is not a theorem of the readings
the redex carries — it is a rule premise, and both rules carry it.

ONE LAYER (2026-09-23).  Until then the contractum was TWO layers, the
outer one `⟪ rewind Θ₂ , mkId A ⟫`, read by `rewind-interior` and
`rewind-conversion`.  Its frame's interior is the exterior it sits at
and its conversion is an identity, so it converted nothing: both proofs
already built the surviving layer AT THE REDEX'S OWN EXTERIOR TYPE `C`
and then wrapped it to re-spell a type it already had.  Deleting the
layer deletes the wrapper, the two premises that minted it
(`Δ ⊢ᶜ Θ₂ ⇒ Δᶜ`, `Δᶜ ∋ Y := A`) and the two rewind readings from this
module.

```
  §1  the small inversions the two cases share
  §2  IDPUSH — PROVED
  §3  CANCELR — PROVED, on the rule repaired 2026-09-19
```

### What the store deleted (2026-09-22)

Every `shiftBy` / `shiftRep` occurrence, and with them `ext-lookup`,
`same-shiftRVars`, `shiftRep-shiftBy`, `tvMono-extendReps` and
`wf-mono`.  A boundary scope carries no bind block, so `rewind Θ₂`'s
interior is `Δ` ITSELF rather than `extendReps (binds Θ₂) Δ`; the
cancelled binder's representation variable IS the outer binder's, not
`numBinds Θ₁ +` it; and the two `env` comparisons are the SAME relation
at the same depth.  Both cases lost about a third of their lines to
that.

### What was deleted earlier (2026-09-19)

Everything this module used to hold about the retired masked-entry
design: `applyUnlocks` / `applyChanges` lookup transports (§1), the
`shiftScope` / `rewind` / `_++_` list algebra (§2), the `scope` /
`interior` context identities (§3), the frame lemmas as EQUALITIES and
the unbind-only refutation (§4, §4b), and `_⊢ᵐ_` for the two new frames
(§5).

### §1 — the small inversions

`sameTy-var`: two ordinary spellings of ONE representation variable.
Both sides of a `_⊢_≈_⊣_` between variables are `same-var`s, so the
judgement is a pair of lookups at a common representation variable.
`sameTy-tgt-var` is the same when only the TARGET is known to be a
variable.  `bindR-inj`: a representation binding determines its
payload; `var-inj`: a representation VARIABLE is determined by the type
it reads as.

### §2 — `preserve-IdPush`

The surviving boundary is the revealing one, so its exterior type is the
redex's own exterior type `C`, presented OUTSIDE Θ₂'s unbinds — at the
plain exterior `Δ`, which is where `C` is nameable.  That is what
retires the old wall: the case needs no scoping invariant.

FOUR MOVES, one per premise of the contractum's `env`:

```
  FRAME       `Θ₁ ++ Θ₂`, whose interior is the inner frame's own
              (`merged-interior`) and whose conversion context the rule
              carries.
  INTERIOR    `V`, retyped EXACTLY where it was.
  CONVERSION  `unseal X′`.  Its representation IS the OUTER binder's —
              with the store there is no bind block to shift it past,
              which is the `idpush-name` equation of proof/IdLayer.agda
              in its store form.  Its ordinary spelling is the
              rule-carried `X′`.
  EXTERIOR    `C`, re-spelled into the merged conversion context.  The
              re-spelling exists because a conversion reading only ADDS
              names (`conversion-live`), so every name of the merged
              frame's OWN exterior survives into it.
```

The local `where` block names, in order: the binder `Y` names and the
exterior type it represents; `Y`'s own representation payload, which IS
that same type read on the outer conversion context — inverted out of
the redex's own `conv-unseal`, since the rule no longer carries the
lookup; `X`'s representation, which IS `Y`'s (`idpush-name`, with no
bind block to cross); and the re-spelled exterior type with the
conversion it lets us mint.

### §3 — `preserve-CancelR`

WHAT THE 2026-09-19 REPAIR BOUGHT.  The old rule re-spelled the inner
layer's identity type FROM the OUTER conversion context and so asserted
that `A′` denotes the SAME representation as `A`, where the inner
`env`'s bind-prefix comparison demanded a shift of it (history: the
premise was `SameTyExt (numBinds Θ₁)`).  That was refuted at a
reachable redex (`notes/CancelRShiftWall.agda`,
`notes/CancelRReachabilityWitness.agda`).  The repaired premise reads
the cancelled `seal X`'s OWN source `Aᵢ` at Θ₁'s conversion context
`Δ₁ᶜ`.

WITH THE STORE the two readings that had to be reconciled are the SAME
reading: there is no bind block, so the shift the old proof had to
recover (`∋ʳ-push`, `eqRB`) is the identity, and the cancelled binder's
representation variable IS the outer binder's.  The premise is still
read at `Δ₁ᶜ` — a different NAME MAP, which is what `_⊢_≈_⊣_` is for —
so the rule is unchanged; only its proof shrinks.

THE PROOF IS `preserve-IdPush`'s.  It diverges only in the conversion:
`IdPush` mints `unseal X′`, whose SOURCE is a variable and whose TARGET
is a LOOKUP; `CancelR` mints `mkId A′`, whose source and target are the
SAME type, so ONE type must satisfy both premises of the `env` — and the
two meet because the representation the seal's source names at `Δ₁ᶜ` is
the outer binder's payload.

## proof/IdLayer.agda

THE ID-LAYER FACTS — what makes `IdPush` and `CancelR` legitimate.

```
  §1  the pushed name is ALREADY WRITTEN in the inner `id (` X)`
      conversion (`idpush-name`), and the same argument fixes
      `CancelR`'s two names (`cancel-name`): typing forces X and Y to
      name ONE representation variable.  Neither rule invents a
      variable, and neither needs an equation as a premise.
  §2  `unseal` is the ONLY active conversion an id-(` X) layer can ever
      meet, so the id-base branch of `Active` is vacuous for these
      rules.
  §3  the naked drop `V ⟪ Θ , id A ⟫ -→ V` — the door, closed: it is
      sound exactly when the boundary changes NO FRAME.
```

### What the two universes change (2026-09-19)

§1 used to be an EQUATION between ordinary de Bruijn indices,
`X ≡ numBinds Θ₁ + Y`, because one universe carried both roles and
`shiftBy` moved a name.  Here the two conversions are read on DIFFERENT
name maps that can reorder relative to each other, so no equation
between `X` and `Y` is available or wanted: the fact is one universe
up, about the REPRESENTATION VARIABLE each name denotes.  That is the
form `proof/MoveScope.preserve-IdPush` consumes.

### What the store changes (2026-09-22)

The two names denote the SAME representation variable, not one
`numBinds Θ₁` above the other: a boundary scope carries no bind block,
so there is no prefix between the inner conversion context and the
outer one.  `push-rep` therefore lost its depth argument and its
`shiftRep` bookkeeping, and both `env` comparisons it reads are the one
relation `_⊢_≈_⊣_` at equal depth.

WHAT WAS DELETED.  `convCtx-unbind` — "a conceal is invisible to the
conversion context" as an EQUALITY between computed contexts — has no
two-universe counterpart.  The relational statement of the same fact is
`conv-unbind` itself (`Boundary.agda` §3), which skips an unbind outright.

### §1 — the names are forced

`push-rep` is the heart of both cases, on the two `env` premises alone.
The inner boundary's exterior type `B` is read at the OUTER interior;
its own conversion spells it `` ` X `` and the outer conversion spells
it `` ` Y ``.  Since the store experiment there is no bind prefix
between the two readings, so the two names denote the SAME
representation variable.

Stated on NAME MAPS: like `_⊢_≈_⊣_` itself, the judgement reaches a
context only through the `names` projection, which does not determine
it, so the contexts are not inferable from the two premises.

`idpush-name`: in any typed id-layer under an `unseal`, the inner
`id (` X)`'s variable NAMES the pushed conversion's binder.  `IdPush`
therefore invents no representation variable.  `cancel-name` is THE
SAME FACT FOR CANCEL: the inner `seal X` has the same TARGET spelling
`` ` X ``, so the same two premises settle it, and `CancelR` needs no
premise relating its two names either.

### §2 — the only active conversion an id-layer meets is `unseal`

`same-base-source`: a base ordinary type denotes a base representation
type.

`outer-id-base-untypeable`: a wrapper whose conversion is `id (` X)`
has a VARIABLE exterior type, and an outer `id A` conversion at a BASE
type demands a base interior.  So the id-base branch of `Active` is
unreachable over this left-hand side.

The argument runs through the representation universe: the outer `id A`
forces the inner boundary's exterior type to be a base type, and
`≈-base-target` (`proof/Canonical.agda`) carries a base type to a base
type across the exterior comparison — but the inner conversion's target
is a variable.

A boundary can never conceal the name its OWN conversion cites —
`value-var-visible` (`Terms.agda`) says a value's variable type is
visible on the value's exterior context, because `env`'s last conjunct
checks it there.  So "Θ₁ unbinds `Y` while the conversion cites `Y`" is
untypeable.

### §3 — the naked drop

`V ⟪ Θ , id A ⟫ -→ V` is UNSOUND, because `V` is typed on the boundary
scope's INTERIOR, not on `Δ`.  A concrete failing instance
(`naked-drop-trap`): the boundary's conversion cites an ordinary name
that `Δ` does not have at all.

§3b, the sound side condition: the drop is sound exactly when the
boundary changes NO FRAME.  Then both induced contexts are the exterior
itself and the identity conversion fixes the type, so the interior
derivation IS the exterior one (`drop-empty-frame`).

## proof/Progress.agda

PROGRESS for the two-universe conversion-boundary calculus.

The ordinary cases are the standard induction, using
`proof/Canonical.agda`.  Boundary reductions additionally construct the
relational context readings and re-spellings carried by the new rules.
`Peel`'s package is proved in `Boundary.agda` / `Conversion.agda`.

PROGRESS RETURNS THE STORE CHANGE TOO.  A step is `Δ ⊢ M -→ M′ ∣ δ`, so
every clause names the `δ` its rule makes: `new R` for the three
∀-eliminations, `none` everywhere else, and the congruences pass up
whatever the premise returned while shifting the sibling by `↑ᴹ[ δ ]`.

The 2026-09-20 repair of `TyPeelR-⟪⟫` (today `Nu-⟪⟫`) added NO
parameter.  Its moved
boundary's conversion reading and the retention that names the moved
spelling are PROVED here as `addUnbind0-reading`, from the unbind-skipping
transport `Boundary.snoc-unbind0-conversion-ren`.

### §2 — the boundary reading packages

`MergedReading` — the conversion reading of `Θ₁ ++ Θ₂` retains the
source whose spelling both id-layer rules move into that merged frame:

* repaired `CancelR` (2026-09-19) moves the cancelled seal's source,
  read at Θ₁'s conversion context;
* `IdPush` moves a variable read at the same context.

`_⊆ᵃ_` states only NAME AVAILABILITY; `Conversion.respell-ty` then
constructs the `_⊢_≈_⊣_` premise at the exact type being moved.  The
statement retains the INNER conversion context only: both rules read
the spelling they move at that context, so the former outer-retention
component had no consumer.  Since the store experiment it is read over
`Δ` ITSELF — Θ₂ has no binds to push first.  It is proved here from
`Boundary.merged-conversion-exists`, which is what made progress
unconditional on 2026-09-21.

`addUnbind0-reading` — THE MOVED BOUNDARY'S OWN READING (2026-09-20, the
repair's progress obligation).  The repaired `Nu-⟪⟫` carries the
moved boundary's conversion reading and a `SameConv` pinning the moved
spelling, so progress must CONSTRUCT that reading.  It is not a new
assumption: the unbind-skipping transport `conv-weaken` / `conv-snoc-unbind`
and the representation renaming are assembled by
`Boundary.snoc-unbind0-conversion-ren`, and all this wrapper adds is the
`RepWk suc` witness for the cell `inst Θ` mints, read off
`inst-boundarywf`.

THE RENAMING IS THE WHOLE POINT.  The retained names are
`map suc (names Δ′ᶜ)`, NOT `names Δ′ᶜ`: the allocation moves every
representation index the old conversion context named up by one.  The
unrenamed inclusion is FALSE, and §6b of `Examples.agda` is the
witness.

### §4 — the boundary cases of the induction

* `progress-unseal`: an active `unseal` sees a value at a variable
  type.  `canon-var` exposes either `CancelR`'s or `IdPush`'s inner
  layer; the two `BoundaryWf` witnesses then feed the proved
  merged-reading theorem.
* `progress-env`: once the interior is a value, conversion
  classification decides whether the whole boundary is a value or one
  of the four active redex shapes.
* `progress-peel`: a function-conversion wrapper carries its own
  `BoundaryWf` and the domain conversion typing needed by the core
  `peel-premises-env` theorem.
* `progress-ν-∀conv`: a `ν` over a `∀`-conversion wrapper; the outer
  conversion's `_⊢_≈_⊣_` premise exposes the interior `∀` body and is
  exactly `Nu-⟪⟫`'s re-spelling premise.  At a `Λ` interior it is
  `Nu-⟪Λ⟫`, otherwise `nu-⟪⟫`.
* `nu-⟪⟫` — THE MOVED READING IS REPRESENTATION-SHIFTED FIRST.
  `readable` reads the old conversion at `underΛ Δ′ᶜ`; the rule wants
  it at `underΛ (renNameCtx suc Δ″ᶜ Δ′ᶜ)`, whose name map is
  `map suc (names Δ′ᶜ)` — the SIBLING SHIFT, with no bind-block offset
  to compute since the store experiment.  So the reading is transported
  along the representation renaming the allocation makes (`sameᶜ-ren`,
  past the `Λ` by `names-underΛ-ren`), and only THEN respelled into the
  moved boundary's own context by the retention `addUnbind0-reading`
  supplies.  Doing the respell first — the 2026-09-20 dead end — leaves
  the reading in the unrenamed map.
* the `Λ` case is immediate: the value restriction means `⊢Λ` hands us
  the body's value proof.

## proof/TypeSafety.agda

TYPE SAFETY: the composition of progress and preservation along a run.
Both component theorems are unconditional — preservation since
2026-09-20, and progress since 2026-09-21, when the last parameter
`MergedReading` was proved.  The public statement lives in
`TypeSafety.agda`.

SINCE THE STORE (2026-09-22) THE RUN MOVES THE CONTEXT.  Every step
returns the change it made, so the state a run reaches is typed at
`runCtx r`, not at `Δ`, and progress is applied THERE.

The `WfCtx Δ` premise is preservation's (see `notes/DECISIONS.md`,
2026-09-18): progress needs none, but safety RETYPES every state the
run reaches, and retyping is what a duplicate name map breaks.  The
theorem: a well-typed closed term at a well-formed context, after any
number of steps, is a value or can step again — it never gets stuck.

## proof/Residual.agda

SOUNDNESS OF THE RESIDUAL LAYER (`Residual.agda`): a residual names a
position IN THE CONTRACTUM — `plug D N` is the step's target and
`plug C M` its source.  These are the sanity lemmas for the statement
of color preservation; the theorem itself is
`proof/ColorPreservation.agda`, after Jeremy's review of the statement.

* `plug-renCtxᴿ`: renaming through a context is renaming the plugged
  term.  Since the store there is only ONE renaming: the
  representation-only `renᴹᴿ`.
* `plug-↑`: the SIBLING SHIFT through a context — the three halves of
  `↑ᴹ[ δ ]` (`Residual.agda` §3) rebuild exactly the shifted term.
* `substᵐ-ivar`: a pointwise-identity substitution is the identity.
* `plug-substCtx`: substituting through a context is substituting the
  plugged term.  At a boundary frame the frame is TERM-CLOSED, so the
  substitution neither enters the frame nor reaches the hole and both
  sides are the original plug.
* `image-sound`'s `Λ` case: `crossΛᴹ` is written with the paired
  renaming, whose ordinary half is the identity; `renᴹ²-ord-id` is what
  identifies it with `renᴹᴿ suc`.

## proof/ColorPreservation.agda

COLOR PRESERVATION — the proof (statement approved by Jeremy,
2026-09-21; `ColorPreservation.agda` states it publicly).

### The shape

`residual-frame` is the PER-STEP theorem: from the source position's
frame derivation it CONSTRUCTS the target position's, at the context
`apply δ Δ` the step's store change left, with the scope-map equation
`names Δ₂ ≡ map ρ (names Δ₁)`.

Every rule but the movers is frame-for-frame — the interior lemmas of
`Boundary.agda` §3a supply the new boundary frames' readings
(`inst-interior`, `liftᴮ-interior`, `dual-interior`,
`merged-interior`).  The movers — `Nu-⟪⟫`'s inner boundary, the
siblings an allocating congruence shifts, and `Beta`'s copies under
`crossΛᴹ` — go through `⊢C-ren`, the transport of a frame derivation
along a representation-only renaming, whose boundary case is
`interior-ren` / `RepWk` (`Boundary.agda` §3d) and whose conclusion is
exactly the `holeᴿ` the residual's ρ index records.

`residuals-color` composes the per-step equations along `ρ′ ∘ ρ`,
re-typing each intermediate term by `preservation` and carrying its
context's well-formedness by `preservation-wf` — which is where the
theorem's `WfCtx Δ` premise is spent.

### What the store changed (experiment 2, 2026-09-22)

`Peel`'s argument no longer crosses a bind block — `dual-interior`
lands it at the exterior itself — so `repwk-wkN` / `wkN-+` are gone
from this proof, and with them the last use of the typing premise
inside `residual-frame`: what the per-step theorem needs now is the
AMBIENT's well-formedness, because the sibling shift is `repwk-alloc`
at the allocated payload (`same-wfᴿ`, `step-alloc`).  The three
`Alloc`-indexed transports `⊢C-shift`, `interior-apply` and `⊢C-len`
are the whole store bookkeeping.

### The section map

* §1 map bookkeeping.  `map-suc-ext`: renaming and the `Λ` shift
  commute on a name map.
* §2 the frame judgement ignores the representation STORE beyond its
  LENGTH: the refinement `abstR → bindR R` of a slot (`Nu-Λ`'s,
  `Nu-⟪Λ⟫`'s) transports every `⊢C` derivation, names untouched.
* §3 the frame judgement is functional.
* §4 `Beta`'s substitution never moves a frame: boundary frames are
  term-closed and every other frame ignores its side terms.
* §5 the dual `crossΛᴹ` mints has a reading at EVERY context: it unbinds
  exactly the fresh name the `Λ` added, and slot 0 is fresh in the
  shifted remainder.
* §6 THE TRANSPORT (`⊢C-ren`): a frame derivation moves along a
  representation-only renaming, and the hole's scope map moves by
  exactly the renaming `holeᴿ` delivers there.  The boundary case is
  `interior-ren`, and since the store it runs at the SAME ρ — there is
  no bind block to step past.
* §6a THE STORE CHANGE, on a frame derivation and on a reading.  A step
  that allocates moves every position by the sibling shift; a step that
  does not moves nothing at all, ON THE NOSE.
* §7 the copies: `Beta`'s argument, followed to each occurrence.  The
  ambient at depth `k` is `underΛᵏ k` of the redex's, and each `Λ`
  crossed contributes one `crossΛ-interior` frame and one `suc`
  transport — which is exactly the `holeᴿ suc D ∘ ρ` the residual's
  index composes.
* §8 THE PER-STEP THEOREM.  The ambient's well-formedness is spent only
  where an allocation's payload must be known well formed
  (`step-alloc`, `same-wfᴿ`).  Two cases worth naming: the `Peel`
  argument moves VERBATIM — `dual-interior` says the dual's interior IS
  the exterior the argument was already read at — and `Nu-⟪⟫`'s
  inner boundary is the one mover left inside a redex, a SIBLING of the
  `Λ` slot the allocation consumes, so it takes exactly `suc`.
* §9 THE THEOREM: compose the per-step equations along the run,
  re-typing each contractum by preservation and carrying its context's
  well-formedness by `preservation-wf`.  The run's target position is
  read at `runCtx rs`, the context the run ends at.
* §10 THE COLOR THEOREM proper (Jeremy, 2026-09-21): color is about
  TYPE variables only — which ordinary names are live at the hole — not
  the representation variables they denote.  `map ρ` moves only the
  entries, never a position, so the corollary is the length equation.

## proof/Adversary.agda

THE SOUNDNESS GATE, and the adversaries of the previous design,
refuted.

A CONCEAL MUST CITE A REPRESENTED BINDER.  That is the whole gate, and
it is a one-line inversion: `conv-seal` has no other premise.  Under
the design before the representation-variable split the same fact
needed `mwf↓` + `Reversal≈`, or `mwf↓x` + `starOnly` + `SkelEq`, and
the adversary passed `≡`, `≈Δ̄` and `SkelEq` (only `starOnly` refused
it).

### What the two universes change

`Δ ∋ X := A` is now a SQUARE (`Ctx.agda` §5): ordinary name `X` names a
representation variable α, α carries a `bindR R`, and `A` is `R` read
back through the current ordinary name map.  The gate therefore refuses
a seal for TWO INDEPENDENT REASONS — the name may be absent from the
map (§2b), or the representation variable it names may be `abstR` (§2).
Neither can be repaired by a change list: an `unbind` deletes a name and
a `bind` restores one, and NO change rewrites a representation
binding.

WHAT WAS DELETED (2026-09-19).  The masking half of this module —
`bind-claims-a-unbind` and `bind-mentions-no-rep`, statements about
`∋lk`, `Nameable` and `applyChanges` — has no two-universe
counterpart: a bind no longer clears a bit at a retained entry, it
INSERTS a name, and what it claims is `Ξ ∋ʳ α` plus freshness, which is
already the rule's own premise (`step-bind`, `Boundary.agda` §2).

### §1 — the gate

`seal-cites-representation`, spelled out: the cited ordinary name is
LIVE, the representation variable it names is REPRESENTED, and the
seal's source type is that representation read on the conversion
context.  No other premise exists.

### §2 — the adversary (the old `⊢3n-adv`)

At a type context where ordinary name 0 names an ABSTRACT
representation variable — `Λ`-bound, no payload — the adversary
exported `7 : ℕ` at the abstract type.  Here the boundary is
UNMINTABLE, because `seal 0` demands `Δadv ∋ 0 := A`, whose middle
component asks `abstR` to be a `bindR`.

`Θadv` is the boundary scope the adversary used to hide behind: it
unbinds the very name its conversion cites.  A conversion context SKIPS a
unbind, so the unbind buys nothing — the seal is still read where the slot
is abstract.

### §2b — the second gate, new on this branch

A conceal at a UNBOUND name.  The old design kept an unbound slot's entry
and marked it; here an unbind DELETES the ordinary name.  A seal at a name
the interior lost is therefore refused by the NAME half of the square
rather than by the representation half — and this is the reading that
replaces `∋lk`.

### §3 — `bad`: two spellings of one fact, inexpressible

An inner conceal at representation `ℕ` under a binder whose
representation is `∀Z.Z→Z`.  The two spellings cannot disagree, because
there is only ONE: `seal 0` reads the binder, so the source type IS the
binder's representation, read back through the name map.

The stored payload, looked up, is `∀ZZ` again: `⇑ᵗ` moves only the FREE
representation occurrences, and `∀ZZ` has none; and `∀ZZ` has exactly
one ordinary reading on `names Δbad`.  The adversary's term is `7`
behind that conceal, presented at `` ` 0 ``.  It is refused by the
seal's SOURCE type alone: `env` makes the boundary's interior type and
the conversion's source two spellings of one representation, and
`7 : ℕ` cannot spell `∀Z.Z→Z`.

### §4 — cancel's type equation

At a cancel the inner conceal's SOURCE type and the outer reveal's
TARGET type are the SAME lookup square on the SAME conversion context,
hence equal — once the name map is a function, which is exactly what
`WfCtx.name-fn` says and what every `BoundaryWf` supplies.  This one
lemma replaces `cancel-agree` + `Reversal≈` + `SkelEq` + `xrep-stored`
+ `MergeOK`'s two type equations.

## proof/Canonicity.agda

THE CANONICITY INVARIANT — the BINDER-NAME reading.

Every conversion that reduction ever writes on a wrapper is a member of
the CANONICAL FAMILY: it is a subtree, a re-spelling, or a mint of
`reveal X B`, `conceal X B`, `mkId A`, or `unseal X`.  This file states
that family as an inductive predicate, proves the four closure facts
the rules need (MINT / DECOMPOSE / RENAME / RE-SPELL), lifts it to
terms, and proves it PRESERVED BY REDUCTION (`canon-step`) —
UNCONDITIONALLY since 2026-09-24: before `ν`, `canon-step` and
`canon-steps` took the hypothesis `CanonTyPeelR`, which is refuted, and
the `Nu` rules removed the one mint that needed it.

### What the family says

It used to say two things at once: a POLARITY SHAPE (`unseal` leaves
covariant, `seal` leaves contravariant) and a NAME (every non-identity
leaf cites the SAME binder `X`, shifted under each `` `∀ `` exactly as
`reveal`/`conceal` shift it).  The first half was a restatement of what
the indexed typing judgement already forced, and it went with the index
(Jeremy's ruling, § Conversion.agda / NO POLARITY): a mixed tree like
`seal 0 ↦ seal 1` is now perfectly typeable, and the retired
`TyPeelR`'s contractum WAS one.  The SECOND half is the content that survives, and it is what
`CanonAt X c` states.

### What the two universes add (2026-09-19)

`Peel` no longer carries its crossing argument's conversion `s` onto
the dual: the dual's conversion context is a DIFFERENT name map, so the
rule carries the dual's own spelling `s′` with a `SameConv` relating
the two (§ Reduction.agda / Peel).  Canonicity must therefore RE-SPELL,
and that is §5.  The family is stated a second time one universe up —
`CanonAtᴿ`, on REPRESENTATION variables — `SameConv` transports it down
and back, and the way back needs the target name map to be a FUNCTION.
So `canon-step` takes `Unique (names Δ)`, for the same reason `det`
takes a typing derivation (`notes/DECISIONS.md`, 2026-09-18):
uniqueness is a property of the context, not a premise of a rule.
Every other rule's mint is a subtree, a `mkId`, or an `unseal` at a
name the rule already carries.

The re-spelling needs one more distinction the one-universe design did
not: a conversion all of whose leaves are identities (`AllId`) names no
binder at all, so it is canonical at EVERY name and its re-spelling has
no name to inherit.  Both transports therefore return a SUM.

The term-level invariant (`CanonC`) quantifies the name existentially,
because a term's wrappers name different binders.

### §1 — the canonical family

`CanonAt X c` — every non-identity leaf of `c` cites the binder `X`.  A
`` `∀ `` pushes a binder in front of the leaves, so the name it tracks
is `suc X`, which is precisely the shift `reveal`/`conceal` perform on
the `` `∀ `` case.

`CanonC` is the term-level reading: a wrapper's conversion cites SOME
single binder.  It has to be existential, and single-name is what the
`Nu` rules' STACKING keeps true: the retired `TyPeelR`'s minted
conversion `instReveal 0 s` read TWO binders in one wrapper — the
conversion's own, and the one the instantiation just bound at slot 0 —
which is exactly what `¬CanonTyPeelR` (§8) records.  The `Nu` rules put
the two in two different wrappers.

`AllId` — the name-free members of the family: every leaf is an
identity.  These are canonical at every name, and they are the ones a
re-spelling cannot read a name off.

### §2 — MINT

(a) `reveal`/`conceal` — the conversion the compiler writes into a `ν`
and `Nu-⟪⟫` writes into the one it pushes — by mutual induction on the
type it is minted from — the same recursion `reveal`/`conceal` are defined
by.  (b) `allId-mkId`: the identity at an arbitrary type — `CancelR`'s
and `IdPush`'s residue — is the name-free half of the family.
`canonC-unseal` is `IdPush`'s other mint: the pushed `unseal` at the
name the rule carries.

### §3 — DECOMPOSE

`Peel` reads `s ↦ t` apart; the DOMAIN comes back at the SAME binder,
and is then re-spelled onto the dual's name map (§5).

`Nu-⟪Λ⟫`/`Nu-⟪⟫` read `∀ s` apart and move the body `s` VERBATIM into
the middle layer (`canonC-all`): the decomposition only walks the name
past the binder.  (The retired `TyPeelR` then MINTED on the body,
`instReveal 0`, which is where the two-binder trees came from.)

### §4 — RENAME

`renᴹ²` (hence the representation-only renamings `Peel` and
`Nu-⟪⟫` perform) renames the conversions it passes with its
ORDINARY component.  The name moves with that renaming.

### §5 — RE-SPELL

THE FAMILY ONE UNIVERSE UP.  A representation-universe conversion is
canonical at a REPRESENTATION VARIABLE.  `_⊩_~_` shifts that variable
under a `` `∀ `` exactly as `CanonAt` shifts the ordinary name, because
its `` `∀ `` clause reads the body at `zero ∷ shiftReps η`.

* DOWN (`canon-rep`): a conversion canonical at the ordinary name `X`
  denotes a representation conversion canonical at the representation
  variable `X` names — unless it names nothing at all.
* UP (`canon-name`): on a name map that is a FUNCTION, a representation
  conversion canonical at α has only one ordinary reading, so its
  spelling cites one name throughout.
* THE RE-SPELLING (`canonC-respell`): `Peel` carries
  `SameConv Δᵈ s′ Δᶜ s`; the `Unique` its first context needs is
  `dual-unique` at the rule's own two readings.

### §6 — lifting to terms

`CanonTm M` — every wrapper in `M` carries a canonical conversion.
Structural, with no condition on the boundary scopes: canonicity is a
property of CONVERSIONS.  Renaming a term renames its conversions with
the renaming's ORDINARY component (§4 covers them); a
representation-only renaming leaves every conversion name where it was.

### §7 — term substitution

Boundaries are TERM-CLOSED: `shiftᵐ` and `substᵐ` return a wrapper
untouched (`TermSubst.agda`).  So no conversion is ever renamed by term
substitution, and canonicity is preserved for free — the only wrappers
in the result are those already in `N`, those carried in by σ, and THE
DUAL WRAPPER FRAME-EXACT BETA MINTS AT EACH CROSSED `Λ`, whose
conversion is `mkId`, the name-free half of the family (`allId-mkId`).

Term-variable renaming touches no conversion (a wrapper is
term-closed), so canonicity passes through `renⁿ` unconditionally.  A
variable image is canonical outright; a VALUE image is closed, so the
term-variable weakening leaves it alone.  THE `Λ` CROSSING (`canon-⇑ᴵ`):
a value image acquires the DUAL WRAPPER, whose conversion is
`mkId (⇑ᵗ A)` — name-free, hence canonical at every name — over the
value weakened in the REPRESENTATION universe only (§6).

### §8 — the invariant, rule by rule

```
  Nu-Λ     moves `ν`'s own conversion onto the new boundary — `ct-ν`
           already made it canonical, and a compiled `ν`'s is
           `reveal 0 C` (§9).
  Beta     substitutes — §7, wrappers are opaque to `substᵐ`.
  Peel     DECOMPOSES `s ↦ t` and RE-SPELLS the domain onto the dual's
           name map (§5); the argument is moved verbatim, which
           touches no conversion name.
  Nu-⟪Λ⟫ / Nu-⟪⟫
           both DECOMPOSE `∀ s` and move the body VERBATIM into the
           middle layer; `ν`'s own conversion is the outer layer.  The
           Λ clause moves nothing; the wrapper clause renames the moved
           boundary, appends an unbind to its frame and RE-SPELLS its
           `∀ s′` as `∀ s″` (§5, at the moved boundary's own reading),
           and its pushed `ν` MINTS `reveal 0 (⇑Bᵢ′)` (§2).  All
           unconditional: no conversion cites two binders.
  CancelR  MINTS `mkId A′` and `mkId A` — name-free leaves of the family.
  IdPush   MINTS BOTH conversions: the pushed `unseal X′` (binder X′,
           which the rule carries) and the residue `mkId A`.
  Drop$ / Drop-true / Drop-false
           contract to a literal; no wrappers at all.
  ξ-*      structural; `ξ-⟪⟫` transports `Unique` through
           `interior-unique`, and the `Nu-⟪⟫` case uses
           `unique-shift` before `interior-unique`.
```

WHAT THE RETIRED `TyPeelR`'S MINT OWED THE FAMILY, as a statement,
kept as the record of the wall: `CanonTyPeelR`.
IT FAILS on the `∀` conversion `` `∀ (id (` 0) ↦ seal 1) `` — a
polymorphic ARGUMENT that crossed a `Peel`, `conceal 0 (∀Y. Y ⇒ X)`.
That conversion cites the ONE binder `X` (slot 1 under the `` `∀ ``),
but its mint `seal 0 ↦ seal 1` cites TWO: the binder `TyPeelR` just
bound at slot 0 and the crossed boundary's at slot 1.  The mint TYPED
(it was `preserve-TyPeelR-Λ`'s case; the tree was untypeable only under
the retired polarity index) — it is the SINGLE-BINDER reading that it
left.  Under the `Nu` rules the same crossing stacks
`⟪ …, id (` 0) ↦ seal 1 ⟫` under `ν`'s own `⟪ inst [] , c ⟫`: two
wrappers, one binder each.

### §9 — sources

Compilation from plain System F (`Compile.agda`) introduces no
boundary at all, and every `ν` it writes carries `reveal 0 B`, which §2
puts in the family: every wrapper in a reachable term was minted by a
reduction step or is a `ν`'s reveal, so §8 is the whole story.  Stated
for the record (`Plain`, with `pl-ν`; `canon-source`).

### §10 — the mint lemmas, on the ground

The compiler's `reveal` at a function type is the `↦`-tree whose domain
is the DUAL family.  The wrapper frame-exact `Beta` mints at a crossed
`Λ` is name-free.  And a TWO-BINDER tree — `seal` leaves at two
different names — is outside the family, though (unlike under the
retired polarity index) it is perfectly TYPEABLE: it is what the
retired `TyPeelR` minted, and the FRAMES, not a global index, are what
keep the two binders apart — which is what the `Nu` rules' stacking
does.

### Retired

* "the old §10 validated the invariant on the regression corpus; it is
  dropped while `strong-rep-nu.Examples` is unported on this branch"
  — `Examples.agda` landed on 2026-09-21 and is gated by `All.agda`;
  the corpus validation has not been restored, so the note said
  something that is no longer true of the branch.  The ground-level
  mint checks it sat beside are the current §10.
* "`ξ-Λ` and `ξ-⟪⟫` transport `Unique`" — there is no `ξ-Λ`; the live
  transports are as listed in §8 above.

## proof/ShiftAudit.agda

THE SHIFT AUDIT — every place a rule MOVES A SUBTERM, checked against
FRAME EXACTNESS (Jeremy, 2026-09-08: "frame exactness is the main point
of Strong System F").

### The criterion

Whenever a rule moves a subterm to a new position, the subterm's TYPE
CONTEXT at the new position must be EXACTLY its context at the old
position, up to

* (i) the movement past the binders it CROSSED, and
* (ii) refinement `abstR → bindR R` of a representation variable it
  could ALREADY name (the `Nu` rules' cell, which `ν`'s conversion
  reveals).

Any variable the subterm COULD NOT name before and CAN name after is a
FRAME LEAK, even when the subterm's shifted indices cannot reach it:
the frame must SAY THE TRUTH about what the subterm may name.

### What the two universes changed (2026-09-19)

The frame identities stopped being EQUATIONS BETWEEN COMPUTED CONTEXTS.
There is no `interior Θ Δ` to write an equation about: a boundary scope
RELATES an exterior to an interior, and the audit's per-site facts are
exactly the transport lemmas of `Boundary.agda` §3a — `dual-interior`
for `Peel`, `merged-interior` for `CancelR` and `IdPush`.  So §2 and §6
CITE them rather than restating them.

### What the store changed (2026-09-22), and why most of the file is shorter

A boundary scope carries no bind block, so THERE ARE NO BINDS TO MOVE A
SUBTERM PAST, and the audit's central question — "does the moved
subterm's frame gain a slot it could not name?" — becomes vacuous at
every site but one.

* `Peel` no longer renames its argument at all (§2).  The old
  obligations `Peel-move-ordinary`, `Peel-move-represent`,
  `Peel-frame-names` and `Peel-dual-numBinds` were about the bind block
  the dual's interior used to carry; the dual's interior is now the
  exterior ITSELF, so they are retired.
* `TyPeelR-⟪⟫` (today `Nu-⟪⟫`) moves its boundary by the UNIFORM
  SIBLING SHIFT `renᴹᴿ suc` (§3), not by an `extN (numBinds Θ′) suc`
  computed from the crossed scope; the old `TyPeelR-⟪⟫-move-ordinary`
  survives, as `Nu-⟪⟫-move-ordinary` and `Nu-⟪⟫-move-conversion`, in
  the form that still says something — a representation renaming leaves
  every ordinary annotation and every conversion in place.
* `CancelR` / `IdPush` (§6) keep both frame identities, now stated at
  the plain exterior.  `Move-outer-numBinds` / `Move-inner-numBinds`
  are retired with `numBinds`.

WHAT THE STORE ADDED is §8: the congruences now SHIFT THE REDEX'S
SIBLINGS, and the shift has to be exactly the move the context makes.
That is the one new frame-exactness obligation of the experiment, and
it holds definitionally at both `Alloc`s.

### The section map

```
  §1  the site table
  §2  Peel                    — EXACT, by `dual-interior`; NO shift
  §3  the three Nu rules     — Nu-Λ and Nu-⟪Λ⟫ shift nothing; Nu-⟪⟫
      is the sibling shift plus one appended unbind
  §4  TERMINATION — the tower measure, and why the rejected repair
      (wrap the moved value in the new binder's dual) stalls on it
  §5  Beta                    — the `ƛ` and `Λ` crossings do not interfere
  §6  CancelR / IdPush        — exact, inner AND outer
  §7  Drop$ / Drop-true / Drop-false — vacuous
  §8  the ξ rules             — the sibling shift IS the context move
  §9  dead shift machinery
```

The verdicts are the module itself.  `notes/ShiftAudit.md` is the
ARCHIVED 2026-09-08 audit, written against the bind-block calculus: read
it for the leak's diagnosis and the four rejected repairs, never for a
verdict on the live rules.

### §1 — the sites

Every place in the live development where a TERM is renamed, shifted or
substituted (`grep renᴹ² renᴹᴿ wkᴹ ⇑ᴹ renⁿ shiftᵐ crossΛᴹ substᵐ`):

```
  RULES that move a subterm
    Peel        `W`, verbatim, inside the frame
                `⟪ dual Θ , s′ ⟫`                        §2  EXACT
    Nu-⟪Λ⟫      `(N ⟪ liftᴮ Θ , s ⟫) ⟪ inst [] , c ⟫`       §3  refinement
    Nu-⟪⟫       `renᴹᴿ suc` on the moved boundary, plus
                `++ (unbind 0 0 ∷ [])` on its change list   §3  EXACT
    Nu-Λ        `N ⟪ inst [] , c ⟫`                       §3  refinement
    Beta        `N [ W ∶ A ]ᵐ`, i.e. `substᵐ`/`crossΛᴹ`   §5  EXACT
    CancelR     `V ⟪ Θ₁ ++ Θ₂ , mkId A′ ⟫`                §6  EXACT
    IdPush      `V ⟪ Θ₁ ++ Θ₂ , unseal X′ ⟫`               §6  EXACT
    Drop$ / Drop-true / Drop-false                        §7  vacuous
    ξ-*         the SIBLINGS move, by `↑ᴹ[ δ ]`           §8  EXACT

  TRANSPORTS, not rules (no term is moved by a reduction; these are the
  lemmas the cases above are PROVED with, and each one's renaming or
  reading argument is supplied at the site):
    `⊢renᴿ`, `renᴹ²`, `renⁿ`, `⊢renⁿ`, `⊢weakenⁿ`,
    `canon-renᴹ²`/`canon-renⁿ` (proof/Canonicity.agda).
```

### §2 — `Peel`

The crossing argument's frame is the EXTERIOR ITSELF.  `W`'s frame,
before: `Δ`.  After: the dual's interior, which `dual-interior` says is
`Δ` — NOT ONE ORDINARY NAME AND NOT ONE REPRESENTATION BINDER ADDED OR
REMOVED.  Criterion (i) with nothing to cross: EXACT, and the rule
carries `W` verbatim.  `Peel-no-alloc`: and `Peel` allocates nothing,
so its siblings do not move either.

### §3 — the three `Nu` rules

`Nu-Λ` MOVES NOTHING.  `N` already lives one `abstR` binder in
(`⊢Λ`), and the allocation REFINES that binder to `bindR R` in place
while `inst []` gives it ordinary name 0 (`Nu-Λ-restores-name-0`).  So
the frame move is criterion (ii) and there is no renaming at all — the
contractum mentions no `renᴹᴿ`.

`Nu-⟪Λ⟫` IS THE SAME REFINEMENT ONE BOUNDARY IN, with the two layers
STACKED: the outer `inst []` restores name 0, and the middle `liftᴮ Θ`
is the crossed frame read under it.  Read inside out they are exactly
the fused `inst Θ` the retired `TyPeelR-Λ` wrote —
`Nu-⟪Λ⟫-stacks-to-inst : inst Θ ≡ liftᴮ Θ ++ inst []`, by `refl` — so
`N`'s frame is the one it had under `TyPeelR-Λ`, and criterion (ii)
again.  The crossed conversion moves verbatim and is read at the middle
layer's conversion context, which is the crossed one refined.

THE WRAPPER CLAUSE, `Nu-⟪⟫`.  The moved boundary crosses ONE freshly
allocated cell and ONE fresh ordinary name for it, and its appended
`unbind 0 0` DELETES that ordinary name again.  So the move is the
plain SIBLING SHIFT — representation-only, `renᴹᴿ suc` — and the moved
boundary's ordinary indices keep their positions.  That is the whole of
the 2026-09-08 repair, restated in the universe that now carries it.  A
`ν` the shift passes keeps its type argument and conversion
(`Nu-⟪⟫-move-ordinary`), and so does a boundary
(`Nu-⟪⟫-move-conversion`): both are read on their own scope.

The appended unbind names ordinary position 0 and the cell the allocation
just minted, which is representation index 0 — and it is APPENDED, so
it acts FIRST (the change list is read head-last).  Since
`Boundary = List Change` the rule WRITES that snoc,
`Θ′ ++ (unbind 0 0 ∷ [])`, so there is nothing left to state: the old
`TyPeelR-⟪⟫-addUnbind0` was `refl` on one and the same list.

### §4 — termination, the tower measure

The wrapper clause's contractum contains

```
    ν (` 0) · (… ⟪ … ++ (unbind 0 0 ∷ []) , `∀ s″ ⟫) ⟨ reveal 0 (⇑Bᵢ′) ⟩
```

under its two stacked layers, which IS again a redex.  It is not a regress, and the measure says why:
the number of nested boundaries above the `Λ`.

* `towerHeight-renᴹᴿ`: no renaming changes it — which is what makes the
  measure usable at all, since both candidate repairs rename the moved
  value.  `towerHeight-↑ᴹ`: and neither does the sibling shift, at
  either `Alloc`.
* `Nu-⟪⟫-height`: THE MEASURE STRICTLY DECREASES.  The ∀-value the
  contractum's pushed `ν` instantiates is ONE BOUNDARY SHORTER than
  the one the redex's `ν` instantiated.
* `fixA-height-stalls`: THE REJECTED REPAIR STALLS AT THE SAME MEASURE.
  Fix (a) — wrap the moved value in the new binder's dual, with an
  identity conversion at the value's own type — puts the ∀-value under
  a FRESH boundary, so the height is the redex's height again: nothing
  is consumed.  THIS is the difference between (a) and the installed
  clause: `Nu-⟪⟫` CONSUMES a boundary that was already there, (a)
  MINTS a new one.
* `mkId-∀`: AND IT IS SELF-FEEDING.  An identity conversion at a `∀`
  type is NECESSARILY a `` `∀ `` conversion — `conv-id` wants a base
  type and `conv-idv` a variable, so `mkId` has no other spelling —
  hence the inserted layer is INERT `I-all`, hence the wrapped value
  sitting under a `ν` is ITSELF a `Nu-⟪Λ⟫`/`Nu-⟪⟫` redex.  Fix (a) does not
  converge: it inserts one layer per step, forever.
* `value-↑ᴹ`: values and inertness survive the renamings the rules
  perform, which is what makes fix (a)'s regress feed itself and what
  lets the installed clause fire again on its own contractum.
  (`inert-renᶜ`, `value-renᴹ²` and `value-renᴹᴿ` moved to
  `proof/TermSubst.agda` §2, where the typing-transport lemmas need
  them for `⊢Λ`'s value premise.)
* `canon-∀-height`: WHERE THE DESCENT STOPS.  A `∀`-value of tower
  height 0 is a `Λ` (`canon-∀` has no third shape), so once
  `Nu-⟪⟫` has consumed the tower it is `Nu-⟪Λ⟫` that fires —
  and `Nu-⟪Λ⟫` neither renames nor unbinds anything (§3).  So the run
  is `height − 1` wrapper steps then one `Λ` step, and never more.
* `progress-Λ-at-0` states that as the progress clause it decides,
  against the LIVE relation: at tower height 0 the step is
  `Nu-⟪Λ⟫`, which ALLOCATES the cell for the type argument's
  representation — the contractum is named, and so is the change.

### §5 — `Beta`, the two crossings do not interfere

THE `ƛ` CLAUSE.  A `ƛ` binds a TERM variable, so no type frame changes
and `shiftᴵ` must not touch the type side at all.  It does not: on a
value image it is the IDENTITY, which is correct because a value image
is TERM-CLOSED — and it stays term-closed, because `crossΛᴹ W A` is a
BOUNDARY and `env` types its interior at `Γ = []`.

`⇑ᴵ-shiftᴵ-comm`: the two crossings DO NOT INTERFERE (design law:
simultaneity).  Crossing a `ƛ` then a `Λ` is crossing a `Λ` then a `ƛ`,
on the nose, for EVERY image — which is what makes the two clauses of
`substᵐ` independent.

`Beta-Λ-crossing`: THE `Λ` CROSSING IS REP-ONLY, AND ITS UNBIND IS WHAT
MAKES IT SO.  A value image crossing a `Λ` is weakened in the
representation universe and wrapped in `(unbind 0 0 ∷ [])`, whose unbind
deletes the ordinary name the `Λ` just bound.  So the image's ordinary
indices keep their positions — criterion (i) with nothing to shift.
`Beta-no-alloc`: `Beta` allocates nothing, so the substitution moves no
representation.

### §6 — `CancelR` / `IdPush`, the merged frame is exact

THE ONE FRAME LEFT (the one `V` lives in) is preserved ON THE NOSE: the
merged frame's interior IS the inner frame's own.  Θ₂'s ordinary changes
have travelled inward and the surviving boundary REAPPLIES them (`_++_`
puts Θ₂'s change list at the tail of Θ₁'s, where the reading runs it
FIRST).  The redex's outer conversion is not transported: it is
cancelled (`CancelR`, whose `mkId A′` is re-minted at the seal's own
source) or re-read on the merge (`IdPush`'s `unseal X′`).

`V` is not renamed at all — it retypes exactly where it was.  That is
why neither rule's contractum mentions a renaming, and neither
allocates.

WHAT THE ONE-LAYER CONTRACTUM DELETED (2026-09-23).  `Move-outer-frame`
and `Move-outer-conversion` audited the second, outer layer — a rewind
whose interior is the exterior it sits at, carrying an identity.  No
rule builds that layer any more, so the two obligations went with it.

### §7 — the drop rules, the frame change in the OTHER direction

`($ n) ⟪ Θ , id A ⟫ → $ n` moves the literal from the boundary scope's
interior OUT to `Δ`: Θ's unbinds are undone, so the new frame can be
STRICTLY MORE NAMEABLE.  That is a frame gain in the direction the
criterion also forbids — but it is VACUOUS, because a literal names no
type variable at all: `⊢$`, `⊢true` and `⊢false` type it at EVERY type
context and every term context.

`Drop$-only-numerals`: AND NO OTHER TERM CAN TAKE THE STEP.  The rule's
left-hand side is the LITERAL ITSELF — the drop rules are the only ones
whose interior pattern is a constructor rather than a variable — so
there is nothing to generalize.  Progress needs no more: a closed value
at a base type IS a literal (`proof/Canonical.agda`, `canon-base`),
which is why the syntactic restriction costs nothing.

### §8 — the ξ rules, the sibling shift IS the context move

Each congruence reduces a subterm IN PLACE, at the very type context
the corresponding TYPING rule reads it on:

```
  ξ-⟪⟫   premise at the boundary scope's INTERIOR = `env`'s premise
         context
```

(`ξ-·-l`, `ξ-·-r`, `ξ-ν` read their premise at `Δ` itself, and there
is no `ξ-Λ`: `strong-rep-nu` never reduces under a type binder.)
This is not an equation: `ξ-⟪⟫` CARRIES the interior reading, which is
the same object `env` carries, so the two contexts are identified by
`interior-functional` rather than by `refl`.

THE NEW OBLIGATION OF THE STORE.  A congruence leaves a SIBLING behind
— the other operand of an application, or the boundary scope the
interior stepped inside — and the step may have allocated a cell.  The
sibling must move by EXACTLY the move the context made, or its frame
lies about which cell each of its representation indices names.  Both
are read off the same `Alloc`, so the obligation holds
DEFINITIONALLY: at `none` both are the identity, and at `new R` the
context gains `bindR R` at index 0 and `map suc` on its name map while
the sibling gets `renᴹᴿ suc` / `renᴮᴿ suc`.

And the reading of the shifted scope at the shifted context is the
shifted reading: that is `interior-ren` at `suc`, the fact `preserve`'s
`ξ-⟪⟫` case consumes.  Cited, not restated: `Boundary.agda` §3d.

### §9 — dead shift machinery

`shiftᵐ = renⁿ suc` (`proof/TermSubst.agda` §3) and `canon-shiftᵐ`
(`proof/Canonicity.agda`) have NO CONSUMERS: frame-exact substitution
weakens an image with `shiftᴵ`, which is `suc` on a variable image and
the IDENTITY on a value image (§5), so the term-variable shift is never
applied to a term.  `renⁿ` itself is LIVE — `⊢renⁿ` at the identity
renaming is what proves `⊢weakenⁿ`, the lemma that lets a term-closed
image type at an arbitrary term context.

Recorded, not deleted: an audit proposes, it does not land.
