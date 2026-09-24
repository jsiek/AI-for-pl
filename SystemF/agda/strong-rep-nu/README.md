# Strong System F — `SystemF/agda/strong-rep-nu/`

## strong-rep-nu (2026-09-24)

A VARIANT of `SystemF/agda/strong-rep-store/`, forked verbatim at
`main` 694fe461 (after PR #208).  Two experiments have landed, both on
2026-09-24, and the differences from strong-rep-store are `ν` (first
part below) and merging boundaries (second part, 5d98bbe2).

### Part 1: `ν` replaces type application

* **type application is gone from the run-time language; `ν` replaces
  it.**  The run-time term `ν A · L ⟨ c ⟩` (`Terms.agda`, borrowed in
  shape from GTPLC's `ν A · L •⟨ c ⟩`) evaluates `L` to a `∀`-value,
  allocates a fresh store cell for `A`'s representation, instantiates
  `L` there, and converts the result with the Conversion `c`.  Its
  typing rule `⊢ν` accepts ANY `c` whose types line up at the
  conversion context of `TyBetaBoundary` over the allocation.  The
  compiler writes `c = reveal 0 C` for an operator `L : ∀ C`, so the
  reveal that `TyBeta` used to mint at run time is now written at
  compile time, and the old `·[ B , A ]` annotation `B` is gone.
  Proposal and Jeremy's four answers: `notes/NuSketch.md`;
  `notes/DECISIONS.md`, 2026-09-24.

What changed with it:

| strong-rep-store | strong-rep-nu | contractum |
|---|---|---|
| `TyBeta` | `Nu-Λ` | `N ⟪ inst [] , c ⟫`, the conversion `ν` carries |
| `TyPeelR-Λ` | `Nu-⟪Λ⟫` | `(N ⟪ liftᴮ Θ , s ⟫) ⟪ inst [] , c ⟫`, STACKED |
| `TyPeelR-⟪⟫` | (none) | `Nu-⟪⟫` for the first part of the day; deleted in Part 2 as unreachable |
| `ξ-·[]` | `ξ-ν` | none: a congruence |

* **Stack, don't fuse.**  `TyPeelR-Λ` wrote one layer,
  `N ⟪ inst Θ , instReveal 0 s ⟫`, which fused the crossed conversion
  `s` with the reveal.  `Nu-⟪Λ⟫` moves `s` VERBATIM into a middle layer
  over `liftᴮ Θ` (Θ shifted one step in both universes) and puts `ν`'s
  own `c` outside it on `inst []`.  `Boundary.agda` gains `liftᴮ`, with
  `inst Θ = liftᴮ Θ ++ [bind 0 0]`, so read inside out the two stacked
  scopes are the old fused `inst Θ` (`Nu-⟪Λ⟫-stacks-to-inst`,
  `proof/ShiftAudit.agda` §3).  No rule mints `instReveal` any more.
  Since Part 2 the stacked pair is a `Merge` redex, and `Merge` fuses it
  on the next step by general composition.
* **Every reveal is written by the compiler.**  Until Part 2 one
  run-time reveal was left: `Nu-⟪⟫` pushed a `ν` at the new name inward
  and minted that `ν`'s conversion `reveal 0 (⇑Bᵢ′)`.  With one boundary
  per value the interior of a `∀`-value's boundary is a `Λ`, so
  `Nu-⟪⟫` never fires, and it was deleted with its two carried
  spellings `Bᵢ′` and `s″`.
* **A source language and a compiler.**  `Source.agda` is plain System
  F with the standard `L [ A ]`, over a COUNT of type variables, with
  the same value restriction on `Λ` and a derivation-building checker
  `inferˢ`.  `Compile.agda` defines `compile` on typing derivations,
  because `reveal 0 C` needs the operator's type.  `CompileTyping.agda`
  states `compile-⊢`, `compile-closed` and `compile-safe`; the proofs
  are in `proof/Compile.agda`.  `compile-⊢` needs `CtxWf Δ Γ` (every
  type in the term context is well formed), because without it the
  statement is false for open terms: at `Γ = [∀ (` 5)]` the source term
  `x [ℕ]` types, but its compiled `ν` needs `Δ ⊢ᵗ B` for a result type
  that names a variable `Δ` does not have.  `SourceExamples.agda`
  writes each of the twenty plain-System-F programs of `Examples.agda`
  as source and proves `compile … ≡ E.X₀` by `refl`.
* **Consequences.**  `instReveal`, its lemmas and the refuted record
  `¬CanonTyPeelR` were deleted.  The stacked layer cost steps (before
  Part 2):
  K 9→11, J 10→12, G 13→16, H 9→11, E 19→30, V 24→49, I 9→12,
  N 16→20, C 22→33, S 14→16.  Three historical wall records were
  dropped from `notes/All.agda` because their checked content is exact
  states of runs through the retired rules:
  `CancelRReachabilityWitness`, `RawRunProbe` and `AddLock0Wall`.  The
  files were then deleted here; strong-rep-store's `notes/` holds their
  checked versions.  `Show.agda` renders `ν` as `(ν X:=A · L ⟨ c ⟩)`,
  naming the cell `ν` will allocate and reading `c` under that name.

### Part 2: merging boundaries (5d98bbe2)

A value now carries AT MOST ONE boundary, and a boundary directly over
a value's boundary is a redex of one new rule, `Merge`, which merges
the two frames and COMPOSES the two conversions.  Proposal, census and
Jeremy's decisions: `notes/MergeSketch.md` (status IMPLEMENTED);
`notes/DECISIONS.md`, 2026-09-24, "merging boundaries".

* **Conversions are normal forms in three sorts** (`Conversion.agda`
  §1), after GTLC's three coercion normal-form sorts, with GTPLC's
  chain association:

      g ::= id A | c ↦ c | ∀ c                    Mid   the structural middle
      t ::= mid g | seal X | t ⨾seal X            Tail  a seal chain, associates LEFT
      c ::= tail t | unseal X | unseal X ⨾ c      Conv  an unseal chain, associates RIGHT

  with `⌞ g ⌟ = tail (mid g)`.  Each sort has its own typing judgement,
  `_⊢ᵐ_∶_⇝_`, `_⊢ᵀ_∶_⇝_` and `_⊢_∶_⇝_`.  The forms are TIGHT: a bare
  `seal X` or `unseal X` stands for an identity middle, a chain extends
  only a non-identity (`¬ IsIdᵀ t` in `conv-seal-seq`, `¬ IsIdᶜ c` in
  `conv-unseal-seq`), and `NoCancel X c` forbids `unseal X` directly
  before a bare `seal X`.  Seals and unseals still carry only the
  ordinary NAME: conversions stay REP-FREE, with the representation read
  through the lookup square.  The sorts are syntactic but NOT
  endpoint-indexed; that option was withdrawn to keep representation
  variables.
* **Composition** `Δ ⊢ c₁ ⨟ c₂` (first `c₁`, then `c₂`;
  `Conversion.agda` §4b) is an untyped function that takes the context
  first.  The context is used by `repOf Δ X` (the lookup square
  `∋:=?`, now in `Lookup.agda`) to write `mkId` of `X`'s representation
  where `seal X` meets `unseal X`, and by `underΛ` under `∀`.  The
  smart constructors `_⨾sealˢ_` and `unseal_⨾ˢ_` keep the result tight.
  Its typing lemma (`proof/Compose.agda`) is

      ⊢⨟ : Unique (names Δ) → Δ ⊢ c₁ ∶ A ⇝ B → Δ ⊢ c₂ ∶ B ⇝ C
         → Δ ⊢ (Δ ⊢ c₁ ⨟ c₂) ∶ A ⇝ C
* **Values** (`Terms.agda` §3): `Simple` (`S-$`, `S-true`, `S-false`,
  `S-ƛ`, `S-Λ`) and `Value` (`V-simple`, and
  `V-⟪⟫ : Simple U → InertTail t → Value (U ⟪ Θ , tail t ⟫)`).  A value
  boundary's source type is not a variable, so its conversion is a
  tail; the inert tails are everything but `id` at a base type.
* **The rules** (`Reduction.agda`) are ten: `Nu-Λ`, `Beta`, `Peel`,
  `Nu-⟪Λ⟫`, `Merge`, `Drop`, `ξ-·-l`,
  `ξ-·-r`, `ξ-ν`, `ξ-⟪⟫`.  `Merge` rewrites
  `(U ⟪ Θ₁ , tail t₁ ⟫) ⟪ Θ₂ , c₂ ⟫` to
  `U ⟪ Θ₁ ++ Θ₂ , Δ⋉ᶜ ⊢ tail t₁′ ⨟ c₂′ ⟫`: both conversions are
  weakened at the merged conversion context `Δ⋉ᶜ` (the carried `t₁′`
  and `c₂′`, pinned by `SameConv`) and composed there.  It SUBSUMES
  `CancelR` (`seal X` then `unseal X`) and `IdPush` (`id X` then
  `unseal X`), which are deleted, and it also merges the inert pairs
  that used to stack.  `Nu-⟪⟫` is deleted as unreachable (Part 1).
  `Nu-⟪Λ⟫` keeps its stacked contractum and `Merge` fuses it next.  The
  crossing-spelling law now has three carried spellings: `Peel`'s `s′`
  and `Merge`'s `t₁′` and `c₂′`.
* **Consequences.**  `proof/Canonicity.agda` is RETIRED: its
  single-binder invariant is exactly what merging gives up (a chain
  `seal Y ⨾seal X` names two binders).  `proof/AddUnbind0.agda` (used
  only by `Nu-⟪⟫`) and `notes/CancelRShiftWall.agda` (about `CancelR`)
  are deleted.  Preservation instantiates `proof.Preserve.Impl` at
  `cross-Λ-⊢`, `shift-⊢`, `preserve-Peel` and `preserve-Merge`
  (`proof/MoveScope.agda`); progress has `merge-redex`
  (`proof/Progress.agda`); `det` handles `Merge` by
  `sameConv-src-unique`; the tower measure is at most one on a value
  and `Merge` lowers it (`Merge-height`, `proof/ShiftAudit.agda` §4).
  The top-level theorem statements are unchanged.
* **Runs got shorter**: K 11→9, G 16→14, H 11→10, E 30→16, V 49→19,
  I 12→10, N 20→15, B 15→13, C 33→19, S 16→15; the others are
  unchanged.
* **Files.**  New: `Lookup.agda` (the lookup functions, below
  `Conversion.agda`; `TypeCheck.agda` re-exports them),
  `proof/Compose.agda`, `notes/MergeSketch.md`, `notes/StackCensus.agda`
  (where boundaries stack, over every state of every run).  Deleted:
  `proof/Canonicity.agda`, `proof/AddUnbind0.agda`,
  `notes/CancelRShiftWall.agda`.
* **Inspiration**, recorded in `notes/MergeSketch.md`: GTLC's three
  normal-form sorts, GTPLC's chain association, GTSF's strict/cross
  categories, and GTSFImp's `Conv↑`/`Conv↓`, the closest relative,
  which does not merge.

A regenerated run, `Examples.agda` §1a (`showRun 0 5 P₀-⊢`).  The
first step is `Nu-Λ`; the `Merge` step is the old `CancelR`:

    Ξ = []
    ((ν X:=ℕ · (ΛY. (λx:Y. x)) ⟨ (seal X ↦ unseal X) ⟩) · 7)
      --[Nu-Λ]-->
    Ξ = [α := ℕ]
    (((λx:X. x) ⟪ ↥X , (seal X ↦ unseal X) ⟫) · 7)
      --[Peel]-->
    Ξ = [α := ℕ]
    (((λx:X. x) · (7 ⟪ ↓X , seal X ⟫)) ⟪ ↥X , unseal X ⟫)
      --[Beta]-->
    Ξ = [α := ℕ]
    ((7 ⟪ ↓X , seal X ⟫) ⟪ ↥X , unseal X ⟫)
      --[Merge]-->
    Ξ = [α := ℕ]
    (7 ⟪ ↥X , ↓X , id ℕ ⟫)
      --[Drop]-->
    Ξ = [α := ℕ]
    7
        -- VALUE

Where to read on: `notes/notes.md` is the calculus with the `ν` rules
and `Merge`; `Commentary.md` § Conversion.agda / §4b,
§ Reduction.agda / Nu-Λ, Nu-⟪Λ⟫ and Merge, and § Terms.agda / §3 and
§4 — ⊢ν; `notes/NuSketch.md` and `notes/MergeSketch.md` for the design
alternatives that were considered.

Everything below this line is strong-rep-store's documentation, kept
as the inherited record, with the module map, gate and tools brought up
to date.  Wherever it says `TyBeta`, `TyPeelR-Λ`, `ξ-·[]` or
`L ·[ B , A ]`, read `Nu-Λ`, `Nu-⟪Λ⟫`, `ξ-ν` and `ν A · L ⟨ c ⟩`;
wherever it says `CancelR` or `IdPush`, read `Merge`; `TyPeelR-⟪⟫` has
no successor.  Where it and this section disagree, this section and the
file charters win.

## What this directory is (2026-09-23)

A VARIANT of `SystemF/agda/strong-rep-var/`, forked verbatim at the
`main` commit that merged PR #207, to experiment with changes to the
design.  Three experiments have landed; the differences from
strong-rep-var are:

* **the value restriction on type abstraction.**  `⊢Λ` requires the
  body to be a value — `⊢Λ : Value N → underΛ Δ ∣ ⤊ Γ ⊢ N ⦂ C → Δ ∣ Γ ⊢
  Λ N ⦂ `∀ C` — and the congruence `ξ-Λ` is gone: nothing reduces under
  a type binder.  `V-Λ` still carries `Value N` (redundant on well-typed
  terms, kept so that `Value` and the untyped reduction relation are
  verbatim strong-rep-var's).  Consequences: `Value` is stated before
  the typing judgement in `Terms.agda`; `proof/TermSubst.agda` proves that
  values survive every renaming and substitution (`value-renⁿ`,
  `value-renᴹ²`, `value-renᴹᴿ`, `value-substᵐ`), which the
  typing-transport lemmas need to rebuild `⊢Λ`'s premise; `value?` and
  `inert?` moved from `Eval.agda` to `TypeCheck.agda` because `infer`
  needs them; the `Λ` case of `progress` is immediate; and the example
  programs whose `Λ` body was a variable or an application now carry a
  dummy `λy:ℕ` under the `Λ` and an extra `· 0` at the use site.

* **the store** (experiment 2, 2026-09-22).  A boundary carries no bind
  block: the representation a ∀-elimination mints is allocated on the
  ambient representation context and a step returns the change it made,
  `δ : Alloc`.  `Boundary = List Change`, and a boundary changes NAMES
  only.  `notes/RepStoreSketch.md`; `notes/DECISIONS.md`, 2026-09-22.

* **the one-layer `CancelR`/`IdPush` contractum** (experiment 3,
  2026-09-23).  Both rules used to build a TWO-layer contractum, the
  outer layer being `⟪ rewind Θ₂ , mkId A ⟫` — an identity conversion
  over a frame whose interior is the exterior it sits at
  (`rewind-interior`).  That layer was a no-op: `preserve-CancelR` and
  `preserve-IdPush` already typed the inner layer at the redex's own
  exterior type, and wrapped it only to weaken the type it already
  had.  Both contracta are now ONE layer —
  `V ⟪ Θ₁ ++ Θ₂ , mkId A′ ⟫` and `V ⟪ Θ₁ ++ Θ₂ , unseal X′ ⟫` — and the
  premises that existed only to mint the discarded `mkId A`,
  `Δ ⊢ᶜ Θ₂ ⇒ Δᶜ` and `Δᶜ ∋ Y := A`, are gone from both rules; `Y` is
  constrained by the redex's typing, which is all the metatheory ever
  used it for (`idpush-name`, `cancel-name`, `proof/IdLayer.agda`).
  Consequences: `det` no longer needs `∋:=-det` for the outer lookup,
  `bdyRedex` no longer calls `cancelPremises?`, `proof/ShiftAudit.agda`
  §6 is the merged frame alone, and NO rule builds a `rewind` any more.
  Every run in `Examples.agda` got shorter — §7c `C` from 41 steps to
  22, §5b `V` from 40 to 24.  `notes/DECISIONS.md`, 2026-09-23.

Everything below this section is strong-rep-var's documentation with the
module prefix renamed; where the two developments differ, this section
and the file charters win.

## Purpose

System F with type abstraction enforced **at run time**.  Instantiating
`(ΛX. N) [A]` does not substitute `A` into `N`; it installs a
**boundary** `M ⟪ Θ , c ⟫` whose boundary scope `Θ` stores `A` as the
representation of a fresh variable, and whose conversion `c` says leaf
by leaf which side of the boundary may see that representation.

What this directory adds is the **two-universe redesign**: the two jobs
the old type-variable slot did at once are split into two de Bruijn
universes (`Ctx.agda`).

* a **representation variable** α is runtime storage.  A representation
  context `Ξ` binds it abstractly (`abstR`) or to a payload
  (`bindR R`), and a payload's free variables are representation
  variables.
* an **ordinary type variable** X is lexical — `∀X.A`, `ΛX. N`, and
  every type annotation.  A name map `Γ` holds exactly the live
  ordinary names and says which α each one names.

A type context is the pair `Ctxᵗ = Ξ ∣ Γ`.  A boundary scope's changes,
`unbind X α` and `bind X α`, delete and insert **ordinary names**; no
change ever removes or weakens a representation entry, so weakening
with respect to type variables is never used — that is what "strong"
means.  Everywhere but `TyBeta`, a subterm a rule moves is renamed in
the representation universe alone (`renᴹᴿ`), so its ordinary positions
do not move at all.

The mathematical presentation of the live calculus, in named-variable
notation, is **`notes/notes.md`**.  The design log — decisions as
definitions, worked examples, probe verdicts — is
**`notes/DECISIONS.md`**.

## Status

All six public theorems hold with **no module parameters, no
postulates, no holes**, under `agda --safe`:

| theorem | statement (`strong-rep-nu.TypeSafety`) |
|---------|----------------------------------|
| `progress` | a well-typed closed term is a value or steps |
| `preservation` | a step preserves the type |
| `preservation*` | so does a run |
| `type-safety` | after any run, a value or a further step |
| `det` | reduction is deterministic |
| `value-¬step` | values do not step |

The premises are deliberately **not uniform**.  `preservation`,
`preservation*` and `type-safety` take `WfCtx Δ`; the premise-free form
is false, because a contractum can mint a `BoundaryWf` whose exterior
field demands well-formedness from a redex that mentioned no ordinary
type variable at all (the counterexample is written out in
`Preservation.agda`'s charter and in `notes/notes.md`, "Metatheory").
`progress` takes no such premise — every boundary typing node carries
its own `BoundaryWf`.  `det` takes the **redex's typing derivation**, from
which it reads the name-map uniqueness the rules used to carry as
premises (`notes/DECISIONS.md`, 2026-09-18, "uniqueness comes from
typing, not reduction").

Preservation became unconditional on **2026-09-20**, when
`RepWeakenTyping`, `CrossΛTyping` and `AddUnbind0Typing` were all proved
(`proof/RepWeaken.agda`, `proof/AddUnbind0.agda`); progress and type
safety became unconditional on **2026-09-21**, when the last parameter,
`MergedReading`, was shrunk to the retention `CancelR` and `IdPush`
actually consume and then proved by `Boundary.merged-conversion-exists`
(`notes/DECISIONS.md`, 2026-09-21; `notes/PLAN.md`, "Current status").
Since the merge port (2026-09-24) `AddUnbind0Typing` and its module are
gone with `Nu-⟪⟫`, and `merged-conversion-exists` serves `Merge`; the
preservation cases are `preserve-Peel` and `preserve-Merge`.

The gate, run **cold**, from `SystemF/agda`:

    make -C strong-rep-nu check

`check` is `agda` plus `postulate-check`.  `agda` is
`agda --safe -v0 All.agda`: `All.agda` is the aggregate driver, so
type-checking it type-checks the core, `TypeCheck.agda`, `Eval.agda`,
the three theorem modules, `Examples.agda`, `Show.agda`,
`proof.Compose`, the three audits no other top-level module reaches
(`proof.Adversary`, `proof.IdLayer`, `proof.ShiftAudit`; the fourth,
`proof.Canonicity`, was retired on 2026-09-24) and `notes.All`, which
gates the eight checked wall, probe and census modules under `notes/`.  `postulate-check` is a recursive grep for `postulate`,
`{!`, `TERMINATING`, `NON_TERMINATING`, `NO_POSITIVITY_CHECK` and
`NO_UNIVERSE_CHECK` over **every** `.agda` under the directory —
top level, `proof/` and `notes/` alike — discarding matches on lines
whose first non-blank characters are `--`, so a mention in a
whole-line comment is allowed and a live one fails the build.

**The crossing-spelling defects.**  Six defects of one kind were found
and repaired, and they are the reason the rules look the way they do.
The law they left behind is stated in `Reduction.agda`'s charter: when
a rule **moves a subterm between two name maps**, the moved spelling is
**carried by the rule as a named premise** and pinned by a `Same…`
relation — `SameConv` for a conversion, `_⊢_≈_⊣_` for a type or a bare
name — and is **never computed by a fixed renaming**, because the two
contexts can reorder relative to each other.  Three carried spellings
are live today: `Peel`'s `s′` and `Merge`'s `t₁′` and `c₂′`.  The table
is the history of the five installed before the merge port, each after
its own machine-checked refutation; since 2026-09-24 only the first row
is live, `Merge`'s two spellings replace the `X′` and `A′` rows, and the
two `Nu-⟪⟫` rows went with that rule:

| spelling | rule | date | wall module |
|---|---|---|---|
| `s′` | `Peel` | 2026-09-18 | `notes/CrossingAudit.agda`, `notes/PeelPremise.agda` |
| `Bᵢ′` | `TyPeelR-⟪⟫` (retired) | 2026-09-18 | `strong-rep-store/notes/ForallPayloadWall.agda` |
| `X′` | `IdPush` (retired) | 2026-09-18 | `strong-rep-store/notes/ForallPayloadWall.agda` |
| `A′` | `CancelR` (retired) | 2026-09-19 | `notes/CancelRShiftWall.agda` (deleted 2026-09-24; git history), `strong-rep-store/notes/CancelRReachabilityWitness.agda` |
| `s″` | `TyPeelR-⟪⟫` (retired) | 2026-09-20 | `strong-rep-store/notes/AddLock0Wall.agda` |

The sixth defect of the same reading discipline hit the **conversion
context** itself rather than a spelling: a conversion reading skips
unbinds, so a later `bind` can meet a name that is already live, which
is the clause `conv-bind-live` (2026-09-17, `strong-rep-store/notes/ReUnlockWall.agda`,
`Boundary.agda` §3).  The six are tabulated against what the named
presentation hides in `notes/notes.md`, "The six weakening repairs".

**Frame exactness.**  Beyond the six theorems the development carries
the *shift audit*: every rule that moves a subterm, checked against the
criterion that the subterm's type context at the new position be
exactly its context at the old one, up to the binders it crossed and
the refinement `abstR → bindR R` of a variable it could already name.
It is not a single theorem statement but a site-by-site check —
`proof/ShiftAudit.agda`, §2 `Peel`, §3 the two `Nu` rules, §4 the
tower measure (at most one boundary on a value, and `Merge` lowers it),
§5 `Beta`, §6 `Merge`, §7 the drop, §8 the congruences — resting on the relational transport
lemmas `dual-interior` and `merged-interior` of `Boundary.agda` §3a.  Its headline here is that at every site but
`TyBeta`'s the ordinary component of the move is the identity.  The
verdicts are that module; `notes/ShiftAudit.md` is the ARCHIVED
2026-09-08 audit, written against the bind-block calculus, and is where
the leak's diagnosis and the four rejected repairs live.

**Relation to `SystemF/agda/strong/`.**  That directory is the earlier
**masked-entry** design, in which a type-context slot was a `Binding`
under a lock bit (`unmasked b` / `masked b`) and the two contexts a
boundary induces were *computed* (`interior Θ Δ`, `convCtx Θ Δ`).  It
is untouched by this branch and remains the `main`-branch development.
This directory is the redesign that replaced the lock bit with the two
universes: an unbind **deletes** an ordinary name, a bind **inserts**
one, and both induced contexts are **relations**, not functions of the
exterior.  Nothing here imports anything there.  `Design.md` in this
directory is a carried-over copy of `strong/Design.md` and describes
that older calculus, not this one.

## Module map

Each file keeps a short charter at its top; the design, history and
rationale commentary that used to sit inline is **`Commentary.md`**,
keyed by module and definition in source order.

### The calculus (top level)

| file | one line |
|------|----------|
| `Types.agda` | the type syntax `Ty` and its substitution operations — `renameᵗ`/`substᵗ` with `extᵗ`/`extsᵗ`/`⇑ᵗ`, `_[_]ᵗ`, and the index-directed `single-at`/`_[_:=_]ᵗ`.  Definitions only, and no universe tag: the same `Ty` is read either as an ordinary type or as a representation payload |
| `Ctx.agda` | **the two de Bruijn universes and every relation over them**: `RepBinding` (`abstR`/`bindR R`), `RepCtx`, `TyCtx` and the pair `Ctxᵗ = reps ∣ names`; the lookup family up to the square `_∋_:=_`; ordinary type formation `_⊢ᵗ_` and payload formation `_⊢ᴿ[_]_`; the two readings of a `Ty` (`_⊢_~_`, `_⊢_≈_⊣_`); well-formedness `WfCtx` with `Unique`/`ValidNames`/`WfRepCtx`; **the store** — `allocate R Δ`, which pushes a fresh cell at address 0 and moves every existing representation variable up by one, with `Alloc = none | new R` and `apply` (experiment 2, 2026-09-22) — the insert/delete relations, and the renaming interface `RepWk`.  Definitions only.  The bind-block machinery (`pushRepBinds`/`extendReps`/`_⊢ᴮ_`/`shiftRVars`/`shiftRep`/`SameTyExt`/`shiftByᵇ`) was deleted with the bind block |
| `Boundary.agda` | the boundary scope `Boundary = List Change` (an ALIAS since 2026-09-22; the one-field record went the way of the bind block) — a SEQUENTIAL list of `unbind X α`/`bind X α`, and NOTHING ELSE since experiment 2 landed: the representation a ∀-elimination mints lives in the ambient store, so a boundary changes NAMES only — with its two RELATIONAL readings, `_⊢ⁱ_⇒_`, which performs every change, and `_⊢ᶜ_⇒_`, which SKIPS unbinds (hence `conv-bind-live`); their functionality and the §3a–§3d transports (`dual-interior`, `rewind-interior`, `merged-interior`, `merged-conversion-exists`, the representation-renaming lemmas); the witness `BoundaryWf`; and the derived boundary scopes `rewind` (no rule builds one since 2026-09-23 — see the one-layer contractum below) and `inst` (the dual of a scope is §2's `dual` itself) — merging is plain `_++_` and the unbind-0 frame is the snoc `Θ ++ (unbind 0 0 ∷ [])`, both written out where they are used |
| `Lookup.agda` | the lookup functions `lookupˡ?`, `find?`, `lookupʳ?`, `unread?` and the lookup square `∋:=?`, each returning the ordinary derivation.  They sit BELOW `Conversion.agda`, whose composition reads a sealed name's representation through `∋:=?`; `TypeCheck.agda` re-exports them |
| `Conversion.agda` | conversions as NORMAL FORMS in three sorts (since 2026-09-24): the middle `Mid` (`id` / `_↦_` / `` `∀ ``), the seal chain `Tail` (`mid` / `seal` / `_⨾seal_`) and the unseal chain `Conv` (`tail` / `unseal` / `unseal_⨾_`), with `IsId` and `NoCancel`; the three judgements `_⊢ᵐ_∶_⇝_`, `_⊢ᵀ_∶_⇝_`, `_⊢_∶_⇝_` with NO polarity index; `mkId`, the canonical mints at a slot (`reveal`/`conceal`), COMPOSITION `Δ ⊢ c₁ ⨟ c₂` (§4b, with `repOf` and the smart constructors), the weakening relation `SameConv` with its uniqueness and `weaken` lemmas, `conv-ren`, the inversions and `conv-types-unique` |
| `Terms.agda` | terms, whose last constructor is the boundary `_⟪_,_⟫`; the `InertTail`/`Inert`/`Active` split with `act-or-inert`; `Simple` and `Value`, with AT MOST ONE boundary on a value (`V-⟪⟫ : Simple U → InertTail t → Value (U ⟪ Θ , tail t ⟫)`); and the typing judgment `_∣_⊢_⦂_`, whose boundary rule `boundary` TAKES a `BoundaryWf Δ Θ Δᵢ Δᶜ` instead of computing contexts and compares all three sides by `_⊢_≈_⊣_`, and whose `⊢Λ` carries the VALUE RESTRICTION `Value N` |
| `TermSubst.agda` | the PAIRED type renaming (`ren²`, `renᴹ²`) and its representation-only traversal `renᴹᴿ`; **the sibling shift** `↑ᴹ[ δ ]`/`↑ᴮ[ δ ]`, which is `renᴹᴿ suc`/`renᴮᴿ suc` when a step allocated a cell and the identity when it did not; and FRAME-EXACT substitution — `Img`, `crossΛᴹ`, `substᵐ`, `_[_∶_]ᵐ` — which wraps a value crossing a `Λ` in that binder's dual rather than shifting it.  ONLY what a top-level file names lives here; the lemmas and the term-variable renaming moved to `proof/TermSubst.agda` on 2026-09-22 |
| `Reduction.agda` | `_⊢_-→_∣_` with **ten** rules — a step returns the CHANGE `δ : Alloc` it made to the store, so the contractum lives at `apply δ Δ` and each congruence shifts the redex's siblings by `↑ᴹ[ δ ]` — `Nu-Λ`, `Beta`, `Peel`, `Nu-⟪Λ⟫`, `Merge`, `Drop` and the four congruences `ξ-·-l`, `ξ-·-r`, `ξ-ν`, `ξ-⟪⟫` (no `ξ-Λ`: nothing reduces under a type binder) — the multi-step `_⊢_-→*_` (each step's change applied to the tail's context) with `runCtx` and `value-¬step`.  (`det`, which takes the redex's typing derivation and concludes `M₁ ≡ M₂ × δ₁ ≡ δ₂`, is `proof/Determinism.agda`.)  Its charter states the crossing-spelling law and lists the three carried spellings |
| `TypeCheck.agda` | an executable, DERIVATION-PRODUCING checker for every judgment above: `wfCtx?`, `interior?`/`conversion?`/`boundaryWf?`, the readings `read?`/`sameTy?`/`sameTyExt?`/`weaken?`, `∋:=?`, `wfTy?`, `convTy?`, `infer`, `check⊢`, and the forcing family `tc`/`tk`/`tu`/`tf`/`tr` with the inferring `sq!`, `mw!`, `ty!`.  Every result is a `Maybe` of the ORDINARY derivation, so there is no soundness theorem to owe |
| `Eval.agda` | the evaluator: `step`, leftmost-outermost, RETURNS the derivation it found, so soundness is its type; `eval` iterates it with fuel and CHECKS every contractum at the run's type; `Trace` with `illtyped` as the one way a type is lost, `Checked`, `traceEnd`/`traceTerms`/`traceLen`/`evalTerms`, `trace-sound`, and `Reaches k n ⊢M V`, which states endpoint, step count, "no state lost the type" and value in ONE equation |
| `Progress.agda` | the statement `Progress`, stated premise-free, and `progress`, a one-line wrapper around `proof.Progress.Impl.progress`; unconditional since 2026-09-21 |
| `Preservation.agda` | `Preservation`, `PreservationWf` and `Preservation*` stated in full and proved by instantiating `proof.Preserve.Impl` at `RepWeaken.cross-Λ-⊢`, `RepWeaken.shift-⊢`, `PeelDual.preserve-Peel` and `MoveScope.preserve-Merge`; the charter explains why `WfCtx Δ` is part of the statement |
| `TypeSafety.agda` | the public theorem surface: the six theorems above, stated in full in one place rather than re-exported, every right-hand side a delegation |
| `Examples.agda` | the living regression: **eleven sections** (§1 baseline runs, §2 the vacuous-Λ family, §3 `Nu-⟪Λ⟫` from closed plain source, §4 the reveal mirror, §5 the tower, §6 polymorphic payloads, §7 functions that cross, §8 the cancel shift witness, §9 hand-built boundaries at a non-empty ambient, §10 what substitution does at a crossing, §11 refutations and non-vacuity) and **23 `Reaches` runs**.  All ten reduction rules fire in §§1–8; §9a and §9b are the only two runs pinned state by state, by `evalTerms` |
| `Source.agda` | the SOURCE language: plain System F with the standard `L [ A ]`, typing `n ∣ Γ ⊢ˢ M ⦂ A` over a count of type variables, the value restriction on `Λ`, and the derivation-building checker `inferˢ` |
| `Compile.agda` | `compile`, on source typing derivations: structural except `⟦L [A]⟧ = ν A · ⟦L⟧ ⟨ reveal 0 C ⟩`; `compile-value` |
| `CompileTyping.agda` | the elaboration theorems `compile-⊢` (with `CtxWf Δ Γ`), `compile-closed`, `compile-safe`, thin wrappers over `proof/Compile.agda` |
| `SourceExamples.agda` | every plain `Examples` program as source, with `compile (inferˢ …) ≡ E.X₀` by `refl` |
| `Residual.agda` | **the color-preservation statement layer** (2026-09-21): one-hole contexts `TermCtx`/`plug`; the type context AT THE HOLE `Δ ⊢C C ⊣ Δ′`, whose `names` is the hole's SCOPE MAP; `renCtxᴿ`/`holeᴿ` and `substCtx`/`holeEnv` (representation-only renaming and `Beta`-substitution through a context, and what reaches the hole), with the Alloc-indexed sibling shift `↑ᶜ[ δ ]`/`↑ᴴ[ δ ]`/`↑ʳ[ δ ]`; `Residual r C M ρ D N`/`Residuals`, indexed by the representation renaming ρ the move delivers to the hole.  Since experiment 2 that ρ is `idᵗ` everywhere but in a sibling an allocating step shifted (the pushed-in boundary of the retired `Nu-⟪⟫` was the other exception) — `Peel`'s argument moves VERBATIM.  Redex nodes are consumed; the `Drop` rules consume their literal; a substituted variable's position becomes the argument copy's (`CopyResidual`) |
| `ColorPreservation.agda` | TWO theorems.  `color-preservation : ColorPreservation` is the color theorem proper — color is about type variables only, so a residual position's lexical type-variable scope keeps its size: `length (names Δ₂) ≡ length (names Δ₁)`.  It is a corollary of the stronger `scope-map-preservation : ScopeMapPreservation` — the whole scope map is the old one under the run's representation renaming: `names Δ₂ ≡ map ρ (names Δ₁)`.  The source position is read at `Δ` and the target at `runCtx rs`, the context the run ends at.  Both carry `WfCtx Δ` (spent re-typing the run's middle terms by `preservation`/`preservation-wf`) and have premise-free closed forms at `empty`.  Proofs in `proof/ColorPreservation.agda`; the concrete instance is `notes/ColorPreservationProbe.agda` |
| `Show.agda` | de Bruijn → named renderer, printing the two universes differently — α, β, γ for representation variables, X, Y, Z for the ordinary names that denote them (see **Tools**) |
| `All.agda` | aggregate driver: type-checking it type-checks the whole development |

### The proofs (`proof/`)

| file | one line |
|------|----------|
| `Types.agda` | the bottom of the hierarchy: `substᵗ-cong`, `extsᵗ-renᵗ`, `substᵗ-renᵗ`.  It imports `strong-rep-nu.Types` and the standard library and nothing else |
| `TypeSubst.agda` | the algebraic theory of type substitution — `_⨟ᵗ_`, the congruences, the fusion laws, `sub-sub`, `substitution`, `exts-sub-cons` — a deliberate mirror of `SystemF/agda/extrinsic/TypeSubst.agda`.  Its only client here is `proof.Preserve` |
| `Ctx.agda` | every fact about the two universes: the determinacy suite `det` consumes (`∋ˡ-det`, `∋ʳ-det`, `same-rep-unique`, `sameTy-src-unique`, `∋:=-det`, `unique-lookup`), the name-map half of representation renaming, the insert/delete relations, and `RepWk`'s instances `repwk-abst₀`/`repwk-cons₀`/`repwk-abst` with `wfctx-ren` and `∋:=-ren` |
| `Preserve.agda` | the preservation induction: `⊢ᵗ-of` (type well-formedness recovered from typing), the minted-conversion typings `⊢reveal`/`⊢conceal`, the `Nu` cases, `preserve-Drop`, `preserve-Beta`, the crossing-case statements `PeelCase` and `MergeCase`, and `module Impl`, which assembles them |
| `Progress.agda` | the progress induction, `module Impl`: the ordinary cases over `proof.Canonical`, and the boundary cases constructing the relational readings and weakenings the rules carry; a boundary over a boundary value is ALWAYS a `Merge` redex (`merge-redex`) |
| `Canonical.agda` | canonical forms — `simple-¬var`, `canon-simple-∀`, `canon-base`, `canon-ℕ`, `canon-⇒`, `canon-∀` — all driven by the observation that an INERT tail's target type determines the head constructor, so no inert tail has a base target and, with one boundary per value, the interior of a ∀-value's boundary is a `Λ` |
| `TermSubst.agda` | the proof half of the term renaming/substitution API, in the section numbers its material had at top level: the derived `id²`/`renᶠ`/`renᴹ`/`wkN`/`wkᴹ`/`⇑ᴹ`; values under renaming (`inert-renᶜ`, `value-renᴹ²`, `value-renᴹᴿ`, `value-renⁿ`, `value-substᵐ`); the ordinary-identity agreement `renᴹ²-ord-id` with its `-pointwise-id` helpers; TERM-VARIABLE renaming `extⁿ`/`renⁿ`/`shiftᵐ` with `⊢renⁿ`, `renⁿ-id`, `⊢weakenⁿ`; the `⤊` transports; and the typed images `_∣_⊢ⁱ_⦂_` with `⊢imgTm`, `shiftᴵ-⊢`, `extᴵ-⊢` |
| `Compose.agda` | **composition is well typed**: `⊢⨟ : Unique (names Δ) → Δ ⊢ c₁ ∶ A ⇝ B → Δ ⊢ c₂ ∶ B ⇝ C → Δ ⊢ (Δ ⊢ c₁ ⨟ c₂) ∶ A ⇝ C`, with the chain premises `¬ IsId` and `NoCancel` rebuilt, never assumed.  §1 `isIdᶜ-types`, §2 the lookup functions are complete (`repOf-sound`), §3 the smart constructors, §4 `⊢⨟` one lemma per sort |
| `PeelDual.agda` | the `Peel` crossing: the dual is an INVERSE (`dual-interior`), so the argument crosses by a representation-only weakening; §1 weakens a TYPED conversion across the crossing (`weaken-⊢`), and §3 is `preserve-Peel` |
| `RepWeaken.agda` | the two transports with an identity ordinary component, proved at a CUT over an arbitrary `RepWk ρ Ξ Ξ′`: `⊢renᴿ`, and from it `rep-weaken-⊢` (what `Peel` consumes) and `cross-Λ-⊢` (what `Beta`'s crossing consumes).  The hard case is `boundary`, whose six premises transport one lemma apiece |
| `MoveScope.agda` | **the scope move**: `Merge` keeps both frames, MERGED as `Θ₁ ++ Θ₂`, weakens both conversions onto the merged conversion context (`weaken-⊢`) and composes them there (`⊢⨟`).  §1 the merged context retains both old ones (`merged-keeps₁`, `merged-keeps₂`), §2 gluing two readings of one representation, §3 `preserve-Merge` |
| `IdLayer.agda` | the id-layer facts about the two `Merge` redexes the retired `IdPush` and `CancelR` handled: typing already forces the two names to denote ONE representation variable (`idpush-name`, `cancel-name`), which is why composition's seal-then-unseal clause compares no names; `unseal` is the only active conversion an id-layer can meet; and the naked drop is sound exactly at a frame that changes nothing |
| `Adversary.agda` | the soundness gate: a conceal must cite a REPRESENTED binder, and the two universes refuse it twice over — the name may be absent from the map, or the representation variable it names may be `abstR` |
| `ShiftAudit.agda` | **the shift audit**: every rule that moves a subterm, checked site by site against frame exactness, plus the tower measure (at most one boundary on a value; `Merge-height`: `Merge` lowers it) and the refutation of the rejected wrap repair |
| `Residual.agda` | soundness of the residual layer: `plug C M` is the step's source and `plug D N` its contractum (`residual-source`, `residual-sound`, `residuals-sound`), via `plug-renCtxᴿ`, `plug-↑` and `plug-substCtx` — the sanity gate on the statement's data |
| `ColorPreservation.agda` | **the color-preservation proof**: `⊢C-ren` transports a frame derivation along a representation-only renaming (`interior-ren`/`RepWk` at boundary frames), `⊢C-len` transports it across the `abstR → bindR R` slot refinement, `⊢C-shift`/`interior-apply` transport it along a step's store change, `residual-frame` constructs the target frame per step at `apply δ Δ` (minted frames read by `inst-interior`/`dual-interior`/`merged-interior`/`crossΛ-interior`), and `residuals-color` composes along `ρ′ ∘ ρ`, re-typing by `preservation` and carrying well-formedness by `preservation-wf`; `residuals-color-length` is the color corollary |
| `TypeSafety.agda` | `type-safety` = `progress ∘ preservation*` |

## Tools

`Show.agda` renders de Bruijn terms, types, representation payloads,
conversions, boundary scopes, type contexts and whole evaluator
traces into named notation, driven non-interactively by
`scripts/render_term.sh` (which uses the type-error trick:
`oops : e ≡ ""; oops = refl` makes Agda print `e`'s normal form).  Run
it from the repo root.  A term:

    scripts/render_term.sh 'showTmIn 0 Q₀' \
        'open import strong-rep-nu.Examples'
    ((ΛX. (λx:X. (ΛY. x) [ℕ])) [ℕ] · 7)

a type context — `Δ₆` is the non-empty ambient of `Examples` §9:

    scripts/render_term.sh 'showTCtx Δ₆' \
        'open import strong-rep-nu.Examples'
    α := ℕ ∣ X↦α

The first argument is any `String` expression; the rest are extra
import lines, and the script picks the renderer to match them — an
import line mentioning `strong.` selects the OLD development's
`strong.Show`, and anything else gets `strong-rep-nu.Show`.  Entry
points: `showTmIn n M`, `showTyIn n A`, `showRepIn n R`,
`showConvIn n c`, `showBndIn n Θ c`, `showTermsIn n Ms` and
`showTCtx Δ`.  `n` is the number of ambient ordinary names; ordinary
slot 0 is named `X` and denotes representation variable `α`.

To render a whole **run** rather than a state, use `showRun n k ⊢M`,
which evaluates with fuel `k` and prints one state per line, each arrow
labelled by the rule that fired (`showTrace n tr` does the same for a
`Trace` you already have):

    scripts/render_term.sh 'showRun 1 2 Tcancel-⊢' \
        'open import strong-rep-nu.Examples' | sed 's/\\n/\n/g'
    Ξ = [α := ℕ]
    ((7 ⟪ seal X ⟫) ⟪ unseal X ⟫)
      --[Merge]-->
    Ξ = [α := ℕ]
    (7 ⟪ id ℕ ⟫)
      --[Drop]-->
    Ξ = [α := ℕ]
    7
        -- VALUE

(the script reads the string out of an Agda type error, so the newlines
arrive escaped — hence the `sed`).

Conventions: representation variables cycle `α`, `β`, `γ`, `α′`, …, and
the ordinary name at the same position cycles `X`, `Y`, `Z`, `X′`, …,
so `X` is by construction the ordinary name of `α`.  Term binders cycle
`x`, `y`, `z`, `f`, `g`, `h`, then primes.  A boundary scope's binds print
first as `↑α:=R`, then its changes IN THE ORDER THEY ACT — `↓X` for a
`unbind`, `↥X` for a `bind` — and the conversion last, read on the
conversion context rather than the interior's.  If a rendered change
shows a Latin letter other than the one its representation was
allocated with, the name map and the representation have come apart,
which is the defect class the six repairs were about.

**Never hand-transcribe de Bruijn** into a note or a report — render
it.

## `notes/` index

| file | one line |
|------|----------|
| `notes.md` | the mathematical presentation of the current calculus, named-variable notation |
| `PLAN.md` | the experiment's plan and running status block, the port's history, and a resume section for another machine |
| `TODO.md` | the live handoff queue — empty: the COLOR PRESERVATION port is complete (statement approved and proof landed 2026-09-21); the file records the two deltas flagged for Jeremy |
| `ColorPreservationProbe.agda` | the color-preservation statement on ONE RUN — `ΛX. ((ΛY. λx:(X⇒X). x) [X]) · (λx:X. x)`, three steps (TyBeta, Peel, Beta), the argument's `Residuals` derivation, its `⊢C` contexts at both ends, and `names Δ₃ ≡ map ρ★ (names Δ₀)` by `refl`: the TyBeta ALLOCATES a cell and `ξ-·-l` hands the argument that allocation's `suc`, so α's index shifts by one and the map is otherwise unchanged |
| `DECISIONS.md` | **the design log**, in date order: decisions stated as definitions, worked examples, probe verdicts, and Jeremy's rulings.  Start at the end |
| `DesignSpace.md` | **the map**: a mermaid graph of the fifty-one design points explored 2026-09-01…06, edges labelled with the evidence that moved the design, plus the legend and the through line |
| `DesignPoints.md` | the map's glossary: one entry per node id, same order, each with a pointer into `DECISIONS.md`, `Design.md`, `Examples.agda` or a commit |
| `BoundarySurvey.md` | the empirical record of the earlier boundary bookkeeping: the master table plus the bookkeeping-independent requirements the redesign had to meet |
| `RedesignAdvice.md` | survey data → design advice; the four answers (central rep storage, keep simultaneity, use Conversion, definitional cancel) |
| `RuleRepairs-TyPeelR-CancelR.md` | the proposed repairs to those two rules, before/after, run on the breaking examples |
| `ShiftAudit.md` | **the shift audit, ARCHIVED** (Jeremy, 2026-09-08): the criterion, the site-by-site verdict table, the leak in detail with its witness, the four candidate fixes with their hazards, and the verdict — the `canon-∀` split, installed as `TyPeelR-Λ` / `TyPeelR-⟪⟫`.  The table is written against the bind-block calculus and its last two rows against the two-layer contractum, so the LIVE audit is `proof/ShiftAudit.agda`; this file is kept for the diagnosis and the rejected repairs |
| `CancelRReachability.md` | is the `CancelR` defect REACHABLE from closed source?  Yes (2026-09-19) — the witness (`strong-rep-store/notes/CancelRReachabilityWitness.agda`), the two controls, and the repair path it settled |
| `BoundaryRules.md` | the earlier decision memo on boundary-manipulation rules |
| `DualLicenseDesign.md` | the dual-conceal licence of the first design, fully ruled |
| `PreservationEndgame.md` | the preservation endgame plan of the first design |
| `ParameterizedCastCalculi.md` | digest of Siek & Chen, *Parameterized Cast Calculi and Reusable Meta-theory for Gradually Typed Lambda Calculi* (JFP 31(e30), 2021) — the source of the active/inert methodology |
| `Zdancewic-embeddings.md` | digest of Zdancewic, Grossman & Morrisett, *Principals in Programming Languages* (ICFP'99) |
| `SyntacticTypeAbstraction.md` | digest of Grossman, Morrisett & Zdancewic, *Syntactic Type Abstraction* (TOPLAS 22(6)) |
| `TypeAbstractionComparison.md` | the design set against the polymorphism of Grossman, Morrisett & Zdancewic, *Syntactic Type Abstraction* (TOPLAS 22(6)) — centred on **tightness**: they have no out-of-scope type variable, because their type variables are global allocated names in a monotone knowledge base, not lexically scoped binders, so tightness is vacuous there whatever the evaluation order |
| `old/notes-v1.md` | the **refuted** first design note |
| `old/notes-v3.md` | the superseded short predecessor of `notes.md`, kept for history |
| `old/PLAN-v1.md` | the first design's plan, retired with the invariant hunt |

`notes/` also holds the **checked wall and probe modules** — the
machine-checked refutations and witnesses behind the repairs above.
All four are gated by `notes/All.agda`, which `All.agda` opens last, so
`make check` type-checks them with everything else: `CrossingAudit`,
`PeelPremise`, `RepresentationVariablesProbe` and `RepWeakenBindsWall`;
`notes/All.agda`
also gates `ColorPreservationProbe` and the stack census `StackCensus`
(2026-09-24).  (`CancelRReachabilityWitness`, `RawRunProbe` and
`AddLock0Wall` pinned runs of the retired rules and live on in
strong-rep-store's `notes/`; `CancelRShiftWall`, about `CancelR`, was
deleted in the merge port and lives on in the git history;
`ReUnlockWall` and `ForallPayloadWall`, the walls for `CancelR`,
`IdPush` and `TyPeelR-⟪⟫`, were deleted after it and live on in
strong-rep-store's `notes/`.)  The index above lists the main notes, not
every file in the directory.

Three PDFs sit at the top level for the digests above:
`parameterized-cast-calculi-…pdf`, `p197-zdancewic.pdf`,
`p1037-grossman.pdf`.

## Where to go next

* **`notes/notes.md`** — the calculus itself, in named-variable
  notation: syntax, the two context universes, the boundary scope readings,
  conversion and term typing with the three normal-form sorts and
  composition, all ten reduction rules, a worked `Merge` run, the metatheory with its premises argued, the six
  weakening repairs, and a notes ↔ Agda correspondence table that
  names the gap at every rule.
* **`notes/PLAN.md`** — how it got here: what was ported, what was
  rewritten, the errors testing found, and the completed plan record.
* **`notes/DECISIONS.md`** — why it is that calculus and not another,
  in date order.  Start at the end.
* **`notes/TODO.md`** — what is open: nothing — the COLOR PRESERVATION
  port is complete; the file records the two deltas flagged for Jeremy.
* **`Design.md`** — carried over from `SystemF/agda/strong/` and **not
  updated**: it describes the masked-entry calculus (`masked b`, the
  computed `interior Θ Δ`), not this one.  `notes/notes.md` supersedes
  it here.
