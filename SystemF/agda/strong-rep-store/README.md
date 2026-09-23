# Strong System F — `SystemF/agda/strong-rep-store/`

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
  exterior type, and wrapped it only to re-spell the type it already
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
change ever removes or re-spells a representation entry, so weakening
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

| theorem | statement (`strong-rep-store.TypeSafety`) |
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

The gate, run **cold**, from `SystemF/agda`:

    make -C strong-rep-store check

`check` is `agda` plus `postulate-check`.  `agda` is
`agda --safe -v0 All.agda`: `All.agda` is the aggregate driver, so
type-checking it type-checks the core, `TypeCheck.agda`, `Eval.agda`,
the three theorem modules, `Examples.agda`, `Show.agda`, the four
audits no other top-level module reaches (`proof.Adversary`,
`proof.IdLayer`, `proof.Canonicity`, `proof.ShiftAudit`) and
`notes.All`, which gates the ten checked wall and probe modules under
`notes/`.  `postulate-check` is a recursive grep for `postulate`,
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
contexts can reorder relative to each other.  Five carried spellings
are live today, each installed after its own machine-checked
refutation:

| spelling | rule | date | wall module |
|---|---|---|---|
| `s′` | `Peel` | 2026-09-18 | `notes/CrossingAudit.agda`, `notes/PeelPremise.agda` |
| `Bᵢ′` | `TyPeelR-⟪⟫` | 2026-09-18 | `notes/ForallPayloadWall.agda` |
| `X′` | `IdPush` | 2026-09-18 | `notes/ForallPayloadWall.agda` |
| `A′` | `CancelR` | 2026-09-19 | `notes/CancelRShiftWall.agda`, `notes/CancelRReachabilityWitness.agda` |
| `s″` | `TyPeelR-⟪⟫` | 2026-09-20 | `notes/AddLock0Wall.agda` |

The sixth defect of the same reading discipline hit the **conversion
context** itself rather than a spelling: a conversion reading skips
unbinds, so a later `bind` can meet a name that is already live, which
is the clause `conv-bind-live` (2026-09-17, `notes/ReUnlockWall.agda`,
`Boundary.agda` §3).  The six are tabulated against what the named
presentation hides in `notes/notes.md`, "The six re-spelling repairs".

**Frame exactness.**  Beyond the six theorems the development carries
the *shift audit*: every rule that moves a subterm, checked against the
criterion that the subterm's type context at the new position be
exactly its context at the old one, up to the binders it crossed and
the refinement `abstR → bindR R` of a variable it could already name.
It is not a single theorem statement but a site-by-site check —
`proof/ShiftAudit.agda`, §2 `Peel`, §3 the two `TyPeelR` clauses with
§4's tower measure for termination, §5 `Beta`, §6 `CancelR`/`IdPush`,
§7 the drops, §8 the congruences — resting on the relational transport
lemmas `dual-interior` and `merged-interior` of `Boundary.agda` §3a.  Its headline here is that at every site but
`TyBeta`'s the ordinary component of the move is the identity.  The
verdict table and the rejected repairs are `notes/ShiftAudit.md`.

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
| `Conversion.agda` | conversions `id` / `seal` / `unseal` / `_↦_` / `` `∀ ``, the judgment `Δ ⊢ c ∶ A ⇝ B` with NO polarity index, `mkId`, the canonical mints at a slot (`reveal`/`conceal`, `instReveal`/`instConceal`), the re-spelling relation `SameConv` with its uniqueness and `respell` lemmas, `conv-ren`, the inversions and `conv-types-unique` |
| `Terms.agda` | terms, whose last constructor is the boundary `_⟪_,_⟫`; the `Inert`/`Active` split with `act-or-inert`; `Value`; and the typing judgment `_∣_⊢_⦂_`, whose boundary rule `env` TAKES a `BoundaryWf Δ Θ Δᵢ Δᶜ` instead of computing contexts and compares all three sides by `_⊢_≈_⊣_` — the exterior premise's `SameTyExt (numBinds Θ)` collapsed into it when the bind block went — and whose `⊢Λ` carries the VALUE RESTRICTION `Value N` |
| `TermSubst.agda` | the PAIRED type renaming (`ren²`, `renᴹ²`) and its representation-only traversal `renᴹᴿ`; **the sibling shift** `↑ᴹ[ δ ]`/`↑ᴮ[ δ ]`, which is `renᴹᴿ suc`/`renᴮᴿ suc` when a step allocated a cell and the identity when it did not; and FRAME-EXACT substitution — `Img`, `crossΛᴹ`, `substᵐ`, `_[_∶_]ᵐ` — which wraps a value crossing a `Λ` in that binder's dual rather than shifting it.  ONLY what a top-level file names lives here; the lemmas and the term-variable renaming moved to `proof/TermSubst.agda` on 2026-09-22 |
| `Reduction.agda` | `_⊢_-→_∣_` with **fourteen** rules — a step returns the CHANGE `δ : Alloc` it made to the store, so the contractum lives at `apply δ Δ` and each congruence shifts the redex's siblings by `↑ᴹ[ δ ]` — `TyBeta`, `Beta`, `Peel`, `TyPeelR-Λ`, `TyPeelR-⟪⟫`, `CancelR`, `Drop$`, `Drop-true`, `Drop-false`, `IdPush` and the four congruences `ξ-·-l`, `ξ-·-r`, `ξ-·[]`, `ξ-⟪⟫` (no `ξ-Λ`: nothing reduces under a type binder) — the multi-step `_⊢_-→*_` (each step's change applied to the tail's context) with `runCtx` and `value-¬step`.  (`det`, which takes the redex's typing derivation and concludes `M₁ ≡ M₂ × δ₁ ≡ δ₂`, is `proof/Determinism.agda`.)  Its charter states the crossing-spelling law and lists the five carried spellings |
| `TypeCheck.agda` | an executable, DERIVATION-PRODUCING checker for every judgment above: `wfCtx?`, `interior?`/`conversion?`/`boundaryWf?`, the readings `read?`/`sameTy?`/`sameTyExt?`/`respell?`, `∋:=?`, `wfTy?`, `convTy?`, `infer`, `check⊢`, and the forcing family `tc`/`tk`/`tu`/`tf`/`tr` with the inferring `sq!`, `mw!`, `ty!`.  Every result is a `Maybe` of the ORDINARY derivation, so there is no soundness theorem to owe |
| `Eval.agda` | the evaluator: `step`, leftmost-outermost, RETURNS the derivation it found, so soundness is its type; `eval` iterates it with fuel and CHECKS every contractum at the run's type; `Trace` with `illtyped` as the one way a type is lost, `Checked`, `traceEnd`/`traceTerms`/`traceLen`/`evalTerms`, `trace-sound`, and `Reaches k n ⊢M V`, which states endpoint, step count, "no state lost the type" and value in ONE equation |
| `Progress.agda` | the statement `Progress`, stated premise-free, and `progress`, a one-line wrapper around `proof.Progress.Impl.progress`; unconditional since 2026-09-21 |
| `Preservation.agda` | `Preservation` and `Preservation*` stated in full and proved by instantiating `proof.Preserve.Impl` at `RepWeaken.cross-Λ-⊢`, `AddUnbind0.addUnbind0-⊢`, `PeelDual.preserve-Peel`, `MoveScope.preserve-CancelR` and `MoveScope.preserve-IdPush`; the charter explains why `WfCtx Δ` is part of the statement |
| `TypeSafety.agda` | the public theorem surface: the six theorems above, stated in full in one place rather than re-exported, every right-hand side a delegation |
| `Examples.agda` | the living regression: **eleven sections** (§1 baseline runs, §2 the vacuous-Λ family, §3 `TyPeelR` from closed plain source, §4 the reveal mirror, §5 the tower, §6 polymorphic payloads, §7 functions that cross, §8 the `CancelR` shift witness, §9 hand-built boundaries at a non-empty ambient, §10 what substitution does at a crossing, §11 refutations and non-vacuity) and **23 `Reaches` runs**, merged into one file on 2026-09-21.  All fourteen reduction rules fire in §§1–8; §9a and §9b are the only two runs pinned state by state, by `evalTerms` |
| `Residual.agda` | **the color-preservation statement layer** (2026-09-21): one-hole contexts `TermCtx`/`plug`; the type context AT THE HOLE `Δ ⊢C C ⊣ Δ′`, whose `names` is the hole's SCOPE MAP; `renCtxᴿ`/`holeᴿ` and `substCtx`/`holeEnv` (representation-only renaming and `Beta`-substitution through a context, and what reaches the hole), with the Alloc-indexed sibling shift `↑ᶜ[ δ ]`/`↑ᴴ[ δ ]`/`↑ʳ[ δ ]`; `Residual r C M ρ D N`/`Residuals`, indexed by the representation renaming ρ the move delivers to the hole.  Since experiment 2 that ρ is `idᵗ` everywhere but in `TyPeelR-⟪⟫`'s pushed-in boundary and in a sibling an allocating step shifted — `Peel`'s argument now moves VERBATIM.  Redex nodes are consumed; the `Drop` rules consume their literal; a substituted variable's position becomes the argument copy's (`CopyResidual`) |
| `ColorPreservation.agda` | TWO theorems.  `color-preservation : ColorPreservation` is the color theorem proper — color is about type variables only, so a residual position's lexical type-variable scope keeps its size: `length (names Δ₂) ≡ length (names Δ₁)`.  It is a corollary of the stronger `scope-map-preservation : ScopeMapPreservation` — the whole scope map is the old one under the run's representation renaming: `names Δ₂ ≡ map ρ (names Δ₁)`.  The source position is read at `Δ` and the target at `runCtx rs`, the context the run ends at.  Both carry `WfCtx Δ` (spent re-typing the run's middle terms by `preservation`/`preservation-wf`) and have premise-free closed forms at `empty`.  Proofs in `proof/ColorPreservation.agda`; the concrete instance is `notes/ColorPreservationProbe.agda` |
| `Show.agda` | de Bruijn → named renderer, printing the two universes differently — α, β, γ for representation variables, X, Y, Z for the ordinary names that denote them (see **Tools**) |
| `All.agda` | aggregate driver: type-checking it type-checks the whole development |

### The proofs (`proof/`)

| file | one line |
|------|----------|
| `Types.agda` | the bottom of the hierarchy: `substᵗ-cong`, `extsᵗ-renᵗ`, `substᵗ-renᵗ`.  It imports `strong-rep-store.Types` and the standard library and nothing else |
| `TypeSubst.agda` | the algebraic theory of type substitution — `_⨟ᵗ_`, the congruences, the fusion laws, `sub-sub`, `substitution`, `exts-sub-cons` — a deliberate mirror of `SystemF/agda/extrinsic/TypeSubst.agda`.  Its only client here is `proof.Preserve` |
| `Ctx.agda` | every fact about the two universes: the determinacy suite `det` consumes (`∋ˡ-det`, `∋ʳ-det`, `same-rep-unique`, `sameTy-src-unique`, `∋:=-det`, `unique-lookup`), the name-map half of representation renaming, the insert/delete relations, and `RepWk`'s instances `repwk-abst₀`/`repwk-cons₀`/`repwk-abst` with `wfctx-ren` and `∋:=-ren` |
| `Preserve.agda` | the preservation induction: `⊢ᵗ-of` (type well-formedness recovered from typing), the minted-conversion typings `⊢reveal`/`⊢conceal`, `preserve-TyBeta`, the three drops, `preserve-Beta`, `preserve-TyPeelR-Λ`, `preserve-TyPeelR-⟪⟫`, the crossing-case statements, and `module Impl`, which assembles them |
| `Progress.agda` | the progress induction, `module Impl`: the ordinary cases over `proof.Canonical`, the boundary cases constructing the relational readings and re-spellings the rules carry, and `addUnbind0-reading`, which proves the moved boundary's conversion reading for `TyPeelR-⟪⟫` |
| `Canonical.agda` | canonical forms — `canon-base`, `canon-ℕ`, `canon-⇒`, `canon-∀`, `canon-var` — all driven by the observation that an INERT conversion's target type determines the head constructor, so no inert conversion has a base target |
| `TermSubst.agda` | the proof half of the term renaming/substitution API, in the section numbers its material had at top level: the derived `id²`/`renᶠ`/`renᴹ`/`wkN`/`wkᴹ`/`⇑ᴹ`; values under renaming (`inert-renᶜ`, `value-renᴹ²`, `value-renᴹᴿ`, `value-renⁿ`, `value-substᵐ`); the ordinary-identity agreement `renᴹ²-ord-id` with its `-pointwise-id` helpers; TERM-VARIABLE renaming `extⁿ`/`renⁿ`/`shiftᵐ` with `⊢renⁿ`, `renⁿ-id`, `⊢weakenⁿ`; the `⤊` transports; and the typed images `_∣_⊢ⁱ_⦂_` with `⊢imgTm`, `shiftᴵ-⊢`, `extᴵ-⊢` |
| `Canonicity.agda` | the canonical conversion family `CanonAt X c` (subtrees, re-spellings and mints of `reveal`/`conceal`/`mkId`/`unseal`), its four closure facts, its representation-level twin `CanonAtᴿ` for the `SameConv` transports, and `canon-step`: the family survives reduction |
| `PeelDual.agda` | the `Peel` crossing: the dual is an INVERSE (`dual-interior`), so the argument crosses by a representation-only weakening; §1 re-spells a TYPED conversion across the crossing (`respell-⊢`), and §3 is `preserve-Peel` |
| `RepWeaken.agda` | the two transports with an identity ordinary component, proved at a CUT over an arbitrary `RepWk ρ Ξ Ξ′`: `⊢renᴿ`, and from it `rep-weaken-⊢` (what `Peel` consumes) and `cross-Λ-⊢` (what `Beta`'s crossing consumes).  The hard case is `env`, whose six premises transport one lemma apiece |
| `AddUnbind0.agda` | `addUnbind0-⊢`, preservation's last parameter, on the statement the 2026-09-20 `TyPeelR-⟪⟫` repair gave it: the moved boundary's typing, whose six `env` premises split into a representation-only half and a conversion half that must be re-spelled because a conversion reading skips the appended unbind |
| `MoveScope.agda` | **the scope move**: both `CancelR` and `IdPush` neutralise a two-layer wrapper's OUTER conversion, so the two frames merge into the one the contractum keeps (`Θ₁ ++ Θ₂`).  §1 the shared inversions, §2 `preserve-IdPush`, §3 `preserve-CancelR` on the rule repaired 2026-09-19 |
| `IdLayer.agda` | why `IdPush` and `CancelR` need no name-relating premise: typing already forces the two names to denote ONE representation variable (`idpush-name`, `cancel-name`), `unseal` is the only active conversion an id-layer can meet, and the naked drop is sound exactly at a frame that changes nothing |
| `Adversary.agda` | the soundness gate: a conceal must cite a REPRESENTED binder, and the two universes refuse it twice over — the name may be absent from the map, or the representation variable it names may be `abstR` |
| `ShiftAudit.agda` | **the shift audit**: every rule that moves a subterm, checked site by site against frame exactness, plus the tower measure that makes `TyPeelR-⟪⟫` terminate and the refutation of the rejected wrap repair |
| `Residual.agda` | soundness of the residual layer: `plug C M` is the step's source and `plug D N` its contractum (`residual-source`, `residual-sound`, `residuals-sound`), via `plug-renCtxᴿ`, `plug-↑` and `plug-substCtx` — the sanity gate on the statement's data |
| `ColorPreservation.agda` | **the color-preservation proof**: `⊢C-ren` transports a frame derivation along a representation-only renaming (`interior-ren`/`RepWk` at boundary frames), `⊢C-len` transports it across the `abstR → bindR R` slot refinement, `⊢C-shift`/`interior-apply` transport it along a step's store change, `residual-frame` constructs the target frame per step at `apply δ Δ` (minted frames read by `instantiate-interior`/`dual-interior`/`merged-interior`/`addUnbind0-interior-ren`/`crossΛ-interior`), and `residuals-color` composes along `ρ′ ∘ ρ`, re-typing by `preservation` and carrying well-formedness by `preservation-wf`; `residuals-color-length` is the color corollary |
| `TypeSafety.agda` | `type-safety` = `progress ∘ preservation*` |

## Tools

`Show.agda` renders de Bruijn terms, types, representation payloads,
conversions, boundary scopes, type contexts and whole evaluator
traces into named notation, driven non-interactively by
`scripts/render_term.sh` (which uses the type-error trick:
`oops : e ≡ ""; oops = refl` makes Agda print `e`'s normal form).  Run
it from the repo root.  A term:

    scripts/render_term.sh 'showTmIn 0 Q₀' \
        'open import strong-rep-store.Examples'
    ((ΛX. (λx:X. (ΛY. x) [ℕ])) [ℕ] · 7)

a type context — `Δ₆` is the non-empty ambient of `Examples` §9:

    scripts/render_term.sh 'showTCtx Δ₆' \
        'open import strong-rep-store.Examples'
    α := ℕ ∣ X↦α

The first argument is any `String` expression; the rest are extra
import lines, and the script picks the renderer to match them — an
import line mentioning `strong.` selects the OLD development's
`strong.Show`, and anything else gets `strong-rep-store.Show`.  Entry
points: `showTmIn n M`, `showTyIn n A`, `showRepIn n R`,
`showConvIn n c`, `showBndIn n Θ c`, `showTermsIn n Ms` and
`showTCtx Δ`.  `n` is the number of ambient ordinary names; ordinary
slot 0 is named `X` and denotes representation variable `α`.

To render a whole **run** rather than a state, use `showRun n k ⊢M`,
which evaluates with fuel `k` and prints one state per line, each arrow
labelled by the rule that fired (`showTrace n tr` does the same for a
`Trace` you already have):

    scripts/render_term.sh 'showRun 1 2 Tcancel-⊢' \
        'open import strong-rep-store.Examples' | sed 's/\\n/\n/g'
    Ξ = [α := ℕ]
    ((7 ⟪ seal X ⟫) ⟪ unseal X ⟫)
      --[CancelR]-->
    Ξ = [α := ℕ]
    (7 ⟪ id ℕ ⟫)
      --[Drop$]-->
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
| `ShiftAudit.md` | **the shift audit** (Jeremy, 2026-09-08): the criterion, the site-by-site verdict table, the leak in detail with its witness, the four candidate fixes with their hazards, and the verdict — the `canon-∀` split, installed as `TyPeelR-Λ` / `TyPeelR-⟪⟫` |
| `CancelRReachability.md` | is the `CancelR` defect REACHABLE from closed source?  Yes (2026-09-19) — the witness (`notes/CancelRReachabilityWitness.agda`), the two controls, and the repair path it settled |
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
All ten are gated by `notes/All.agda`, which `All.agda` opens last, so
`make check` type-checks them with everything else:
`ReUnlockWall`, `ForallPayloadWall`, `CrossingAudit`, `PeelPremise`,
`CancelRReachabilityWitness`, `RawRunProbe`,
`RepresentationVariablesProbe`, `RepWeakenBindsWall`, `AddLock0Wall`
and `CancelRShiftWall`.  The index above lists the main notes, not
every file in the directory.

Three PDFs sit at the top level for the digests above:
`parameterized-cast-calculi-…pdf`, `p197-zdancewic.pdf`,
`p1037-grossman.pdf`.

## Where to go next

* **`notes/notes.md`** — the calculus itself, in named-variable
  notation: syntax, the two context universes, the boundary scope readings,
  conversion and term typing, all fourteen reduction rules, a worked
  `CancelR` run, the metatheory with its premises argued, the six
  re-spelling repairs, and a notes ↔ Agda correspondence table that
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
