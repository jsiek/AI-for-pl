# Strong System F — `SystemF/agda/strong/`

## Purpose

System F with type abstraction enforced **at run time**.  Instantiating
`(ΛX. N) [A]` does not substitute `A` into `N`; it installs a
**boundary** `M ⟪ Θ , c ⟫` whose context morphism `Θ` binds `X` to the
representation `A`, masks whatever the interior may not name, and whose
conversion `c` says leaf by leaf which side of the boundary may see the
representation.  A variable's representation is stored exactly once, at
the entry that binds it, and every other mention resolves it by looking
the **name** up along the enclosing type context.  A masked slot is never
dropped or re-spelled — its entry is retained (`masked`), so weakening with
respect to type variables is never used; that is what "strong" means.
This is **v2**, the conversion-boundary design.  **v1** — one combined
boundary `M ⟪ Θ , B₀ ⟫` carrying a list of reveals and conceals together
with a single boundary type, with representations *copied* into every
boundary that mentioned them — is on `main` and its note is
`notes/old/notes-v1.md`; it is **refuted** (subject reduction is false;
`notes/DECISIONS.md`, "THE PRESERVATION VERDICT (2026-09-05)").

The informal definition of the live calculus is **`Design.md`**.  The
design log — decisions as definitions, examples, probe verdicts — is
**`notes/DECISIONS.md`**.

## Status

All six public theorems hold with **no module parameters, no postulates,
no holes**, under `agda --safe`:

| theorem | statement (`strong.TypeSafety`) |
|---------|----------------------------------|
| `progress` | a well-typed closed term is a value or steps |
| `preservation` | a step preserves the type |
| `preservation*` | so does a run |
| `type-safety` | after any run, a value or a further step |
| `det` | reduction is deterministic |
| `value-¬step` | values do not step |

The gate, run **cold**, from `SystemF/agda`:

    make -C strong check

which is `agda --safe -v0 All.agda` plus a hygiene grep for
`postulate` / `{!` / `TERMINATING` / `NON_TERMINATING` /
`NO_POSITIVITY_CHECK` / `NO_UNIVERSE_CHECK` in every `.agda` under
`strong/` (including `notes/old/`).  `All.agda` is the aggregate driver:
type-checking it type-checks the whole development.

## Module map

### The calculus (top level)

| file | one line |
|------|----------|
| `Types.agda` | System F types in de Bruijn form; renaming and parallel substitution; `_[_]ᵗ` and the at-a-slot substitution `_[_:=_]ᵗ` |
| `TypeSubst.agda` | the type-level renaming/substitution algebra (`rename-cong`, `rename-rename-commute`, and friends) |
| `Ctx.agda` | **the type context**: entries `abst` / `bind A` / `masked E`, lookup (`∋e`, `∋tv`, `∋ X := A`), well-formed types, the two transports (`Ren`, `⊑`), injective renamings, in-place `mask`/`unmask`, and the bind prefix `pushBinds` with `shiftBy` |
| `Conversion.agda` | conversions `id` / `seal` / `unseal` / `_↦_` / `` `∀ ``, the judgment `Δ ⊢ c ∶ A ⇝ B`, `mkId`, both transports, the inversions, and `conv-types-unique` |
| `Terms.agda` | the context morphism (`bind`/`lock`/`unlock`, `repsOf`, `numBinds`, `scope`, `unlockedScope`, `interior`, `convCtx`), `_⊢ᵐ_`, terms, the typing judgment with `env`, `Inert`/`Active` + `act-or-inert`, and `Value` |
| `TermSubst.agda` | `renᴮ`/`renᴹ`/`wkᴹ`, `⊢rename` (with `Inj ρ`), `⊢retag` (along `⊑`), term substitution, `⊢subst`, `preserve-Beta` |
| `Reduction.agda` | `reveal`/`conceal` and their conversion analogues, `dual`, the scope move (`scopeOf`, `dropLocks`, `_⋉_`), the seven rules plus five congruences, `_-→*_`, `value-¬step`, `det` |
| `Progress.agda` | `progress`, with the boundary case split out as `progress-env` and `TyPeelR`'s premise read off the redex (`∀-conv-premise`) |
| `Preservation.agda` | `preservation` / `preservation*` as `proof.Preserve.Impl` instantiated at the three downstream cases, plus the per-rule statements and `⊢ᵗ-of-closed` |
| `TypeSafety.agda` | the public theorem surface: the six theorems above, stated in full |
| `All.agda` | aggregate driver |
| `Examples.agda` | the regression corpus: 14 sections of runs and refutations, most from closed plain System F source, §14 being the pre-boundary counterexample run in v2 (see `Design.md` for which example illustrates which rule) |
| `Show.agda` | de Bruijn → named renderer (see **Tools**) |
| `PLAN.md` | **historical**: the v1 handoff plan (PR #189); superseded by `Design.md` + `notes/DECISIONS.md` |

### The proofs (`proof/`)

| file | one line |
|------|----------|
| `Preserve.agda` | the preservation induction: `⊢ᵗ-of` (which replaces a context well-formedness premise), the minted-conversion typings `⊢reveal`/`⊢conceal`/`⊢instReveal`/`⊢instConceal`, `preserve-TyBeta`, `preserve-Drop$`, `preserve-TyPeelR`, the three case statements, and `module Impl` |
| `PeelDual.agda` | the `Peel` case: `interior-dual` and `convCtx-dual` in general, and `preserve-Peel` |
| `MoveScope.agda` | **the scope move**: the list algebra of `scopeOf`/`dropLocks`/`_⋉_`, `interior-dropLocks`, the unconditional frame lemmas `frame-move`/`convCtx-move`, `move-∋`, `⊢ᵐ-⋉`, the lock-only refutation, and `preserve-CancelR` / `preserve-IdPush` |
| `Canonical.agda` | canonical forms: `canon-base`, `canon-ℕ`, `canon-⇒`, `canon-∀`, `canon-var` |
| `Canonicity.agda` | the canonical conversion family (`reveal`/`conceal`/`mkId` subtrees) and its closure under the rules |
| `IdLayer.agda` | why `IdPush` and `CancelR` need no name-relating premise: typing forces `X ≡ numBinds Θ₁ + Y` (`idpush-name`, `cancel-name`), and `unseal` is the only active conversion those left-hand sides meet |
| `MaskFacts.agda` | no boundary operation can take a binder away (masking retains, unlocking recovers); the old cancel residue is not well formed |
| `Adversary.agda` | the soundness gate: a conceal must cite a live binder, and v1's adversaries refuted by that one inversion |
| `PreserveObstruct.agda` | the four refutation witnesses, three of which now record the **positive** fact after the repairs (§2 `TyPeelR`, §4 the wall witness) |
| `TypeSafety.agda` | `type-safety` = `progress ∘ preservation*` |

Four modules are **historical records of the invariant hunt** — the
search for a side condition that would ground the premise
`interior Θ₂ Δ ⊢ᵗ A` for the old `CancelR`/`IdPush` contracta.  The scope
move removed the need for it entirely.  They compile, they carry
`RETIRED` banners, nothing in the main development depends on them, and
each is a machine-checked refutation of a candidate design.
**Deletion pending Jeremy's call** (closed-world repo):

| file | the candidate it kills |
|------|------------------------|
| `WallReach.agda` | `RepWf` ("no lock blocks a slot a nameable binder's rep names") as a global term invariant — refuted on a reachable run |
| `WallGrounding.agda` | folding `RepWf` into `_⊢ᵐ_`'s lock clause — impossible: the unsound and the reachable witness share the same `(Δ, Θ)` |
| `ChainScoped.agda` | the rep **chain** as the invariant — preserved by the rules but not `⊑`-stable |
| `IdPushReach.agda` | the reachability verdict for the old `IdPush` configuration, and `maskOnly` |

## Tools

`Show.agda` renders de Bruijn terms, types, conversions, context
morphisms and type contexts into named notation, driven
non-interactively by `scripts/render_term.sh` (which uses the type-error
trick: `oops : e ≡ ""; oops = refl` makes Agda print `e`'s normal form).
Run it from the repo root:

    scripts/render_term.sh 'showTmIn 0 P₀' 'open import strong.Examples'
    scripts/render_term.sh 'showTCtx Δi' \
        'open import strong.proof.PreserveObstruct'

The first argument is any `String` expression; the rest are extra import
lines.  Entry points: `showTmIn n M`, `showTyIn n A`, `showConvIn n c`,
`showBndIn n Θ c`, `showTCtx Δ`, and `showTCtxAt d i sup Δ` when you want
to supply your own names for the free slots.  `n` is the ambient type
context's length; slot 0 is named `X`.

Conventions: type variables cycle `X`, `Y`, `Z`, `X′`, …; term binders
cycle `x`, `y`, `z`, `f`, `g`, `h`, then primes; `V` and `W` are reserved
for value metavariables and never generated.  Type binder names are
**globally unique across one rendered term** — two sibling `Λ`s never
both print as `ΛX` — and binds are named oldest-first so an older bind
keeps its name when `TyPeelR` prepends a newer one.  Morphism entries
print as `↑X:=A` (`bind`), `↓X` (`lock`), `↥X` (`unlock`); a `masked` entry
prints as `⌷[…]`.

**Never hand-transcribe de Bruijn** into a note or a report — render it.

## `notes/` index

| file | one line |
|------|----------|
| `DECISIONS.md` | **the design log**, in date order: decisions stated as definitions, worked examples, probe verdicts, and Jeremy's rulings.  Start at the end |
| `BoundarySurvey.md` | the empirical record of v1's boundary bookkeeping: the master table plus the bookkeeping-independent requirements the redesign had to meet |
| `RedesignAdvice.md` | survey data → design advice; the four answers (central rep storage, keep simultaneity, use Conversion, definitional cancel) |
| `RuleRepairs-TyPeelR-CancelR.md` | the proposed repairs to those two rules, before/after, run on the breaking examples |
| `BoundaryRules.md` | the earlier decision memo on boundary-manipulation rules (v1-era) |
| `DualLicenseDesign.md` | the v1 dual-conceal licence, fully ruled (v1-era) |
| `PreservationEndgame.md` | the v1 preservation endgame plan (v1-era) |
| `ParameterizedCastCalculi.md` | digest of Siek & Chen, *Parameterized Cast Calculi and Reusable Meta-theory for Gradually Typed Lambda Calculi* (JFP 31(e30), 2021) — the source of the active/inert methodology |
| `Zdancewic-embeddings.md` | digest of Zdancewic, Grossman & Morrisett, *Principals in Programming Languages* (ICFP'99) |
| `SyntacticTypeAbstraction.md` | digest of Grossman, Morrisett & Zdancewic, *Syntactic Type Abstraction* (TOPLAS 22(6)) |
| `old/notes-v1.md` | the **refuted** v1 design note |
| `old/*.agda` | the v1 probe files and the retired v1 `Reduction`/`Terms`/`Typing` |

Three PDFs sit at the top level for the digests above:
`parameterized-cast-calculi-…pdf`, `p197-zdancewic.pdf`,
`p1037-grossman.pdf`.

## Where to go next

* **`Design.md`** — the calculus: syntax, the two type contexts a
  boundary induces, all typing rules with `env` explained premise by
  premise, all reduction rules with a rendered example each, the
  metatheory's proof shape, the design laws, and (Appendix A) the full
  list of helper names.
* **`notes/DECISIONS.md`** — why it is that calculus and not another.
