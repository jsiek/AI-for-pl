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

Beyond the six, the development carries a **tightness** result about the
reduction relation itself — reduction never takes a term the exterior
refuses to one it accepts (design law 2, `Design.md` §8).  It is not a
theorem statement but a rule-by-rule check backed by five frame
identities: `proof/DualTightness` for `Peel`'s `unlock` half, `Examples`
§15 for every other rule that moves a subterm into a new frame, and the
frame-identity table in `Design.md` §7.  Every rule passes; the one
recorded exception, `Beta` at an *erasing* body, is a dropped argument
rather than a scope gain.

The gate, run **cold**, from `SystemF/agda`:

    make -C strong check

which is `agda --safe -v0 All.agda` plus a hygiene grep for
`postulate` / `{!` / `TERMINATING` / `NON_TERMINATING` /
`NO_POSITIVITY_CHECK` / `NO_UNIVERSE_CHECK` in every `.agda` under
`strong/` — which, since the v1 probes were deleted, is exactly the
development (`notes/` is `.md` only).  `All.agda` is the aggregate
driver: type-checking it type-checks the whole thing.

## Module map

### The calculus (top level)

| file | one line |
|------|----------|
| `Types.agda` | System F types in de Bruijn form; renaming and parallel substitution; `_[_]ᵗ` and the at-a-slot substitution `_[_:=_]ᵗ` |
| `TypeSubst.agda` | the type-level renaming/substitution algebra (`rename-cong`, `rename-rename-commute`, and friends) |
| `Ctx.agda` | **the type context**: entries `abst` / `bind A` / `masked E`, lookup (`∋e`, `∋tv`, `∋ X := A`), well-formed types, the two transports (`Ren`, `⊑`), injective renamings, in-place `mask`/`unmask`, and the bind prefix `pushBinds` with `shiftBy` |
| `Conversion.agda` | conversions `id` / `seal` / `unseal` / `_↦_` / `` `∀ ``, the judgment `Δ ⊢ c ∶ A ⇝ B`, `mkId`, both transports, the inversions, `conv-types-unique`, and the canonical conversions minted at a slot (`reveal`/`conceal`, `instReveal`/`instConceal`) |
| `CtxMorph.agda` | the context morphism as a **pair** — `record CtxMorph = morph (binds : List Ty) (changes : List Change)`, the binds a PARALLEL block and the changes a SEQUENTIAL `lock`/`unlock` list — with `numBinds`, the type contexts it induces (`applyChanges`/`applyUnlocks` at the list, `scope`/`unlockedScope`/`interior`/`convCtx` at the morphism) and their refinement transports, the well-formedness judgement `Δ ⊢ᵐ Θ` as a pair of halves (`_⊢ʳ_` reps, `_⊢ˢ_` changes), and the derived morphisms `dual` (Peel) and `rewind`/`_⋉_` (the scope move) |
| `Terms.agda` | terms, the typing judgment with `env`, `Inert`/`Active` + `act-or-inert`, and `Value` (re-exports `CtxMorph`) |
| `TermSubst.agda` | `renᴮ`/`renᴹ`/`wkᴹ`, `⊢rename` (with `Inj ρ`), `⊢retag` (along `⊑`), term substitution, `⊢subst`, `preserve-Beta` |
| `Reduction.agda` | the seven rules plus five congruences, `_-→*_`, `value-¬step`, `det` |
| `Progress.agda` | the statement `Progress` and `progress`, a one-line wrapper around `proof.Progress.progress` |
| `Preservation.agda` | `preservation` / `preservation*` as `proof.Preserve.Impl` instantiated at the three downstream cases, plus the per-rule statements and `⊢ᵗ-of-closed` |
| `TypeSafety.agda` | the public theorem surface: the six theorems above, stated in full |
| `Eval.agda` | the evaluator: `step` **is** `progress`, `eval` iterates it with fuel under `preservation`, `Trace` stores the step derivations, `trace-sound` / `traceFinal` / `trace-unique`, `evalTerms`, and `showTrace` / `ruleName` |
| `All.agda` | aggregate driver |
| `Examples.agda` | the regression corpus, **15 sections**: §§1–9 and §§11–14 of runs and refutations, most from closed plain System F source, §14 being the pre-boundary counterexample run in v2, and §15 the **tightness tests, rule by rule** (§10 was deleted with the invariant hunt; later numbers are unchanged).  Seven of the runs are additionally pinned against the **generated** trace, `evalTerms n ⊢X₀ ≡ …` by `refl`.  See `Design.md` for which example illustrates which rule |
| `Show.agda` | de Bruijn → named renderer (see **Tools**) |

### The proofs (`proof/`)

| file | one line |
|------|----------|
| `Preserve.agda` | the preservation induction: `⊢ᵗ-of` (which replaces a context well-formedness premise), the minted-conversion typings `⊢reveal`/`⊢conceal`/`⊢instReveal`/`⊢instConceal`, `preserve-TyBeta`, `preserve-Drop$`, `preserve-TyPeelR`, the three case statements, and `module Impl` |
| `PeelDual.agda` | the `Peel` case: `interior-dual` and `convCtx-dual` in general, and `preserve-Peel` |
| `MoveScope.agda` | **the scope move**: the list algebra of `shiftScope`/`rewind`/`_⋉_`, `interior-rewind`, the frame **equalities** `interior-⋉-rewind`/`convCtx-⋉-rewind` (with `convCtx-move` the one surviving `⊑`), `move-∋`, `⊢ᵐ-rewind`, `⊢ᵐ-⋉`, the lock-only refutation `¬frame-locksOnly`, and `preserve-CancelR` / `preserve-IdPush` |
| `Progress.agda` | the progress induction: the boundary case split out as `progress-env`, `TyPeelR`'s premise read off the redex (`∀-conv-premise`), and `progress` itself |
| `Canonical.agda` | canonical forms: `canon-base`, `canon-ℕ`, `canon-⇒`, `canon-∀`, `canon-var` |
| `Canonicity.agda` | the canonical conversion family (`reveal`/`conceal`/`mkId` subtrees) and its closure under the rules |
| `IdLayer.agda` | why `IdPush` and `CancelR` need no name-relating premise: typing forces `X ≡ numBinds Θ₁ + Y` (`idpush-name`, `cancel-name`), and `unseal` is the only active conversion those left-hand sides meet |
| `MaskFacts.agda` | no boundary operation can take a binder away (masking retains, unlocking recovers); the old cancel residue is not well formed |
| `Adversary.agda` | the soundness gate: a conceal must cite a live binder, and v1's adversaries refuted by that one inversion |
| `PreserveObstruct.agda` | the four refutation witnesses, three of which now record the **positive** fact after the repairs (§2 `TyPeelR`, §4 the wall witness) |
| `DualTightness.agda` | **tightness of the crossing**, Jeremy's test (2026-09-06) and its repair: the redex that is ill typed at the exterior now has an ill-typed contractum too (`¬⊢Contractum`), (†) `interior (dual Θᵤ) (interior Θᵤ Δᵤ) ≡ Δᵤ`, the positive control at a `lock`, and the VACUOUS UNLOCK refused (`¬⊢ᵐΘᵥ`).  The same test at every other rule that moves a subterm is `Examples` §15 |
| `MwUObstruct.agda` | which outer frame the scope move may use, on one configuration: `dropLocks Θ₂` **refuted** (the moved unlock goes vacuous), `bindsOnly Θ₂` **refuted** (the frame's own rep loses its unlock), `rewind Θ₂` does both jobs — and why the rep half reads its reps on `unlockedScope Θ Δ` rather than on the plain exterior |
| `TypeSafety.agda` | `type-safety` = `progress ∘ preservation*` |

**The invariant hunt** — the search for a side condition that would
ground the premise `interior Θ₂ Δ ⊢ᵗ A` for the old `CancelR`/`IdPush`
contracta — carried four record modules (`WallReach`, `WallGrounding`,
`ChainScoped`, `IdPushReach`).  The scope move removed the need for the
premise entirely and every candidate side condition was refuted, so the
four were **deleted** (Jeremy, 2026-09-06; closed-world repo).  The record
itself lives in `notes/DECISIONS.md` (2026-09-06 entries); the two
artifacts worth keeping survived the deletion as
`proof/MaskFacts.mask-only` (the mask-only fact, once an interface) and
`Examples` §12/§12b (the wall context reached from closed source, and the
wall witness stepping after the move).

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

To render a whole **run** rather than a state, evaluate it first
(`Eval.agda`) and print the trace — one state per line, each arrow
labelled by the redex rule that fired:

    scripts/render_term.sh 'showTrace 0 (eval 6 ⊢P₀)' \
        'open import strong.Examples' 'open import strong.Eval' \
      | sed 's/\\n/\n/g'

(the script reads the string out of an Agda type error, so the newlines
arrive escaped — hence the `sed`).

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
| `DesignSpace.md` | **the map**: a mermaid graph of the fifty design points explored 2026-09-01…06, edges labelled with the evidence that moved the design, plus the legend and the through line |
| `DesignPoints.md` | the map's glossary: one entry per node id, same order, each with a pointer into `DECISIONS.md`, `Design.md`, `Examples.agda` or a commit |
| `BoundarySurvey.md` | the empirical record of v1's boundary bookkeeping: the master table plus the bookkeeping-independent requirements the redesign had to meet |
| `RedesignAdvice.md` | survey data → design advice; the four answers (central rep storage, keep simultaneity, use Conversion, definitional cancel) |
| `RuleRepairs-TyPeelR-CancelR.md` | the proposed repairs to those two rules, before/after, run on the breaking examples |
| `BoundaryRules.md` | the earlier decision memo on boundary-manipulation rules (v1-era) |
| `DualLicenseDesign.md` | the v1 dual-conceal licence, fully ruled (v1-era) |
| `PreservationEndgame.md` | the v1 preservation endgame plan (v1-era) |
| `ParameterizedCastCalculi.md` | digest of Siek & Chen, *Parameterized Cast Calculi and Reusable Meta-theory for Gradually Typed Lambda Calculi* (JFP 31(e30), 2021) — the source of the active/inert methodology |
| `Zdancewic-embeddings.md` | digest of Zdancewic, Grossman & Morrisett, *Principals in Programming Languages* (ICFP'99) |
| `SyntacticTypeAbstraction.md` | digest of Grossman, Morrisett & Zdancewic, *Syntactic Type Abstraction* (TOPLAS 22(6)) |
| `TypeAbstractionComparison.md` | the FINAL design set against the polymorphism of Grossman, Morrisett & Zdancewic, *Syntactic Type Abstraction* (TOPLAS 22(6)) — centred on **tightness**: they have no out-of-scope type variable, and §8 shows why weak reduction is what buys them that |
| `old/notes-v1.md` | the **refuted** v1 design note |
| `old/PLAN-v1.md` | the v1 plan, retired with the invariant hunt |

`notes/` now holds **`.md` only**.  The v1 Agda probes that accompanied
`old/notes-v1.md` (the retired v1 `Reduction`/`Terms`/`Typing` and fifteen
probe and scratch files) imported v1 modules — `strong.Context`,
`strong.Boundary`, `strong.BReduction`, `strong.Weakening`,
`strong.Unfold` — and so could not type-check on this branch at all.  They
were **deleted** (2026-09-06); they are preserved on `main`, the v1 tree,
at commit `c5db9f59` under `SystemF/agda/strong/notes/old/`, where they
compile.

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
