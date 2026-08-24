# Replacement-closed universal clauses — design note

Status: design (2026-08-24), not yet implemented.  This is the
resolution design for Finding E (see FUNDAMENTAL-PROPERTY-PLAN.md):
the termination obstruction in the dynamic-slot universal reveal, and
the canonical-forms obstruction in the one-sided universal reveal.

## Idea

A value related at a universal imprecision (`∀⊑∀` or `∀⊑`) stores not
just the instantiation chain for its own body type, but a *family* of
chains: one for every finite sequence of slot-conversion wrappers
applied to the (precise) value.  Revealing or concealing such a value
at a dynamic slot — the operation that today has no well-founded
reconstruction — becomes a *projection* from the stored family, plus
syntactic endpoint fixups.

The regress of Finding E is grounded because the families of the
*result* values of a chain head are stored in their own clauses,
which exist by the global induction of the fundamental lemma (on
typing derivations and the step index), not by any local recursion.

## Validated structural facts (checked against the code)

1. `UniversalsRelated` and `RightUniversalsRelated` are phantom in
   their derivation index `p`: the heads mention only
   `(W, Bᴾ, Bᴵ, k, Vᴵ, Vᴾ)`.  Family entries therefore need no
   per-descendant derivations.
2. In `RightUniversalsRelated` heads, the imprecise term is the bare
   lifted value — the imprecise side never steps.  Hence the family
   construction for `∀⊑` is *generic* (see below).
3. The producers of `∀⊑∀`-clauses each know their imprecise value's
   application step syntactically: the Λ-intro
   (`universals-related-from-body`, both sides `Λ`), the universal
   cast (`proof/LR-narrow/Cast.agda` ~4900, cast-β), and the
   reveal/conceal assemblies (β-reveal-∀ / β-conceal-∀).  The only
   producers of `∀⊑`-clauses are the Λ-intro
   (`right-universals-related-from-body`) and the assemblies.
4. `DynamicSemanticAtom` is public (`LR-narrow/Atoms.agda`), so the
   sequence datatype below is definable on the LR side; only the
   `DynamicSlot` view (10 lines, currently proof-side) needs to move
   or be duplicated publicly.

## The sequence datatype

IMPLEMENTED (2026-08-24): `LR-narrow/SlotSequence.agda`, which also
now publicly hosts `DynamicSlot` (moved from
`proof/LR-narrow/RevealStatements.agda`, which re-exports it).

The sequences are indexed by the *bodies* of the universal types they
act on; the wrapper's type argument is always the universal type:

    data UniWrap (W) : Ty (suc Δᴾ) → Ty (suc Δᴾ) → Set where
      reveal-dyn  : (d : DynamicSlot W) (B : Ty (suc Δᴾ))
        → UniWrap W B
            (replaceTy (suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B)
      conceal-dyn : (d : DynamicSlot W) (B : Ty (suc Δᴾ))
        → UniWrap W
            (replaceTy (suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B) B
      reveal-inert  : (X R B) → X ∉ᵗ `∀ B → UniWrap W B B
      conceal-inert : (X R B) → X ∉ᵗ `∀ B → UniWrap W B B

    UniWraps W B C  -- composable sequences (innermost first), with
    wrapTerm : UniWraps W B C → Term Δᴾ → Term Δᴾ
    _++ˢ_    : composition, for the tail projection

Body-indexing is a correction found while typechecking the skeleton:
sequences indexed by whole types do NOT stay universal-headed — a
`conceal-dyn` whose type argument is a *variable* body with a
universal representative conceals a universal type into a variable
type, leaving the family's domain.  Fixing the wrapper's type
argument to `` `∀ B `` makes every step body-to-body by construction.

The two dynamic kinds serve `blocked-dyn-reveal-universal` and
`blocked-dyn-conceal-universal`; the two inert kinds (arbitrary
variable with a non-occurrence witness — subsuming the paired-slot
case) serve `blocked-precise-reveal`/`-conceal`.

## The clause change

In `LR-narrow/LogicalRelation.agda`, the chain component of the
`∀⊑∀` clause becomes (and `∀⊑` mutatis mutandis, with `Bᴵ` unbound):

    Σ[ Bᴾ ] Σ[ Bᴵ ]
      (embedPrecise (core W) (`∀ Bᴾ) ≡ `∀ Aᴾ)
      × (embedImprecise (core W) (`∀ Bᴵ) ≡ `∀ Aᴵ)
      × (∀ {Bᴾ'} (σ : UniWraps W Bᴾ Bᴾ')
          → UniversalsRelated W p Bᴾ' Bᴵ (suc k)
              Vᴵ (wrapTerm σ Vᴾ))

The old chain is the `[]`-entry, so existing consumers
(`UniversalInstantiation`, the paired dispatch, `Closure`) project
`[]` — a mechanical rewrite of destructuring sites.  Entries are at
the same index (the wrappers are precise-only, index-preserving),
which the same-index dynamic-seal design (Finding D) already
accommodates; the LR's termination pragma argument is unchanged (the
family adds a quantifier, not a recursion).

## Why the regress is grounded

The generic one-step lemma (`family-extend`, per wrapper kind):

    chain of V at Bᴾ  →  chain of (wrapTerm [w] V) at (action w Bᴾ)

is proved exactly like the existing reveal/conceal inners: expand the
precise β (`related-precise-bind-step-expand`, index-preserving),
instantiate V's given chain head at the fresh dynamic name `＇0`, then
apply the computations-level wrappers (`dyn-revealed-computations`
etc.) at the body and fresh types.  The critical difference from
today: the value-level universal cases *inside* those computations
wrappers — the plug-values steps at ∀-shaped subtypes, including the
whole fresh type when it is ∀-shaped — are projections from the
families stored in the clauses of the *returned values*, not
recursive reconstructions.  Those families exist because every
LR-related value carries one by definition.  So `family-extend`
terminates on the type-size fuel of the computations wrappers alone,
and the family of a value is built by induction on the sequence.

Storing the family is what breaks Finding E's regress: deriving
families on the fly from bare chains would recurse through result
values with no measure (the instantiation types are λ-bound), which
is exactly the refuted situation.

## Producer obligations

* `∀⊑` (right-universal): `family-extend` is generic (imprecise side
  inert), so a single lemma
  `family-of-chain : chain → ∀ σ → entry σ` (induction on σ) serves
  every producer; the Λ-intro and the assemblies keep their current
  `[]`-chain constructions and append `family-of-chain`.
* `∀⊑∀`: the head of a wrapped pair still steps the *imprecise*
  application, so the family cannot be built generically from the
  chain (an arbitrary related value's application step is unknown —
  the canonical-forms obstruction).  Instead each producer builds the
  family by the same σ-induction, using its concrete imprecise step
  (Λ-β for the intro, cast-β for the universal cast, β-reveal-∀ /
  β-conceal-∀ for the assemblies); the σ-step instantiates the
  σ-prefix entry at the fresh paired names `(＇0, ＇0, X⊑X)`,
  mirroring `conceal-universal-inner`.  Three producer sites, each a
  generalization of an existing inner from `[]` to `σ`.

## Consumer rewrites (the payoff)

* `DynamicReveal`'s universal case (both directions): project the
  `reveal-dyn`/`conceal-dyn` entry, fix up endpoints — discharging
  `blocked-dyn-reveal-universal`/`-conceal-universal`.  The dynamic
  statement then recurses on type fuel only, with ∀ non-recursive.
* `PreciseReveal`'s universal case: project the inert entries —
  discharging `blocked-precise-reveal`/`-conceal`.  This also
  dissolves the canonical-forms gate: the imprecise application step
  that the consumer cannot perform was performed by the producer.
* The obligation record `RevealObligations` becomes empty and can be
  deleted; the module parameters `ob` disappear.

## Closure lemmas

* Downward: pointwise (chains are downward-closed already).
* Future: lift a sequence along `W ≼ W′` (slots lift by
  `dyn-slot-future`/`EntryLift`; non-occurrence by `liftCenter-∉ᵗ`-
  style lemmas on the precise side) and commute `wrapTerm` with
  `liftPreciseTerm` (single-wrapper versions `lifted-reveal-precise`
  / `lifted-conceal-precise` exist).
* Reindex (`⊑-unique` fixups): unchanged pattern.

## Open risks

1. Volume: LR clause change + sequence module + closure lemmas +
   three producer upgrades + four obligation discharges.  Comparable
   to the Finding-D fallout, likely two to three sessions.
2. The inert-wrapper entries transport along `replaceTy-absent`;
   the with-abstraction pitfalls seen in the dispatch (context
   rewriting) will recur and need the established view/transport
   idioms.
3. The `∀⊑∀` producers' σ-induction at the cast site composes the
   cast-β with the wrapper βs; the expansion lemmas exist
   (`related-paired-bind-step-expand`) but the redex bookkeeping is
   the largest single proof.
4. The family quantifier puts `SlotWraps` (hence the dynamic-atom
   records) inside the LR clause; `Set₁` bookkeeping should be
   unaffected but must be confirmed early with a skeleton typecheck.

## Suggested implementation order

1. `LR-narrow/SlotSequence.agda`: datatype, `wrapTerm`, composition
   — DONE (this commit); lifting along futures remains.
2. Clause change + mechanical `[]`-projections at existing
   destructuring sites; get the tree green with families produced
   only where trivially possible (`family-of-chain` for `∀⊑` may
   land here if the generic proof goes through early).
3. `∀⊑` producers + `DynamicReveal`/`PreciseReveal` right-universal
   projections.
4. `∀⊑∀` producers (intro, cast, assemblies), then the paired
   projections, then delete the obligation record.
