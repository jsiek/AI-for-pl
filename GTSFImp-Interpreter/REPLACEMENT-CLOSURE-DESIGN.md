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

## Revisions found while planning the implementation (2026-08-24)

Revision 1 (Kripke families).  The family must quantify over futures
at storage time: a value lifted to a future world must be wrappable
at the future world's *new* dynamic slots, which a per-world family
cannot cover, and repairing it inside the future-closure lemma would
make `Closure` depend on the reveal machinery (a module cycle).  The
stored component is therefore

    ∀ {W′} (W≼W′ : Future W W′) {Bᴾ′}
      (σ : UniWraps W′ (liftPreciseBody W≼W′ Bᴾ) Bᴾ′)
    → RightUniversalsRelated W′
        (liftCenterDynamicBodyImprecision W≼W′ p)
        Bᴾ′ (liftImpreciseTy W≼W′ Bᴵ) k
        (liftImpreciseTerm W≼W′ Vᴵ)
        (wrapTerm σ (liftPreciseTerm W≼W′ Vᴾ))

Future closure then composes futures, and the `(future-refl, [])`
projection is definitionally the old chain.

Revision 2 (Finding F — the `∀⊑∀` entries are unstateable).  A family
entry for a `∀⊑∀`-related pair with a precise-only (dynamic or inert)
wrapper has heads relating an *unwrapped imprecise application* to a
*wrapped precise application*.  Their joint evaluation starts with a
precise-only β of the wrapper at the real instantiation type `Sᴾ`,
allocating a precise name bound to `Sᴾ` with no imprecise partner
allocation (the imprecise application steps by whatever the abstract
imprecise value dictates, and pairing its step with the wrapper β
produces instead an inner precise application at the paired fresh
name, whose own bind is an alias of a paired name).  Neither
intermediate world is classifiable: dynamic atoms require `⊑ ★`
representative imprecision, paired atoms require the imprecise
allocation, and there is no atom kind for a precise-only allocation
at non-`★` imprecision.  Resolving this needs a world-model
extension (one-sided precise atoms at arbitrary representative
imprecision `embP Rᴾ ⊑ T`, generalizing dynamic atoms from `T = ★`),
plus, for the one-sided obligations at `∀⊑∀`, the imprecise
canonical forms already noted.  Step 4's `∀⊑∀` part is therefore
deferred; the family lands in the `∀⊑` clause only, and the four
obligations narrow to `∀⊑∀` sources.

Revision 3 (kit-based producer integration).  The family construction
needs the dynamic and one-sided computations statements, which are
obligation-parameterized, while the producers
(`proof/LR-narrow/Universal.agda`) and the compatibility layer are
not.  Rather than re-parameterizing that layer, the producers take a
*family kit* — a record of family builders whose type is
obligation-free — as an argument, mirroring the record pattern
already used by `proof/LR-narrow/FundamentalAssembly.agda`; the kit
value is constructed in the obligation-parameterized layer from the
generic `family-extend` lemmas and supplied at assembly time.

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

## Implementation log — step 2 landed (2026-08-24)

The clause change and every consumer rewrite are done and green
(commit "Store the replacement-closed family in the right-universal
clause"):

* `RightUniversalFamily` added to `LR-narrow/LogicalRelation.agda`
  (Kripke-indexed, per Revision 1) and installed as the chain
  component of the `∀⊑` clause;
* `LR-narrow/UniversalFamily.agda` defines the kit as a **record**
  (`RightUniversalFamilyKit` with field `to-family`);
* `proof/LR-narrow/Closure.agda` gained
  `right-universals-related-transport`,
  `right-universal-family-reindex` and
  `right-universal-family-future` (future composition), and the three
  `∀⊑` future-closure sites use them;
* `proof/LR-narrow/UniversalInstantiation.agda` projects the family
  at `(future-refl, [])`, which reduces definitionally to the old
  chain — as designed;
* the kit is threaded as an argument through the producer chain
  (`proof/LR-narrow/Universal.agda`, `proof/LR-narrow/Fundamental.agda`
  and their public wrappers); those exports are leaves, so the
  propagation stops there;
* `RevealObligations` gained a single new field
  `right-universal-family-kit`, used by the four `∀⊑` assemblies in
  `RevealStructural.agda` to turn their `heads` chains into families.

### Elaboration idioms discovered (needed for every family site)

1. **Eager implicit insertion.**  A family is a Π-type whose leading
   arguments are implicit, so an application `f a b` in a position
   expecting a family has its implicits inserted as metas and fails
   with `UnequalHiding`.  Every family-valued expression must be
   η-expanded: `λ W≼W′ σ → f a b W≼W′ σ`.
2. **Checking mode is required.**  The η-expanded lambda only gets
   its implicit lambdas inserted if the expected type is known, so
   family components must sit in checked positions — not in
   signature-less `let`/`where` bindings — and any step index the
   expected type depends on must be pinned (`{k = suc j}`).
3. **Non-injective type families.**  `RightUniversalsRelated`
   pattern-matches on the index, so unifying two of its applications
   never solves metas.  Every helper whose conclusion is one of them
   must receive `{W}`, `{p}`, `{Bᴾ}`, `{Bᴵ}`, `{k}` explicitly.

### Step 3 recipe (next session)

Discharging `blocked-dyn-reveal-universal` (and its three siblings)
is *not* a one-liner projection, because the obligation receives the
target derivation `q` rather than constructing it, and
`replace-⊑` — the lemma the paired dispatch uses to build the target
— requires paired mode `X⊑X`, which a dynamic slot does not have.
The workable route is to **match on both `p` and `q`** instead of
invoking `⊑-unique`:

* refute every shape whose precise endpoint is not a `∀`-type by
  `()` on `sourceᴾ` / `targetᴾ` (`embedPrecise (`∀ B₁)` is
  definitionally `∀`-headed, so the equations are absurd);
* `p = I.∀⊑ …`: the source carries a family; the wrapped value's
  family is `λ W≼W′ σ → fam W≼W′ (reveal-dyn d† _ ∷ σ)` with `d†`
  the lifted dynamic slot (`dyn-slot-future`), the term equality
  from `dyn-slot-precise-*-lift`, and the body-type equality from
  `liftPreciseBody-replace`.  Note `q` must still be analysed: with
  the same imprecise endpoint `Aᴵ` but a different precise endpoint,
  `q` may be `∀⊑`, `∀⊑∀`, `∀⊑★`, `∀★⊑★` or `bot⊑★`, so this case
  splits further; only the `∀⊑`/`∀⊑` combination is a projection,
  and the others need their own (mostly refutation) arguments;
* `p = I.∀⊑∀ …`: blocked by Finding F (no family is stateable);
* `p = I.∀⊑★ …` / `I.∀★⊑★`: the value is a dynamic payload pair, so
  the reveal must go through `RightDynamicPayloadRelated` — a
  separate argument, not a family projection;
* `p = I.bot-elim` / `I.bot⊑★`: refute via the bottom-value lemmas
  (they must be imported into `DynamicReveal`).

The same analysis applies to `blocked-dyn-conceal-universal` and,
with paired slots and a non-occurrence witness in place of the
dynamic slot, to `blocked-precise-reveal`/`-conceal`.

Once those land, the kit itself is provable (chain → family by
induction on σ, each step using the now-total computations wrappers),
and `RevealObligations` collapses to the Finding-F residue.

## Implementation log — step 3 landed (2026-08-24)

Step 3 is complete and green (commit "Discharge the universal wrapper
cases down to paired sources").  The step-3 recipe above was
simplified in three ways before implementation:

1. **No target analysis.**  The chain is phantom in its derivation
   index (`right-universals-phantom` transports with *no* endpoint
   equations), and the target derivation is forced by constructing a
   replaced alternative and transporting with
   `value-imprecision-reindex`.  The alternative is built by a new
   left-only replacement lemma
   (`replace-left-⊑` in `proof/LR-narrow/ReplaceImprecision.agda`):
   replacement of a variable on the left needs no mode premise, only
   that the variable avoids the right-hand side — which holds for
   dynamic slots because their center is skipped by the imprecise
   embedding (`dyn-embed-∉`).  Applied at the top derivation it
   reduces to constructor form, so the replaced clause computes.
2. **Value-level central helpers.**  Each of the four statements'
   `∀`-case delegates to one value-level helper
   (`precise-universal-value`/`-conceal-value` in `PreciseReveal`,
   `dyn-universal-value`/`-conceal-value` in `DynamicReveal`)
   dispatching on the source derivation: non-`∀` sources are refuted
   by the embedding equation, the bottom sources by
   `no-precise-bottom-value`, the star-universal sources recurse into
   the dynamic payload at the smaller index (the payload derivation
   is one of the same shapes, so the recursion is structural on the
   step index), the right-universal source projects the stored
   family, and only the paired universal source invokes the
   obligation.
3. **Ground un-replacement by refutation.**  The dynamic conceal at
   `∀⊑★` must transfer the payload shape's ground derivation from the
   replaced type back to the source type.  The key: the source's star
   premise pins the bound variable to the paired mode, so any
   `∀⊑`-shaped ground derivation — whose bound variable occurs, and
   occurrence reflects through replacement
   (`replaceTy-∈-reflect`) — contradicts `star-no-occurrence`.  What
   survives is `∀⊑∀` against the universal ground, rebuilt directly
   from the source premise (`conceal-shape-∀★`), and the bottom
   derivation, which survives replacement unchanged; the other
   grounds are refuted (`conceal-shape-⇒`/`-ι`,
   `⊑-var-right-nonvar`).

The obligations are now **value-level and `∀⊑∀`-only**: the four
blocked fields take `ValueImprecision W (I.∀⊑∀ p₀) k` (or produce
it, for the conceal direction), and the reveal development has no
other gaps besides the kit.

### Remaining (step 4 tail)

* Internalize the kit: `family-extend` (four wrapper kinds, each
  mirroring an existing assembly inner) built inside the statements
  construction from the now-total dynamic and one-sided computations
  statements, then `RevealObligations` shrinks to the four
  `∀⊑∀`-fields.  The construction is well-founded: the wrappers'
  computations recursions are type-fueled and their `∀`-cases are now
  projections, and the family is built by induction on the sequence.
* The `∀⊑∀` residue itself is Finding F (world-model extension) plus
  imprecise canonical forms — recorded in the plan.

## The `∀⊑∀` residue — path analysis (2026-08-24)

The four remaining obligations reduce to one construction: the chain
head for a pair whose precise side alone is wrapped, relating
`(Vᴵ ⦂∀ Bᴵ[Sᴵ], (Vᴾ ↑ ∀↑c) ⦂∀ B′[Sᴾ])`.  Tracing the joint
evaluation with the discharged machinery in view:

1. Pairing the imprecise application's β with the precise wrapper β
   lands in the ordinary paired bind world — the original Finding-F
   trace was overly pessimistic about this step.
2. Gap (i): the imprecise step witness for an abstract value — the
   canonical-forms gate.  Resolution: extend the families to the
   `∀⊑∀` clause, built per producer (each of the Λ-intro, the
   universal cast, and the reveal/conceal assemblies knows its
   imprecise value's step); alternatively a one-shot interpreter
   canonical-forms lemma (every imprecise universal value's
   application first-steps with a bind at the instantiation type).
3. Gap (ii), the true core: after the paired β the precise side holds
   the inner application at the fresh name.  Consuming it through the
   source chain head at the paired fresh names fails (application
   versus body on the imprecise side; contraction produces
   α-mismatched stores), and stepping it forces a precise-only bind
   whose representative is a paired name — Finding F exactly.  The
   model asymmetry is confirmed in the code: `TargetSemanticAtom`
   (imprecise-only allocations) carries no constraint at all, and
   *paired* aliases are already classifiable; only the one-sided
   precise alias is unrepresentable.

Ruled-out shortcuts, with reasons: phantom imprecise store entries
break positional naming; a name-versus-content simulation on the
precise side is false in a sealing calculus; making the precise
embedding a substitution (collapsing aliases) destroys the
injectivity inversions used throughout.

Two honest resolutions, both calculus-level:

* (a) Alias-transparent imprecision (recommended): `VarImp` becomes
  `VarImp Δ` with a third mode `X⊑ᵗ T` and one new leaf rule
  (`μ X ≡ X⊑ᵗ T → μ ⊢ T ⊑ B → μ ⊢ ＇X ⊑ B`).  The precise-only
  alias bind gets an atom at mode `X⊑ᵗ (embP R)`, the precise bind
  expansion gains an alias variant needing no `⊑ ★` derivation, and
  the `∀⊑∀` head closes through the producer's body relation.
  Uniqueness survives by mode disjointness; the narrowing
  isomorphism is unaffected (compile-time environments are
  alias-free).  Fallout is broad but mechanical: every mode analysis
  gains a case, plus the per-producer `∀⊑∀` families.
* (b) Substituting reveal β: change `β-reveal-∀`/`β-conceal-∀` to
  substitute the conversion instead of allocating the indirection.
  Eliminates the alias at the source, and with the `∀`-cases now
  projections no size regress returns — but when the slot variable
  occurs in the instantiation type the substituted conversion is not
  slot-generated, so the whole slot-wrapper machinery would need
  generalizing, on top of operational-semantics and type-safety
  surgery.  More elegant, worse fallout, and it changes the calculus.

Sequencing: internalize the kit first (orthogonal); then (a),
starting from the `VarImp Δ` core change, then the producer
families, then delete `RevealObligations`.

## Alias-transparent imprecision as fused transitivity (2026-08-24)

Refinement of resolution (a), prompted by the observation that some
versions of imprecision carry transitivity.

The connection is exact.  The alias variable is definitionally equal
to its representative's embedding `T` (store unfolding), so the alias
leaf

    μ X ≡ X⊑ᵗ T  →  μ ⊢ T ⊑ B  →  μ ⊢ ＇X ⊑ B

is the composite of an unfolding axiom `＇X ⊑ T` with an arbitrary
`T ⊑ B`: one transitivity step with a fixed left leg.  With a
transitivity rule and that single axiom the alias rule is derivable;
fusing the composite into one syntax-directed leaf is the standard
move in the other direction, and the right one here, because a
transitivity rule destroys derivation uniqueness (`⊑-unique`), on
which the whole reveal development leans, whereas the fused leaf
keeps derivations unique by mode disjointness.  Since the left leg is
definitional unfolding rather than a proper imprecision step, what
the alias needs is only "transport along store equality" — much
weaker than full `⊑`-transitivity, which is itself delicate in this
judgment (mode-environment composition, the `∀⊑` side conditions;
GTSFImp has `⊑-unique` and no `⊑-trans`, while the developments that
do have composition — GTSF's quotiented term imprecision, the
EndpointMLB factorization — pay for it with quotients or
factorization machinery).

The world model already fuses such composites at leaves; the alias
atom completes the pattern uniformly:

* paired atom: name ≐ `Rᴾ` left, name ≐ `Rᴵ` right,
  `embP Rᴾ ⊑ embI Rᴵ` stored aside; leaf `＇Z ⊑ ＇Z`;
* dynamic atom: name ≐ `R` left, nothing right; the leaf `＇Z ⊑ ★`
  is the fused composite "unfold to `embP R`, then `R ⊑ ★`", with the
  star premise stored once in the atom (`dynamicRep-related`);
* alias atom: the same with `T ⊑ B` for arbitrary `B` — the existing
  `X⊑★` mode is the `B = ★` special case (unification is possible
  but adding a third mode is less invasive than reshaping every
  `X⊑★` match).

Consequences: the leaf's metatheory should be developed as
"closure under unfolding" (occurrence up to unfolding;
`replace-left-⊑` at an alias substitutes exactly the premise), and
the first theorem to formalize is conservativity: substituting
unfoldings away maps extended derivations to current ones, and
compile-time environments are alias-free, so the paper-level
judgment is untouched.

### Correction: transitivity is admissible, so do not fuse

The fusing above was justified by the claim that a transitivity rule
would destroy derivation uniqueness.  That premise is wrong for this
judgment: GTSFImp imprecision is transitive *as a theorem* —
`⊑-trans` in `GTSFImp/ImprecisionComposition.agda` (upstream PR #186,
merged 2026-08-25), a plain structural function with no side
conditions, no postulates and no pragmas, over a fixed `μ`.  Being
admissible it adds no derivations, so it coexists with `⊑-unique`
(indeed uniqueness makes `⊑-trans` canonical: any two ways of
composing agree, which is what the reveal development needs when it
composes derivations across world stages).

Consequently the fused rule is unnecessary.  The extension reduces to
the **minimal unfolding axiom**, with no derivation premise at all:

    μ X ≡ X⊑ᵗ T  →  μ ⊢ ＇X ⊑ T

and the general alias statement `μ ⊢ ＇X ⊑ B` is then a *theorem*,
`⊑-trans` of that leaf with `T ⊑ B`.  This is strictly better:

* every structural case analysis (`star-no-occurrence`,
  `replace-⊑`, `replace-left-⊑`, `⊑-unique`, the vacuity lemmas,
  renaming and substitution) gains a **leaf** case rather than a
  recursive one;
* the leaf's conclusion is fixed by the mode, so it can overlap only
  with the *unguarded* `X⊑X` leaf, and only for a cyclic alias
  (`μ X ≡ X⊑ᵗ (＇ X)`); `X⊑★` is mode-disjoint.  The uniqueness
  repair therefore narrows to that one case — guard `X⊑X` with
  `μ X ≡ X⊑X`, or keep alias environments acyclic, which the world
  model's allocation order already gives;
* the semantic atom stores no derivation at all (contrast
  `dynamicRep-related`): the mode carries `T`, and anything else is
  computed with `⊑-trans` on demand.

Transitivity does **not**, however, remove the need for the leaf.
The missing fact is `＇X ⊑ ＇c` (alias against the paired centre it
aliases), and composition cannot reach it: the only rules with a
variable on the left are `X⊑X` and `X⊑★`, so a middle `M` with
`＇X ⊑ M` must be `＇X` or `★`; and `★ ⊑ ＇c` is underivable because
`★` is maximal (only `★⊑★` has `★` on the left).  So the leaf is
genuinely new information — transitivity refines *how much* is added,
not *whether*.

Note also that `X⊑★` cannot simply be re-expressed as
`X⊑ᵗ T` plus `T ⊑ ★`: `instᵐ` uses `X⊑★` for the `∀`-elimination's
bound variable, which has no representative.  The three modes —
paired, unconstrained, alias — stay genuinely distinct.

### Effect on the narrowing/widening isomorphism

`NarrowWiden` gives polarized presentations with derivation
isomorphisms `Widening μ A B ≅ μ ⊢ A ⊑ B ≅ Narrowing μ B A`.

* The isomorphism survives by construction.  The alias leaf always
  unfolds the *precise* endpoint, and the polarized presentations
  keep that endpoint in a fixed role — the widening's source and the
  narrowing's target — including through the contravariant domain
  flips (`w-⇒` embeds a narrowing whose target is again the precise
  side).  So each presentation gains exactly one mirrored
  constructor —

      w-alias : μ X ≡ X⊑ᵗ T → Widening μ (＇ X) T
      n-alias : μ X ≡ X⊑ᵗ T → Narrowing μ T (＇ X)

  (premise-free, per the transitivity correction below; the general
  polarized forms follow from transitivity, which transfers to the
  polarized systems through the existing isomorphism)

  — and the derivation isomorphism extends one case per direction,
  commuting with the unfolding erasure, so the isomorphism theorem
  itself remains conservative over the alias-free fragment.  The
  narrowing reading is the semantically self-evident one: a type
  narrows to a runtime name exactly by narrowing to what the name is
  bound to — the operational name-versus-content intuition that
  generated the alias problem in the first place.
* The real pressure is on uniqueness and determinism, not the
  isomorphism.  The identity-variable leaves (`X⊑X`, `w-idˣ`,
  `n-idˣ`) are currently unguarded, so a cyclic alias environment
  (μ X ≡ X⊑ᵗ (＇ X)) would give two derivations of `＇X ⊑ ＇X`
  (the identity leaf, and the alias leaf around it), breaking
  `⊑-unique` and the determinism of the polarized systems (a known
  pressure point — GTPLC records a narrowing/widening determinism
  counterexample).  Two repairs: (i) guard the identity-variable
  leaves with `μ X ≡ X⊑X`, making all variable leaves mode-disjoint
  and uniqueness syntactic again — mechanical fallout at every
  `X⊑X` use; or (ii) restrict to well-founded alias environments
  (allocation-ordered, which the world model already guarantees via
  `dynamicFresh`) and prove uniqueness under that invariant.  The
  logical relation only ever produces (ii)'s environments, but (i)
  is the cleaner metatheory.
* The one LR-side consumer of the isomorphism
  (`narrowing→imprecision` in `LogicalRelation`) is applied to
  compile-time derivations, which are alias-free — unaffected.

## Implementation log — kit removed from the reveal development
(2026-08-25)

Internalizing the kit turned on a structural question: the kit was
being used *inside* the statements it would have to depend on, so
proving it in place was circular.  The circularity is removed by
building the assemblies' families by **precomposition** instead:

* `UniWrap`/`UniWraps` now act on **both** endpoints (four indices:
  source and target precise body, source and target imprecise type),
  with `wrapTermᴾ` and `wrapTermᴵ`.  This was forced: the assemblies'
  target values are wrapped on the imprecise side too, so a
  precise-only sequence cannot express them.  The six constructors
  are reveal/conceal at a paired slot (both endpoints), at a dynamic
  slot (precise only) and at an inert paired slot (precise only, with
  the non-occurrence witness).  `PairedSlot` and its accessors moved
  to `LR-narrow/SlotSequence.agda` beside `DynamicSlot`, re-exported
  from `RevealLifting`/`SlotLifting` so downstream imports are
  unchanged.
* `reveal-paired-family` and `conceal-paired-family`
  (`RevealStructural.agda`) build the wrapped value's family by
  precomposing the source value's stored family with the paired
  wrapper, transporting along the lift/replace commutations
  (`liftPreciseBody-replace`, `replace-imprecise-lift`) and the term
  commutations (`lifted-reveal-precise`/`-imprecise`,
  `lifted-conceal-precise`/`-imprecise`).  Phantomness of the chain
  in its derivation index (`right-universals-phantom`) does the rest.
* The two *absent* assemblies need no new machinery at all: their
  targets are wrapped on the precise side only, which is exactly what
  `precise-universal-value`/`precise-universal-conceal-value`
  already produce, so their whole `at-every-index` collapses to one
  call plus a `⊑-unique`-style reindex.

Consequently **`RevealObligations` no longer mentions the kit**: the
record is now exactly the four value-level `∀⊑∀` fields, all of them
Finding-F.  The reveal development is free of the kit.

### What is left of the kit

`RightUniversalFamilyKit` survives only as an explicit argument of
the *producers* (`proof/LR-narrow/Universal.agda` and
`proof/LR-narrow/Fundamental.agda`), where the `Λ` introduction must
supply a family for a value it built itself.  Discharging it needs
the six one-step extensions in chain form:

    endpoints + chain for (Vᴵ, Vᴾ) at (B, C)
      → chain for (wrapTermᴵ₁ w Vᴵ, wrapTermᴾ₁ w Vᴾ) at (B′, C′)

plus induction on the sequence, in a new module after
`RevealStructural` that draws `Below` from the completed
`statements-all` (no circularity remains, since the statements no
longer mention the kit).

The raw material already exists and typechecks: the paired
extensions are precisely the `heads` of `reveal-right-universal` /
`conceal-right-universal` (with `reveal-right-universal-head`/
`-inner` and their conceal duals), and the dynamic and inert
extensions are the `[]`-projections of `dyn-universal-value` and
`precise-universal-value`.  Those functions are currently unused by
the assemblies — they were kept deliberately for this purpose.  The
one restatement needed is to take endpoints-plus-chain rather than a
full value relation, since a bare chain carries no endpoints.

## Implementation log — the six extensions (2026-08-26)

All six one-step chain extensions are **proved and green**
(`proof/LR-narrow/UniversalFamilyKit.agda`):
`reveal-paired-chain`, `conceal-paired-chain`, `reveal-inert-chain`,
`conceal-inert-chain`, `reveal-dyn-chain`, `conceal-dyn-chain`.

Supporting work that landed with them:

* the universal wrapper *heads* were restated on a bare instantiation
  chain — a small record `RightUniversalData` (the `∀⊑` clause tuple
  with the family replaced by a chain, plus the endpoint typings), so
  they no longer presuppose the family they are used to build.  The
  `with`-preambles that re-derived the chain's body types from the
  clause disappeared, since the record already fixes them;
* two entirely new head/inner pairs for the dynamic slot,
  `reveal-dyn-universal-head`/`-inner` and
  `conceal-dyn-universal-head`/`-inner`, adapted from the absent
  (one-sided) variants but with the body wrapper at the lifted
  dynamic slot (`dyn-revealed-computations` /
  `dyn-concealed-computations`) and the body derivation replaced by
  `replace-left-⊑`;
* the inert wrappers were weakened to carry the *precise*
  non-occurrence `slotXᴾ s ∉ᵗ `∀ B` rather than the centre fact
  `center s ∉ᵗ Bc`.  This was forced: the producer of inert entries
  (`precise-universal-value`) only has the precise fact, and the
  centre fact does not follow from it.  The absent heads needed the
  precise fact anyway, so they got simpler;
* the endpoint helpers (`revealed-endpoints`, `concealed-endpoints`,
  `dyn-reveal-endpoints`, `dyn-conceal-endpoints`,
  `precise-reveal-endpoints`, `precise-conceal-endpoints`) now take
  `TypedEndpoints` instead of a full `ValueImprecision`, since that
  is all they ever used.

## Finding G — conceal wrappers must carry their target derivation

Assembling the extensions into `to-family` (iterate along the
sequence, then project) hits a genuine obstruction, not bookkeeping.

Each extension step must hand the next step a derivation at the
wrapped types, because the heads build the *body* imprecision
derivation from it (`liftCenterDynamicBodyImprecision p₀`, then
`t₀`).  For a **reveal** wrapper that derivation is constructible —
`replace-⊑` at a paired slot, `replace-left-⊑` at a dynamic slot,
and the identity for an inert one.  For a **conceal** wrapper it
would have to be *un*-replaced, and un-replacement is false:

    take B = ＇(suc X) with X the slot variable and R = ‵ι, so
    replaceTy (suc X) (⇑ᵗ R) B = ‵ι.  Then
    `∀ ‵ι ⊑ ★` is derivable (∀⊑★), but `∀ ＇(suc X) ⊑ ★` is not:
    ∀⊑★ would need `extᵐ μ ⊢ ＇(suc X) ⊑ ★`, i.e. mode `X⊑★` at a
    variable whose mode is the paired `X⊑X`.

So the conceal constructors of `UniWrap` must carry the imprecision
derivation of their *target* body, alongside its `NonVar` and
occurrence witnesses — data that every consumer of a conceal entry
already has (it is the derivation of the clause it is producing), but
that cannot be recovered from the wrapper's types alone.  That is the
next step: widen the three conceal constructors, thread the extra
fields through the three conceal consumers (`conceal-right-universal`,
`precise-universal-conceal-value`, `dyn-universal-conceal-value`),
and then the iteration and `to-family` are pure bookkeeping.

## Implementation log — the kit is discharged (2026-08-26)

`universal-family-kit : RightUniversalFamilyKit` is **proved**
(`proof/LR-narrow/UniversalFamilyKit.agda`), and
`right-universal-value-compatible` there is the `Λ` introduction with
the kit supplied, so the producers no longer carry it as a
hypothesis.  No postulates, no new pragmas.

Finding G was resolved by widening the wrappers, which are our own
definition (`LR-narrow/SlotSequence.agda`), not part of the GTSFImp
calculus.  Rather than only patching the conceal cases, every wrapper
now carries a `BodyImprecision` for the bodies it *produces* — the
clause data (`NonVar`, the zero occurrence, and the centre
imprecision) that a `∀⊑` clause records.  Every consumer already has
it, since it is the data of the clause it is building, and carrying
it uniformly also spared the reveal wrappers from rebuilding their
target derivations with `replace-⊑` / `replace-left-⊑`.

Three refinements made the assembly go through:

* **Canonical embeddings.**  `BodyImprecision` fixes its centre types
  as `embedPreciseBody W B` and `embedImprecise W C` instead of
  carrying them existentially with equations.  With the existentials,
  two data for the *same* bodies had propositionally-but-not-
  definitionally equal centre types, which broke the one-sided
  endpoint helpers (they require the two derivations to share an
  imprecise endpoint).  Canonical form makes those equations `refl`.
  `body-imprecision-of` rebuilds the record from a clause's own
  equations, and `body-imprecision-future` transports it to a future
  world.
* **Shapes, not value witnesses.**  The paired wrappers need the
  imprecise conversion to be a value.  Carrying the `RevealValue` /
  `ConcealValue` witness fails, because it is not stable under
  renaming: a `ConcealValue` at a variable type is a `seal`, which
  becomes an identity once the slot changes.  The wrappers carry a
  `UniShape` (function or universal) instead, from which both
  witnesses follow and which lifts along futures trivially.
* **Inert steps keep the incoming data.**  For the inert wrappers the
  bodies are unchanged, so the step reuses the incoming
  `BodyImprecision` and transports the chain along
  `replaceTy-absent`; using the carried one would have demanded that
  two derivations of the same statement be definitionally equal.

The iteration is then `extend-wraps`, a fold of `extend-wrap` along
the sequence, and `to-family` lifts the data to the demanded future
(`data-future`), folds, and projects the chain — transported to the
family's own derivation by `right-universals-phantom`, which is
sound precisely because the chain is phantom in its derivation.

**State of the development.**  `RevealObligations` is now exactly the
four `∀⊑∀` fields, all of them Finding F; every other universal
statement is proved, and the replacement-closure programme is
complete.

## Alias-transparent imprecision — validated core, staged plan
(2026-08-26)

The extension was implemented in the core and typechecked there, then
reverted so the shared calculus stays green: completing it is a
multi-session refactor of GTSFImp, and the tree cannot sit red in the
meantime.  What the attempt established:

### The rule must be the fused one after all

The earlier "do not fuse" correction was itself wrong on one point.
The minimal unfolding axiom `μ X ≡ X⊑ᵗ T → μ ⊢ ＇X ⊑ T` is **not
closed under transitivity**: `⊑-trans (unfold eq) q` would have to
produce `＇X ⊑ C`, which the axiom only yields when the mode records
`C` rather than `T`.  So keeping the upstream `⊑-trans` true *forces*
the fused rule

    alias : μ X ≡ X⊑ᵗ T  →  μ ⊢ T ⊑ B  →  μ ⊢ ＇X ⊑ B

which is closed by `⊑-trans (alias eq p) q = alias eq (⊑-trans p q)`.
Transitivity's role is thus the opposite of what the correction said:
it does not let us shrink the rule, it pins the rule's shape.  With
modes being constructors of `VarImp`, the three variable leaves are
mode-disjoint, so `⊑-unique` survives with **no** acyclicity side
condition and the unguarded `X⊑X` leaf can stay as it is.

### The core change (typechecked)

`VarImp` becomes context-indexed, with a weakening, and `extendᵐ`
weakens the modes it shifts:

    data VarImp (Δ : TyCtx) : Set where
      X⊑X : VarImp Δ ; X⊑★ : VarImp Δ ; X⊑ᵗ : Ty Δ → VarImp Δ
    ⇑ᵛ : VarImp Δ → VarImp (suc Δ)
    extendᵐ v μ (suc X) = ⇑ᵛ (μ X)      -- was: μ X

Because `extᵐ μ (suc Z)` no longer reduces to `μ Z`, every mode
equation crossing a binder needs transport.  Four one-line lemmas
suffice and were proved: `ext-mode-paired`, `ext-mode-star` (by
`cong ⇑ᵛ`) and their inverses `ext-mode-paired-inv`,
`ext-mode-star-inv` (by casing on the mode; the alias mode never
lifts to a paired or dynamic one).

### Remaining work, and the obstacle class that makes it non-mechanical

* ~87 exhaustive matches on `_⊢_⊑_` (48 in GTSFImp, 39 in the
  interpreter) each need an `alias` case, most of them recursive.
* ~111 `VarImp` signatures need the context index — in world-lifting
  operations the mode belongs to the *extended* context
  (`VarImp (suc Δ)`).
* The genuinely non-mechanical part: existing metatheory whose
  hypotheses mention only the dynamic mode.  `⊑-env-mono`
  (`proof/DGG/WorldDecay.agda`) maps a derivation along
  `∀ Z → μ Z ≡ X⊑★ → μᵈ Z ≡ X⊑★`, which says nothing about aliases
  and so becomes *false* at the new leaf; it needs the extra premise
  `∀ Z T → μ Z ≡ X⊑ᵗ T → μᵈ Z ≡ X⊑ᵗ T`, and each of its four users
  must supply it.  Expect a handful of similar strengthenings —
  every lemma that abstracts over an environment change is a
  candidate.

Suggested staging: (1) core plus the four transport lemmas; (2) the
`VarImp` index across world constructions; (3) the `alias` cases in
GTSFImp, strengthening environment-change hypotheses as they surface,
to a green `GTSFImp/All.agda`; (4) the same in the interpreter, ending
with the LR clause and the alias atom; (5) the alias bind expansion
and the `∀⊑∀` head, discharging the four obligations.  Steps 1–2 are
done and reproducible from this note; the branch was reverted only to
keep the tree green.

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
