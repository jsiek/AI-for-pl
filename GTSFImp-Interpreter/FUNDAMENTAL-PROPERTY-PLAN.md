# Fundamental property of the logical relation

This is the working goal and milestone record for the logical relation in
`GTSFImp-Interpreter/LR-narrow`. Update it when a milestone is completed or a
new proof obligation changes the route to the theorem.

## Current goal

Prove the fundamental property for every derivation of compiled term
imprecision:

```agda
fundamental :
  (d : forgetWorld W ∣ Γ ⊢² Mᴾ ⊑ Mᴵ ∶ p)
  → FundamentalProperty d
```

By the definition in `LR-narrow/TermRelation.agda`, this means constructing,
for every step index `k`, the open logical-relation judgment

```agda
CompiledTermRelation p k Γ Mᴾ Mᴵ
```

The final theorem must recurse over the complete
`proof.DGG.CastTermImprecision._∣_⊢²_⊑_∶_` derivation, cover every
constructor, and introduce no proof holes or new postulates.

## Current proof boundary

The LR infrastructure and many individual compatibility lemmas are checked.
In particular, the development has compatibility for variables, lambdas,
applications, constants, blame, primitives, ordinary paired and one-sided
casts, structural universal introduction, one-sided universal introduction,
and part of universal elimination.

The immediate obstruction is not the outer universal constructor lemma.
`universal-fundamental`, `right-universal-fundamental`, and
`right-universal-smart-fundamental` already consume the appropriate body
motives. The missing work is to construct those body motives recursively from
the body imprecision derivations.

The total theorem is assembled in
`proof/LR-narrow/FundamentalAssembly.agda` (checked 2026-08-23) on the
insertion-generalized motive `InsertedFundamentalProperty` of
`LR-narrow/Insertion.agda`. Its `Assembly.fundamental` recurses over every
CTI constructor below an arbitrary world insertion; the constructors without
a checked compatibility lemma are the fields of `RemainingObligations`, each
stated with the insertion-generalized induction hypothesis for its premises.
Closing the theorem means inhabiting that record by induction, not by
assumption.

Constructor coverage (25 CTI constructors):

| status | constructors |
|---|---|
| closed by checked lemma | `x⊑x²`, `κ⊑κ²`, `blame⊑²`, `ƛ⊑ƛ²`, `·⊑·²`, `⊕⊑⊕²`, `•⊑•²` at `∀⊑∀`, `•⊑²` at `∀⊑` |
| closed relative to `CastValueObligations` (Finding B) | `cast⊑cast²`, `⊑cast²`, `cast⊑²` |
| open (M1, steps 6–8) | `Λ⊑Λ²`, `Λ⊑²`, `Λ⊑²-smart-comma` |
| open (M2) | `⊑reveal²`, `⊑conceal²`, `reveal⊑²`, `conceal⊑²-seal-star-open`, `conceal⊑²-source-ok`, `reveal⊑reveal²`, `conceal⊑conceal²`, `packaged-seal-star²` |
| open (M3) | `•⊑•²` at `∀⊑`, `bot-elim`; `•⊑²` at `∀⊑∀`, `∀★⊑★`, `∀⊑★`, `bot-elim`, `bot⊑★` |

## Next milestones

### 1. Insertion-generalized fundamental recursion

Decision (2026-08-23): replace syntactic transport of body derivations by a
recursion motive generalized over a *center insertion* from the derivation's
syntactic world into the semantic world. Design in
`INSERTION-MOTIVE-DESIGN.md`. The induction hypothesis is then applied to the
literal premise in every case; the universal cases need only world-level
lifting of insertions, not derivation-level transport.

1. Define `WorldInsert ρᴾ ρᴵ π Wᶜ W′` in `GTSFImp/proof/DGG/WorldInsert.agda`
   (both-sided generalization of `TargetExtend.TargetInsert`), with
   transport of `_⊑ᵂ⟨_⟩_`, of `CtxImp`, and of context lookup.
2. Prove the lifting lemmas: an insertion `Wᶜ ↪ W′` lifts to
   `liftWorldBoth X⊑X Wᶜ ↪ bothBindWorld X⊑X W′ R R′`,
   `liftWorldLeft X⊑★ Wᶜ ↪ leftOnlyWorld X⊑★ W′ R`, and the smart-comma
   premise world; and insertions compose with LR `Future`s.
3. Define the generalized motive `InsertedFundamental` in
   `LR-narrow/TermRelation.agda`: for every semantic `W` and insertion
   `ins : Wᶜ ↪ forgetWorld W`, the open relation holds for the renamed
   endpoint terms, transported context, and transported type imprecision.
   The identity insertion recovers `FundamentalProperty`.
4. Restate the compatibility lemmas without derivation premises (typing
   premises where typing is needed: `lambda`, casts), so that they apply to
   renamed terms. `application` and `primitive` already ignore them.
5. Re-assemble `FundamentalAssembly` on the new motive for the non-binder
   constructors, then `ƛ⊑ƛ²`.
6. Prove reveal compatibility at a fresh paired center: values related at
   `B` in the bound extension give `V ↑ 〖 zero , ⇑R ↑ B 〗` related at
   `B [ R ]ᵗ ⊑ B′ [ R′ ]ᵗ`. No LR lemma treats `_↑_`/`_↓_` conversions yet;
   this is needed by every route to the universal body motive and is the
   core of Milestone 2's `reveal⊑reveal²`. Finding (2026-08-23): the fresh
   atom of a paired bind has an *arbitrary* relation (parametricity), and
   the reveal at `B = ＇0 ⇒ ＇0` seals the arguments, so this lemma holds
   only in the world whose atom at center `0` is the *canonical* atom
   (sealed payloads related at `R ⊑ R′`). Consequently:
   a. define the canonical paired atom from `r : R ⊑ᵂ R′`;
   b. prove reveal and conceal compatibility at center `0` in the
      canonical-atom world, by induction on `B`;
   c. prove atom irrelevance: relations at a derivation whose types do
      not mention center `0` are invariant under replacing the semantic
      entry at `0` (world-transformer induction over the value relation,
      comparable to the future-monotonicity proof in `Closure.agda`).
   The alternative is to change the LR's universal clauses to test only
   the canonical atom; that touches the LR definition, its recursion
   structure, `Closure.agda`, and every universal lemma, and forfeits
   parametricity. Decision (2026-08-23): keep parametricity; pursue a–c.
   Blocking finding (2026-08-23), found while designing 6a: semantic atoms
   are lifted to future worlds by `Atoms.weaken-semantic-atom`, whose
   relation is `LiftedRelation`, relating only *weakenings* of values from
   the allocation world. Hence in any future world a value of the fresh
   type `＇0` that mentions a later-allocated name is never atom-related,
   for every atom, canonical or not. The reveal at a negative occurrence
   of `＇0` seals arguments obtained in future worlds (rule
   `(V ↑ (c ↦↑ d)) · W —→ (V · (W ↓ c)) ↑ d`), so the body's function
   relation cannot be applied to them. Concrete non-derivable instance:
   the Church numeral `Λ λg λx. g x` at `∀ ((＇0 ⇒ ＇0) ⇒ ＇0 ⇒ ＇0)`
   instantiated at `★`, where `g` may return a `★` value carrying a name
   allocated during its own evaluation. The universal clause is
   semantically true for it but not derivable from the body relation.
   Required LR repair: make atom relations Kripke (indexed by the
   extension of the allocation world, e.g. by the endpoint OPEs or by a
   core insertion), with monotonicity in place of `LiftedRelation`;
   `weaken-semantic-atom` then precomposes the extension. This touches
   `Atoms.agda`, `World.agda`, `Closure.agda`, and the paired/dynamic atom
   constructions in `TypeApplication.agda`.
   Resolution (2026-08-23): a world-indexed atom is not definable
   (positivity), and an OPE-indexed one cannot express the canonical
   relation. Adopted instead: canonical slots. A paired slot records
   `(Rᴾ, Rᴵ, r)`; the `X⊑X` clause relates `Uᴵ ↓ seal` and `Uᴾ ↓ seal`
   exactly when the payloads are related at `r` one index lower, defined in
   the consulting world (Kripke by construction). Dynamic slots record
   `(Rᴾ, r★ : Rᴾ ⊑ ★)` likewise. The universal clauses quantify over
   representation pairs instead of atoms; parametricity is relative to
   LR-definable relations. Implemented and checked across the whole LR
   (`make check` passes); 6a is thereby done and 6c is unnecessary.
7. Close `Λ⊑Λ²`: lift the insertion under the binder
   (`WorldInsert.liftBoth-insert`, checked), instantiate the hypothesis at
   the canonical-atom test world, apply 6b, transfer by 6c to the
   observer's atom, and reconcile closing substitutions with type-body
   closing and future lifting.
8. Close `Λ⊑²` and `Λ⊑²-smart-comma` likewise (`liftLeft-insert`,
   checked; `X⊑★` reveal on the source side only; target unchanged); cover
   nested universals by composition of insertions. Do not treat
   `SmartCommaLiftᴸ` as semantic world transport: any alias-merged center
   must receive the LR semantic entry required by the body relation.

Status (2026-08-23): steps 1–5 are checked
(`GTSFImp/proof/DGG/WorldInsert.agda`, `LR-narrow/Insertion.agda`,
`LR-narrow/FutureInsertion.agda`,
`proof/LR-narrow/FundamentalAssembly.agda`), and 6a is subsumed by the
canonical slots. Step 2's smart-comma lift is deferred to Milestone 2:
`smart-merge-alias` embeds the fresh source variable at an existing target
center, which no OPE-embedded semantic world can represent after any
allocation, so it is a rebase; `smart-fresh-behind` only needs the center
map of `WorldInsert` generalized from an OPE to an injective renaming.
Note for step 7: composition of embeddings has no general law on cast
terms (`renameEnv∼` fills off-image variables differently for `empty` and
`skip`); only the weakening-step law `renameᵗᵐ-shift` holds and is used.

Step 6b status (2026-08-23): the atomic reveal cases are checked
(`proof/LR-narrow/RevealAtomic.agda`), and the generic evaluation-frame
machinery for the structural cases is checked and committed:
`proof/LR-narrow/FramePhases.agda` (abstract `Frame`, phase
decomposition and reassembly of returning/blaming runs),
`proof/LR-narrow/FrameComposition.agda` (paired, precise-only and
imprecise-only composition of an operand computation with a continuation
under a frame), and `proof/LR-narrow/RevealFrames.agda` (reveal and
conceal frame instances). The structural reveal/conceal lemma itself is
blocked by the following finding.

Finding A (blocking, needs a decision): the index-0 content of the LR
blocks the structural reveal lemma. `ComputationsRelated` quantifies over
`n ≤ k`, so at index 0 it still demands that the precise side terminate
whenever the imprecise side is a value, and `ValueImprecisionᵏ zero` for
`∀⊑` therefore carries `RightUniversalsRelated _ zero` (precise
instantiation terminates with results related at index 0). Frame
composition consults the continuation at index `k ∸ n`, which is 0 when
the operand consumes all the gas, so the reveal lemma needs its own
index-0 instance for values with `∀⊑` content. Unfolding that content for
`V ↑ `∀↑ c` requires the lemma again at the freshly bound slot for the
type `B₀[R/X]`, which is not smaller than `∀ B₀`; and at an unseal the
payload's content is unavailable at index 0 (the atom clauses only hold
one index lower). No well-founded measure was found (the ∀⊑-count of the
derivation fails because `∀⊑` also derives `∀ A ⊑ ★`, so substituting a
representation for a dynamic slot can re-create `∀⊑` nodes). Two ways
out:
  Resolution (2026-08-23): (a) adopted and checked (commit "Index the
  computation relation by strictly available steps"); `make check` passes.
  (a) Recommended: change `ComputationsRelated` to quantify over `n < k`
      (index = number of imprecise steps strictly available). Then
      returned pairs always sit at index ≥ 1, `ValueImprecisionᵏ zero`
      becomes `TypedEndpoints` uniformly, `RightUniversalsRelated _ zero`
      becomes trivial, and the reveal lemma goes through by strong
      induction on the index with the frame machinery. The gradual
      guarantee is unchanged (use index n+1 for an n-step run). Cost: a
      mechanical refactor of ~650 index-bound sites across
      `proof/LR-narrow` (Cast 109, CastComposition 101, Application 73,
      TypeApplication 65, Primitive 63, ...); most `k = zero` branches
      simplify to a trivial lemma.
  (b) Keep `n ≤ k` and prove syntactic termination of instantiation,
      cast, reveal and conceal chains on typed precise values (a
      coercion-normalization argument; needs a measure over values and
      consistency derivations including `inst`/`gen`, and canonical
      forms), then derive index-0 adequacy from typing. Estimated larger
      and more delicate than (a), and (b) still leaves the non-well-founded
      `∀⊑` clause at index 0 in the LR definition.

Finding B (pre-existing, independent of 6b): `proof/LR-narrow/Cast.agda`
contains three `{-# TERMINATING #-}` proofs that are circular, not merely
unrecognized recursions. `related-value-precise-cast` and
`related-value-imprecise-cast` supply themselves (at the same lifted
arguments) as the continuation of the one-sided cast composition; since
the operand is a value, the continuation is consulted on the same term with
the same gas, so evaluating `forward-return` would loop. `related-value-
casts` does the same through `related-value-casts-composed` for the cases
`∀⊑∀`, `⇒⊑★`, `ι⊑★`, `X⊑★`, `∀⊑`, `∀⊑★`, and for `⇒⊑⇒` with `!`/`gen`
casts (introduced in commit 73f1da81 in place of holes). These cases are
therefore not proven. Resolution (2026-08-23): the circular proofs were
removed; the open statements are the record `CastValueObligations` in
`LR-narrow/CastObligations.agda` (`precise-cast-values`,
`imprecise-cast-values`, and `paired-cast-values` restricted to the
enumerated `OpenPairedCastCase`), `proof/LR-narrow/Cast.agda` is
parameterized by it, and `RemainingObligations.cast-values` carries it into
the assembly. Genuine proofs need the cast to be decomposed by the cast
reduction rules (ground/expand/tag-untag/β-⇒/β-∀/inst/gen) with a
recursion on the consistency derivation, much as the `★⊑★` cases already
do. The remaining `TERMINATING` pragma on `related-value-casts` covers a
recursion that is well founded by (index, derivation) but passes through
the composition continuation; converting it into a checked well-founded
recursion is follow-up work.

Step 6b progress (2026-08-23, checked): the structural reveal and conceal
at a paired slot are proved for the fragment `RevealSafe` — the atomic
imprecision forms closed under function imprecision, plus the two bottom
forms — by strong induction on the step index, with no `TERMINATING`
pragma (`proof/LR-narrow/RevealStructural.agda`, 1.4k lines). Supporting
files: `proof/LR-narrow/RevealLifting.agda` (renaming and future-lifting
laws for `〖_,_↑_〗`, `makeConceal` and `replaceTy`; paired slots and
their transport along futures), `proof/LR-narrow/ConcealAtomic.agda`
(atomic conceal cases, including sealing at the slot's own variable),
`proof/LR-narrow/ArgumentFrame.agda` (the `V · □` frame and closed
application of related function values to related argument
computations). The function case decomposes `(V ↑ (c ↦↑ d)) · U` by
`β-reveal-⇒` into the concealed argument, the application, and the
revealed result, composed through the argument and reveal frames; the
conceal case is dual through `β-conceal-⇒`.

Finding C (open, blocks the universal case of 6b): `∀⊑∀` is deliberately
excluded from `RevealSafe`. The reveal of a universal value reduces by
`β-reveal-∀`:

    (V ↑ `∀↑ c) ⦂∀ B [ A ] —→[ bind A ]
      (⇑V ⦂∀ (bind A ▷ᵇ C) [ ＇ 0 ]) ↑ c ↑ 〖 0 , ⇑A ↑ B 〗

so the source value is instantiated at the *freshly allocated name*
`＇ 0` inside a world that has already allocated `A`, i.e. two
allocations. The LR's universal clause instead supplies the behaviour of
`liftV ⦂∀ liftC [ R ]` — one allocation, at the representation type `R`
chosen by the observer. Bridging the two needs a re-instantiation
property ("instantiating at a name bound to `R` behaves like
instantiating at `R`") that the LR does not have. Recommended repair:
restate `UniversalsRelated` (and `RightUniversalsRelated`) to quantify
over a *fresh paired slot in a future world* rather than over a
representation pair `(Rᴾ, Rᴵ, r)`. That is the same data the canonical
slots already record, it matches the reduction exactly, and it removes
the mismatch at the cost of re-proving the universal introduction and
elimination compatibilities against the new clause.

This milestone is complete when `RemainingObligations` no longer has body
motive fields and `Assembly.fundamental` closes the three universal
introduction constructors by recursion.

Superseded route, kept for reference: inhabit `SourceBindTransport²ᵀ` and
`BothBindTransport²ᵀ` via a source-side and a paired analogue of
`TargetExtend.⊢²-target-insert` (see
`GTSFImp/proof/DGG/notes/t4-d3-source-both-transport-gap.red`). Cost
estimate: `TargetExtend.agda` is 3.7k lines plus 1.2k in
`CenterRename.agda`; each analogue is comparable, and transported
sub-derivations would require height recursion.

### 2. Prove compatibility for the rebase-sensitive cast forms

Add open-term compatibility for the remaining reveal, conceal, and packaged
seal constructors:

- `CTI.⊑reveal²` and `CTI.⊑conceal²`;
- `CTI.reveal⊑²`;
- `CTI.conceal⊑²-seal-star-open` and
  `CTI.conceal⊑²-source-ok`;
- `CTI.reveal⊑reveal²` and `CTI.conceal⊑conceal²`;
- `CTI.packaged-seal-star²`.

These proofs must transport the semantic world consistently with each CTI
rebase and must preserve the occupied/unoccupied distinction used by the
`X⊑★` LR clauses.

### 3. Finish universal elimination

Complete the cases not covered by the current structural type-application
lemmas. The operator premise `p∀` of `CTI.•⊑•²` admits three constructors and
that of `CTI.•⊑²` admits six (`FundamentalAssembly.pairedView` and
`rightView` enumerate them):

- `CTI.•⊑•²` with `p∀` of the form `∀⊑` (a universal target is a legal `B`
  for `∀⊑`) or `bot-elim`;
- `CTI.•⊑²` with `p∀` of the form `∀⊑∀`, `∀★⊑★`, `∀⊑★`, `bot-elim`, or
  `bot⊑★`.

Some of these may be refutable from the CTI premises rather than proved; a
refutation is an acceptable inhabitant of the obligation.

Returned worlds must continue to factor through the paired extension selected
by the pre-allocation universal application observation.

### 4. Assemble the total fundamental theorem

The recursion exists as `Assembly.fundamental` in
`proof/LR-narrow/FundamentalAssembly.agda`. Instantiate `RemainingObligations`
with the results of Milestones 1–3, then state the public theorem in
`LR-narrow/Fundamental.agda` with its proof script in
`proof/LR-narrow/Fundamental.agda`. If the body inductions need the recursion
on transported derivations, merge the assembly into a single
height-indexed recursion at that point.

### 5. Validate the completed development

For each submilestone, run the narrowest relevant Agda check while developing.
Before declaring a milestone complete, run:

```text
git diff --check
make -C GTSFImp-Interpreter check
```

Also load `GTSFImp-Interpreter/LR-narrow/LRNarrowAll.agda` through Agda MCP.
The final check must find no unsolved metas, interaction holes, or new
postulates in the fundamental-property dependency closure. The only
permitted postulate is `funext` in `proof/LR-narrow/FunExt.agda`; the
Makefile has no `postulate-check` target yet, so scan with
`rg -n 'postulate|\{!' LR-narrow proof` and expect exactly that hit.

## Git policy

- Work on branch `codex/gtsf-big-dgg`.
- Its push target is the configured upstream
  `peterthiemann/codex/gtsf-big-dgg`.
- Commit this plan and the source changes that belong to the fundamental
  property. Commit each coherent, Agda-checked milestone or independently
  useful checked submilestone separately, with an imperative commit message.
- Include required proof support under `GTSFImp/proof/DGG` when it is part of
  the same checked milestone. Do not include unrelated user changes, scratch
  files, generated `.agdai` files, or other build artifacts.
- Push every completed milestone commit to
  `peterthiemann/codex/gtsf-big-dgg`. Do not push these proof-development
  commits to `main`, do not force-push, and do not rewrite published history.
- Do not merge or rebase `main` merely as part of a proof milestone. Integrate
  upstream changes only as a separately requested and separately checked
  operation.
- Any proposed change to the live CTI relation in
  `GTSFImp/proof/DGG/CastTermImprecision.agda` requires explicit user approval
  before editing it, following the repository's rule-change review policy.
