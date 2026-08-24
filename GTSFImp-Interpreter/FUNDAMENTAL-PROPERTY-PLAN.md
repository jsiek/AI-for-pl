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

Step 6b status (2026-08-24, checked): the fragment is gone and the
paired universal case `∀⊑∀` is closed. The reveal development is now
parameterized by an explicit obligations record
(`proof/LR-narrow/RevealStatements.agda`): the four statement families
(`RevealAt`, `ConcealAt`, `PreciseRevealAt`, `PreciseConcealAt`) are
bundled as `Statements` and proved together by one well-founded
induction on the step index; `RevealSafe` and `NoUniversal` are
deleted, and the still-open universal imprecisions — `∀⊑`, `∀★⊑★`,
`∀⊑★` (paired, via the `BlockedImprecision` view) and a universal
precise type in the one-sided reveal/conceal — are the four fields of
`RevealObligations`, each receiving `Below k` so a later proof can
recur through the same induction. The `∀⊑∀` case itself
(`proof/LR-narrow/RevealStructural.agda`): after `β-reveal-∀`/
`β-conceal-∀`, the source universal's `UniversalsRelated` head is
instantiated at the freshly allocated paired name `＇ 0` (its
representation imprecision is `X⊑X`, and
`open-shifted-body : renameᵗ (extᵗ suc) B [ ＇ 0 ]ᵗ ≡ B` identifies the
instantiated body), the post-bind relation is weakened, and the result
is wrapped by two paired reveal (resp. conceal-then-reveal)
compositions — the lifted old slot inside the body, then the fresh
slot, whose target equalities go through
`replace-zero-open : replaceTy 0 (⇑ S) B ≡ ⇑ (B [ S ]ᵗ)`. The
replaced-body imprecision is produced by `replace-⊑`
(`proof/LR-narrow/ReplaceImprecision.agda`: replacement at a
paired-mode variable preserves `⊑`), and the arbitrary target
derivation `q` of the dispatch is forced to the constructed
`I.∀⊑∀` form by `PI.⊑-unique`, so no case analysis on `q` is needed.
Value-level assembly (`reveal-universal`, `conceal-universal`) mirrors
the function case with a chain of `reveal-universal-head` /
`conceal-universal-head` applications. The scaffold note
`notes/universal-head-scaffold.agda.txt` is deleted (the hole is
filled in the build).

Finding C (superseded in part; revised 2026-08-23 after a closer
analysis, resolution architecture landed 2026-08-24 as described
above). Two separate things kept `RevealSafe` small; the earlier "two
allocations / re-instantiation" formulation of this finding was
imprecise and is superseded by what follows.

Universal cases status (2026-08-23). The four open forms are not four
independent tasks; they interlock, and two of them need machinery that
does not exist yet. What is checked so far
(`proof/LR-narrow/UniversalReveal.agda`): the evaluator's step at a
revealed or concealed universal value (`reveal-type-app-step-question`,
`conceal-type-app-step-question`), the fresh paired slot a type
application allocates (`fresh-slot`), the body-level lifting laws for
`replaceTy` (`liftPreciseBody-replace`, `liftImpreciseBody-replace`),
head extraction from a `UniversalsRelated` chain (`universals-head`),
and the weakening of a post-bind relation to a plain future relation
(`post-bind-weaken`). The `∀⊑∀` head's *statement*, its redex
equalities, and its paired bind-step expansion also check; that
scaffold is parked in `notes/universal-head-scaffold.agda.txt` (it is
not in the build because its body is still a hole).

Analysis of each form:

* `∀⊑∀` (paired). Feasible, and the largest single piece. After the
  paired `bind S` step, the source universal must be instantiated *at
  the freshly allocated name* — which the LR's clause supports, since it
  quantifies over arbitrary representation types and `＇ 0` is one; the
  price is one extra alias slot in the result world, which the
  `PostBindValueRelation` factorization tolerates. Remaining: an
  instantiation lemma for imprecision derivations (`subst-⊑` with the
  substitution `singleSubᵗ (＇ 0)`; the side condition is vacuous at the
  paired mode), the `＇ 0 ⊑ᵂ ＇ 0` witness, and two nested reveal
  compositions (old slot inside the body, then the fresh slot) with
  `PostBindValueRelation` on both sides — the generic frame composition
  already supports arbitrary `R`/`S`, and
  `computations-related-post-bind-compose` repackages the results.

* `∀⊑` (right universal). The precise endpoint does a *precise-only*
  allocation at a dynamic slot, which the LR can express
  (`preciseBindWorld`, `future-precise`), and the alias it then
  allocates is also dynamic, so it is expressible too. Missing: a
  generic precise-only bind-step expansion (only the `Λ`-specific
  `related-precise-type-beta-expand` exists), and a one-sided reveal at
  a *dynamic* slot — a development comparable to
  `proof/LR-narrow/PreciseReveal.agda`, but where the slot's variable
  does occur and the `X⊑★` clauses (`DynamicAtomHolds`,
  `AlignedDynamicAtomRelated`) drive the seal handling.

* `∀⊑★`, `∀★⊑★`. These reduce, through the tag clause
  (`RightDynamicPayloadRelated` at the ground `∀ ★`), to the *one-sided*
  reveal at a universal type — the case `NoUniversal` currently excludes
  from `proof/LR-narrow/PreciseReveal.agda`. There the imprecise
  endpoint carries no conversion, so only the precise endpoint takes the
  `bind S` step, and a precise-only allocation bound to a *paired*
  representation is not expressible: `future-precise` demands the slot
  be dynamic (`Rᴾ ⊑ ★`), while the fresh paired slot's centre has mode
  `X⊑X`. The way out is to step the imprecise endpoint as well — it is a
  type application of a value, so it is a redex — which needs canonical
  forms for imprecise universal values, plus a treatment of the `β-∀`
  case where the imprecise step is a `keep` step (a cast-wrapped
  universal peels one `∀ᶜ` per step, so the index does not decrease and a
  nested induction on the imprecise value is required).

Consequence (resolved 2026-08-24 by the obligations record): the
safety fragment (`RevealSafe`) and the `NoUniversal` restriction could
not be dropped one form at a time, because the universal reveal needs
the induction hypothesis at *arbitrary* imprecision forms (the body of
a universal is arbitrary, and the fresh slot's representation
imprecision is the observer's choice). Rather than landing all four
forms together, the whole development is parameterized by
`RevealObligations`, so `∀⊑∀` is closed unconditionally while `∀⊑`,
`∀★⊑★`, `∀⊑★` and the one-sided universal case remain as record
fields; the `∀⊑★`/`∀★⊑★` obstruction above is the gate for
discharging them.

C1 status (2026-08-23): `⇒⊑★` is closed. The one-sided ("identity
wrapper") reveal and conceal are proved for universal-free precise types
in `proof/LR-narrow/PreciseReveal.agda` by a lexicographic recursion on
(type size, step index); `proof/LR-narrow/StarNoOccurrence.agda` shows a
paired slot's center variable cannot occur in a type imprecise below `★`,
so the precise wrapper contains no unseal and `replaceTy` is the
identity; `proof/LR-narrow/SlotLifting.agda` holds the slot and frame
lifting laws now shared by the paired and one-sided developments. The
fragment `RevealSafe` therefore has a `safe-⇒⊑★` constructor carrying
`NoUniversal` for both components. Remaining: `∀⊑∀`, `∀⊑★`, `∀★⊑★`,
`∀⊑`, and lifting the `NoUniversal` restriction (which is exactly what
the universal cases would buy).

C1. The ★-target forms are asymmetric, not blocked. For `A ⊑ ★` the
imprecise structural conversion degenerates: `〖 X , R ↑ ★ 〗 = id↑ ★`
and `makeConceal X R ★ = id↓ ★`, so the imprecise side takes an identity
reveal step while the precise side reveals structurally (a function
conversion for `⇒⊑★`, a universal one for `∀⊑★`, `∀★⊑★`). The two
endpoints therefore no longer have matching shapes, and the result must
be re-established through the tag clauses: at `⇒⊑★` the value relation is
`RightDynamicPayloadRelated`, so the goal reduces to the (proved)
function case applied to the payload one index lower, then re-tagged.
The same holds for `∀⊑★`/`∀★⊑★` (needing the universal case first) and
for `∀⊑` (needing `RightUniversalsRelated`). These are genuine work, but
no new principle: expected order is `⇒⊑★`, then `∀⊑∀`, then `∀⊑★`,
`∀★⊑★`, `∀⊑`.

C2. The paired universal `∀⊑∀` propagates a safety requirement onto the
observer's representation. Revealing a universal value gives
`V ↑ `∀↑ 〖 suc X , ⇑R ↑ B₀ 〗`, and instantiating it at the observer's
representation `S` reduces by `β-reveal-∀` to

    (⇑V ⦂∀ ⇑B₀ [ ＇ 0 ]) ↑ 〖 suc X , ⇑R ↑ B₀ 〗 ↑ 〖 0 , ⇑S ↑ B 〗
      where B = replaceTy (suc X) (⇑R) B₀

i.e. two structural reveals in sequence: first the *old* slot in the body
type `B₀`, then the *freshly allocated* slot in the already-replaced type
`B`. The inner type application is supplied by the source value's
`UniversalsRelated` head instantiated at the fresh slot's own endpoint
variables `(＇ Xᴾ, ＇ Xᴵ)`; that yields exactly the right terms, at the
cost of one extra alias slot in the result world, which the
`PostBindValueRelation` factorization tolerates. The obstruction is
elsewhere: the second reveal runs at *source* imprecision equal to the
first reveal's *target*, which contains the current slot's representation
imprecision `r`. So the second reveal needs `RevealSafe r` — and when the
lemma is then used at the fresh slot, `r` is the imprecision the observer
chose, which is arbitrary. Two ways out:
  (a) Recommended: remove the fragment by proving C1 as well; safety then
      holds for every derivation and the requirement disappears.
  (b) Restrict `UniversalsRelated` to quantify only over representation
      pairs whose imprecision lies in the fragment, and carry
      `RevealSafe (rep-related (atom s))` as a slot invariant. This
      weakens the universal clause (observers could no longer instantiate
      at `★`-ish types) and forces the universal introduction and
      elimination compatibilities to be re-proved against it.

Finding D (resolved 2026-08-24 by the semantic-worlds route, chosen
by the user; found the same day while attacking the `∀⊑`
obligation). The paired reveal at `∀⊑` — and every reveal that
eliminates a *dynamic* seal — is blocked by an index-accounting
mismatch in the logical relation, not by missing machinery.

The obstruction. The dynamic-seal clause is contractive: at
`I.X⊑★` the relation at index `suc k` records the sealed payload
against the imprecise value only at index `k`
(`DynamicAtomHolds (ValueImprecisionᵏ k W) …` in
`LR-narrow/LogicalRelation.agda`). At a *paired* slot the same
contractiveness is harmless because unsealing is a paired step — the
imprecise endpoint's unseal is a real interpreter step, which pays the
decrement. At a *dynamic* slot the imprecise endpoint has no wrapper,
so the structural reveal's unseal is a precise-only step and nothing
pays: from a sealed pair at `suc k` one can only conclude the unsealed
pair at `k`. The shortfall is real for higher-order representation
types (the `suc k`-level content of `FunctionsRelated` strictly
exceeds the `k`-level content); only for base-type representations is
the relation index-independent.

Where it bites in the `∀⊑` reveal. The revealed value
`Vᴾ ↑ 〖 X , R ↑ `∀ B₀ᴾ 〗` must satisfy `RightUniversalsRelated` at
the replaced types; its head at chain index `suc j` concludes at
`suc j` and decomposes (after `β-reveal-∀`, a precise-only `bind`
step — the generic expansion now exists:
`related-precise-bind-step-expand` in
`proof/LR-narrow/BindStepExpansion.agda`) into the source's head
instantiated at the fresh name `＇ 0`, the paired reveal of the old
slot inside the body (fine: the source imprecision is the
sub-derivation `p₀`, so a lexicographic (index, derivation-size)
refinement of the induction handles the same-index recursion), and
finally the dynamic reveal of the fresh slot — where the shortfall
strikes. The accounting works out at every chain index `suc j < k`
(instantiate the source's head one index higher: the spare unit pays
for exactly one unseal layer; nested unseals under arrows are paid by
the β-steps of the applications above them), and also at the top
index when the imprecise world type `Bᴵ` is atomic (`ι`, `★`, or a
variable: the imprecise reveal `〖 Xᴵ , Rᴵ ↑ Bᴵ 〗` is then `id↑`- or
`unseal`-shaped, not a value form, so the imprecise endpoint takes one
real step). It fails only for the head *at* the statement's own index
when `Bᴵ` is `⇒`- or `∀`-shaped (the imprecise wrapper is a value
form and contributes no step). The same obstruction affects the
`∀⊑`/dynamic sub-cases of the one-sided reveals and the Λ-body
motives of `RemainingObligations` (which face the same
`〖 0 , ⇑ R ↑ B 〗` wrapper after `β-Λ`).

Resolution options:
  (a) Semantic worlds: store, per dynamic atom, its payload relation
      as an intrinsically indexed relation in the world (Ahmed-style),
      with a coherence condition tying it to the syntactic relation at
      smaller indices. Principled; removes the contractiveness at its
      source; a large refactor of `WorldCore`/`Atoms` and every world
      lemma.
  (b) Decremented statements: state the `∀⊑` reveal (and a dynamic
      one-sided reveal family) as index-decrementing
      (`ValueImprecision p (suc k) → … at k`) and thread the spare
      unit through the frame compositions. The interior accounting
      closes, but composite forms containing `∀⊑` (a function type
      with a `∀⊑` codomain, a `∀⊑∀` body containing `∀⊑`) inherit the
      decrement at their own top index, so the statement family splits
      by an "involves a dynamic seal" predicate — invasive and still
      leaves top-index gaps in the already-proved cases.
  (c) Defer: keep `∀⊑` as a `RevealObligations` field and design step
      7 (`Λ⊑Λ²` and the other reveal consumers) first; if every
      consumer invokes the reveal immediately after a real imprecise
      step (a β or an unseal on the imprecise side), the decremented
      form (b) suffices with no split, because the consumer supplies
      the spare unit at the point of use.
  (d) Partial fragment now: prove the `∀⊑` reveal for atomic `Bᴵ`
      (where the imprecise wrapper pays), refining the obligation to
      the value-shaped `Bᴵ` cases only.

Resolution (landed 2026-08-24, option (a) in the lightweight form).
Storing opaque per-atom relations in worlds would make worlds
circular (relations quantify over future worlds); instead the same
effect is obtained syntactically: a dynamic atom's payload relation
*is* the logical relation at its recorded representation imprecision,
and that recursion is well-founded at the *same* step index by
allocation order.  Concretely: `DynamicSemanticAtom` gains a
`dynamicFresh` field (every center variable of the embedded
representation is strictly greater — allocated earlier — than the
slot's own variable; populated at the fresh-atom constructor and the
three weakenings via `rename-∈ᵗ-inversion`), and the `X⊑★` clause's
`DynamicAtomHolds` disjunct and the `★⊑★` clause's
`DynamicAtomTagRelated` disjunct now instantiate the payload relation
at `suc k` instead of `k`.  The ground-tag payloads
(`DynamicPayloadRelated`, `RightDynamicPayloadRelated`) and the
paired-atom clauses stay contractive — their eliminations take real
imprecise steps.  The recursion is covered by the existing
`TERMINATING` pragma on the definition (argument documented at the
pragma) and by three documented pragmas on the future-lifting
closure proofs, whose `X⊑★` cases now recurse at the same index into
the representation imprecision.  With this change the unseal
accounting closes: a dynamic seal eliminated by a precise-only step
yields its payload at the full index.

`∀⊑` status (2026-08-24, checked). On top of the resolution, the
following landed, and the *reveal* at `∀⊑` is closed for every
imprecise center except the atomic ones:

* the generic precise-only allocation expansion
  (`related-precise-bind-step-expand`, index-preserving, in
  `proof/LR-narrow/BindStepExpansion.agda`);
* the lexicographic (step index, source-derivation size) refinement
  of the reveal induction (`sizeᵖ` and its renaming/lifting
  preservation in `proof/LR-narrow/ImprecisionSize.agda`; sized
  paired statements, `LexBelow`, `Below`, `below-restrict`,
  `below-at` in `proof/LR-narrow/RevealStatements.agda`; the nested
  well-founded induction in `RevealStructural.agda`) — the `∀⊑`
  head's body reveal runs at the same index at the strictly smaller
  lifted `p₀`;
* the one-sided dynamic-slot reveal and conceal
  (`proof/LR-narrow/DynamicReveal.agda`, ~1.1k lines): `DynamicSlot`
  with the subst-free `IsDynamicEntry` view, slot transport along
  futures, the seal case consuming/producing `DynamicHolds` at the
  same index, identity and function cases by (type size, index)
  recursion, `⊑★`-payload recursion through the ground view; the
  universal precise type is the `blocked-dyn-*-universal` obligation
  pair; wired as the `DynRevealAt`/`DynConcealAt` components of the
  statement bundle;
* the `∀⊑` reveal itself (`RevealStructural.agda`):
  `reveal-right-universal-inner`/`-head` (instantiate the source's
  `RightUniversalsRelated` head at the fresh dynamic name `＇ 0`,
  paired reveal of the old slot inside the body at the smaller
  derivation, dynamic reveal of the fresh slot), the value assemblies
  `reveal-right-universal` (value-form imprecise wrappers, i.e. `⇒`-
  and `∀`-shaped `Bᴵ`) and `reveal-right-universal-star` (`Bᴵ = ★`:
  the imprecise wrapper is `id↑ ★` and steps; the old slot cannot
  occur by `star-no-occurrence`, so the body reveal is the one-sided
  precise reveal), and the dispatch split
  (`right-universal-general` forces the target derivation by
  `⊑-unique` against the `replace-⊑`-built `I.∀⊑`).

Update (2026-08-24, checked): the atomic-target reveal is now also
closed except for the variable hit.  `paired-no-occurrence` in
`proof/LR-narrow/StarNoOccurrence.agda` generalizes
`star-no-occurrence`: a variable at the paired mode `X⊑X` occurs on
the left of a derivation only opposite an occurrence of itself on the
right, so when the paired center avoids the imprecise center type,
both replacements are the identity.  The `absent` trio in
`RevealStructural.agda` (`reveal-right-universal-absent-inner`/
`-head`/`-absent`, with `right-universal-absent-general` forcing the
target derivation, which is the source transported along the identity
replacement) closes `Bᴵ = ‵ ι`, the missed variable `Bᴵ = ＇ Y` with
`Y ≢ slotXᴵ s` (decided by the neutral `var-decision` view so the
blocked branch keeps its hypotheses at their original types), and
re-derives the former `★`-route as the instance `avoid = ∉-star` (the
special-cased star trio is deleted).  A small `liftCenter-∉ᵗ` lemma
transports non-occurrence along futures.

Still blocked at `∀⊑` (through the unchanged `blocked-reveal`/
`blocked-conceal` obligations):

* the reveal at the variable hit `Bᴵ = ＇ (slotXᴵ s)`: the imprecise
  wrapper unseals, and the payload pair after the unseal has no
  semantic content — the `∀⊑` clause records nothing about the
  imprecise value's seal structure.  Suggested resolution: enrich the
  `∀⊑` clause with the seal structure when the imprecise center is a
  paired-mode variable (`Vᴵ ≡ Uᴵ ↓ seal …` with the payload pair
  related one index lower — the unseal is an imprecise step, so a
  contractive field is exactly right, unlike Finding D).  The natural
  producer of such pairs is the conceal direction at the same hit, so
  the enrichment should land together with `∀⊑`-conceal, and ideally
  in one design pass with the `∀⊑★`/`∀★⊑★` gate (tags there, seals
  here: both expose imprecise runtime structure);
* the whole conceal direction at `∀⊑` (the dual decomposition —
  paired conceal of the body, dynamic reveal of the fresh slot,
  `makeConceal` value forms including the seal hit — is mapped but
  not yet written).

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
