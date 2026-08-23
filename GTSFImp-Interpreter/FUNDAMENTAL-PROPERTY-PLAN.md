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
`proof/LR-narrow/FundamentalAssembly.agda` (checked 2026-08-23). Its
`Assembly.fundamental` recurses over every CTI constructor; the constructors
without a checked compatibility lemma are the fields of
`RemainingObligations`, each stated with the structural induction hypothesis
the recursion can actually supply (`Hypothesis`: the fundamental property at
every semantic world realizing the premise's syntactic world). Closing the
theorem means inhabiting that record by induction, not by assumption.

Constructor coverage (25 CTI constructors):

| status | constructors |
|---|---|
| closed by checked lemma | `x⊑x²`, `κ⊑κ²`, `blame⊑²`, `ƛ⊑ƛ²`, `·⊑·²`, `⊕⊑⊕²`, `cast⊑cast²`, `⊑cast²`, `cast⊑²`, `•⊑•²` at `∀⊑∀`, `•⊑²` at `∀⊑` |
| outer lemma checked, body motive open (M1) | `Λ⊑Λ²`, `Λ⊑²`, `Λ⊑²-smart-comma` |
| open (M2) | `⊑reveal²`, `⊑conceal²`, `reveal⊑²`, `conceal⊑²-seal-star-open`, `conceal⊑²-source-ok`, `reveal⊑reveal²`, `conceal⊑conceal²`, `packaged-seal-star²` |
| open (M3) | `•⊑•²` at `∀⊑`, `bot-elim`; `•⊑²` at `∀⊑∀`, `∀★⊑★`, `∀⊑★`, `bot-elim`, `bot⊑★` |

## Next milestones

### 1. Complete the universal body inductions

1. Prove the source-side insertion operation identified in
   `GTSFImp/proof/DGG/notes/t4-d3-source-both-transport-gap.red`.
2. Combine source and target insertion to obtain the paired insertion needed
   when an LR test binder and a nested syntactic type binder occur in opposite
   center orders.
3. Use those results to provide checked inhabitants of
   `SourceBindTransport²ᵀ` and `BothBindTransport²ᵀ`, which are currently
   parameters of the generic term-imprecision transport driver.
4. Define the recursive symmetric body induction producing
   `UniversalBodyFundamentalProperty` for the premise of `CTI.Λ⊑Λ²`.
5. Define the recursive one-sided body induction producing
   `RightUniversalBodyFundamentalProperty` for both `CTI.Λ⊑²` variants.
   Cover value targets, target casts, the remaining non-value target
   constructors, nested universals, and the smart-comma case. Do not treat
   `SmartCommaLiftᴸ` as semantic world transport: any alias-merged center must
   receive the LR semantic entry required by the body relation.

This milestone is complete only when the body motives are derived by
structural induction rather than supplied as assumptions to the outer
constructor lemmas.

Cost note (2026-08-23): the existing target-side analogue,
`GTSFImp/proof/DGG/TargetExtend.agda`, is 3.7k lines (plus 1.2k in
`CenterRename.agda`), with one lifting lemma per world former and a 350-line
derivation recursion. Steps 1–3 above are a comparable investment for the
source side and again for the paired version. Before starting, decide between
this route and the alternative below.

Alternative to evaluate: generalize the recursion motive over a center
insertion from the derivation's syntactic world into the semantic world
(instead of transporting the derivation syntactically). The LR compatibility
lemmas are largely derivation-free (`application-compatible` and
`primitive-compatible` ignore their derivation premises; the cast and lambda
lemmas use them only for endpoint typing), so they may survive a renamed
restatement. The rebase × insertion commutation lemmas are needed on either
route. Note that structural recursion alone cannot close the universal cases:
the test binder is allocated at a *future* world, so the future's allocations
fall behind the syntactic binder; if transported sub-derivations must feed the
recursion, recurse on derivation height rather than structure.

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
