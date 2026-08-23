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
lemmas:

- the bottom-elimination branch of `CTI.•⊑•²`;
- the remaining result-imprecision branches of `CTI.•⊑²`, including
  `∀★⊑★`, `∀⊑★`, and `bot⊑★`.

Returned worlds must continue to factor through the paired extension selected
by the pre-allocation universal application observation.

### 4. Assemble the total fundamental theorem

Define `fundamental` by exhaustive recursion on the CTI derivation. Reuse the
checked compatibility lemmas for the completed cases and the body inductions
from Milestone 1 for universal introduction. Keep the public theorem statement
in `LR-narrow/Fundamental.agda` and its proof script in
`proof/LR-narrow/Fundamental.agda`.

### 5. Validate the completed development

For each submilestone, run the narrowest relevant Agda check while developing.
Before declaring a milestone complete, run:

```text
git diff --check
make -C GTSFImp-Interpreter check
```

Also load `GTSFImp-Interpreter/LR-narrow/LRNarrowAll.agda` through Agda MCP.
The final check must find no unsolved metas, interaction holes, or new
postulates in the fundamental-property dependency closure.

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
