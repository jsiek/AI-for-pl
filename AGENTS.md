## Language Definition + Metatheory Checklist (Join over `AI-for-pl`)

This section is a "maximal join" over the language developments in this repo
(`STLC`, `lambda`, `SystemF`, `GTLC`, `GTSF`, `PolyCast`, `PolyUpDown`,
`PolyImp`, `PolyG`, `PolyBlameI`): if a component appears as a standard part of
at least one mature development here, it is listed.

Use this as guidance when creating a new language folder.

### 1) Core language definition (always)

- [ ] `Types` module: type grammar plus well-formedness (`WfTy`) or intrinsic
  typing indices.
- [ ] `Terms` / main language module: term grammar, values, and key syntactic
  forms. The constructor names for values should be the same as those for terms.
- [ ] Context and lookup machinery: term contexts, type contexts (if
  polymorphic), membership judgments.
- [ ] Static semantics: typing judgment(s), including all
  introduction/elimination rules.
- [ ] `Reduction` module: values, frames, and small-step reduction.
- [ ] `Eval` module: executable function `eval` .
- [ ] Renaming/substitution infrastructure: use parallel renaming and parallel
  substitution as the primary setup (at term level, and at type level when the
  language has type binders), then derive single-variable substitution as a
  special case.
  - Definitions/operators to provide (core term-level API): `Rename`/`Subst`,
    action on syntax (`rename`, `subst`), binder extension/lifting (`ext`,
    `exts`, `⇑`/`lift`), weakening renaming (`wk`), composition
    (`seq`/`_⨟_`), convert renaming to substitution (`ren`), identity (`id`), 
    and single/cons environments  (`singleEnv`, `_•_`/`cons`).
  - Derived API: define single-variable substitution from parallel substitution
    (`N [ M ]`-style), plus definitional lemmas showing it matches the chosen
    single-environment encoding.
  - Congruence/extensionality lemmas: `rename-cong`, `subst-cong`, and extension
    congruence (`ext-cong`, `exts-cong`) so equal environments yield equal
    renamed/substituted syntax.
  - Lookup transport lemmas: lookup/membership mapping under
    renaming/substitution (`renameLookup`, `substLookup`,
    `map∋`/`unmap∋`-style) for contexts/stores.
  - Identity lemmas: `rename-id` and `subst-id`.
  - Composition/fusion lemmas: `rename-rename` composition (`rename-comp` /
    `rename-rename-commute`) and substitution composition (`subst-subst` /
    `sub-sub`).
  - Renaming-substitution commutation (both directions): `rename-subst` /
    `rename-subst-commute`, plus term-level variants often named `ren-sub` and
    `sub-ren`.
  - Binder-lifting coherence lemmas: `ext-comp`, `exts-ext`, `ext-exts`,
    `exts-seq`, and shift/weakening interaction (`rename-shift`,
    `subst-⇑`-style).
  - Preservation-facing corollaries: the final single-variable substitution
    theorem(s) for typing, obtained as corollaries from the parallel
    infrastructure.
  - Scope split: put polymorphic specializations (type-level rename/subst,
    opening/instantiation commutation, mixed term/type commutation) in Section
    4, and gradual/store/seal-specific variants
    (`renameˢ`/store-lift/`inst★`/`ν` source lemmas) in Sections 5 and 7.
- [ ] Administrative lemmas: weakening/lookup-map/extensionality-style lemmas
  needed by preservation.
- [ ] File charter in every source file: a short top-of-file comment stating the
  file's purpose, scope, primary exports/theorems, and key dependencies.
- [ ] Preferred file naming conventions: use `Types`, `Terms`, `TypeSubst`,
  `TermSubst`, `Reduction`, `Progress`, `Preservation`, `TypeSafety`, `Eval`,
  `Examples`, `README` for design rationale, and `Design` for informal
  definitoin of the language design. Prefer `UpperCamelCase.agda` for module
  files and stable canonical names over ad-hoc abbreviations.

### 2) Baseline metatheory (default target)

- [ ] Canonical forms lemmas for the main type constructors.
- [ ] Progress.
- [ ] Preservation.
- [ ] Type safety theorem (or `progress + preservation` exported clearly).
- [ ] Multi-step closure and multi-step preservation (if using small-step).
- [ ] Substitution theorems: term substitution and, when needed, type
  substitution commuting lemmas.
- [ ] Determinism and/or normalization/confluence when part of the design goal
  (e.g. `Termination`, `CoercionNormalForm`, full-beta confluence work).

### 3) Testing, examples, and executable artifacts

- [ ] `Examples` module with representative well-typed programs.
- [ ] `Eval`/`Reduction` execution examples: show expected reduction/evaluation
  outcomes.
- [ ] Companion evidence for example terms: in `Examples`-style modules, every
  top-level executable term declaration (`name : Term`) should include both a
  typing derivation (`name-⊢`) and a reduction/evaluation witness
  (`name-↠` or evaluator result theorem). For helper/library terms
  that are not directly
  runnable to data, include at least one explicitly named fully-applied
  companion example that is.
- [ ] Prefer data endpoints for tests: example reductions should finish at
  `Bool`/`ℕ` constants (or other first-order data values in the language), not
  higher-order functions. If an example currently stops at a function, extend it
  with additional applications until it reaches a data constant.
- [ ] Complete reduction-rule exercise set: maintain a small coverage catalog
  where the example suite collectively exercises every dynamic semantics rule at
  least once.
- [ ] Regression examples for tricky metatheory edges (substitution through
  binders, casts at polymorphic boundaries, etc.).
- [ ] Cross-check implementation style if available (e.g. parallel Agda/Lean
  files as in `STLC` and `lambda`).
- [ ] Design/notes document capturing intended semantics and proof strategy.

### 4) Polymorphic-language extras (`SystemF`, `Poly*`, `GTSF`)

Add these when the language has universal quantification or type-level binders.

- [ ] Type-level renaming and substitution operators.
- [ ] Type-substitution lemmas for terms/typing derivations.
- [ ] Instantiation/generalization metatheory (`Λ`, type application).
- [ ] Optional but recommended: representation bridges (`intrinsic`/`extrinsic`
  isomorphism) and relational theorems such as parametricity/free theorems.

### 5) Gradual-typing extras
`GTLC`, `GTSF`, `PolyImp`, `PolyUpDown`, `PolyBlameI`

These are language-kind-specific and do not apply to fully static calculi.

- [ ] Consistency relation (or equivalent compatibility relation).
- [ ] Precision/imprecision (or separate widening/narrowing) relation.
- [ ] Cast/coercion typing and operational semantics.
- [ ] Static gradual guarantee (typing-level monotonicity wrt precision).
- [ ] Dynamic gradual guarantee (runtime behavior monotonicity wrt precision).
- [ ] Proof-supporting properties of consistency/precision
  (reflexive/transitive-like facts, substitution compatibility, etc.).
- [ ] If blame is modeled: blame-safety/precision properties and explicit blame
  behavior examples.

### 6) Cast/coercion-calculus extras (`GTLC`, `PolyCast`, `Poly*`)

Add these when casts are first-class semantic objects.

- [ ] Coercion syntax + typing judgment.
- [ ] Coercion reduction/equality (if normalized or equated).
- [ ] Coercion compilation/correctness links (if compiling casts to coercions).
- [ ] Normal-form and algebraic properties needed by evaluator/metatheory.

### 7) Store/stateful-language extras
`PolyCast`, `PolyImp`, `PolyUpDown`, `PolyBlameI`

Only needed when evaluation depends on runtime store components.

- [ ] Store syntax/representation and store typing invariants.
- [ ] Reduction/eval rules that thread store explicitly.
- [ ] Progress/preservation statements lifted to term+store configurations.
- [ ] Example executions that exercise heap/cell/cast interactions.

### 8) Suggested "definition of done" for new languages

- [ ] Core definition complete and readable (`Types`, terms, contexts, typing,
  reduction).
- [ ] Baseline metatheory complete (`progress`, `preservation`, substitution).
- [ ] Relevant language-kind-specific subsection above completed.
- [ ] Examples and evaluator traces added for nontrivial programs.
- [ ] At least one design note documenting key choices and non-obvious lemmas.
- [ ] Entire folder type-checks cleanly in Agda (and Lean, if dualized).

# Design Notes and Informal Proof Notes

## Design notes

When writing design notes for a calculus or translation:

- Match the style of nearby design notes when there is an established local
  style.
- Prefer named variables and named substitution in expository notes, even when
  the Agda mechanization uses de Bruijn indices.
- State important relations as explicit definitions, not just by implication
  from later rules. For example, if typing uses consistency, include the full
  definition of consistency.
- Include important derived rules as theorem statements when they are used
  pervasively in the exposition.
- When presenting formal relations in prose, prefer the actual formal clauses
  and side conditions over informal labels such as "atomic case" or
  "identity-like case".
- Put formal terms, judgments, and propositions in backticks in the prose and
  headings so they stand out from the surrounding explanation.
- When giving reduction relations in notes, prefer a clean mathematical
  presentation with the notation used consistently throughout the document.

## Informal proofs

When writing informal proof documents:

- Emphasize reduction sequences and proof shape over long prose explanations.
- Name the lemmas that justify the important reasoning steps.
- Do not call out constructor names or minor helper lemmas in the prose.
- State lemmas and theorem goals in concise formal mathematical prose using
  `if ... then ...`. Avoid inference-bar formatting in informal proof notes.
- If a proof is by cases, use Markdown headings such as `### Case 1. ...` rather
  than separator lines.
- Make case headings direct and formula-shaped when possible. For example, write
  `Case 1. λx. N ⊑ λx. N'` instead of a descriptive sentence.
- Phrase case headings according to the relation or judgment that the proof is
  analyzing. If the induction is on a derivation of `c ⊑ A' ?ℓ`, the case
  headings should be instances of that relation.
- When a case naturally breaks into stages, prefer one compact proof sketch or
  one annotated diagram over many tiny fragments, unless the extra splitting is
  genuinely clarifying.
- Keep the explanatory text short when a diagram already shows the proof
  structure.
- Prefer "show, don't tell": when a prose sentence informally describes the
  shape of a witness term or a reduction step, replace it with the explicit term
  equation and a diagram whenever practical.
- When inversion gives a more specific term shape, state that shape explicitly.
  For example, write facts such as `V = cast W [ G ! ]` and continue the proof
  with `W`.

## Diagrams

When using ASCII diagrams in informal proofs:

- Use `Diagram:` as the label, not `Picture:`.
- Use diagrams only when reduction is part of the theorem or proof step. If a
  statement does not involve reduction, prefer a textual proof sketch without a
  diagram.
- Reduction should be vertical.
- Precision should be horizontal.
- Put the less precise term on the left and the more precise term on the right.
- Do not use code fences around diagrams unless there is a strong reason; plain
  ASCII diagrams are preferred. If Markdown rendering requires preservation of
  alignment, use simple indented code blocks.
- Align vertical arrows carefully with the source and target terms in the chosen
  monospaced font. In particular, make sure the arrow column agrees with both
  the top and bottom term on that side.
- Diagrams should depict reductions of whole terms, not just reductions of
  subterms pulled out of context. If a lemma is applied to a subterm, keep the
  surrounding context in the displayed term and say the lemma is used "lifted
  through" that context.
- Only place a horizontal precision relation on a row when the proof is actually
  establishing that relation at that point.
- If a diagram annotates steps, use the annotations for lemma applications or
  uses of the induction hypothesis, not for obvious reduction-rule names.
- In diagram annotations, cite lemmas directly by name and say what facts they
  are applied on. Treat induction-hypothesis annotations the same way.
- If a term persists unchanged down one side of a diagram, keep the vertical
  arrow continuous and label the corresponding segment with `0` steps.
- If an annotation would collide with the right-hand column, shift the whole
  right-hand side further right or split the annotation across multiple lines.

# Agda Development Notes

## Use "constructor form indices" for data type constructors (from 2-26-03-30)

In Agda, constructor form indices are indices of an indexed data type that are
expressed using only data constructors (like zero, suc, \[\], or *∷*) and
variables, rather than defined functions (like addition *+* or maximum max).
Adhering to this form is crucial because Agda's built-in unification algorithm
has difficulty solving equality problems involving user-defined functions that
do not immediately reduce to a constructor-based form.

To resolve "cannot unify" or "I'm not sure if there should be a case" errors
caused by complex indices, you should refactor your data types and proofs. Avoid
Functions in Indices: If a type has a function call in its index, for example,
max n m ≤ u, the unifier will struggle to match max n m with other terms
(e.g., n + k). Use Equality Proofs Internally: Instead of an index f(x), use an
explicit equality proof within the data type's definition to relate the
function's result to the expected value. The type could become something like D
: A → Set where a constructor takes an argument of type f x ≡ y.

## Agda `with` style (from 2026-03-24)

For `with` clauses, if there are two or more cases, use explicit function-name
case clauses rather than `...` shorthand. This will avoid problems that arise
with nested `with` clauses.

## Agda `rewrite` + local `where` quirk (from 2026-04-03)

When a clause uses `rewrite` and need to reference new helper functions, do not
put those helpers in a local `where` block because they will not be in scope.
Instead define helpers as top-level definitions.

## Agda recursive function termination / `with` style (from 2026-03-24)

Agda termination checking can be tripped by helper functions that took the
recursive function as a higher-order argument.

Working fix:

- Inline those helpers instead of passing recursive function as an argument.
- For nested `with` clauses, use explicit function-name case clauses rather than
  `...` shorthand. (Problems with nested `with` clauses may have been the reason
  for introducing the helper in the first place.)

This avoids confusing Agda's termination checker and keeps recursive functions
accepted without `{-# TERMINATING #-}`.

## Agda line-break style (from 2026-04-11)

Avoid premature line breaks in simple applications. If a definition is a direct
application with short arguments, keep it on one line.

Prefer:

    V⊢′ = cong-⊢⦂ refl refl refl (cong `∀ (sym eq-src)) V⊢

Over:

    V⊢′ =
      cong-⊢⦂
        refl
        refl
        refl
        (cong `∀ (sym eq-src))
        V⊢

## Substitution and heterogeneous equality playbook (from 2026-04-03)

When a proof gets stuck in "subst hell", use this pattern.

- Isolate transport in one place with heterogeneous equality. For dependent
  mismatches that differ only by definitional transport, use a single bridge
  lemma (for example `≅-to-≡` plus `≡-subst-removable`) instead of
  spreading `subst` casts throughout the recursive proof.
- Keep a small `Heq` toolbox module for reusable congruence lemmas
  (`Hcongₙ`-style helpers). This keeps proof scripts readable and avoids
  re-deriving dependent congruence each time.
- Keep the main theorem in its direct form whenever possible. Prefer statements
  like `subst ... M ≡ M` over casted variants. Introduce casts only at
  boundary lemmas that truly need transport.
- Normalize indices aggressively with small rewrite lemmas. Prove and reuse
  identities such as context-substitution identity, extension identity, and
  type-substitution identity so most branches close by `refl`.
