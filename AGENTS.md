## Working agreements

- Never read or write files outside the current directory (AI-for-pl/).
- **Present problems and design alternatives to Jeremy with a concrete
  example, always** (standing request, 2026-09-04): when reporting a
  problem, a counterexample, or a set of candidate solutions, lead with a
  concrete program/term/trace that exhibits it, and show each alternative
  acting ON THAT EXAMPLE, before (or instead of) any general description.
  Jeremy: "I'm able to process examples MUCH faster than general
  descriptions."  A colored/annotated trace is welcome for anything
  scope- or boundary-related.
- This is a closed-world repository: prefer direct internal references and a
  small canonical public surface over compatibility re-exports, aliases, or
  wrapper files. When consolidating APIs, delete obsolete shims instead of
  preserving them for hypothetical external users.
- Do not clutter the repository root. Place files where they belong from the
  start: design notes, investigation reports, pre-flight records, and
  completed-arc scratch files go under the language's notes directory (e.g.
  `GTSFImp/proof/DGG/notes/`, checked with an extra `-i` include when they
  are Agda files); proof modules go under the language's `proof/` tree. A
  scratch file may sit at the root only while its arc is ACTIVELY being
  worked, and must be moved (or deleted) when the arc completes (2026-08-12).
- Do not introduce new named aliases merely for parts of lemma or theorem
  statements. Inline existential witnesses, conjunctions, and other conclusion
  structure in the statement itself so the full claim is readable at the use
  site. Add a named definition only when it is a genuine reusable concept, not
  just a shorthand for a proof obligation.
- Changes to the live term-imprecision relation in
  `GTSFImp/proof/DGG/CastTermImprecision.agda` require 
  the user's explicit permission
  before editing that file. The permission request must show the entire
  rule being changed with both the before and after the change.
  The request must explain why the relation needs to change and include
  the relevant imprecision and reduction square, which the terms fully
  normalized and with variables as names instead of de Bruijn indices.
  When displaying imprecision, use the Imp Ladder table format.
  Here's the ladder for checkpoint 8 of example 12.

```
#   source term            A:src     ηᴸA:ctr    ⊑ costs               ηᴿB:ctr    B:tgt      target term
─────────────────────────────────────────────────────────────────────────────────────────────────────────
1   □ ↑ unseal X           ℕ         ℕ          ι⊑★                   ★          ★          ─
2   □ ⟨ ★↦＇X ⟩            ＇X       ＇X        mark X⊑★ at X         ★          ★          ─
3   □ ⟨ id★ ⟩              ★         ★          ★⊑★                   ★          ★          □ ⟨ id★ ⟩
4   □ ↑ unseal Z           ★         ★          ★⊑★                   ★          ★          ─
5   ─                      ＇Z       ＇Z        mark X⊑★ at Z  ⚡     ★          ★          □ ↑ unseal Zᴿ
6   □₁ · □₂                ＇Z       ＇Z        Z ≈ Z  (X⊑X)          ＇Z        ＇Zᴿ       □₁ · □₂
7   ├ □ ↑ unseal Y ⇒-rev   ＇Z⇒＇Z   ＇Z⇒＇Z    Z ≈ Z, twice          ＇Z⇒＇Z    ＇Zᴿ⇒＇Zᴿ  □ ↑ unseal Yᴿ ⇒-rev
8   │  λx. □               ＇Y⇒＇Y   ＇Y⇒＇Y    Y ≈ Y, twice          ＇Y⇒＇Y    ＇Yᴿ⇒＇Yᴿ  λx. □
9   │   x                  ＇Y       ＇Y        Y ≈ Y                 ＇Y        ＇Yᴿ       x
10  └ □ ↓ seal Z           ＇Z       ＇Z        Z ≈ Z + matched-      ＇Z        ＇Zᴿ       □ ↓ seal Zᴿ
                                                seal-★-partner
11    □ ⟨ ＇X↦★ ⟩          ★         ★          ★⊑★                   ★          ★          ─
12    □ ↓ seal X           ＇X       ＇X        mark X⊑★ at X +       ★          ★          ─
                                                X unoccupied
13    ─                    ℕ         ℕ          ι⊑★                   ★          ★          □ ⟨ ℕ! ⟩
14    7                    ℕ         ℕ          ℕ⊑ℕ                   ℕ          ℕ          7
```

## Subagent launch notes

- When launching full-history forked subagents, do not also specify
  `agent_type`, `model`, or `reasoning_effort`; full-history forks inherit those
  settings from the parent. If a specific worker type is needed, spawn without a
  full-history fork and include the needed context in the prompt or in a repo
  handoff file.
- If spawning fails because the agent thread limit is reached, reuse existing
  subagents with `send_input` or close unneeded agents before trying to create
  more.

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
- [ ] Public/private split for trust: keep language definitions and main theorem
  statements in the language's top-level directory, move private proof scripts
  and helper lemmas to a `proof/` subdirectory, and expose each main theorem at
  top level as a thin wrapper around its corresponding `proof/*` theorem.
  The main theorems should be explicitly stated and not just imported
  as public from the corresponding `proof/*` file.

### 2) Baseline metatheory (default target)

- [ ] Canonical forms lemmas for the main type constructors.
- [ ] Progress.
- [ ] Preservation.
- [ ] Type safety theorem (or `progress + preservation` exported clearly).
- [ ] In public theorem statements with existential witnesses, prefer
  `∃[ x ] ...` notation over `Σ A (λ x -> ...)`.
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
- In Markdown documents, delimit displayed LaTeX with `$$ ... $$`. Do not use
  `\[ ... \]`; Obsidian does not render those delimiters reliably.
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

## World-grid diagrams

When an informal proof shows worlds changing over time or across scopes, use a
world grid:

- Time flows down. Draw reduction/evolution edges vertically and label each
  edge with the reduction or evolution step that produces the next world.
- Scope depth grows to the right. Indent a deeper-scope world to the right of
  its origin and label the scope edge `rebase@pivot`.
- Render each world as one snapshot with one cell per center variable, in center
  order:

      ⟨X: src-entry ⊑[mark] tgt-entry │ …⟩

  An endpoint entry is `pivot↦type`, using the endpoint pivot name and its
  direct store entry. Write `─` when that side has no pivot at the center.
  The mark is the center's `X⊑X` or `X⊑★` mark.
- Name source and center type variables `X`, `Y`, `Z` by position, repeating
  them with subscript groups (`X₁`, ..., `Z₂`, ...) beyond three. Prime target
  names after any subscript (`X′`, `X₁′`); reserve `♭0`, `♭1`, ... for binders.
- Read these three intended properties directly from the grid:
  - A right-only cell (source `─`, target present) has target store entry `★`.
  - A cell whose source store entry is `★` and whose mark is `X⊑★` has no
    right occupant (target `─`).
  - Scope edges with the same `rebase@pivot` that enter one world all originate
    at the same world.
- Mechanization status: the only live general predicate today is `WFWorld`,
  which checks precise-mark alignment. The full `WorldInvariants` companion is
  forthcoming in PR #177 and will mechanize all three properties above.
- Fixture/legacy worlds may violate the intended properties; the grid makes
  such violations visible, which is its purpose.
- Snapshots pasted into `.red` notes must be generated by
  `proof.DGG.WorldSnapshot.worldSnapshot`, not drawn by hand.

Small example (the second world adds a right-only dynamic cell; the scope edge
then rebases at the surviving source pivot):

    W₀  ⟨X: X↦ℕ ⊑[X⊑X] X′↦ℕ⟩
    │ β-inst
    ▼
    W₁  ⟨X: ─ ⊑[X⊑★] X′↦★ │ Y: X↦ℕ ⊑[X⊑X] Y′↦ℕ⟩
          ╲ rebase@X
            W₁′  ⟨X: ─ ⊑[X⊑★] X′↦★ │ Y: X↦ℕ ⊑[X⊑X] Y′↦ℕ⟩

## Imprecision ladders

When an informal proof inspects a term-imprecision derivation, use an
imprecision ladder:

- Each row is one `⊢²` node, ordered outside-in with the conclusion first.
- An application forks into `├` function and `└` argument rows; deeper rows
  inherit the `│` continuation column.
- In a term column, `□` is the child syntax and `─` is a silent side of a
  one-sided rule. Show only the syntax contributed by that node.
- The seven columns are source term, `A`, `ηᴸA`, `⊑ costs`, `ηᴿB`, `B`,
  and target term, in that order.
- Name source and center type variables `X`, `Y`, `Z` by position, repeating
  them with subscript groups beyond three; prime target names after the
  subscript, and reserve the `♭` namespace for type binders.
- Columns 3–4–5 carry the alignment obligation. The `⊑ costs` cell is the
  direct reading of that center comparison, including any occupancy premise.
- Ladders pasted into notes must be generated by
  `proof.DGG.ImpLadder.impLadder`, not drawn by hand.

# Agda Development Notes

## Agda reduction sequence proof style

When writing Agda proofs of reduction sequences, use the local chain notation
for the reduction relation at hand instead of nested constructor applications.
Put each intermediate term on its own indented line, put the step justification
on the following `—→⟨ ... ⟩` line, and always end the written chain with `∎`
so the final term is explicit in the code.

When a proof reuses an existing multi-step reduction segment, use the local
transitive chain syntax, such as `_—↠⟨_⟩_` or `_—↠[_]⟨_⟩_`, and still finish
with the relation's reflexive terminator. For store-changing chains in
GTSFImp, that means writing the final term followed by `∎[]`.

In reduction-chain proofs, do not use underscores to make the chain's
arguments implicit: write out the intermediate and final terms (and the
store-change indices, where the relation carries them) as explicit
arguments. The point of the chain notation is that a reader can follow
the terms in the code; an `_` defeats it.

Prefer:

    twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    sucᶜ · (sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    sucᶜ · `suc `zero
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc (`suc `zero)
  ∎

For store-changing reductions with a reused tail proof, prefer:

    M
  —→[ keep ]⟨ step ⟩
    N
  —↠[ χs ]⟨ N↠P ⟩
    P ∎[]

Over nested `—→⟨_⟩_` / `↠-step` constructor applications when proving
reduction sequences.

## Function extensionality is allowed

It is acceptable to postulate or import function extensionality in Agda proofs
when it removes proof-engineering friction. Prefer using the standard library's
`Axiom.Extensionality.Propositional` interface when possible, and keep the
assumption localized near the proof infrastructure that needs it.

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

## Agda line-break style (from 2026-04-11 and 2026-04-20)

Avoid premature line breaks in simple applications. If a definition is a direct
application with short arguments, keep it on one line, under the contraint of
using at most 80 columns per line.

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

When the line goes over 80 columns, break the line and insert
appropriate indentation, but then use the rest of the 80 columns in
the next line.

Prefer

    eq-close = trans (cong (λ X → (⇑ᵗ X) [ ＇ zero ]ˢᵗ) eq-src)
                     (closeν-inline-open Aν)

Over:

    eq-close =
      trans
        (cong (λ X → (⇑ᵗ X) [ ＇ zero ]ˢᵗ) eq-src)
        (closeν-inline-open Aν)

## Agda type-signature line-break style (from 2026-07-28)

When a definition's type spans multiple lines, put the definition name and its
implicit parameters on the first line. Put each implication arrow at the
beginning of its continuation line, not at the end of the preceding line.

Prefer:

    canonical-⇒ : ∀ {Δ : TyCtx}{Σ : TyStore}{V : Term}{A B : Ty}
      → Value V
      → Δ ∣ Σ ∣ [] ⊢ V ⦂ (A ⇒ B)
      → FunView V

Over:

    canonical-⇒ :
      ∀ {Δ : TyCtx}{Σ : TyStore}{V : Term}{A B : Ty} →
      Value V →
      Δ ∣ Σ ∣ [] ⊢ V ⦂ (A ⇒ B) →
      FunView V



## Agda mixfix notation style (from 2026-04-15)

When constructors or operators are declared in mixfix form, write both terms and
patterns in that mixfix form rather than in fully-applied underscore form.

Prefer:

    p ；tag G
    p ；seal α
    unseal α ； p
    untag G ℓ ； p

Over:

    (_；tag_ p G)
    (_；seal_ p α)
    (unseal_；_ α p)
    (untag_；_ G ℓ p)

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

## Avoid catch-all cases in proofs

Prefer exhaustive case splits.


## Never add redundant postulates

Never add a postulate whose type (the logical formula) is the same as
another theorem or postulate. This can lead to wasting time on
circular reasoning during proof development.
