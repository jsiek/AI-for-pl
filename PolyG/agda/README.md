# PolyG (Agda): PolyGν, PolyCν, and graduality

A mechanization of the ∀ν fragment of PolyGν and its cast calculus PolyCν,
following Max New's PhD thesis, Chapter 10
(`papers/new2020-thesis-semantic-foundation-sound-gradual-typing.pdf`).
The fragment has booleans, functions, `?`, seal/unseal, tag tests, `Λν`
and instantiation `let x = M {X ≅ B}; N`, and leaves out pairs and `∃ν`.

Graduality is proved by a denotational method: a graph model with a seal
counter and consistency, and relations with worlds that relate finite
lists jointly.  The design and the reasons for it are in
`PolyG/notes/denotational-graduality.md`.

Check everything with `make check` (`agda --safe`, plus a check for
postulates and holes).

## Public modules

- **Language:**
  - `Types`, `Terms`, `Reduction`, `Typing`, `StoreWf`: PolyCν.
    Reduction is call-by-value and deterministic.
  - `GradualTerms`, `Compile`: PolyGν and its elaboration into PolyCν.
  - `TermPrecision`, `GradualTermPrecision`: term precision for the two
    languages.
- **Metatheory:**
  - `TypeSafety`: progress, preservation, type safety, determinism.
  - `CompileMeta` (with `CompileInvariants`): elaboration preserves
    typing and precision (the thesis's Lemma 218).
- **The denotation:**
  - `GraphModel`, `Denotation`: the graph model and the denotation of
    PolyCν.
  - `DenotationMeta` (with `DenotInvariants`): consistency, soundness,
    and adequacy of the denotation.
- **The theorem:**
  - `GradualityDefinitions`: observations, convergence, failure,
    divergence.
  - `MetaTheory`: the graduality theorem `graduality`.
- **Running programs:**
  - `Eval`: a one-step function `step` (value, ℧, a step with its
    derivation, or stuck) and a fuel-bounded evaluator `eval` that
    returns the final configuration with its `—↠` derivation.  Both
    compute on closed terms.
  - `Examples`: closed PolyGν programs (the thesis's §10.2.1 examples:
    the identity at 𝔹 with seal/unseal, with a ? input, without the
    seal; `const`; nested instantiation; tag tests; casts at ? and at
    function types; let and if) and PolyCν programs, each with a typing
    derivation and a run to true, false or ℧ checked by computation;
    two instances of the graduality theorem.
  - `ExamplesCoverage`: a checked catalog showing that the example
    runs use every reduction rule.

## Proofs (`proof/`)

- **Type safety:** `TypeSubst`, `TypingSubst`, `Progress`,
  `Preservation`, `Determinism`.
- **Elaboration:** `PrecisionProps`, `CompileTyping`, `CompilePrecision`.
- **The denotation:**
  - `TermSubst`, `ScopedProps`: syntactic lemmas;
  - `DenotProps`, `DenotSubst`: monotonicity, finite support, β laws,
    substitution;
  - `DenotConsistency`, `DenotSoundness`, `DenotAdequacy`.
- **Graduality:**
  - `DenotRelation`: the reflection and preservation relations;
  - `DenotRelationProps`, `DenotCastProps`: properties of the relations
    and the casts;
  - `DenotCast`: the eight cast lemmas;
  - `DenotFundamental`: the fundamental lemma;
  - `DenotGraduality`: the theorem.

`PolyG/popl2020/` holds an earlier port of the POPL 2020 paper's version
(with `hide` and inside-out instantiation).  It is not part of this
development.
