# A Denotational Proof of Graduality for PolyGν

Status: design on paper; nothing here is mechanized yet.  This is the
warm-up for GTSFImp (Section 11).  It follows the GTLC design,
`GTLC/notes/denotational-gg.md`, and the GTLC mechanization in
`GTLC/agda/` (`GraphModel.agda`, `Denotation.agda`, `proof/Denot*.agda`).

The language is PolyGν and its cast calculus PolyCν as in Max New's PhD
thesis, *A Semantic Foundation for Sound Gradual Typing* (Northeastern,
2020), Chapter 10
(`papers/new2020-thesis-semantic-foundation-sound-gradual-typing.pdf`).
That chapter expands New, Jamner and Ahmed (POPL 2020), and departs from
it in how `∀ν` is instantiated (Section 2).

Scope, as decided:
* the `∀ν` fragment: booleans, `if`, `let`, functions, `?`,
  `seal`/`unseal`, `is(G)?`, `Λν`, and instantiation;
* no pairs and no `∃ν`;
* graduality only, not parametricity.

Conventions, as in the thesis (and opposite to GTLC): in a precision
derivation `A⊑ : Aₗ ⊑ Aᵣ` and in `Mₗ ⊑ Mᵣ`, the left side is the *more*
precise one (`tag_G(A⊑) : A ⊑ ?`).

## 1. Summary

* **Seals are created in lockstep.** The more precise and the less
  precise program create seals together (Section 2), so one counter
  serves both sides and related seals are equal.  The paper's partial
  bijection between the two stores is the identity.
* **The denotation threads that counter.** A term denotes, for each
  starting counter `n`, a set of results `ret v n′` and `err`.
  Divergence is the empty set, as in GTLC.  The store's types are not
  part of the denotation, since reduction never reads them.
* **A `Λν` denotes a graph** from the fresh seal its instantiation
  creates to the result of its body.  This is the thesis's reading:
  instantiation creates the seal.
* **Seals carry their precision; there are no worlds.** (This replaces
  the world-based design of the first draft; Section 5 explains why
  worlds fail here.)  Each instantiation carries a label, a precision
  derivation that does not affect evaluation.
  * The two related programs are relabeled so that corresponding
    instantiations carry the same label, namely the derivation `B⊑`
    that term precision gives for their instantiating types.
  * A seal in the model is a number with the closed label of the
    instantiation that created it.
  * So a sealed value carries the derivation that relates its contents
    on the two sides.
* **The relations are indexed only by a precision derivation and a seal
  environment.** They are the two relations of GTLC (reflection `▹` and
  preservation `◃`), each defined by recursion on its element.  There
  is no world, no Kripke quantification, no step indexing, and no
  typing in the relation.
* **The proof has the GTLC shape.**
  * The fundamental lemma is two independent inductions on PolyCν term
    precision, with eight cast lemmas: up and down casts on either side,
    for each relation.
  * Elaboration preserves term precision (the thesis's Lemma 218), so
    the theorem is stated for PolyGν.
  * The theorem follows from soundness, adequacy and type safety.

## 2. Instantiation, and why seals are created in lockstep

In the thesis, instantiation is an ANF-style binding form,

    let x = M {X ≅ B}; N

* `M : ∀ν X.A`.
* `N` is typed with a *known* type variable `X ≅ B` and `x : A`.
* The result type of `N` must not mention `X`.

At run time, `M` evaluates to a polymorphic function proxy
`Λν {X. ([B⊑↕], M₀)}`, which is a `Λν` with a stack of the casts applied
to it so far.  Then:

    Σ ▷ E[let x = Λν {X. ([B⊑↕], M₀)} {Y ≅ A}; N]
      ↦ Σ, σ : A ▷ E[let x = ⟨B⊑[σ/X]⟩↕ M₀[σ/X]; N[σ/Y]]

A cast at `∀ν X.A⊑` on a proxy pushes `A⊑` onto its stack.  It neither
creates a seal nor runs anything.

This replaces the `hide` form and the inside-out `M {X ≅ A}` of the
POPL paper, which the existing `PolyG/*.agda` files follow.  The only
rule that creates a seal is instantiation, and no cast rule creates
one.  Term precision is structural apart from casts (Section 7), so two
related programs reach their instantiations in the same order until the
more precise one fails:
* branches agree, because related booleans are equal;
* `is(G)?` agrees, because related values in `?` carry the same tag.

So the `k`-th seal created on the left is the `k`-th created on the
right, and both sides have the same counter at related points.

Lockstep fails in GTSFImp, where `inst` and `gen` casts create seals on
one side only (Section 11).

## 3. The model

A seal is a natural number together with a *label*: a closed precision
derivation, the label of the instantiation that created it (Section 5).
A type environment `δ` maps type variables to labelled seals; `θ` is
its seal-number part, which is all that casts and tags need.

Values and results:

    v ::= true | false | seal σ ℓ v | inj G v
        | (U , m) ⟼ r        function entry: arguments U at counter m
        | (σ , ℓ) ⟼∀ r       Λν entry: instantiated at labelled seal (σ , ℓ)
        | ν                  the empty closure
    r ::= ret v m | err

* `U` is a finite nonempty list of values.
* `G` is a closed ground: `σ`, `Bool`, `? → ?` or `∀ν X.?`.
* Values never contain `err`, so GTLC's `ValSet` and `NoErr` bookkeeping
  disappears.
* A computation denotes, for each starting counter, a set of results.
  An environment holds sets of values, as in GTLC.

For a set of results `R`:

    ⌊R⌋ₘ   = { v | ret v m ∈ R }             the values at counter m
    R ≫= K = { err | err ∈ R }
           ∪ ⋃ₘ { r | ⌊R⌋ₘ ≠ ∅ , r ∈ K ⌊R⌋ₘ m }

The guard `⌊R⌋ₘ ≠ ∅` is GTLC's `Conv`.  Grouping results by their final
counter is the only new thing about bind.

Closures, as GTLC's `Λ` and `●`, with the counter carried in the entry:

    Λ F      = { (U , m) ⟼ r | r ∈ F (mem U) m , U ≠ [] } ∪ {ν}
    F ●ₘ E   = { r | (U , m) ⟼ r ∈ F , mem U ⊆ E }
    Λν F     = { σℓ ⟼∀ r | r ∈ F σℓ } ∪ {ν}
    F ◆ σℓ   = { r | σℓ ⟼∀ r ∈ F }

The body of a `Λν` entry for seal `σ` starts from counter `σ + 1`,
because instantiation creates seal `σ` from counter `σ`.

## 4. The denotation

`⟦M⟧ S δ ρ n`, for PolyCν, where `S` gives the labels of the seals that
exist before evaluation starts (runtime terms name them as `tseal σ`).
`ret D n` is `{ ret v n | v ∈ D }`.  Selected clauses:

    ⟦x⟧                   = ret (ρ x) n
    ⟦℧⟧                   = {err}
    ⟦λx:A. M⟧             = ret (Λ (λ E m → ⟦M⟧ δ (E • ρ) m)) n
    ⟦M N⟧                 = ⟦M⟧ n ≫= λ F n₁ → ⟦N⟧ n₁ ≫= λ E n₂ → F ●ₙ₂ E
    ⟦Λν{X.(cs, M)}⟧       = ret (Λν (λ σℓ → ⟦cs⟧ (⟦M⟧ (σℓ • δ) ρ (σ + 1)))) n
    ⟦let x = M{X≅B|ℓ}; N⟧ = ⟦M⟧ n ≫= λ F n₁ →
                            F ◆ (n₁ , ⟦ℓ⟧θ) ≫= λ E n₂ →
                            ⟦N⟧ ((n₁ , ⟦ℓ⟧θ) • δ) (E • ρ) n₂
    ⟦seal α M⟧            = ⟦M⟧ n ≫= λ E n₁ → ret (seal (δ̂ α) E) n₁
    ⟦unseal α M⟧          = ⟦M⟧ n ≫= λ E n₁ → ret (unseal (δ̂ α) E) n₁
    ⟦is(G)? M⟧            = ⟦M⟧ n ≫= λ E n₁ → ret (test (θ̂ G) E) n₁
    ⟦⟨A⊑⟩↕ M⟧             = ⟦M⟧ n ≫= ⟦↕ , A⊑⟧ θ

* `⟦ℓ⟧θ` closes the label by replacing its type variables with their
  seals.
* `⟦cs⟧` applies a cast stack, innermost first.
* Casts never change the counter.  `⟦↕ , A⊑⟧ θ E m` is defined by
  recursion on `A⊑`:

    ?, Bool, α          ret E m
    A⊑ → B⊑             ret (Λ (λ E′ m′ → ⟦↕⁻ , A⊑⟧ E′ m′ ≫= λ E₁ m₁ →
                                  E ●_{m₁} E₁ ≫= ⟦↕ , B⊑⟧)) m,  guarded by E ≠ ∅
    ∀ν X. A⊑            ret (Λν (λ σℓ → E ◆ σℓ ≫= ⟦↕ , A⊑⟧ (σ • θ))) m,  guarded
    ↑ tag_G(A⊑)         ⟦↑ , A⊑⟧ E m ≫= λ E₁ m₁ → ret (inj (θ̂ G) E₁) m₁
    ↓ tag_G(A⊑)         the payloads tagged θ̂ G, cast down by A⊑,
                        and err if some element has another tag

The tag clause is GTLC's `proj`.  The `∀ν` clause is the thesis's proxy
rule read as a graph: the pushed cast runs after the body, at the seal
the instantiation creates.

## 5. Labels instead of worlds

The first draft related seals through a *world*: for each seal, the
precision derivation relating its contents on the two sides, chosen
existentially when the seal is created, with Kripke quantification in
the closure clauses.  That design fails in a set-based graph model.

* **Where it fails.** A set of results at one counter can contain
  elements from different evaluation paths.  For example, a function's
  graph has entries for every list of arguments, including lists that
  mix `true` and `false`.
  * Two paths can create the same seal number at different
    instantiations, whose right-hand types differ.
  * The relation then picks a different world for each element, and
    the worlds cannot be merged.
  * Merging is needed wherever several elements are consumed together:
    bind over a group, and application of an entry to a list of
    arguments.
* **Two repairs that do not work.**
  * Putting the instantiating type in each seal only moves the problem:
    the right-hand type is still existential.
  * When a seal hidden in `?` is projected back and unsealed, the type
    has to match the environment's, and nothing links the two.

**The fix.** Make the relating derivation part of the seal itself.
* Each instantiation `let x = M{X≅B|ℓ}; N` carries a label `ℓ`, a
  precision derivation that evaluation ignores.  It is stored with the
  seal and copied into the seal's identity in the model.
* For the proof, the two related programs are relabeled from the
  precision derivation, so that both sides of each `⊑inst` rule carry
  its `B⊑ : Bₗ ⊑ Bᵣ`.
* A seal then has the same number *and* label on both sides (lockstep),
  and the label says how its contents are related.  The relations need
  no world and no Kripke quantification.
* Elaborated programs carry the reflexive label `idᵖ B`.  The theorem
  transfers from the relabeled programs to the elaborated ones by a
  lockstep simulation: labels do not affect evaluation.

## 6. The relations

There are two relations:
* reflection, `θ ⊢ A⊑ ⊢ r ▹ R′`: a left (more precise) result is
  matched by the right set;
* preservation, `θ ⊢ A⊑ ⊢ R ◃ r′`: a right (less precise) result is
  matched by the left set, or the left fails.

Reflection, on results:

    θ ⊢ A⊑ ⊢ err ▹ R′          = ⊤
    θ ⊢ A⊑ ⊢ ret v m ▹ R′      = θ ⊢ A⊑ ⊢ v ▹ᵛ ⌊R′⌋ₘ

On values, by recursion on the left element `v` and then on `A⊑`:

    Bool         b                 b ∈ D′
    ?            inj G u           G⊑ ⊢ u ▹ᵛ { u′ | inj G u′ ∈ D′ }
    tag_G(A⊑)    u                 A⊑ ⊢ u ▹ᵛ { u′ | inj (θ̂ G) u′ ∈ D′ }
    α            seal σ ℓ u        σ ≡ θ̂ α ,
                                   ℓ ⊢ u ▹ᵛ { u′ | seal σ ℓ u′ ∈ D′ }
    A⊑ → B⊑      (U , m) ⟼ r       ν ∈ D′ × ∀ E′ , U ≠ [] →
                                   A⊑ ⊢ U ▹* E′ → B⊑ ⊢ r ▹ (D′ ●ₘ E′)
    ∀ν X. A⊑     (σ , ℓ) ⟼∀ r      ν ∈ D′ ×
                                   (σ • θ) ⊢ A⊑ ⊢ r ▹ (D′ ◆ (σ , ℓ))
    A⊑ → B⊑, ∀ν X. A⊑     ν        ν ∈ D′
    anything else                  ⊥

* `G⊑` is the reflexive derivation of the ground `G`, which relates the
  payloads of two values in `?`.
* The seal clause reads the label from the value and interprets it as
  a closed derivation.
* Preservation is the mirror image, by recursion on the right element.
  Its error clause is `err ∈ R` (the more precise side may fail).
* `▹*` and `◃*` are the pointwise extensions to argument lists, as in
  GTLC.

Termination: the `tag_G` clause keeps the element and shrinks `A⊑`, and
every other clause shrinks the element.  So the order is lexicographic,
element first (Agda accepts it).

The environment relation for the fundamental lemma pairs related value
sets for term variables.  For a known `X ≅ B⊑` it requires that `δ X`
carry the label `⟦B⊑⟧θ`; the closing lemma (`θ ⊢ p` iff `θ₀ ⊢ ⟦p⟧θ`)
connects the label to the open derivation in the seal and unseal cases.

## 7. Term precision

* **PolyCν** (thesis Fig. 10.25–10.26, restricted to the fragment).
  `Γ⊑ ⊢ Mₗ ⊑ Mᵣ : A⊑`, where `Γ⊑` has three kinds of entry:
  * `x : A⊑` for a term variable;
  * `X` for an abstract type variable;
  * `X ≅ B⊑` for a known type variable.

  The rules:
  * One structural rule per term former, with the same constructor on
    both sides.
  * `let x = Mₗ{X≅Bₗ}; Nₗ ⊑ let x = Mᵣ{X≅Bᵣ}; Nᵣ` takes `B⊑ : Bₗ ⊑ Bᵣ`
    and pushes `X ≅ B⊑`.
  * `Λν` pushes `X`.
  * `seal X` and `unseal X` use the `X ≅ B⊑` of `X`.
  * The four one-sided cast rules (up or down, on the left or the
    right).
  * There is no `℧ ⊑ M` rule.
* **PolyGν** (thesis Fig. 10.24): structural, with ascription related
  at the precision of the two ascribed types.

Precision derivations are unique when they exist (the thesis's
Lemma 219), so the cast rules need composition (its Lemma 221) but no
coherence side condition.  Gradual meet is the greatest lower bound
(its Lemma 222), which the `if` case of elaboration needs.

## 8. The proof

* **Fundamental lemma**: one induction per relation, on PolyCν term
  precision.  The environment relation is described at the end of Section 6.  The
  cases:
  * instantiation: both sides instantiate at seal `n` with label
    `⟦B⊑⟧θ` and continue at counter `n + 1`;
  * `Λν`: the `∀ν` clause, with the body's induction hypothesis at
    `(σ , ℓ) • δ` for every labelled seal;
  * `seal` and `unseal`: the seal clause and the environment's
    `X ≅ B⊑`;
  * `is(G)?`: tags agree on `?`;
  * casts: the cast lemmas.
* **Cast lemmas**, by induction on derivations, for each relation:
  * an up cast on the left or right moves `AC⊑` to `BC⊑` or `AB⊑`;
  * a down cast moves it back.

  These are GTLC's coercion lemma, organised by the thesis's four rules.
  * The `tag_G` cases are GTLC's `inj`/`proj` cases.
  * The `∀ν` case follows the closure clause, at the same seal.
* **Soundness** (a step `Σ ▷ M ↦ Σ′ ▷ N` gives
  `⟦N⟧ |Σ′| ⊆ ⟦M⟧ |Σ|`) needs:
  * the type-substitution lemma `⟦M[σ/X]⟧ δ = ⟦M⟧ (σ • δ)`;
  * the term-substitution lemma.

  It does not need typing: each cast clause is defined to match its
  reduct.
* **Adequacy**: an element `ret v m ∈ ⟦M⟧ |Σ|` comes from a reduction to
  a value with the same observation, ending in a store of length `m`.
  As in GTLC, it uses determinism of reduction.
* **Theorem** (observational form, as in GTLC): for closed PolyGν terms
  `Mₗ ⊑ Mᵣ`, with elaborations run from the empty store:
  * if `Mₗ` reaches a value, `Mᵣ` reaches one with the same observation;
  * if `Mᵣ` reaches a value, `Mₗ` reaches one with the same observation
    or fails;
  * if `Mᵣ` fails, so does `Mₗ`;
  * if `Mₗ` diverges, `Mᵣ` diverges, and if `Mᵣ` diverges, `Mₗ` diverges
    or fails.

  The divergence clauses use type safety.  An observation is `bool b` or
  `other`, with `inj` and `seal` stripped.

## 9. The new development

The existing files `PolyG/*.agda` follow the POPL paper, with `hide`
and an instantiation that only names an existing type variable.
Reading them showed three problems:

* **Reduction is not deterministic.** The frames `appR□` and `pairR□`
  take any term, not a value.
* **Type safety is not established.**
  * `progress` is stated over static typing, which cannot type a seal.
  * `preservation` rests on 10 postulates.
  * One of them, `rightTy-ground`, is false: with `p = pDyn` and
    `G = GBool`, `rightTy p = TDyn ≠ TBool`.
* **The surface language can only instantiate `∀` inside a package
  body.**

So the warm-up is a new development in `PolyG/agda/`, laid out as in
AGENTS.md, following the thesis:

* **Definitions:**
  * `Types` (types, grounds, precision derivations, type substitution);
  * `Terms` and `Reduction` (PolyCν with proxies, value-restricted
    frames);
  * `Typing` (runtime typing over a store);
  * `GradualTerms` and `Compile` (PolyGν, consistency, meet,
    elaboration);
  * `TermPrecision` and `GradualTermPrecision`.
* **Proofs** (`proof/`): determinism, progress, preservation, type
  safety, elaboration preserves typing and precision.
* **The denotational development:** `GraphModel`, `Denotation`, then
  `proof/Denot*` (properties, soundness, adequacy, relations, cast
  lemmas, fundamental lemma, theorem) and `MetaTheory`.

The old flat files become obsolete once this is in place.

## 10. Size

The GTLC denotational development is about 3,400 lines.  The fragment
has roughly twice GTLC's term formers, plus the counter and the labels;
estimate 6,000–8,000 lines for the denotational part.  The substrate
(types, terms, typing, reduction, type safety, surface language,
elaboration, both precisions and their lemmas) is another 4,000–6,000.

## 11. What carries over to GTSFImp

* **Carries over:**
  * the counter-threaded graph model;
  * `Λν` graphs indexed by the labelled seal the instantiation creates;
  * relational labels on seal-creating forms in place of worlds;
  * recursion on elements;
  * cast lemmas organised by up/down and left/right.
* **Does not carry over: lockstep.** GTSFImp's `inst` casts create seals
  on one side only (`β-inst` allocates `bind ★`), and its `gen` casts
  use a fresh name as a runtime tag.  So results on the two sides end
  at different counters.
  * A seal created on one side only can carry a label saying how its
    contents relate to the unsealed value on the other side (an
    `X ⊑ ★` mark).
  * Shared seals must still be named the same on both sides.  One way to
    do that is to number shared and one-sided seals separately.
  * This must be done without existential worlds, for the reason given
    in Section 5.

  This is the main new difficulty for GTSFImp; the warm-up does not
  exercise it.
