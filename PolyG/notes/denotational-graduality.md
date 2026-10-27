# A Denotational Proof of Graduality for PolyGν

Status: design on paper (revised: worlds, consistency, joint lists).
The substrate (Section 9) is mechanized; the denotational part is not.  This is the
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

* **Seals are created in lockstep** (Section 2).  One counter serves
  both programs, and a seal has the same number on both sides.  The
  paper's partial bijection between the two stores is the identity.
* **The model is a graph model with a seal counter and consistency.**
  * A term denotes, for each starting counter, a set of results
    `ret v m` and `err`; divergence is the empty set.
  * As in the compiler-correctness development, the binders take only
    consistent argument lists.  So a denotation under a consistent
    environment is a consistent set: its elements are approximations of
    one outcome along one evaluation path.
  * A `Λν` denotes a graph from the fresh seal its instantiation
    creates to the result of its body.
* **The relations use Max's worlds.**
  * A world gives, for each seal created so far, the precision
    derivation that relates its contents on the two sides.
  * A computation's world is existential, extended at each
    instantiation, and closures quantify over future worlds.
* **The relations relate finite lists jointly, not single elements.**
  * An existential world must cover every element that a later step
    uses together: an entry and its argument list, or a group of
    results passed to a continuation.
  * So the relations relate a finite list of elements on one side to a
    set on the other, under one world (Section 5).
  * They are defined by recursion on the total size of the list, and
    then on the precision derivation.
* **The proof has the GTLC shape.**
  * The fundamental lemma is two independent inductions on PolyCν term
    precision, with eight cast lemmas.
  * Elaboration preserves term precision (the thesis's Lemma 218), so
    the theorem is stated for PolyGν.
  * It follows from soundness, adequacy and type safety.

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

Seals are natural numbers.  A seal environment `θ` maps type variables
to seals; `θ̂` extends it to names (`θ̂ X = θ X`, `θ̂ σ = σ`) and to
grounds.

Values and results:

    v ::= true | false | seal σ v | inj G v
        | (U , m) ⟼ r        function entry: arguments U at counter m
        | σ ⟼∀ r             Λν entry: instantiated at the fresh seal σ
        | νλ | ν∀            the empty function and the empty Λν
    r ::= ret v m | err

* `U` is a finite nonempty list of values.
* `G` is a closed ground: `σ`, `Bool`, `? → ?` or `∀ν X.?`.
* Values never contain `err`, so GTLC's `ValSet` and `NoErr` bookkeeping
  disappears.
* There are two empty closures, so that a cast at `⇒` or `∀ν` applied to
  the wrong kind of value denotes nothing, like the stuck term it is.
  With a single `ν`, `cast up (∀⊑ ★⊑) true` would denote a `Λν` and
  adequacy would fail.

**Consistency**, as in the compiler-correctness development:

    b ~ b
    seal σ u ~ seal σ′ u′          iff σ = σ′ and u ~ u′
    inj G u ~ inj H u′             iff G = H and u ~ u′
    (U , m) ⟼ r ~ (U′ , m′) ⟼ r′   iff m = m′ and U ≈ U′ imply r ~ r′
    σ ⟼∀ r ~ σ′ ⟼∀ r′              iff σ = σ′ implies r ~ r′
    νλ ~ νλ, and νλ ~ any function entry (both ways)
    ν∀ ~ ν∀, and ν∀ ~ any Λν entry (both ways)
    ret v m ~ ret v′ m′            iff m = m′ and v ~ v′
    err ~ err
    anything else                  inconsistent

Here `U ≈ U′` holds when every element of `U` is consistent with every
element of `U′`.

For a set of results `R`:

    ⌊R⌋ₘ   = { v | ret v m ∈ R }             the values at counter m
    R ≫= K = { err | err ∈ R }
           ∪ ⋃ₘ { r | ⌊R⌋ₘ ≠ ∅ , r ∈ K ⌊R⌋ₘ m }

Closures bind only finite, nonempty, consistent lists:

    Λ F      = { (U , m) ⟼ r | r ∈ F (mem U) m , U ≠ [] , U ≈ U } ∪ {νλ}
    F ●ₘ E   = { r | (U , m) ⟼ r ∈ F , mem U ⊆ E }
    Λν F     = { σ ⟼∀ r | r ∈ F σ } ∪ {ν∀}
    F ◆ σ    = { r | σ ⟼∀ r ∈ F }

The body of a `Λν` entry for seal `σ` starts from counter `σ + 1`,
because instantiation creates seal `σ` from counter `σ`.

**Consistency theorem.** If every set in the environment is consistent,
so is every denotation.  The proof is by induction on terms, as in the
compiler-correctness development.  As a consequence, all values in a
denotation end at the same counter, because `ret v m ~ ret v′ m′` needs
`m = m′`.

## 4. The denotation

`⟦M⟧ θ ρ n` for PolyCν; a runtime name `tseal σ` denotes `σ`.  `ret D n`
is `{ ret v n | v ∈ D }`.  Selected clauses:

    ⟦x⟧                   = ret (ρ x) n
    ⟦℧⟧                   = {err}
    ⟦λx:A. M⟧             = ret (Λ (λ E m → ⟦M⟧ θ (E • ρ) m)) n
    ⟦M N⟧                 = ⟦M⟧ n ≫= λ F n₁ → ⟦N⟧ n₁ ≫= λ E n₂ → F ●ₙ₂ E
    ⟦Λν{X.(cs, M)}⟧       = ret (Λν (λ σ → ⟦cs⟧ (⟦M⟧ (σ • θ) ρ (σ + 1)))) n
    ⟦let x = M{X≅B}; N⟧   = ⟦M⟧ n ≫= λ F n₁ → F ◆ n₁ ≫= λ E n₂ →
                            ⟦N⟧ (n₁ • θ) (E • ρ) n₂
    ⟦seal α M⟧            = ⟦M⟧ n ≫= λ E n₁ → ret (seal (θ̂ α) E) n₁
    ⟦unseal α M⟧          = ⟦M⟧ n ≫= λ E n₁ → ret (unseal (θ̂ α) E) n₁
    ⟦is(G)? M⟧            = ⟦M⟧ n ≫= λ E n₁ → ret (test (θ̂ G) E) n₁
    ⟦⟨A⊑⟩↕ M⟧             = ⟦M⟧ n ≫= ⟦↕ , A⊑⟧ θ

`⟦cs⟧` applies a cast stack, innermost first.  Casts never change the
counter.  `⟦↕ , A⊑⟧ θ E m` is defined by recursion on `A⊑`:

    ?, Bool, α          ret E m
    A⊑ → B⊑             ret (Λ (λ E′ m′ → ⟦↕⁻ , A⊑⟧ E′ m′ ≫= λ E₁ m₁ →
                                  E ●_{m₁} E₁ ≫= ⟦↕ , B⊑⟧)) m,  if νλ ∈ E
    ∀ν X. A⊑            ret (Λν (λ σ → E ◆ σ ≫= ⟦↕ , A⊑⟧ (σ • θ))) m,  if ν∀ ∈ E
    ↑ tag_G(A⊑)         ⟦↑ , A⊑⟧ E m ≫= λ E₁ m₁ → ret (inj (θ̂ G) E₁) m₁
    ↓ tag_G(A⊑)         the payloads tagged θ̂ G, cast down by A⊑,
                        and err if some element has another tag

The tag clause is GTLC's `proj`.  The `∀ν` clause is the thesis's proxy
rule read as a graph.

## 5. Worlds, and why the relations relate lists

A **world** `W` is a list of closed precision derivations: `W σ` relates
the contents of seal `σ` on the two sides.  `W ⊑ W′` when `W` is a
prefix of `W′`.  As in Max's relation, a computation's world is
existential, and closures quantify over future worlds.  A world also
links the environment to seals.  When a value sealed at `X` is hidden
in `?`, then cast back to `X` and unsealed, the relation for `?`
reads the seal's derivation from the world, and the environment
invariant says the world's entry for `θ X` is `X`'s derivation.

**Why single elements are not enough.** If each element had its own
existential world, a step that uses several elements together would
need to merge their worlds.
* Two such steps: application, which uses an entry together with an
  argument list, and bind, whose continuation uses a whole group of
  results.
* Two worlds of the same length need not agree.  An element can mention
  a seal only in the argument positions of its function entries, where
  nothing pins that seal's derivation.

**Why not sets with a depth index.** Relating whole sets needs an index
for well-foundedness, because the clause for `?` recurses at `? → ?`.
Element depth does not work as that index.
* Elimination produces shallow elements from deep ones: an
  application's result is a sub-element of the entry it uses.
* So a subterm must be related at a higher index than its context.
* That conflicts with an existential world chosen at each index.

**Joint lists.** The relations relate a *finite list* of elements on
one side to a set on the other, jointly, under one world.
* A computation relation gives one existential world per list.
* A function clause takes the arguments of a list of entries jointly,
  and gives one world for their results.
* The recursion is on the total size of the list, which shrinks from a
  list of entries to their arguments and results.  The index is
  determined by the list, so nothing is quantified over indices.
* The fundamental lemma reaches finite lists through finite support:
  each result depends on finitely many elements of its inputs.

**Where consistency is needed.** Consistency is what makes the joint
statements true: one world can serve a list only if the list does not
mix two evaluation paths.
* **On the set side only.** Each relation needs consistency of its
  *set* side only:
  * for reflection, the right (less precise) side;
  * for preservation, the left side.

  A list related to a consistent set cannot mix paths.
  * A list of booleans related to a consistent set contains `true`
    only or `false` only.
  * A list of values in `?` related to a consistent set carries a
    single tag.
* **Where the proof uses it.** At branching: `if`, `is(G)?`, and
  projections.  It also gives a single counter, because a list of
  results related to a consistent set ends at one counter.
* **Not on the list side.** The list side need not be consistent.  It
  could not be required anyway: function entries whose arguments have
  no counterpart are related vacuously, so relatedness does not imply
  consistency.

## 6. The relations

Reflection relates a finite list `L` of left (more precise) values to a
right set: `W ∣ θ ⊢ A⊑ ⊢ L ▹ D′`.  For a finite list `Rs` of left
results:

    W ∣ θ ⊢ A⊑ ⊢ Rs ▹ᶜ R′  =  for each counter m, there is W′ ⊒ W with
                               |W′| = m and
                               W′ ∣ θ ⊢ A⊑ ⊢ (values of Rs at m) ▹ ⌊R′⌋ₘ

Errors in `Rs` need nothing.  On value lists, by recursion on the total
size of `L` and then on `A⊑`:

    Bool        every element is a boolean b with b ∈ D′
    ?           every element is inj G u, and for each G:
                (payloads tagged G) ▹ untag G D′ at G⊑ (closed)
    tag_G(A⊑)   L ▹ untag (θ̂ G) D′ at A⊑
    α           every element is seal σ u with σ = θ̂ α < |W|, and
                (payloads) ▹ unseal σ D′ at W σ (closed)
    A⊑ → B⊑     every element is a function entry or νλ; νλ ∈ D′ if L ≠ [];
                for every sublist L₀ of L and counter m, with L₀ₘ the
                entries of L₀ at m: for every W′ ⊒ W with |W′| = m and
                every consistent E′, if (all arguments of L₀ₘ) ▹ E′ at A⊑
                under W′, then (results of L₀ₘ) ▹ᶜ D′ ●ₘ E′ at B⊑ under W′
    ∀ν X. A⊑    every element is a Λν entry or ν∀; ν∀ ∈ D′ if L ≠ [];
                for each seal σ, with L_σ the entries of L at σ:
                for every W′ ⊒ W with |W′| = σ and every closed B⊑,
                (results of L_σ) ▹ᶜ D′ ◆ σ at A⊑, under W′ ++ [B⊑] and σ • θ

* **Ground derivations.** `G⊑` is the reflexive derivation of the
  ground `G`.  Closed derivations, whether from grounds or from the
  world, are read at a fixed seal environment `θ₀`.
* **Preservation.** It is the mirror image on lists of right elements:
  * a list of right results `Rs′` is related to `R` if `err ∈ R`;
  * otherwise `Rs′` must contain no `err`, and for each counter its
    values must be matched, under one world, by the left set at that
    counter.

  Because `Rs′` is a finite list, the case split is constructive, and
  GTLC's element-by-element escape (`fbind◃`) is no longer needed.
* **Sublists.** The function clause quantifies over sublists so that the
  relations are closed under sublists.  Without it, a sublist's entries
  would get nothing whenever the other entries' arguments fail to match.
  Environments need this closure.
* **Termination.** Every clause shrinks the total size of the list
  except `tag_G`, which keeps the list and shrinks `A⊑`.
* **Basic properties:**
  * monotonicity in the set side;
  * Kripke monotonicity in the world;
  * downward closure under sublists;
  * a list of booleans or of injections related to a consistent set is
    uniform.

**Environments.**
* For reflection, each `ρ′ x` is consistent, and every finite sublist
  of `ρ x` is related to `ρ′ x` at `x`'s derivation, under `W`.
* For preservation, `ρ x` is consistent instead.
* For a known `X ≅ q`: `θ X < |W|` and `W (θ X) = ⟦q⟧θ`, the closed form
  of `q`.
* The closing lemma (`θ ⊢ q` iff `θ₀ ⊢ ⟦q⟧θ`) connects the two.

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

**Fundamental lemma** (reflection; preservation is analogous).  Assume:
* `M ⊑ M′` at `A⊑`;
* related environments at `W`, with `|W| = n`;
* a finite list `Rs` of left results of `⟦M⟧ θ ρ n`.

Then `Rs ▹ᶜ ⟦M′⟧ θ ρ′ n` at `A⊑`.  The proof is by induction on term
precision.  The cases that sank the earlier designs, checked on paper:

* **`let` (bind).** Each result in `Rs` lies in `⟦N⟧ (mem Lᵢ • ρ) m` for
  a finite `Lᵢ` of values of `M`, by finite support.  There is a single
  `m`.  Left values at two counters would need right counterparts at
  both, but the right denotation is consistent, so it ends at one
  counter.  Let `L = ⋃ Lᵢ`.
  * The induction hypothesis for `M` on `L` gives `W₁`.
  * The induction hypothesis for `N`, with `x ↦ (mem L , ⌊⟦M′⟧⌋ₘ)` at
    `W₁`, gives `W₂` for all of `Rs`, by monotonicity in `Lᵢ ⊆ L`.
  * The right-hand results of `N′` under that environment are among the
    right results of the `let`.
* **Application.** Each result comes from an entry `eᵢ` of the
  function's values, used with arguments `Uᵢ` drawn from the argument's
  values.
  * The induction hypothesis for the function on `[eᵢ]` gives `W₁`.
  * The induction hypothesis for the argument on `⋃ Uᵢ`, at `W₁`
    (environments are Kripke monotone), gives `W₂`.
  * The function clause, at `W₂` and the argument's counter, relates
    all the results jointly to `F′ ●ₘ E′`.
* **`λ`.** Fix a counter `m`, a world `W′` and a consistent `E′`, with
  the arguments `A = concat Uᵢ` related to `E′`.
  * The entries' results lie in `⟦N⟧ (mem A • ρ) m`, by monotonicity.
  * The left environment need not be consistent; the right one is,
    because `E′` is.
  * The induction hypothesis for `N` gives the world.
  * On the right, `⟦N′⟧ (E′ • ρ′) m ⊆ Λ F′ ●ₘ E′` by `Λ-β`, using finite
    support and the consistency of `E′`.
* **`Λν` and instantiation.**
  * `Λν`: for each seal `σ`, the induction hypothesis for the body at
    `σ • θ` and `W′ ++ [B⊑]`.  An abstract `X` asks nothing of the
    world.
  * Instantiation: the induction hypothesis for `M` gives `W₁` with
    `|W₁| = n₁`.  The `∀ν` clause at `W₁` with `B⊑ = ⟦q⟧θ` gives
    `W₂ ⊒ W₁ ++ [⟦q⟧θ]`.  The induction hypothesis for `N`, with
    `X ≅ q`, needs `W₂ n₁ = ⟦q⟧θ = ⟦⇑q⟧(n₁ • θ)`.
* **A seal through `?` and back.** Left values `inj σ (seal σ wᵢ)` are
  related at `?`, so the contents `wᵢ` are related at `W σ`.
  * The down-cast lemma at `tag_X` turns this into the relation at `X`.
  * Unseal uses the environment invariant `W (θ X) = ⟦q_X⟧θ` and the
    closing lemma.

  The world is the link that typed seals lacked.
* **Branching.** The condition's left values are related to the right
  condition's values, which are consistent.  So the left values contain
  `true` only or `false` only, and all of `Rs` comes from one branch.
  Tag tests and projections are similar.
* **Casts.** These follow the cast lemmas.

**Cast lemmas**, by induction on the derivations, for each relation:
* an up cast on the left or right moves `AC⊑` to `BC⊑` or `AB⊑`;
* a down cast moves it back.

These are GTLC's coercion lemma, organised by the thesis's four rules.
* The function case pulls the wrapper's arguments through the flipped
  lemma, applies the original entries jointly, and pushes the results
  through, all under the world the function clause provides.
* The `∀ν` case keeps the seal and passes the instantiation's `B⊑`
  through.
* The `tag_G` cases are GTLC's `inj`/`proj` cases.  A projection's
  error on the right is matched on the left because related values
  carry the same tag.

**Soundness.** A step `Σ ▷ M ↦ Σ′ ▷ N` gives `⟦N⟧ |Σ′| ⊆ ⟦M⟧ |Σ|`.  This
needs the type-substitution lemma `⟦M[σ/X]⟧ θ = ⟦M⟧ (σ • θ)` and the
term-substitution lemma, but no typing.

**Adequacy.** An element `ret v m ∈ ⟦M⟧ |Σ|` comes from a reduction to a
value with the same observation, ending in a store of length `m`.  It
uses determinism.  With separate empty closures (`νλ`, `ν∀`), stuck
casts denote nothing, so no typing is needed.

**Theorem** (observational form, as in GTLC).  Take closed PolyGν terms
`Mₗ ⊑ Mᵣ`, with their elaborations run from the empty store:
* if `Mₗ` reaches a value, `Mᵣ` reaches one with the same observation;
* if `Mᵣ` reaches a value, `Mₗ` reaches one with the same observation
  or fails;
* if `Mᵣ` fails, so does `Mₗ`;
* if `Mₗ` diverges, so does `Mᵣ`;
* if `Mᵣ` diverges, every term `Mₗ` reaches can step or is `℧`.

The divergence clauses use type safety.

**What is retired.** The instantiation labels, relabeling and the
label-irrelevance simulation are no longer needed.  The language is
exactly the thesis's.

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

The definitions and these proofs are mechanized.  The old flat files
become obsolete once the denotational part is in place.  The
instantiation labels added for the abandoned label design (Section 8)
are to be removed.

## 10. Size

The GTLC denotational development is about 3,400 lines.  Here there are:
* roughly twice GTLC's term formers;
* a seal counter;
* consistency, with its preservation theorem;
* joint lists and worlds in the relations.

Estimate: 7,000–10,000 lines for the denotational part.  The substrate
(Section 9) is mechanized: about 3,500 lines.

## 11. What carries over to GTSFImp

* **Carries over:**
  * the counter-threaded graph model with consistency;
  * `Λν` graphs indexed by the seal the instantiation creates;
  * worlds;
  * joint-list relations;
  * cast lemmas organised by up/down and left/right.
* **Does not carry over: lockstep.** GTSFImp's `inst` casts create seals
  on one side only (`β-inst` allocates `bind ★`), and its `gen` casts
  use a fresh name as a runtime tag.  So:
  * results on the two sides end at different counters;
  * a world becomes the paper's partial bijection `η` between left and
    right seals, plus one-sided seals marked `X ⊑ ★`.

  With existential worlds per joint list, this is a change to what a
  world is, not to how the relations use it.  It is the main new
  difficulty for GTSFImp, and the warm-up does not exercise it.
