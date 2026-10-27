# A Denotational Proof of the Dynamic Gradual Guarantee for GTSFImp

Status: design on paper; nothing is mechanized.  Revised after review:
the fundamental lemma is on cast-calculus precision, and the GSF and
`Catchup` counterexamples are checked (Section 8).

This builds on the PolyG warm-up:
* `PolyG/notes/denotational-graduality.md`;
* `PolyG/agda/`, PR #214; this branch starts from it.

The PolyG proof is complete, so the questions here are only what changes
for GTSFImp.

Conventions are those of GTSFImp: in `A ⊑ B` and `M ⊑ M′` the left side
is the *more* precise one.

## 1. Summary

* **Same architecture as PolyG.** The plan reuses:
  * a graph model with seal counters and consistency;
  * Max-style worlds;
  * reflection and preservation relations that relate finite lists
    jointly;
  * soundness and adequacy;
  * a fundamental lemma.
* **What is new**, all caused by GTSFImp's implicit polymorphism (the
  `inst` and `gen` casts) and its one-sided precision rules:
  1. **Seals are not created in lockstep.** The two programs keep separate
     counters, and a world relates left seals to right seals, Max's
     partial bijection `η`.
  2. **One-sided seals.** A seal created only on the left, by a left-only
     type application or a left `inst`, is related to *unsealed* values on
     the right, at a derivation `R ⊑ ★` (an `X ⊑ ★` mark).  The relation
     for `★` looks through a left tag on such a seal.
  3. **Seals created by casts.**
     * `inst` creates a seal when the cast is applied.
     * `gen` creates one when its result is instantiated, and uses it as
       a runtime *tag*.
     * A right-only seal never reaches the boundary between the related
       programs, so worlds only count it.
  4. **Conversions.** Sealing and unsealing (`↓ seal`, `↑ unseal`) are
     inserted by allocation; they get their own lemma.
  5. **The fundamental lemma is on cast-calculus precision.** It uses a
     new, simplified term precision for the cast calculus (Section 7)
     with one-sided cast rules, as in PolyG, and elaboration must
     preserve it.  The existing target relation
     (`proof/DGG/CastTermImprecision`, `⊢²`) is not used.
  6. **Two type contexts in precision.** Type precision relates a left
     context and a right context through a variable correspondence: each
     left variable is either paired with a right variable or left-only.
     `X ⊑ Y` needs a pair, and `X ⊑ ★` needs a left-only `X`.  GTSFImp's
     single-context type precision, where `X ⊑ X` is derivable
     unconditionally, is what admits the `Catchup` counterexample
     (Section 8).

## 2. The language, as far as the proof is concerned

* **Intrinsic scoping.** Terms are intrinsically scoped (`Term Δ`).  The
  runtime type context `Δ` holds both bound type variables and seals, and
  allocation extends `Δ` (`bind A`).
* **Seals as numbers.** The denotation interprets type variables by a
  seal environment `θ : TyVar Δ → Seal`, as in PolyG, so de Bruijn
  shifting at allocation is a soundness-lemma matter only.
* **Where seals are created** (`Reduction.agda`):

  | rule | redex | seal created |
  |---|---|---|
  | `β-Λ` | `(Λ V) ⦂∀ B [A]` | `α := A`, then the reveal `V ↑ 〖α , A ↑ B〗` |
  | `β-inst` | `V ⟨inst c⟩`, at the cast | `α := ★`; reveal; then `↑ᶜ (c[★/0])` |
  | `β-gen` | `(V ⟨gen c⟩) ⦂∀ B [C]` | `α := C`; inside `c`, `α` has mode `★∼X` and is used as a ground tag |
  | `β-reveal-∀`, `β-conceal-∀` | conversions at `∀` when instantiated | a seal, as `β-Λ` |

* **Instantiation is administrative.** `Λ` bodies are values and `GenSafe`
  keeps failing checks out of suspended `gen` casts (`Rationale.md`).  So
  an instantiation produces a value without running anything.  Section 6
  uses this.
* **Casts carry modes.** A consistency derivation `μ ⊢ A ∼ B` carries a
  mode environment (`X∼X`, `X∼★`, `★∼X`, `★∼X∼★`).  Ground tags include
  type variables, and so seals at runtime.
* **Source precision** (`GradualTermImprecision.agda`) is structural,
  plus two one-sided rules:
  * `Λ⊑ᴳ` (`Λ V ⊑ N′` at `∀ A ⊑ B`, through `X ⊑ ★`);
  * `[]⊑ᴳ` (`M [T] ⊑ M′`, with `q : T ⊑ ★`).

  Type precision has `X ⊑ ★` marks (`instᵐ`), `∀⊑`, `∀⊑★` and the two
  `bot` rules.

## 3. Which side creates seals

* **Shared.** A type application on both sides (`[]⊑[]ᴳ`) creates a seal
  on each side.  These are paired in the world with the derivation `q`
  that the rule gives for the type arguments.
* **Left-only.**
  * A left-only type application (`[]⊑ᴳ`) creates a left seal with no
    right partner.  Its contents are related to the right program's
    unsealed `★` values at the rule's `q : T ⊑ ★`.
  * A left `inst` cast creates a left seal represented by `★`, so its
    contents are related to right `★` values at `★ ⊑ ★`.
* **Right-only.** A right `inst` cast where the left keeps a `∀` type
  creates a right seal.
  * The right `inst` immediately wraps the instantiated body in the
    reveal `〖α′ , ★ ↑ A〗`.
  * Because `inst` closes the variable at `★`, no tag for `α′` is ever
    created ("no variable-ground consistency casts for `α` remain",
    `Rationale.md`).
  * So `α′`-sealed values exist only inside the right value's graph,
    never at the boundary.
* **Left before right.** The left can never instantiate before the right
  on a shared polymorphic value.
  * If the right keeps a `∀` type, precision forces the left to have one
    too (`∀⊑∀` is the only rule with `∀` on the right), so the left has
    no `inst` there.

  So the left side has every shared seal plus left-only ones, and the
  right side has every shared seal plus invisible right-only ones.

## 4. Worlds

A world is a pair of lists, extended independently:
* **Left entries, by left seal:**
  * `shared σ′ q`, paired with right seal `σ′`, contents related at the
    closed derivation `q`;
  * `left q`, a left-only seal, contents related to right unsealed
    values at `q : R ⊑ ★`.
* **Right entries, by right seal:** `shared σ` or `right` (right-only,
  never consulted by the relations).

`W ⊑ W′` when both lists are prefixes.  The left counter is the left
list's length; the right counter is the right list's.

## 5. The relations

These are the PolyG relations (joint lists, existential world per list,
Kripke closures, consistency on the set side), with these changes:

* **Results.** A list of left results at left counter `m` is related if
  there is a future world with left length `m` and some right length
  `m′` under which its values are related to the right set at `m′`.
  With consistency, the right set has one counter.
* **Seal clause at `‵⊑ X`.** Take a left value `seal σ u` with
  `σ = θ X`:
  * if `W σ = shared σ′ q`: the contents are related at `q` to
    `unseal σ′ D′`;
  * if `W σ = left q`: the contents are related at `q` to `D′` itself.
    This is the clause the `X ⊑ ★` derivation `＇X ⊑ ★` uses.
* **Clause for `★ ⊑ ★`.** For a left value `inj σ u` whose tag is a seal:
  * if `W σ = shared σ′ q`: the payload is related to `untag σ′ D′`;
  * if `W σ = left q`: the payload `u` (sealed at `σ`) is related through
    the left-only seal clause to `D′` itself.  The right program never
    tagged the value with `σ`, since it never created `σ`.

  The `gen` worked example in Section 6 shows why.
* **The `∀` clauses:**
  * `∀⊑∀ p`: a left entry at a fresh left seal `σ` against the right
    entries at a fresh right seal `σ′`, for every future world and every
    closed `q′`, in the world extended with `shared σ′ q′` and `shared σ`.
  * `∀⊑ p` (left `∀`, right not): a left entry at fresh `σ` against the
    right *value set itself* at the current right counter, in the world
    extended with `left q′`.  The right does not instantiate.
  * `∀⊑★ p`: against the right's `∀★`-tagged values, as `∀⊑∀`.
* **Ground grammar.** Function and `∀` entries and the empty closures are
  as in PolyG.  The ground tag grammar adds `ℕ` (constants) and seals.

## 6. Paper checks of the new cases

* **A left-only `Λ` (`Λ⊑ᴳ`).** Left `(Λ X. λx:X. x) [𝔹] true`, right
  `(λx:★. x) (true⟨𝔹!⟩)`, at `∀X.X→X ⊑ ★→★` then `𝔹 ⊑ ★`.
  * The left creates `α` with the world entry `left (𝔹 ⊑ ★)`.
  * The reveal conceals the argument as `seal α true`.  It is related
    through the left-only seal clause to the right argument `inj 𝔹 true`.
  * The body returns it, and the reveal unseals it to `true`.
  * The result is related at `𝔹 ⊑ ★` to the right's `inj 𝔹 true`.
* **`gen` with a left-only type application.** Left `(f ⟨gen c⟩) [C]`,
  where `f : ★→★`, `c` is `X! ↦ ?X` with `X : ★∼X`.  Right: the same
  `f` at `★→★` with no `gen` and no type application.
  * The left creates `α` as `left (C ⊑ ★)`.
  * An argument `v : C` is concealed to `seal α v`, then tagged `α` by
    `X!`, so `f` sees `inj α (seal α v)`.
  * The right `f` sees the corresponding unsealed `★` value.  The `★`
    clause for a left-only tag relates them.
  * If `f` returns its argument, `?X` succeeds on the left and the
    results agree.  If it returns anything else, `?X` fails on the left,
    which reflection allows.
* **A right `inst` while the left stays `∀`, instantiated later.** Right
  `V′ ⟨inst c′⟩` with `α′` created at right counter `n′`; left `V` keeps
  its `∀` type and is instantiated later at left counter `m`, creating
  `σ`.  We have `V ▹ V′` at `∀⊑∀ p₀`, in a world `W` with right length
  `n′`.
  * Choose the future world that extends only the left list, up to
    length `m`.  This is a legal extension: the right made no allocation
    between `n′` and `α′`.
  * Pair `σ` with `α′` there; the `∀⊑∀` clause relates the two bodies.
  * The **conversion lemma** (Section 7) then turns this into the
    relation the conclusion needs, `∀⊑` with `σ` left-only: the right's
    reveal `〖α′ , ★ ↑ A〗` unseals `α′` at the boundary.
  * Instantiation being administrative is what makes this sound.  The
    right instantiated body is a value with no effects, so it does not
    matter that the right did it early.
* **Seal identity under consistency.** Consistency of the right set pins
  the right tag for a shared seal, as in PolyG.  For a left-only seal
  there is no right tag to pin.

## 7. The lemmas

* **Cast-calculus term precision.** This replaces the use of
  `GradualTermImprecision` in the fundamental lemma.
  * It is a new relation between cast terms over two type contexts with
    a variable correspondence (summary item 6).
  * It has structural rules, the one-sided `Λ` and type-application rules
    (left `Λ` or `[T]`, right nothing, through a left-only variable), and
    one-sided cast rules.
* **Cast rules (decision: no factorization).** Factoring a cast through
  a selected lower bound fails, because `lower?` is not monotone (risk 1).
  So casts are related directly, as in an earlier treatment of the same
  problem.
  * **Two-sided cast rule.** From `M ⊑ M′` at `C ⊑ C′`, with consistency
    derivations `c : C ∼ A` and `c′ : C′ ∼ A′` and with `A ⊑ A′`,
    conclude `M ⟨c⟩ ⊑ M′ ⟨c′⟩` at `A ⊑ A′`.  The premise names no bound.
  * **One-sided right cast**, for the projection `★ ∼ ★ ⇒ ★` that
    `compile` inserts on the right of `·⊑·★ᴳ` when the left has a
    function type: from `M ⊑ M′` at `A ⊑ B`, with `c′ : B ∼ C` and
    `A ⊑ C`, conclude `M ⊑ M′ ⟨c′⟩` at `A ⊑ C`.  A matching one-sided
    left rule is added only if `compile` needs one.
* **The cast lemma** is *monotonicity of consistency casts*.  It is
  proved semantically, by induction on the two derivations, for both
  relations, at the level of computations, because `inst` and `gen`
  create seals.
  * The cases where the two sides choose differently are the core: for
    example `inst` then `gen` on one side and `gen` then `inst` on the
    other, as in the counterexample of risk 1.
  * They rely on instantiation being administrative: *when* a seal is
    created does not matter, only which seals and tags are checked.
  * The one-sided right rule is the special case with no cast on the
    left.
* **Elaboration preserves precision.** This becomes direct: at each
  source application, the source typing supplies `c` and `c′` at related
  types, which is exactly the premise of the two-sided rule.
* **Conversion lemma.** The reveal and conceal conversions
  `〖α , R ↑ B〗` and `makeConceal` relate the two forms of a seal:
  * a shared pairing of `α` seen through the conversions;
  * a left-only (or right-only) seal at the boundary.
* **Unchanged from PolyG**, adapted: soundness, adequacy, the
  consistency theorem, monotonicity, finite support and the
  substitution lemmas.  New cases: conversions, primitives (`⊕`, `ℕ`),
  and allocation at casts.

## 8. Risks and open questions

1. **Monotonicity of the selected lower bound: checked, it fails.**
   * **How it was checked.** A brute-force search: `lowerAcc` and type
     imprecision ported faithfully to Python, over all 126 closed types of
     size ≤ 5 and the 1,888 consistent pairs among them.
   * **What it found.** Six violations, all of one shape: the binder-order
     problem GTSF met.  The smallest:

         C  = ∀X.★→X   A  = ∀X.∀Y.X→Y   lower? C A   = ∀X.∀Y.X→Y
         C′ = ∀X.★→X   A′ = ∀X.X→★      lower? C′ A′ = ∀X.∀Y.Y→X

     Here `C ⊑ C′` and `A ⊑ A′`, but the two bounds differ only in binder
     order and are unrelated by `⊑`.
   * **Why `lower?` picks this way.** For `∀` against `∀` it tries `∀ᶜ`,
     then `inst`, then `gen`.  Here `∀ᶜ` fails, because it would need
     `★ ∼ X` with mode `X∼X`.  So the choice falls to the `inst`/`gen`
     order, and that order is not preserved when `A` loses precision.
   * **Is it semantic?** Probably not.  Declaratively, `C′ ∼ A′` has two
     derivations:
     * `inst` then `gen`: create `α` for `X` at cast time, wrap in `gen`
       for `Y`;
     * `gen` then `inst`: `gen` outermost, and `α` created when `Y` is
       instantiated.

     They differ only in *when* `α` is created, not in which seals and tags
     are checked:
     * the input is concealed at `Y`'s seal and tagged with it;
     * the result is sealed at `α` and unsealed to `★`.

     Instantiation is administrative, so the two casts should behave the
     same.  Then the failure is an artifact of factoring each cast
     through the *selected* bound, not a violation of the gradual
     guarantee.
   * **Consequences for the design** (Section 7):
     * Elaboration cannot establish the "right down, right up" route
       through `lower?`.
     * Options:
       * (a) give `Λ`-binder order a canonical choice that is monotone, for
         example always `gen` before `inst`, or by binder position;
       * (b) replace the one-sided right cast rule by a two-sided cast rule
         for casts at related types, proved semantically: monotonicity of
         consistency casts, with no factorization;
       * (c) let the cast-calculus precision carry its own lower-bound
         witnesses, related by a permutation-aware precision on bounds.
     * **Decision: option (b).** It is closest to the semantic proof
       and avoids choosing bounds altogether.  Its cast lemma is then about two derivations
       at related types, and the `inst`/`gen` order question above
       becomes one of its cases.
2. **The GSF counterexample: checked, excluded by precision.**
   * The counterexample (Labrada, Toro and Tanter, Section 8.1) is
     `idX = ΛX.λx:X.x :: X` against `id? = ΛX.λx:?.x :: X`.
     `idX [Int] 1` gives `1`, but `id? [Int] 1` errors.
   * In GTSFImp the two are not related.
     * `Λ⊑Λᴳ` checks the body under `extᵐ`, where `X ⊑ X` only, so
       `λx:X ⊑ λx:★` is not derivable.  `X ⊑ ★` exists only for
       `instᵐ` variables.
     * Those come from `∀⊑` (`Λ⊑ᴳ`), where the right side has no `Λ` and
       no type application at all.
   * This is GSF's *strict* precision for `Λ`-bound variables.  The
     cause of their failure is non-monotone consistent transitivity
     (`⟨Int, α⟩ ∘ ⟨α, Int⟩` against `⟨Int, α⟩ ∘ ⟨?, ?⟩`).  That needs a
     *shared* seal related to `?`, which strict precision forbids.
   * The `X ⊑ ★` that GTSFImp does allow is one-sided: the right program
     never seals.  The relation's left-only seal clause handles it, and
     the related variant checks on paper:
     * left `idX [Int] 1` against right `(λx:★. x) 1`, through `Λ⊑ᴳ` and
       `[]⊑ᴳ`;
     * both give `1`, related at `Int ⊑ ★`.
3. **The `bot` rules.**
   * `bot-intro` blames eagerly, which is fine on the left (an error is
     allowed) and must be matched on the right.
   * `bot-elim` relates the empty universal, which has no closed value.
4. **The `Catchup` counterexample: checked, excluded by two-context
   precision.**
   * `Catchup/ExtraCastRightLemma.agda.pending` relates a left sealed
     value to a right raw `★` value at `＇X ⊑ ★`:
     `(($ 0) ⟨ℕ!⟩) ↓ seal X ★` against `($ 0) ⟨ℕ!⟩`.
   * It then asks for an extra right projection `★ ∼ ＇Y` with
     `＇X ⊑ ＇Y`.  The right term blames, so the operational lemma is
     false.
   * In the semantic design the first pair *is* related: `X` is a
     left-only seal represented by `★`, and its contents `($ 0) ⟨ℕ!⟩` are
     related to the right value at `★ ⊑ ★`.
   * But the extra cast cannot be stated, because `X` is left-only:
     * a left-only `X` has no right partner;
     * so `＇X ⊑ ＇Y` is not derivable in a two-context type precision;
     * so the one-sided right cast rule does not apply.
   * The counterexample exists only because GTSFImp's type precision has
     one shared context, where `X ⊑ X` holds unconditionally even for a
     variable the right program never binds.
   * **Lesson for the new precision:** `X ⊑ Y` must require a paired
     variable.
5. **De Bruijn store shifting.** Allocation shifts the whole term
   (`⇑ᵗᵐ`).  The denotation with seal numbers sidesteps this, but
   soundness needs a renaming lemma for intrinsically scoped terms.

## 8a. Paper sketch: monotonicity of consistency casts

**Statement** (reflection; preservation is the mirror image).  Let:
* `c : C ∼ A` be the left cast and `c′ : C′ ∼ A′` the right cast;
* `C ⊑ C′` and `A ⊑ A′` hold in a two-context type precision;
* `L` be a finite list of left values related to the right set `D′` at
  `C ⊑ C′`, under a world `W`.

Then every finite list of left results of `⟦c⟧ L` is related to
`⟦c′⟧ D′` at `A ⊑ A′`, under an extension of `W` (casts may create
seals).

**Shapes.** Type precision relates a left type to a right type in one of
four ways:
* the same head;
* the right is `★`;
* left `∀` against right non-`∀` (`∀⊑`, which makes the bound variable
  left-only);
* a left variable against `★` (`X ⊑ ★`, with that variable left-only).

The cast heads are `id`, `↦`, `∀ᶜ`, `!`, `？`, `inst`, `gen`, `bot-elim`
and `bot-intro`.  The cases:

1. **Same head on both sides** (including `inst`/`inst` and `gen`/`gen`):
   by the induction hypothesis on the parts.
   * When both sides create a seal at the same step (`inst`/`inst` at the
     cast; `gen`/`gen` at the shared type application), the world gets a
     *shared* entry pairing the two new seals.
2. **Right `!`** (`A′ = ★`): the left result is related at `A ⊑ ★`.
   * The right injects with the ground of `C′`.
   * The relation needs the left's ground to match.  Where `A` is a `∀`
     or a left-only variable, the `∀⊑` and left-only clauses apply
     instead.
3. **Right `？`** (`C′ = ★`): the right projects a tag `G`.
   * Need: if the right projection fails, the left fails too
     (preservation), and if it succeeds, the payloads are related.
   * Related values at `C ⊑ ★` carry the tag of `C`'s ground, or are
     transparent for a left-only seal.  So the right tag differs from
     `G` only when `C`'s ground is incompatible with `A ⊑ A′`.
   * In that case the left cast fails first.  This is the GTLC argument,
     plus the left-only case: if a left value tagged with a left-only
     seal reaches a left `？`, the left fails, which both relations allow.
4. **Left `inst`, right not.**
   * If the right keeps a `∀` type (`C′ = ∀…`, `A′ = ∀…`), then `A` must
     be a `∀` too, since `A ⊑ ∀` forces it.  But `inst` produces a
     non-`∀`, so the case is **impossible**.
   * If `A′ = ★`, the right is `(…)!` with a ground.  The canonical-route
     check below shows the grounds agree.
5. **Left `gen`, right not.** `C ⊑ C′` with `C` non-`∀` forces `C′`
   non-`∀`, and `A ⊑ A′` with `A = ∀…` forces `A′` to be a `∀` or `★`.
   * If `A′` is a `∀`, the right is also `gen`: same head.
   * If `A′ = ★`, the right's `!` injects at `∀★`.  The left `gen` value
     is related to it through the `∀⊑★` clause, by the induction
     hypothesis on `gen`'s body.
6. **Left `∀ᶜ`, right `inst`** (the right instantiates first).
   `C = ∀C₀ ⊑ C′ = ∀C₀′`, and `A` is a `∀` against a non-`∀` `A′`.
   * The right creates `α′` now; the left creates `σ` only when it is
     later instantiated.
   * Use the hypothesis's `∀⊑∀` clause in the world that extends only
     the left list up to `σ`.  This is legal: the right made no
     allocation between `α′` and its own counter at the cast.
   * Pair `σ` with `α′` there.  The induction hypothesis relates the
     bodies.
   * Then a **world-change lemma** turns "`σ` shared with `α′`, seen
     through the right's reveal `〖α′ , ★ ↑ C₀′〗`" into "`σ` left-only"
     under the conclusion's `∀⊑` clause.
   * Instantiation being administrative makes the different timing
     harmless: the right's instantiated body is an effect-free value.
7. **Left `∀ᶜ`, right `gen`** (the right becomes polymorphic).
   `C = ∀C₀ ⊑ C′` (non-`∀`, through `∀⊑`), and `A = ∀A₀ ⊑ A′ = ∀A₀′`
   (shared).
   * Both sides instantiate at the shared type application, creating
     `σ` and `σ′`.
   * The hypothesis's `∀⊑` clause relates the left body at `σ`, with `σ`
     left-only, to the right's *unwrapped* value.
   * The right's `gen` wrapper conceals at `σ′`, tags with `σ′` (`X!`),
     projects `?σ′`, and unseals.
   * The same world-change lemma, in the other direction, turns
     "`σ` left-only against the raw right value" into "`σ` shared with
     `σ′` against the `gen`-wrapped right value".
   * Example: left `ΛX.λx:X.x`, right `(λx:★.x) ⟨gen (X! ↦ ?X)⟩`.  Both
     return the argument; a right `★→★` function that returns another
     tag fails the right `?σ′`.  The hypothesis rules that out: such a
     function is not related to the polymorphic identity at
     `∀X.X→X ⊑ ★→★`.
8. **Different routes between the same types** (the counterexample of
   risk 1).  For example, the left uses `inst` then `gen` while the right
   uses `gen` then `inst`, at `∀X.★→X ∼ ∀Y.Y→★` or more precise pairs.
   * The routes differ in *when* the `X` seal is created (at the cast,
     or at each instantiation of `Y`), not in which seals and tags are
     checked:
     * the input is concealed at `Y`'s seal and tagged with it;
     * the output is sealed at `X`'s seal and unsealed to `★`.
   * By case 6's timing argument, the induction goes through on the
     pair of routes.
   * This needs no bound to be chosen, which is why option (b) works
     where factorization does not.

**The world-change lemma** (cases 6 and 7) is the one genuinely new lemma.
Relate two worlds that differ only in the entry for one left seal `σ`:
* `left q`, where `σ`'s contents are related to raw right values;
* `shared σ′ q`, where they are related to right values sealed at `σ′`,
  or tagged and sealed at `σ′`.

The lemma: a left list is related to a right set `D′` in the first world
if and only if it is related to `wrap D′` in the second.  Here `wrap` is
the right's boundary wrapper:
* the reveal or conceal conversion at `σ′`, for a right `inst`;
* `gen`'s tag/project plus the reveal, for a right `gen`.

The proof is by induction on the precision derivation.  The wrappers are
structural in the type, sealing in negative positions and unsealing in
positive ones, so each clause lines up.

**Coherence of derivations.** The two-sided rule takes *any* pair of
derivations `c`, `c′` at related types.  So the lemma needs any two
derivations of the same judgement to agree semantically.
* Case 8 is the known instance.
* A candidate counterexample was `∀X.X→X ∼ ★` derived either by `∀ᶜ`
  then `!` at `∀★`, or by `inst` then `!` at `★→★`.  With the first,
  a `★` application on the right would blame where the left succeeds.
  But it is **not derivable**: `∀ᶜ` would need `X→X ∼ ★` under mode
  `X∼X`, and `X∼X` cannot reach `★`.  This is the same strictness as in
  risk 2.
* So far, every pair of distinct derivations of the same judgement
  differs only in the timing of seal creation.
* If one turns out not to, the fallback is to require canonical
  derivations (`Consistency2`'s unique evidence) in both the cast rule
  and the source typing.

**Status.**
* Cases 1–3: the GTLC arguments, extended with left-only seals.
* Cases 4 and 5: impossible, or reduce to case 1.
* Cases 6–8: need the world-change lemma and the timing argument.

The sketch finds no counterexample.  What it finds is the world-change
lemma, which needs a precise statement and a paper proof before
mechanization.

## 9. Plan

1. Risks 1, 2 and 4 are checked.  Decision for risk 1: option (b), a
   two-sided cast rule with a semantic monotonicity lemma.
   * Define the cast-calculus term precision (Section 7).
   * Prove that elaboration preserves it.
   * The paper sketch of the cast monotonicity lemma is in Section 8a.
     It found no counterexample.  Next: state and prove on paper the
     world-change lemma it needs.
   Define the cast-calculus term precision (Section 7), and prove that
   elaboration preserves it.
2. Port the PolyG model (`GraphModel`, `Denotation`) to GTSFImp's terms:
   * conversions;
   * consistency casts with modes;
   * `inst` and `gen` creating seals;
   * primitives.
3. Consistency, soundness and adequacy (reusing GTSFImp's type safety).
4. Two-counter worlds; the relations (Section 5); their properties.
5. The conversion lemma; monotonicity of consistency casts.
6. The fundamental lemma on cast-calculus precision; the theorem, in the
   form of
   `proof/DGG/DynamicGradualGuaranteeDef.agda`.

Estimate: larger than PolyG's denotational part, 12,000–16,000 lines,
dominated by the cast monotonicity lemma.  For comparison, the operational
attempt in `proof/DGG` is about 92,000 lines and unfinished.
