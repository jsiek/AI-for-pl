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

## 9. Plan

1. Risks 1, 2 and 4 are checked.  Decision for risk 1: option (b), a
   two-sided cast rule with a semantic monotonicity lemma.
   * Define the cast-calculus term precision (Section 7).
   * Prove that elaboration preserves it.
   * Sketch on paper the cases of the cast monotonicity lemma where the
     two sides' derivations choose differently (`inst`/`gen` order).
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
