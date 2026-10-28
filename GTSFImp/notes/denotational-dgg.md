# A Denotational Proof of the Dynamic Gradual Guarantee for GTSFImp

Status: plan steps 1 and 2 are mechanized, and step 3 is partly
mechanized (Section 9).  Soundness as subject expansion fails for `β-∀`
(Section 8c, mechanized counterexample), so steps 3–6 wait on a decision
about how to prove soundness and adequacy.

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
     counters.  A relational environment says how each left type
     variable's seal relates to the right (paired with a right seal, or
     left-only), and the world says how each left seal's *tag* relates
     (Section 4).
  2. **One-sided seals.** A seal created only on the left, by a left-only
     type application or a left `inst`, is related to *unsealed* values on
     the right, at a derivation `R ⊑ ★` (an `X ⊑ ★` mark).  The relation
     for `★` reads how a left tag on such a seal relates from the world.
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
  | `β-inst` | `V ⟨inst c⟩`, at the cast | `α := ★`; then `V [α]`, which creates a second seal `β := α` when `V` is a `Λ` or `gen` value; reveal `α`; then `↑ᶜ (c[★/0])` |
  | `β-gen` | `(V ⟨gen c⟩) ⦂∀ B [C]` | `α := C`; inside `c`, `α` has mode `★∼X` and is used as a ground tag |
  | `β-reveal-∀`, `β-conceal-∀` | conversions at `∀` when instantiated | a seal, as `β-Λ` |
  | `β-∀` | `(V ⟨∀ᶜ c⟩) ⦂∀ B [C]` | none: becomes `(V [C]) ⟨c[C]⟩`, so `V` creates the seal |

  So the seal of a type application is created by the innermost `Λ` or
  `gen` value it reaches, and for a `gen` value that seal is the tag.

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
* **Left before right.** The left never instantiates a paired variable
  before the right does.
  * This holds only for casts in the eager normal form of Section 8a,
    case 8.  The first version of this note argued it from types alone,
    and that argument was wrong: `inst` may produce a `∀` type.
  * Without the normal form there is a counterexample (case 8).

  So the left side has every shared seal plus left-only ones, and the
  right side has every shared seal plus invisible right-only ones.

## 4. Descriptors, environments and worlds

Revised after the paper proof of the world-change lemma (Section 8b).
The first version kept each seal's relation in the world; that made the
lemma false (Section 8b explains why).

* **Descriptors.** Closed precision derivations become *descriptors*:

      r ::= ι | ★ | r ⇒ r | tag G r | ∀⊑∀ r | ∀⊑ r | ∀⊑★ r | X
          | ◁σ r | ▷σ′ r

  * `◁σ r`: the left values are `seal σ u`, and their contents are
    related at `r`.
  * `▷σ′ r`: the right values are unsealed at `σ′` first.
  * `tag G r`: the right values are untagged at `G` first.  `G` may be a
    right seal.
  * Seals appear as numbers, so a descriptor means the same in every
    world, except at `★` (below).
  * A typing derivation becomes a descriptor by erasing the right type at
    variable leaves: `X ⊑ X′` and `X ⊑ ★` both become `X`.
* **Environments.** A relational environment `η` maps each left type
  variable to a closed descriptor, its *leaf relation*:
  * `X` paired, instantiated at seals `σ`, `σ′` with contents relation
    `q`: `◁σ ▷σ′ q`;
  * `X` left-only, instantiated at `σ`: `◁σ q`.

  This is Reynolds' relational environment.  The leaf relation is not
  in the world.
* **Worlds.** A world is a list of *tag relations*, one per left seal,
  plus the right counter.
  * The tag relation of `σ` is a closed descriptor.  It says how a left
    value tagged `σ` in `★` is related to right values.  Every seal
    gets one: `gen` seals are tags, and so are `Λ` seals, because
    compiled casts use `idᶜ`, where every type variable has the cross
    mode and may be tagged.
  * Shared, when the right tags with its own seal `σ′`:
    `tag σ′ (◁σ ▷σ′ q)`.
  * Transparent, when the right never tags: `◁σ q`.
  * Time-shifted, when the right instantiated earlier (Section 8b):
    `tag β′ (◁σ ▷β′ ▷α′ q)`.
  * Right seals have no entries; no clause consults them.
* `W ⊑ W′` when the list is a prefix and the right counter is `≤`.  The
  left counter is the list's length.

## 5. The relations

These are the PolyG relations (joint lists, existential world per list,
Kripke closures, consistency on the set side), with these changes:

* **Results.** A list of left results at left counter `m` is related if
  there is a future world with left length `m` and some right length
  `m′` under which its values are related to the right set at `m′`.
  With consistency, the right set has one counter.
* **Leaf `X`.** Relate at the leaf relation `η X`.
* **The seal descriptors.** `◁σ r`, `▷σ′ r` and `tag G r` as in
  Section 4.
* **Clause for `★`.** Every left element is an injection.
  * A left element tagged with a ground that is not a seal: as in PolyG.
  * The left elements tagged with a seal `σ`: their payloads are related
    to `D′` itself at the tag relation `W σ`.
* **The `∀` clauses.** Each quantifies over every future world and
  every closed contents relation `q`, and *chooses* a tag relation `t`
  for the new left seal:
  * `∀⊑∀ p`: for `W′` with lengths `σ` and `σ′` and every `q`, there is
    a `t` such that the bodies at `σ` are related to `D′ ◆ σ′` at `p`,
    under `η[X ↦ ◁σ ▷σ′ q]`, in `W′` extended with `t` (and the right
    counter `σ′ + 1`).
  * `∀⊑ p` (left `∀`, right not): for `W′` with left length `σ`, any
    right counter `n′`, and every `q`, there is a `t` such that the
    bodies are related to the right set *itself* at `n′`, under
    `η[X ↦ ◁σ q]`, in `W′` extended with `t`.  The right does not
    instantiate.
  * `∀⊑★ p`: as `∀⊑∀`, against `untag ∀★ D′`.
  * The tag relation is existential because it depends on the right
    value, which may have created its tag seal earlier (Section 8b).
* **Ground grammar.** Function and `∀` entries and the empty closures are
  as in PolyG.  The ground tag grammar adds `ℕ` (constants) and seals.

## 6. Paper checks of the new cases

These were written before the revision of Section 4.  Read `left q` as
the leaf relation `◁σ q` with a transparent tag relation, and
`shared σ′ q` as the leaf relation `◁σ ▷σ′ q` with a shared tag relation.

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
    `c` and `c′` must be in eager normal form, with no `gen` directly
    over `inst` (Section 8a, case 8).
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
  types, which is exactly the premise of the two-sided rule.  Elaboration
  must put its casts in normal form first (Section 7a).
* **Conversion lemma.** The reveal and conceal conversions
  `〖α , R ↑ B〗` and `makeConceal` relate the two forms of a seal:
  * a shared pairing of `α` seen through the conversions;
  * a left-only (or right-only) seal at the boundary.
* **Unchanged from PolyG**, adapted: soundness, adequacy, the
  consistency theorem, monotonicity, finite support and the
  substitution lemmas.  New cases: conversions, primitives (`⊕`, `ℕ`),
  and allocation at casts.

## 7a. The normal form, cast-calculus precision, and elaboration

### The eager normal form

A cast is in *eager normal form* when no `gen` has an `inst` directly
as its body.  As a grammar of consistency derivations (types and side
conditions as in `Consistency.agda`):

    c ::= id ι | id ★ | id X          atoms
        | c ↦ c                       functions
        | ∀ᶜ c                        both sides keep the binder
        | c !  | ？ c                 to and from ★, through a ground
        | inst c                      eliminate the source's binder
        | gen g                       introduce the target's binder
        | bot-elim | bot-intro

    g ::= c ↦ c | ∀ᶜ c | gen g        bodies of gen

* `g` is `GenSafe` without its `inst` case.  `gen` already requires
  `GenSafe` of its body, and the normal form removes one of the four
  heads `GenSafe` allows.
* **Relation to `GenSafe`** (GTSFImp `CastTerms`, GTNF `Coercion.agda`,
  identical in both).
  * Both are restrictions on the head of a `gen` body, and both keep
    something out of the suspended cast:
    * `GenSafe` keeps out *failing checks* (`!`, `？`, `id`, `bot`), so
      that errors happen on time;
    * the normal form also keeps out *allocation*, so that seals are
      created on time.
  * `Rationale.md` admits `gen (inst c)` on purpose: delaying an `inst`
    cannot delay an error.  That is true operationally.  Semantically,
    though, delaying an `inst` replaces one seal shared by all
    instantiations with a fresh seal per instantiation.  The relation
    sees the difference, because a left seal's tag relation is fixed
    when the seal is created (case 8's counterexample).
  * The remaining `gen` bodies, `↦`, `∀ᶜ` and `gen`, are GTNF's inert
    coercions without `G!`.  A `gen` body is then a value-forming cast
    that neither fails nor allocates until applied or instantiated.
  * The opposite choice, a lazy normal form with no `inst` over `gen`,
    does not work.  `inst (∀ᶜ …)` on the left has no lazy alternative
    (the binder order is fixed), but a right `gen (inst …)` would be
    allowed, and that is again the left creating a seal early.
* Read along a `∀`-prefix, a cast first eliminates the source's binders
  (`inst`), then introduces the target's (`gen`).  Seals are created as
  early as possible.
* **Normalization.** `eager c` swaps every `gen (inst d)` to
  `inst (gen d̃)` (Section 8a, case 8) until none is left.
  * Each swap moves one `inst` above one `gen`, so the number of such
    inversions decreases.
  * `eager c` derives the same judgement as `c`.
  * The swap needs an exchange lemma for consistency: exchanging the two
    innermost variables, whose modes are `X∼★` and `★∼X`.

### Where elaboration's casts come from

* The source typing stores declarative consistency evidence: `⊢·` holds
  `A ∼ A′` (parameter against argument), and `⊢⊕` holds `A ∼ arg`.
  * The evidence is arbitrary in a typing derivation.
  * From the checker it is `lower?`'s.
* **`lower?`'s evidence is eager.**
  * The cast read off a lower bound follows the bound's binders
    (`lower-bounds-consistentᵐ`):
    * a binder paired on both sides gives `∀ᶜ`;
    * one paired with the source only gives `inst`;
    * one paired with the target only gives `gen`.
  * `lower?` tries `inst` before `gen`.
  * A brute-force check confirms that no `gen` lands directly over an
    `inst`: all 450 closed types of size ≤ 6, all 13,980 consistent
    pairs.  As a control, trying `gen` first gives 14 violations already
    at size 5.
  * Not covered by the check: the helpers for `★` and for binders
    dropped on both sides (`factor-*-star-lower`, `close-*`).
* **But `compile` flips it.** At an application `compile` inserts
  `symᶜ A∼A′`, and `sym∼` turns `inst` into `gen` and back.  So it
  turns `lower?`'s eager `inst (gen d)` into `gen (inst d′)`, the
  opposite of the normal form.
* **Decision:** `compile` inserts `eager (symᶜ A∼A′)` at applications
  and `eager (A∼arg)` at primitives.
  * This works for any typing derivation, not only the checker's.
  * The cast at `★ ∼ ★ ⇒ ★` is already in normal form.
  * The development has its own `compile` for this, so that the
    operational proof in `proof/DGG` is not disturbed.

### Two-context type precision

* `Φ` relates a left context `Δ` to a right context `Δ′`.  Each left
  variable is marked:
  * `pair Y`: paired with a right variable;
  * `only`: left-only;
  * `dead`: occurs nowhere.
* Every right variable is paired exactly once.  Extending: `Φ ,pair`
  (both sides), `Φ ,only` and `Φ ,dead` (left only).
* `Φ ⊢ A ⊑ A′`, for `A : Ty Δ` and `A′ : Ty Δ′`:

      ★ ⊑ ★     ι ⊑ ι     ι ⊑ ★     X ⊑ Y  if Φ X = pair Y
      X ⊑ ★  if Φ X = only
      A ⇒ B ⊑ A′ ⇒ B′   from A ⊑ A′ and B ⊑ B′
      A ⇒ B ⊑ ★          from A ⊑ ★ and B ⊑ ★
      ∀A ⊑ ∀A′           from Φ ,pair ⊢ A ⊑ A′
      ∀A ⊑ B             from Φ ,only ⊢ A ⊑ B, A not a variable,
                         and 0 occurring in A
      ∀A ⊑ ★             from Φ ,dead ⊢ A ⊑ ★, A not ★
      ∀★ ⊑ ★     ∀X.X ⊑ ∀★     ∀X.X ⊑ ★

* These are `Imprecision`'s rules, with these differences:
  * the right type lives in its own context, so `∀⊑` needs no shift;
  * `X ⊑ X` needs a pair;
  * `∀⊑★` marks its binder `dead`, which is what `Imprecision`'s `extᵐ`
    there amounts to, since its body is `⊑ ★`.
* Derivations should be unique, as `Imprecision`'s are (not yet
  proved).  Only the semantic substitution lemma of the type-application
  cases needs it (below).

### Cast-calculus term precision

`Φ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ p`, with `p : Φ ⊢ A ⊑ A′` and `Γ⊑` a list of type
precisions for the term variables.  The rules cover the terms that
elaboration produces: no conversions, no `blame`, no runtime seals.
* Casts may be at any mode environment, as in `proof/DGG/Elab`:
  renaming a cast changes the mode of a skipped variable.
* Every cast is in normal form.

    x ⊑ x                      at Γ⊑ x
    ƛ N ⊑ ƛ N′                 at p₁ ⇒ p₂,  from N ⊑ N′ at p₂ with p₁
                                 added to Γ⊑
    L · M ⊑ L′ · M′            at p₂,  from L ⊑ L′ at p₁ ⇒ p₂ and
                                 M ⊑ M′ at p₁
    $κ ⊑ $κ,  L ⊕ M ⊑ L′ ⊕ M′  structural
    Λ V ⊑ Λ V′                 at ∀ p,  from Φ ,pair ⊢ V ⊑ V′ at p
                                 (V, V′ values)
    Λ V ⊑ N′                   at ∀⊑ p,  from Φ ,only ⊢ V ⊑ N′ at p
                                 (V a value; N′ any term, unshifted)
    M ⦂∀ A [T] ⊑ M′ ⦂∀ A′ [T′] at r,  from M ⊑ M′ at ∀ p,
                                 q : Φ ⊢ T ⊑ T′ and
                                 r : Φ ⊢ A[T] ⊑ A′[T′]
    M ⦂∀ A [T] ⊑ M′            at r,  from M ⊑ M′ at ∀⊑ p : ∀A ⊑ B,
                                 q : Φ ⊢ T ⊑ ★ and r : Φ ⊢ A[T] ⊑ B
    M ⟨c⟩ ⊑ M′ ⟨c′⟩            at r,  from M ⊑ M′ at p : C ⊑ C′,
                                 c : C ∼ A, c′ : C′ ∼ A′,
                                 r : A ⊑ A′
    M ⊑ M′ ⟨c′⟩                at r,  from M ⊑ M′ at p : A ⊑ C′,
                                 c′ : C′ ∼ A′, r : A ⊑ A′

* As mechanized (`Denot/CastPrecision.agda`), the two type-application
  rules carry their result derivation `r : A[T] ⊑ A′[T′]` (or
  `A[T] ⊑ A′`) instead of computing a substituted `p[q]`, as the source
  rules `[]⊑[]ᴳ` and `[]⊑ᴳ` do.  So no syntactic substitution lemma is
  needed.
* No rule relates the casts `c` and `c′` to each other.  The cast
  monotonicity lemma (Section 8a) is what makes the two cast rules sound.
* There is no one-sided left cast rule, because `compile` never needs
  one.
* Compared with `proof/DGG/CastTermImprecision` (`⊢²`), there are no
  conversion, `blame`, or seal rules.  Those are needed only for terms
  after reduction, and the denotational proof never relates such terms.

### Elaboration preserves precision

**Theorem.** If `μ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p` then
`Φμ ∣ γ̂ ⊢ compile M ⊑ ⌊compile M′⌋ ⦂ p̂`.

* `Φμ` marks each `X⊑X` variable of `μ` as paired and each `X⊑★`
  variable as left-only.
* `⌊·⌋` strengthens a right term or type from `Δ` to `Δ′`, the
  context without the left-only variables.
* `p̂` is `p` in two-context form.

**Why the right side can be strengthened.** In the source relation, the
right term never mentions a left-only variable:
* `Λ⊑ᴳ` checks its body against `⇑ᵗᴳ N′`;
* `[]⊑ᴳ` keeps `M′`.

This is an invariant, proved by induction on the source derivation.

**Translating type precision.** `p̂` exists because, under the
invariant, `μ ⊢ A ⊑ ⇑B` converts to `Φμ ⊢ A ⊑ B`:
* the leaf `X ⊑ X` occurs only with `X` paired, since the right type
  cannot mention a left-only `X`;
* `X ⊑ ★` occurs only with `X` left-only.

So the single-context source relation already behaves like the
two-context one, which is why the `Catchup` counterexample (risk 4) does
not affect the source.

**Proof.** By induction on the source derivation.
* **`x⊑xᴳ`, `ƛ⊑ƛᴳ`, `κ⊑κᴳ`:** structural.
* **`·⊑·ᴳ`:** the function part is structural.
  * The arguments get `eager (symᶜ A∼C)` and `eager (symᶜ A′∼C′)`, at
    `C ⊑ C′` and `A ⊑ A′`.
  * Both are in normal form, so the two-sided cast rule applies.
* **`·⊑·★ᴳ`:**
  * The right function gets `？(id ★ ↦ id ★)`, related to the left
    function by the one-sided right rule at `A ⇒ B ⊑ ★ ⇒ ★`.  The
    premises `A ⊑ ★` and `B ⊑ ★` come from `⇒⊑★`.
  * The arguments are related by the two-sided rule.
* **`·★⊑·★ᴳ`, `⊕⊑⊕ᴳ`:** two-sided cast rules.
* **`Λ⊑Λᴳ`:** the `Λ ⊑ Λ` rule.
* **`Λ⊑ᴳ`:** the `Λ V ⊑ N′` rule.  The source's `⇑ᵗᴳ N′` strengthens back
  to `N′`, so `compile` must commute with renaming.
* **`[]⊑[]ᴳ`:** the source's `q` and `r` are carried over by `back`.
* **`[]⊑ᴳ`:** the same, with `q : T ⊑ ★`.

**Supporting lemmas, as mechanized:**
* `eager` puts a cast in normal form;
* `back`, the converse of `forget`;
* elaboration as a relation (`ElabE`), so that typing derivations do not
  matter, with types aligned by uniqueness of source typing;
* the right program as a renaming of a term of the right context, as in
  `proof/DGG/CompilePreservesImprecision2`, which avoids strengthening.

**Where uniqueness and substitution are needed.** Only in the two
type-application cases of the fundamental lemma.  What is needed there
is a *semantic* substitution lemma, not a syntactic one:
* relating at `p` with `X ↦ q̂` (the contents relation from
  `q : T ⊑ T′`) is the same as relating at `r`, for any
  `r : A[T] ⊑ B[T′]`;
* it is proved by induction on `p`, inverting `r`, and is the
  type-application half of the conversion lemma;
* at an `X` leaf the corresponding part of `r` is some derivation of
  `T ⊑ T′`, and the relation there agrees with the one at `q` only by
  uniqueness of two-context derivations.  This is the one use of
  uniqueness: the cast lemma quantifies over its derivations, and the
  other term rules fix their premises' derivations syntactically.
* Uniqueness should mirror `⊑-unique` in `proof/Imprecision.agda`.

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
4. **Left `inst`, right not** (corrected: `inst` may produce a `∀`, so
   the first version's "impossible" was wrong).  `C = ∀X.C₀`.
   * If `X` is paired with the right's `X′`, the timing lemma of case 8
     says the right is an `inst` too: case 1.
   * If `X` is left-only (`C′` is not a `∀`): the left creates `α := ★`,
     and `V [α]` creates `β`.
     * Use the hypothesis's `∀⊑` clause now, at seal `β`, with contents
       relation `◁α ★`.
     * The left's reveals (unseal `β`, then `α`) take the leaf relation
       `◁β ◁α ★` to `★`.  This is the left-hand counterpart of the
       world-change lemma.
     * Then the induction hypothesis for `c₁[★]` against the whole
       right cast, whatever its head.  The tag relation of `β` is the
       one the hypothesis chose.
5. **Left `gen`, right not.** `C ⊑ C′` with `C` non-`∀` forces `C′`
   non-`∀`.  `A = ∀…` allows three shapes of `A′` (corrected; the first
   version missed the third):
   * `A′` is a `∀`: the right is also `gen`, the same head.
   * `A′ = ★` through `∀⊑★`: the right's `!` injects at `∀★`.  The left
     `gen` value is related to it through the `∀⊑★` clause, by the
     induction hypothesis on `gen`'s body.
   * `A′` any other type, through `∀⊑` (for example `∀X.X→X ⊑ ★→★`,
     right cast `id`, as in Section 6's `gen` example).  The left
     instantiates alone.  Choose the transparent tag relation `◁σ q`:
     the right never tags.  The induction hypothesis on `gen`'s body
     then needs the left's `X!` and `?X` against nothing on the right,
     which is the transparent case of the `★` clause.
6. **Left `∀ᶜ`, right `inst`** (the right instantiates first).
   `C = ∀C₀ ⊑ C′ = ∀C₀′`, and `A` is a `∀` against a non-`∀` `A′`.
   * The right creates `α′ := ★` at the cast, and `β′ := α′` when it
     instantiates its value at `α′`.  The left creates `σ` only when it
     is later instantiated.
   * Use the hypothesis's `∀⊑∀` clause at a world whose left list is
     extended up to `σ`.  Pair `σ` with `β′` at the contents relation
     `▷α′ q₀`.
   * The world-change lemma (Section 8b) goes through the right's
     reveals: from the leaf relation `◁σ ▷β′ ▷α′ q₀` to the left-only
     `◁σ q₀`.
   * The tag relation of `σ` is the one the hypothesis chose.  It may be
     time-shifted (Section 8b's example).
   * Instantiation being administrative makes the different timing
     harmless: the right's instantiated body is an effect-free value.
7. **Left `∀ᶜ`, right `gen`** (the right becomes polymorphic).
   `C = ∀C₀ ⊑ C′` (non-`∀`, through `∀⊑`), and `A = ∀A₀ ⊑ A′ = ∀A₀′`
   (shared).
   * Both sides instantiate at the shared type application, creating
     `σ` and `α′`.
   * Use the hypothesis's `∀⊑` clause at the contents relation
     `tag α′ (▷α′ q)`.  It relates the left body at `σ` to the right's
     *unwrapped* value, which sees the left's `σ`-sealed contents as
     values tagged and sealed at `α′`.
   * `gen`'s body cast projects `?α′` and injects `α′!` at the `X`
     positions.  The world-change lemma's leaf conditions, used inside
     the cast lemma, turn this into `σ` paired with `α′` at `q`.
   * Example: left `ΛX.λx:X.x`, right `(λx:★.x) ⟨gen (X! ↦ ?X)⟩`.  Both
     return the argument; a right `★→★` function that returns another
     tag fails the right `?α′`.  The hypothesis rules that out: such a
     function is not related to the polymorphic identity at
     `∀X.X→X ⊑ ★→★`.
8. **Different routes** (redone in the revised design).  The first
   sketch said that routes differing only in *when* a seal is created
   always behave alike.  That is true of the programs, but the relation
   cannot always express it, so the cast rule needs a normal form.

   **Counterexample without a normal form.**  The left creates a seal
   early and the right late.
   * Take `V = f ⟨gen (X! ↦ id)⟩ : ∀X. X→★→★` with
     `f = λx:★. λy:★. x`.  `V` tags its first argument with its
     instantiation seal and returns it.
   * The judgement `∀X. X→★→★ ∼ ∀Y. ★→Y→★` has two derivations:
     * `inst (gen d)`, with `d = ？X ↦ (Y! ↦ id)`, which instantiates `X`
       at the cast;
     * `gen (inst d̃)`, with `d̃` the same as `d` with the two variables
       exchanged, which instantiates `X` again at each instantiation of
       `Y`.
   * Left `V ⟨inst (gen d)⟩`, right `V ⟨gen (inst d̃)⟩`, related by the
     reflexive two-sided cast rule.
   * The left creates `α := ★` and `V`'s seal `β` once, at the cast.
     Each instantiation of `Y` and application returns the first
     argument tagged with `β`.
   * The right creates `α′_i`, `β′_i` at its `i`-th instantiation, and
     returns the argument tagged with `β′_i`.
   * Both results are opaque at `★`, so the programs are equivalent.
     But the relation at `★` needs the tag relation of `β` to name the
     right's tag seal, and that seal differs from one instantiation to
     the next.  The tag relation of `β` is fixed when `β` is created,
     so no world works.
   * The mirror image, the right creating a seal early and the left late,
     is harmless (case 6): the right side has no world entries, so a
     right seal created once can be paired with many left seals.

   **The eager normal form.** No `gen` directly over `inst`.
   * **Swap lemma.** `gen (inst d)` and `inst (gen d̃)` derive the same
     judgement, with `d̃` the same as `d` with the two variables
     exchanged.
     * The side conditions carry over: `C₀` is not a variable and
       contains `X`, `B` is not a variable and contains `Y`, and neither
       is `★`.
     * The new `gen` needs `GenSafe d̃`.  This holds because `d̃` relates
       two non-variable, non-`★` types, one of which contains `Y`.  So
       its head is `↦`, `∀ᶜ`, `inst` or `gen`, never `!`, `？`, `id` or
       a `bot` rule.
   * Swapping pushes `inst` outward, so every derivable judgement has a
     derivation in normal form.
   * The two-sided cast rule requires both casts in normal form.  Only
     the right cast needs it, but requiring both is simpler.
     Elaboration must produce normal forms.
   * `Consistency2`'s `lower?` tries `inst` before `gen`, the same
     preference.  Whether the casts read off its evidence are already in
     normal form is not yet checked.

   **Timing lemma.** Let `c : C ∼ A` and `c′ : C′ ∼ A′` be in normal
   form, with `C ⊑ C′` and `A ⊑ A′`.  Suppose `c = inst c₁` instantiates
   `C`'s binder `X`, and `X` is paired with `C′`'s binder `X′`.  Then
   `c′ = inst c′₁`.

   *Proof.* `X` occurs in `C₀` (a side condition of `inst`).  Being
   paired, `X` is never under `★`, so `X′` occurs at exactly `X`'s
   positions.  By cases on the head of `c′`:
   * **`∀ᶜ`:** `X′` stays in `A′`, so `A` has a variable `Z ⊑ X′` at
     those positions.  The left cast then needs `X ∼ Z` there, with `X`
     in mode `X∼★`, and no consistency rule derives it: casts do not
     compose through `★`.
   * **`gen`:** follow the chain of `gen`s.  It ends in a cast whose
     source is a `∀` and whose target is neither a variable nor `★`, so
     its head is `∀ᶜ`, `inst` or a `bot` rule:
     * `∀ᶜ` is excluded as above;
     * `inst` directly under `gen` is excluded by the normal form;
     * the `bot` rules are excluded by their types.
   * **`!`:** the ground is either:
     * `★→★`, reached through `inst`: the claim;
     * `∀★`, reached through `∀ᶜ`: excluded, because `X′` occurs and
       mode `X∼X` cannot reach `★`.
   * **`bot-elim`, `bot-intro`:** `C` would be `∀X.X` (and `inst` needs a
     non-variable body), or `X` would not occur.

   So with normal forms the left never creates a paired variable's seal
   before the right.

   **The case itself.** Peel the two casts one head at a time.
   * Each step is one of:
     * case 1 (the same head);
     * case 4 (a left `inst` of a left-only variable, against any
       right cast);
     * case 6 (the right instantiates first);
     * case 7 (a right `gen` against a left `∀ᶜ`).
   * Case 6 may reach through left `gen`s: the left instantiates the
     kept variable one type application later.  The time shift is the
     same, because the hypothesis's `∀⊑∀` clause allows any later left
     world.
   * Example, risk 1's pair:
     * left `gen (∀ᶜ (X_A! ↦ id)) : ∀X.★→X ∼ ∀X.∀Y.X→Y`;
     * right `inst (gen (X_A! ↦ X!)) : ∀X.★→X ∼ ∀X.X→★`.
     * The right's `inst` comes first: case 6, reached through the left's
       `gen`.
     * The two `gen`s pair up: case 1.
     * The left's `Y` against the right's nothing: the `∀⊑` clause.
   * No bound is chosen, which is why option (b) works where
     factorization does not.

**The world-change lemma** (cases 6 and 7) is stated and proved in
Section 8b.  The version first sketched here compared two worlds that
differ in one seal's entry.  That version is false, and fixing it
changed the design of worlds; Section 8b explains why.

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
* Case 4: case 1 by the timing lemma, or a left-only instantiation
  through the hypothesis's `∀⊑` clause.
* Case 5: case 1, the `∀⊑★` clause, or the transparent tag relation.
* Cases 6 and 7: checked on paper with the world-change lemma
  (Section 8b).
* Case 8: needs the eager normal form.  Without it there is a
  counterexample.  With it, the timing lemma reduces case 8 to cases 1,
  4, 6 and 7.

## 8b. The world-change lemma, on paper

**Outcome.** The lemma holds, but not in the form Section 8a first
sketched.  Writing out its proof found two problems with keeping a
seal's relation in the world.  The fix changes the design (Sections 4
and 5 are revised):
1. leaf relations move from the world to a relational environment `η`;
2. the world keeps one *tag relation* per left seal, chosen
   existentially when the seal is created.

After the fix the lemma no longer changes the world.  It changes `η` at
one variable, and it is the right-hand half of Section 7's conversion
lemma.

**Problem 1: later entries mention `σ`.**
* In the first design a world entry was a closed derivation whose seal
  leaves read the world, as in PolyG.
* A later seal's contents can mention `σ`.  For example, the left body
  runs `M [X]` after `σ` exists, creating `σ₂` with contents type `σ`.
* Changing `σ`'s entry then changes the meaning of `σ₂`'s entry, while
  the right values stored for `σ₂` are the same in both worlds.  So
  "related in `W₁` iff related to `wrap D′` in `W₂`" fails at `σ₂`.
* **Fix:** descriptors name seals by number (`◁σ`, `▷σ′`), so they
  mean the same in every world.  A future of one world is then a
  future of the other with the same entries.

**Problem 2: the `★` clause read `σ`'s entry, and neither reading is
right.**
* At `★` the first design looked up whether `σ` is shared (the right
  tags with `σ′`) or left-only (transparent).  Case 6 changes `σ` from
  shared to left-only, which changes the `★` clause at `σ`-tags.
* Neither reading relates the following programs, though they are
  related.
  * Let `f = λy:★. y` and `V = f ⟨gen (X! ↦ id)⟩ : ∀X.X→★`.  `V` tags
    its argument with its instantiation seal and returns it.
  * Left `V`, right `V ⟨inst c′⟩ : ★→★` with `c′ = ？X ↦ id`.  They are
    related at `∀X.X→★ ⊑ ★→★` (`∀⊑`) by the one-sided right cast rule.
  * Context: left `□ [𝔹] true`, right `□ (true⟨𝔹!⟩)`.
  * The left creates `σ := 𝔹` and returns `inj σ (seal σ true)`.
  * The right creates `α′ := ★` at the cast, then `V [α′]` creates
    `β′ := α′`.  It returns `inj β′ (seal β′ (seal α′ (inj 𝔹 true)))`.
  * Both results are opaque at `★`: any projection fails on both
    sides, so the gradual guarantee is not at stake.
  * The shared reading would need `σ` paired with `β′`, but `σ` is
    left-only: the right did not instantiate when the left did.  The
    transparent reading compares `true` with the right's `β′`-tagged
    value at `𝔹 ⊑ ★`, and fails.
* **Fix:** a tag relation per left seal, separate from the leaf
  relation, chosen by the `∀` clause that creates the seal.  Here it is
  `tag β′ (◁σ ▷β′ ▷α′ (tag 𝔹 ι))`.  The right's tag seal `β′` belongs
  to the right value, so only the clause that sees that value can name
  it.
* The tag relation must be a descriptor, valid in any world, because
  cases 6 and 7 reuse the hypothesis's tag relation in the conclusion.

**Statement.** Fix a derivation `p` and a variable `X` of `p` that
occurs only at leaves against a right variable: never under `★`, `tag`
or `∀⊑★`.
* A *right conversion at `X`* is a pair `(u, s)` of operations on right
  value sets, for the positive and the negative leaves of `X`.  Each is
  `𝒱 → ℛ`, may err, and keeps the counter.
* `Conv_p^{u,s}` extends it along `p`:
  * at `X`: `u`;
  * at `ι`, `★`, `tag G r` and other variables: the identity;
  * at `p₁ ⇒ p₂`: the function proxy.  Arguments go through
    `Conv_{p₁}^{s,u}`, then the entries of `D′`, then results go through
    `Conv_{p₂}^{u,s}`.  It contains `νλ` when `D′` does;
  * at `∀⊑∀ r`: the `∀` proxy whose entries at `σ′` are
    `D′ ◆ σ′ ≫= Conv_r`;
  * at `∀⊑ r`: `Conv_r`, since the right has no binder there.
* **Leaf conditions** for closed descriptors `ℓ₁`, `ℓ₂`, at every world
  `W` (`L ▹ R` for a computation `R` means `L ▹` its values at the
  right counter):
  * `(u▹)`: `W ⊢ ℓ₁ ⊢ L ▹ D′` implies `W ⊢ ℓ₂ ⊢ L ▹ u D′`;
  * `(s▹)`: `W ⊢ ℓ₂ ⊢ L ▹ E′` implies `W ⊢ ℓ₁ ⊢ L ▹ s E′`;
  * `(u◃)`, `(s◃)`: the mirror for preservation.  If every finite list
    from `D′` is `◃`-related to `D` at `ℓ₁`, then `u D′` does not err and
    every finite list of its values is `◃`-related to `D` at `ℓ₂`.
    Likewise for `s`.

**Lemma.** If `(u, s)` satisfies the leaf conditions for `ℓ₁`, `ℓ₂`, then
for every `W`, `η`, `L` and `D′`:

    W ⊢ η[X ↦ ℓ₁] ⊢ p ⊢ L ▹ D′
      implies   W ⊢ η[X ↦ ℓ₂] ⊢ p ⊢ L ▹ Conv_p^{u,s} D′

and the mirror statement holds for preservation.

The leaf conditions are symmetric under swapping `(ℓ₁, u)` with
`(ℓ₂, s)`.  So the lemma for `(u, s)` and for `(s, u)` is proved
together, as PolyG's cast cases are generic in the direction (`L▹⇒`,
…).

**Proof.** By induction on the fuel and on `p`, for both directions and
both relations at once.
* **Leaf `X`:** the leaf condition `(u▹)`.
* **`ι`, `★`, `tag G r`, other variables:** `X` does not occur.  The two
  environments agree on the free variables, and `Conv` is the identity.
  The `★` clause reads only tag relations, which the lemma does not
  change.
* **`p₁ ⇒ p₂`.** Take a sublist `L₀`, a counter `m`, a future `W′`, and a
  consistent `E′` with the arguments `▹ E′` at `p₁` under
  `η[X ↦ ℓ₂]`.
  * The swapped lemma on `p₁`: the arguments are related to `E₁`, the
    values of `Conv_{p₁}^{s,u} E′`, at `p₁` under `η[X ↦ ℓ₁]`.  `E₁` is
    consistent, because conversions preserve consistency.
  * `L`'s function clause: the results `▹ᶜ D′ ● E₁` at `p₂`.
  * The lemma on `p₂`, counter by counter, in the worlds that `▹ᶜ`
    provides: the results `▹ᶜ (D′ ● E₁ ≫= Conv_{p₂})`.
  * By finite support, that set is contained in
    `(Conv_{p₁⇒p₂} D′) ● E′`.  Monotonicity in the set side finishes
    the case.
* **`∀⊑∀ r`** (bound `Z ≠ X`).  Given `W′`, `σ`, `σ′` and `q`, the
  hypothesis provides a tag relation `t`.  It also gives the bodies
  `▹ᶜ D′ ◆ σ′` at `r` under `η[X ↦ ℓ₁][Z ↦ ◁σ ▷σ′ q]`.
  * Choose the same `t`.  It is a descriptor, so it means the same in
    the conclusion.
  * Apply the lemma to `r` counter by counter:
    `(Conv D′) ◆ σ′ = D′ ◆ σ′ ≫= Conv_r`.
* **`∀⊑ r`:** the same, against the right set itself, with `Conv_r`.
* **Preservation:** the mirror.  A right error can come only from `u`
  or `s` (for example `gen`'s projection), and the leaf condition
  `(u◃)` rules it out.

The proof never compares two worlds.  The change is all in `η` at `X`,
and both sides extend the world in the same way.

**Instances.**
1. **Case 6** (left `∀ᶜ`, right `inst`), at the right's reveals:
   * the descriptors are `ℓ₁ = ◁σ ▷β′ ▷α′ q₀` and `ℓ₂ = ◁σ q₀`;
   * the conversions are `u` = unseal `β′` then unseal `α′`, and
     `s` = seal `α′` then seal `β′`;
   * the leaf conditions hold by definition, since unsealing after
     sealing is the identity, and unsealing never errs.

   The case, with its timing:
   * The conclusion's `∀⊑` clause provides `W′` (left length `σ`) and
     `q₀`, and asks for a `t`.
   * Apply the hypothesis's `∀⊑∀` clause at the world with `W′`'s left
     list and right counter `β′ = n′ + 1`, with `q′ = ▷α′ q₀`.  The cast
     created `α′ = n′`.  The clause provides `t_h` and the bodies at
     `◁σ ▷β′ ▷α′ q₀`.
   * Then apply this lemma.
   * Then apply the cast lemma's induction hypothesis for `c₀[σ]`
     against `c′[★]`, with `X` left-only on both sides.
   * Then Kripke monotonicity up to `W′`'s right counter.
   * Choose `t = t_h`.
2. **Case 7** (left `∀ᶜ`, right `gen`):
   * `ℓ₁ = ◁σ (tag α′ (▷α′ q))`, the hypothesis's contents relation.  We
     choose it, since the hypothesis's `∀⊑` clause is universal in its
     contents relation.
   * `ℓ₂ = ◁σ ▷α′ q`, the conclusion's.
   * `u` projects `α′` (`?X`) and `s` injects it (`X!`).
   * `(u▹)`: both sides say that the payloads are related at `q` to
     `unseal α′ (untag α′ D′)`.
   * `(u◃)`: `◃` at `ℓ₁` requires every right element to be tagged
     `α′`, so the projection does not err.
   * Here the conversion is not separate from the cast, because `gen`'s
     body cast `c′` also acts at other positions.  So the cast lemma is
     generalized:
     * it takes a source and a target environment, `η_s` and `η_t`,
       which differ at the variables bound by `gen` on the right;
     * the leaf conditions hold at those variables;
     * this lemma's leaf case is that induction's leaf case.
   * Choose `t = t_h`.
3. **The fundamental lemma's type application.** Both sides reveal:
   `σ → T` on the left and `σ′ → T′` on the right.  The reveals take
   `η[X ↦ ◁σ ▷σ′ q̂]` to the substituted derivation `p[q/X]`.  This is
   the two-sided conversion lemma of Section 7.  It is proved the same
   way, with the left conversion handled as in PolyG's left cast lemmas.

**Still open.**
* Case 8 is redone in Section 8a.  It needs the eager normal form for
  casts.
* The coherence obligation of Section 8a remains, now for derivations
  in normal form.

## 8c. Soundness and exact allocation: `β-∀` breaks subject expansion

Found while starting soundness (plan step 3).  Mechanized in
`proof/Denot/BetaAllCounterProbe.agda`.

### The counterexample

* **The terms.** `V = ΛY. ΛX. λx. x : ∀Y.∀X. X ⇒ X`, and the cast
  `c = inst d : ∀X.(X ⇒ X) ∼ ★ ⇒ ★` under `∀ᶜ`, with
  `d = ？X ↦ X!` (X read as `★`).

      redex  = (V ⟨ ∀ᶜ c ⟩) ⦂∀ (★ ⇒ ★) [ 𝔹 ]
      reduct = (V ⦂∀ ∀X.(X ⇒ X) [ 𝔹 ]) ⟨ c [ 𝔹 ]ᶜ ⟩

  `redex —→ reduct` by `β-∀`, a pure step.
* **The denotations, from counter 0.**
  * Redex: the cast value is instantiated at seal 0, which instantiates
    `V` at 0.  Then `inst` creates `α = 1` and instantiates `V`'s body at
    2.  Every result ends at counter **3** (`redex-at-3`).
  * Reduct: the type application instantiates `V` at 0 and reveals on
    `∀X.(X ⇒ X)`.  That reveal is a ∀-conversion,
    `` `∀↑ 〖 1 , 𝔹 ↑ X ⇒ X 〗 ``.  Then `inst` creates `α = 1` and
    instantiates the *conversion* at 2, which instantiates `V`'s body at
    3, as `β-reveal-∀` does.  `ret νλ 4` is a result (`reduct∈`).
  * So `⟦ reduct ⟧ ⊄ ⟦ redex ⟧` (`no-expansion`).

### Where the mismatch is

Checked clause by clause against `Reduction.agda`:

* **`inst` is faithful to `β-inst`.**  It creates `α` at `m`,
  instantiates at `m + 1`, reveals with exactly the reduct's two
  conversions, and casts with `c` read at `★` (the reduct's
  `↑ᶜ (c [ ★/0 ]ᶜ)`).  The `gen`, `Λ` and type-application clauses match
  `β-gen` and `β-Λ` the same way.
* **Counter threading is consistent.**  `≫=` passes the counter along,
  and `◆` ignores it; every caller instantiates at the next free seal:
  * the type application at `n₁`;
  * `∀ᶜ` at the same seal as its own instantiation, since `β-∀` is pure;
  * `inst` at `m + 1`, after `α = m`;
  * a conversion proxy at `σ + 1`.
* **Reduction creates 4 seals on both sides.**  `β-∀` creates none, and
  the reduct creates 4 (`β-Λ`, `β-inst`, `β-reveal-∀`, `β-Λ`).  So
  it is the *redex's* denotation that disagrees with reduction: it ends
  at 3.
* **The faulty clause is `∀ᶜ`, together with the type application's
  reveal.**
  * The denotation instantiates the inner value at `σ`, casts with `c`
    at `σ`, and lets the type application reveal on the target `B`.
  * Reduction reveals on the *source* `A` and then casts with `c[C]`.
  * The number of seals depends on that order, in both directions:
    * an `inst` inside `c` consumes a ∀ of `A`, and in the reduct that
      ∀ is wrapped in a conversion, so the reduct pays one more seal
      (the example above);
    * a `gen` inside `c` produces a ∀ of `B`, and in the redex the
      reveal on `B` wraps it in a conversion, so the redex pays one more
      seal.
* **A candidate repair, (D), not yet checked.**  Let the type
  application pass its argument `C` and its reveal target `B` into the
  polymorphic entry, instead of revealing on `B` itself.  Each value
  form then does what its rule does:
  * `Λ` reveals on the given `B`;
  * `gen c` casts and then reveals on `B`;
  * `∀ᶜ c` passes its own source `A` inward and casts with `c` read at
    `C`;
  * a conversion proxy passes its own source inward.

  This changes the model: entries carry (closed, sealed) types.  The
  second rejected fix below is a cruder form of this idea.  I rejected
  it on a termination argument that may not apply here, because every
  reveal recurses on a type it is given.  Whether casting with `c` at a
  run-time type `C` (for example, a tag at `C`) can be defined by
  structural recursion is the open point.

* Two fixes I tried on paper fail:
  * **Reusing the seal when instantiating at a variable** (so that
    conversions cost nothing).  This is unsound: the inner variable and
    the outer one then share a seal, so a value tagged with the inner
    variable inside the body would pass a projection at the outer one,
    where reduction blames.
  * **Passing the instantiation's types into polymorphic entries**, so
    that a `∀ᶜ` value can reveal on its own source type, as the reduct
    does.  The final reveal then happens at a type that is only known at
    run time, and in the set model the definition of that reveal is not
    structurally recursive.

### A second, smaller problem: identity proxies

* `ground`, `expand` and `β-∀` (through `refl∼ C` in `c [ C ]ᶜ`)
  introduce identity casts at function types.  An identity function proxy
  adds entries with larger argument lists.
* Exact inclusion needs the proxy's set to be contained in the original.
  * This holds for sets of the form `Λᶠ F` with `F` monotone, which
    covers `ground` and `expand`.
  * It fails for a finite argument set `mem U` that the proxy wraps and
    the body returns, which `β-∀` can produce.
* I expect this to break exact inclusion as well.  It is not mechanized.

### What it means for the plan

Soundness as subject expansion with exact counters (PolyG's
`DenotSoundness`) is not available.  The current plan for adequacy has
the same problem, because it states that the final store size equals the
counter.  Both need to relate seals to store variables *up to a
correspondence*, not by equality.  Options:

* **(A) Keep the denotation; prove soundness and adequacy with a logical
  relation between closed terms and denotations.**
  * The worlds are Kripke worlds: a store, a counter, and a map from
    store variables to seals, extended at each instantiation.  Store
    variables that only reduction creates, such as a proxy's variable in
    the example, need not have a seal.
  * At `∀` types the relation quantifies over the instantiation's
    behaviour, so the two sides may create different numbers of seals.
  * At function types the relation for an entry `U ⟼ r` assumes the
    argument is related to *every* element of `U`.  Larger argument lists
    then only make the relation easier, so identity proxies need no
    up-closure lemma.
  * The `β-∀` case becomes a lemma by induction on the cast: a semantic
    cast at the seal, followed by the reveal on `B`, is related to the
    reduct's reveal on `A` followed by `c[C]`.
  * Everything mechanized so far is reused: the model, monotonicity,
    finite support, the bind laws, renaming, substitution and
    consistency.  Steps 4–6 are unchanged.
  * Cost: a second logical relation, typed and Kripke, of roughly the
    size of the step-6 cast lemma.  The semantic side is inductive, so
    no step indexing.
* **(B) Leave the denotational route**: a binary step-indexed Kripke
  logical relation on the operational semantics, as in New, Jamner and
  Ahmed's graduality-and-parametricity proof for PolyGν.  One relation
  instead of two, but steps 2–3 are discarded.  The paper work in
  Sections 8a and 8b transfers in spirit, since it is about relating
  seals and tags.
* **(C) Change the operational semantics** so that allocation is
  compositional, for example by making `β-∀` push the type application
  under the cast differently.  This changes the language, so I have not
  pursued it.

Section 8d checks repair (D) on paper.  As stated it fails, but a
refinement, (D′), passes.  (D′) keeps exact counters and the planned
subject-expansion proof, at the cost of reworking the model and steps
3a–3d.  I now recommend (D′) over (A).

## 8d. Paper check of repair (D)

Result: (D) as stated in Section 8c fails in two places.  A refinement,
(D′), passes the paper check.  It is not mechanized.

### Two problems with (D) as stated

* **The cast needs `C` itself, not just a seal.**
  * The `∀ᶜ`-bound variable has mode `X∼X`, so `c` never tags or
    projects it (`_!` needs `X∼★` or `★∼X∼★`).
  * `c [ C ]ᶜ` (`Consistency.agda:1401`) replaces each `id (＇ X)` with
    `refl∼ C` and substitutes `C` into every type in `c`.
  * The substituted types matter for counting.  `〖_,_↑_〗` is not smart
    at `∀` (`Conversion.agda:86`), so a reveal inside `c` (from `inst`
    or `gen`) that passes through an `X` position builds a `` `∀↑ ``
    proxy at each `∀` of `C`.  Each such proxy costs a seal per
    instantiation.  Read at a seal, the same reveal builds none.
* **Passing the reveal target into the entry is not structural.**
  * A conversion proxy's entry would end with a reveal on the target it
    was given.  `revV` at `∀` builds such a proxy, so `revV` would call
    itself on a type from the run-time argument.  This is the
    termination problem from Section 8c.
  * Passing a syntactic continuation instead only moves the problem:
    `gen` has nothing to pass it to and must run it, and the
    continuation can contain `gen`.

### The refinement (D′)

* **Entries carry the type argument; results carry one flag.**
  * An entry instantiates at a seal `σ` and is given the type argument
    `C`, as a sealed closed type (`θ` substituted into `C`).
  * Each result carries a flag: either *reveal pending* or *done*.
  * Whoever calls `◆` knows its static source type.  When the flag is
    *reveal pending*, the caller reveals on that type.
* **Every caller of `◆` has a static type to reveal on:**
  * the type application `M ⦂∀ B [ C ]` reveals on `B`;
  * `inst` reveals on `A` (the first reveal of the `β-inst` reduct);
  * `∀ᶜ c : ∀A ∼ ∀B` reveals on `A`;
  * a conversion proxy reveals on its own source.
* **Each value form follows its rule:**

  | value | entry at `σ`, given `C` | flag |
  |---|---|---|
  | `Λ M` | `⟦ M ⟧` at `σ` | pending (`β-Λ`) |
  | `V ⟨ gen c ⟩` | `⟦ c ⟧` with the variable at `σ` | pending (`β-gen`) |
  | `V ↑ ∀↑ c`, `V ↓ ∀↓ c`, `revV`/`conV` proxies | inner at `σ+1`; reveal on own source if pending; convert | pending (`β-reveal-∀`, `β-conceal-∀`) |
  | `V ⟨ ∀ᶜ c ⟩` | inner at the *same* `σ`, given `C`; reveal on `A` if pending; `⟦ c ⟧` with the variable at `C` | done (`β-∀`) |

* **A type variable can be represented by a type.**  A new `Rep` case,
  `tyʳ S`, is used only for `∀ᶜ` variables.
  * `id (＇ X)` at `tyʳ S` is the identity proxy of `S`, matching
    `refl∼ C`.
  * A reveal that meets `X` at `tyʳ S` continues as a reveal on `S` in
    which the target does not occur, matching `〖 X , R ↑ C 〗`.
  * Tags and projections never meet `tyʳ`, by the mode argument above.
* **Termination.**
  * Every reveal is on a static type, or on the `S` inside a `tyʳ`.
    The second case is handled by a separate function defined by
    recursion on sealed types, before `revV`.
  * Sealed types are first-order: seal and `★` leaves, plus bound
    variables.  So nothing recurses on a closure.
  * Every clause is structural.
* **Counting.**
  * The counterexample of Section 8c now gives 4 on both sides.  The
    `∀ᶜ` entry reveals `V`'s body on `∀X.(X ⇒ X)`, which builds the
    proxy.  `inst` then pays for that proxy.
  * The `gen` direction: `∀ᶜ` returns *done*, so the type application
    no longer wraps the `gen`'s `∀` in a reveal on `B`.
  * Stacked `∀ᶜ`s: the outer one sees *done* and skips its reveal, as
    `β-∀` applied twice does.
  * `β-∀` creates no seal, and the `∀ᶜ` entry reuses `σ`.
  * The other rules are unchanged from the current denotation.
* **Subject expansion for `β-∀`** reduces to a cast substitution lemma:

      ⟦ c ⟧ᶜ (tyʳ ⌊ C ⌋θ •ʳ θ)  =  ⟦ c [ C ]ᶜ ⟧ᶜ θ

  It holds by induction on `c`, given two commuting lemmas: one for the
  identity proxy and one for the target-free reveal.  It is an
  equality, so `β-∀`'s identity proxies (Section 8c) no longer need an
  inclusion argument.  `ground` and `expand` still need the up-closure
  argument for `Λᶠ` of monotone `F`.
* **Not checked:**
  * `bot-elim` needs a clause under the new entries.  It is never
    observed, so any choice that keeps 3a–3d's lemmas will do.
  * `ground` and `expand` inclusion was argued, not mechanized
    (Section 8c).

### Cost

* **Model and denotation.**  `Val` entries gain the sealed type and
  the flag.  `Rep` gains `tyʳ`.  Six clauses change: `Λ`, type
  application, `∀ᶜ`, `gen`, `inst`, and the two proxy builders.
  `id` gains a case.
* **Proofs.**  Steps 3a–3d (`DenotProps`, `DenotRename`, `DenotSubst`,
  `DenotConsistency`; about 2,400 lines) must be revised.  Most changes
  are in the `∀` cases.  The structure should stay the same.
* **New lemmas.**  The cast substitution lemma above, then soundness
  as subject expansion and adequacy as planned, with exact counters.
* **Compared with (A).**  (D′) changes the model and keeps the simpler
  proof plan.  (A) keeps the model and adds a Kripke logical relation.
  Both stay within the denotational route.

## 9. Plan

1. Risks 1, 2 and 4 are checked.  Decision for risk 1: option (b), a
   two-sided cast rule with a semantic monotonicity lemma.
   * The paper sketch of the cast monotonicity lemma is in Section 8a,
     and the world-change lemma is proved on paper in Section 8b.
   * Case 8 is redone (Section 8a).  It needs casts in eager normal
     form: no `gen` directly over `inst`.
   * Section 7a gives:
     * the normal form's grammar;
     * the finding that `lower?`'s evidence is eager but `compile`'s
       `symᶜ` flips it, so `compile` must apply `eager`;
     * the two-context type precision and the cast-calculus term
       precision;
     * a paper proof that elaboration preserves precision.
   * **Mechanized** (`Denot/`, `proof/Denot/`, public statements in
     `Denot/Meta.agda`, checked by `All.agda`):
     * the normal form and `eager`, with `eager c` in normal form;
     * two-context precision, contained in `Imprecision` (`forget`),
       and the converse for embedded right types (`back`);
     * the cast-calculus term precision;
     * eager elaboration (`ElabE`, `compileᴱ`) and the theorem that it
       preserves precision.
   * Deferred to the type-application cases of the fundamental lemma:
     uniqueness of two-context derivations and the semantic substitution
     lemma (Section 7a).  No syntactic substitution lemma is needed.
2. Port the PolyG model (`GraphModel`, `Denotation`) to GTSFImp's terms.
   **Done** (`Denot/GraphModel.agda`, `Denot/Denotation.agda`):
   * **Values.** Values gain constants, and closed grounds include
     seals.
   * **Allocation is mirrored exactly**, since soundness is subject
     expansion and results carry their final counter:
     * a type application creates one seal;
     * an `inst` cast creates two (`α := ★`, then the value's own
       instantiation at `α`);
     * an instantiation through a ∀-conversion creates two (the
       proxy's, then the inner value's instantiation at it).
   * **Reveals.** The type application reveals with the very conversion
     term that reduction produces, `〖 0 , ⇑ᵗ A ↑ B 〗`.  Its conceal
     parts traverse `A`'s structure through the source types of the
     inner ∀-conversions, as reduction does.
   * **The one type-directed piece.** A ∀-conversion's inner
     instantiation reveals on its source body type, which is not a
     subterm of the conversion.  `revV`/`conV` give that reveal by
     recursion on the type.  Its representation is always a type
     variable, so replacing it keeps the type's shape and the recursion
     is structural.  Soundness needs
     `⟦ 〖 X , ＇Y ↑ C 〗 ⟧↑ ≡ revV C X`.
   * **Casts.** Inside an `inst` cast the instantiated variable is
     represented by `★`, and a tag or projection at it is the identity,
     as `c [ ★/0 ]ᶜ` makes it.
   * **`β-∀` and soundness.** `β-∀` substitutes the instantiation type
     into the cast, so identity casts at that type appear as proxies.
     Soundness needs identity proxies to be the identity on closures,
     which holds for sets of the form `Λᶠ F` with `F` monotone and for
     `Λᴾ G`.
3. Consistency, soundness and adequacy (reusing GTSFImp's type safety).
   **Done so far** (`proof/Denot/`):
   * `DenotProps`: monotonicity, finite support, the bind laws, and the
     β law.  Transformers (`𝒱 → ℕ → ℛ`) are handled generically:
     sequencing, function and ∀ proxies, and gen values each get one
     lemma, and reveals, conversions, casts and terms follow by
     induction.
   * `DenotRename`: invariance under injective renaming of type
     variables, including the shift `⇑ᵗᵐ` that allocation applies.  It
     covers the type application's built conversions `〖 0 , ⇑ᵗ A ↑ B 〗`
     with an arbitrary representation, using the syntactic lemma that
     renaming commutes with `replaceTy`.
   * `DenotSubst`: term renaming and substitution, for β.
   * `DenotConsistency`: every denotation is consistent when the
     environment is.

   **Blocked: soundness as subject expansion fails** for `β-∀`
   (Section 8c; mechanized counterexample in
   `proof/Denot/BetaAllCounterProbe.agda`).  The redex and the reduct
   create different numbers of seals, so the exact-counter inclusion
   `⟦ N ⟧ ⊆ ⟦ M ⟧` does not hold.  Adequacy's "final store size equals
   the counter" has the same problem.  Proposed replacement, option (A)
   of Section 8c: one Kripke logical relation between closed terms and
   denotations, giving soundness and adequacy together.  **Waiting for a
   decision** between options (A), (B) and (C).
4. Descriptors, environments and worlds (Section 4); the relations
   (Section 5); their properties.
5. The conversion lemma; monotonicity of consistency casts.
6. The fundamental lemma on cast-calculus precision; the theorem, in the
   form of
   `proof/DGG/DynamicGradualGuaranteeDef.agda`.

Estimate: larger than PolyG's denotational part, 12,000–16,000 lines,
dominated by the cast monotonicity lemma.  For comparison, the operational
attempt in `proof/DGG` is about 92,000 lines and unfinished.
