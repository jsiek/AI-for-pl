# The dynamic gradual guarantee for GTSFImp by a logical relation

Status: the syntactic layer is carried over and checked.  The relation
is designed on paper (Section 6), and its mechanization has started.

## 1. Goal and route

* **Goal.**  The dynamic gradual guarantee for GTSFImp's cast calculus.
  If closed programs `M ⊑ M′` (`M` more precise), then:
  * if `M` reduces to a value, `M′` reduces to a less precise value;
  * if `M` diverges, `M′` diverges;
  * if `M′` reduces to a value, `M` reduces to a more precise value or
    to `blame`;
  * if `M′` diverges, `M` diverges or reduces to `blame`.
* **Route: option (B)** of `notes/denotational-dgg.md`, Section 8c.
  * A binary, step-indexed, Kripke logical relation on the reduction
    semantics, in the style of New, Jamner and Ahmed's proof of
    graduality and parametricity for PolyGν
    (`papers/new2020-graduality-and-parametricity.pdf`).
  * The guarantee is the relation's fundamental lemma, read at closed
    programs.
* **Why not the denotational route.**  `notes/denotational-dgg.md`,
  Sections 8c–8f, on branch `gtsfimp-denotational` (PR #215):
  * soundness as subject expansion fails for `β-∀` (exact seal counts,
    then identity casts at `∀` types);
  * the repair, option (A), needs two term–denotation relations, one of
    them step-indexed, on top of the denotational guarantee relation;
  * (B) needs one relation.

## 2. Carried over from the denotational branch

The syntactic layer (step 1 of the old plan) is independent of the
denotation.  It moved from `Denot/` to `LR/`, unchanged except for
module names and charters.

| file | content |
|---|---|
| `LR/Precision.agda`, `proof/LR/Precision.agda` | two-context type precision `Φ ⊢ A ⊑ B`, contained in `Imprecision` |
| `LR/EagerCast.agda`, `proof/LR/EagerCast.agda`, `proof/LR/SwapRename.agda` | the eager normal form of casts and `eager` |
| `LR/CastPrecision.agda` | cast-calculus term precision, the relation of the fundamental lemma |
| `LR/Elaborate.agda`, `proof/LR/Elaboration.agda` | eager elaboration, and the theorem that it preserves precision |
| `LR/Meta.agda` | the public statements |

`notes/denotational-dgg.md` is copied unchanged as the record of the
design work.  Its section numbers are cited here and in the charters.

* **Two-context precision.**  The single-context `Imprecision` relates
  `X ⊑ X` for every variable, which admits the `Catchup` counterexample
  (`notes/denotational-dgg.md`, Section 8, risk 4).  The same problem
  would affect any relation that pairs left and right variables.
* **The eager normal form.**  Without it the left program can
  instantiate a paired variable before the right one does
  (`notes/denotational-dgg.md`, Section 8a, case 8).  This is about
  reduction, not about the denotation, so (B) needs it too.

## 3. What transfers from the denotational design

* **Which side creates seals** (Section 3).
  * Shared type applications create a store variable on both sides.
  * A left-only `Λ` or a left `inst` creates a left-only one.
  * A right `inst` while the left stays `∀` creates a right-only one,
    which never reaches the boundary.
* **Leaf relations and tag relations** (Section 4).
  * The relation for a variable's contents belongs in a Reynolds
    environment.
  * The relation for values *tagged* with a variable at `★` belongs in
    the world.
  * Section 8b shows that keeping the contents relation in the world
    makes the world-change lemma false.
* **The `∀` clauses** (Section 5): `∀⊑∀`, `∀⊑` and `∀⊑★`, each choosing
  a tag relation existentially.
* **Paper checks of the new cases** (Section 6): left-only `Λ`, `gen`
  under a left-only type application, and a right `inst` while the left
  stays `∀`.
* **Cast monotonicity** (Section 8a): related values cast at related
  types are related.  In (B) this is the compatibility lemma for casts.
* **The world-change lemma** (Section 8b).

The step-indexed setting changes how the relations are *defined*:

* by the step index and the type, not by recursion on denotational
  values;
* with a later modality wherever a value is used after a step.

It does not change which seals are paired or which relation each one
carries.

## 4. Plan

1. **Design on paper.**
   * Worlds: the step index, the two store sizes, and the variable
     correspondences with their tag relations.
   * The value and expression relations.  As in New–Jamner–Ahmed,
     there are two expression relations, one counting steps on each
     side, because the guarantee is asymmetric in blame and divergence.
   * Check them against the cases of Section 3 above.
2. **Mechanize the worlds and the relations**, with monotonicity
   (Kripke and downward closure in the index).
3. **Compatibility lemmas:**
   * application, type application, primitives;
   * conversions (reveals and conceals);
   * casts (cast monotonicity, Section 8a);
   * the world-change lemma (Section 8b).
4. **The fundamental lemma** for `LR.CastPrecision`.
5. **The dynamic gradual guarantee**, via `elaboration-preserves-precision`
   (`LR/Meta.agda`).

## 5. Open points

* **The `inst` variable.**  It is read as `★`: reduction substitutes
  `★` for it in the cast.  It is never tagged, so its world entry is
  irrelevant (the empty relation will do).  In the cast lemma it is a
  substitution-kind entry at `★` (Section 6.4).
* **Blame on the left.**  The left may blame where the right does not.
  This is the asymmetry the two expression relations encode.
* **Mixed indexing.**  Section 8a's monotonicity argument was by
  induction on the cast.  In the step-indexed setting the induction is
  on the cast, nested inside the step index.

## 6. The relation (paper design)

Written in the first design session.  Notation: `d ∈ {≺, ≻}` is the
direction.  `≺` counts the left program's steps, `≻` the right
program's, as in New–Jamner–Ahmed.  `n` is the stage (the step index).

**Superseded in part.**  Section 6.11 replaces semantic relations with
descriptors, because Agda with `--safe` has no impredicative universe
for them.  This affects 6.1, 6.3, the staged worlds of 6.10, and the
type of `R` in 6.5.  The rest stands.

### 6.1 Why semantic relations, and why staged worlds

* **Two kinds of relation are needed** (Section 3 above, and
  `notes/denotational-dgg.md`, Section 8b):
  * a *leaf relation* for each type variable of the precision
    derivation, in a Reynolds environment `δ`;
  * a *tag relation* for each left store variable, in the world, read
    by the `★` clause.
* **Both are semantic**, as in PolyGν: families of sets of
  world–term–term triples.
* **The syntactic alternative fails.** Making both closed descriptors
  (the old note's `◁σ`, `▷σ′`, `tag G`) does not give a well-founded
  definition:
  * a `∀⊑` clause in `≻` relates a left-only instantiation while the
    right takes no step, so the stage does not drop;
  * the body's leaf for the new variable would then be interpreted at
    the same stage by a descriptor of arbitrary size.
* **With semantic leaves**, the value relation is defined by recursion
  on the precision derivation.  The stage drops only at the `★`
  clause's function and `∀★` grounds, which are guarded.
* **Worlds are staged.**  Semantic tag relations make worlds contain
  relations about worlds.  As in PolyGν, a world of stage `n` holds
  tag relations only at stages `k < n`.

### 6.2 Steps

* `M —→ᵏ[ χs ] N`: exactly `k` steps of `_—→[_]_`, every step counted,
  pure or store-changing.  `χs` composes into an order-preserving
  embedding of the old store into the new one.
* Reduction never reads the store's contents (`Reduction.agda`), so a
  store is just its size `Δ`.

### 6.3 Worlds

* `W n`, a world of stage `n`:
  * the two store sizes `ΔL`, `ΔR`;
  * `tag : TyVar ΔL → Tags n`, where `Tags n` is a relation at each
    stage `k < n`, and a relation at stage `k` is
    `Rel k = (w : W k) → Term (ΔL w) → Term (ΔR w) → Set`.
* Right store variables have no entries: no clause consults them.
* **Restriction.**  `⌊ w ⌋ₖ` for `k ≤ n` drops the tag relations at
  stages `≥ k`.
* **Extension.**  For `w′ : W n′` and `w : W n`, `w′ ⊒ w` holds when:
  * `n′ ≤ n`;
  * there are order-preserving embeddings `ρL : ΔL ↪ ΔL′` and
    `ρR : ΔR ↪ ΔR′`;
  * `tag w′ (ρL X) = ⌊ tag w X ⌋ₙ′` for every `X`.

  Strict extension `w′ ⊐ w` adds `n′ < n`.
* **`RelΩ`** is a relation at every stage, `(k : ℕ) → Rel k`.  It is
  *monotone* when it is closed under extension, with the terms renamed
  by `ρL`, `ρR`.  Every leaf and tag relation is required to be
  monotone.
* **Later.**  `(▷ R)` at stage `0` is everything, and at stage `k + 1`
  in world `w` it is `R` at stage `k` in `⌊ w ⌋ₖ`.

### 6.4 Interpretations

For `Φ : Corr Δ Δ′` and a world with stores `ΔL`, `ΔR`, an
interpretation `δ` has:
* `δl : TyVar Δ → Ty ΔL` and `δr : TyVar Δ′ → Ty ΔR`;
* `ρ : TyVar Δ → RelΩ`, the leaf relation of each left variable.  It
  is ignored for `dead` variables.

An entry is of one of two kinds; the kind matters only for validity:
* **Store-variable kind**: `δl X = ＇ Xl` (and `δr Y = ＇ Xr` when `X`
  is paired with `Y`).  Values at `X` are sealed: `V ↓ seal Xl _`.
* **Substitution kind**: `δl X = T` for any type.  Values at `X` are
  `T`-values.  This is the bound variable of a type application after
  its reveal.

**Validity of `δ` in `w`** ties store-variable entries to the world's
tag relations, so that projections at those variables read the leaf
relation back:
* **paired `X ↔ Y`:** `tag Xl` relates `(Wl , Vr)` exactly when
  `Vr = Wr ⟨ (＇ Xr) ! ⟩` and `ρ X` relates `(Wl , Wr)`;
* **left-only `X`, in `≺`:** `tag Xl = ρ X`;
* **left-only `X`, in `≻`:** `ρ X = ▷ (tag Xl)`.  The leaf is guarded
  (Section 6.6).

The fundamental lemma is stated for interpretations of store-variable
kind that are valid.  Its `δl` and `δr` are then order-preserving
embeddings into the store: the term's type variables are the store
variables of the `Λ`s that enclose it, allocated outermost first.  So
the term is closed by `renameᵗᵐ`, and no type substitution of terms is
needed.  Substitution-kind entries occur only in the `∀` clauses and
in the cast lemma under `∀ᶜ` and `inst`.

### 6.5 The value relation `𝒱ᵈₙ⟦ p ⟧ δ w Vl Vr`

By recursion on `p : Φ ⊢ A ⊑ A′`.  `↑` transports along an
extension; `δ[0 ↦ e]` extends the interpretation.

* **`ι⊑ι`:** `Vl = Vr = $ κ`.
* **`X⊑Y`, `X⊑★`:** the leaf, `ρ X n w Vl Vr`.
* **`★⊑★`:** both are ground injections, `Vl = Wl ⟨ Gl ! ⟩` and
  `Vr = Wr ⟨ Gr ! ⟩`, and by `Gl`:
  * `‵ ι`: `Gr = ‵ ι` and `Wl = Wr = $ κ`;
  * `★⇒★`: `Gr = ★⇒★` and `▷ 𝒱⟦ ★⇒★ ⊑ ★⇒★ ⟧ (Wl , Wr)`;
  * `∀★`: `Gr = ∀★` and `▷ 𝒱⟦ ∀★ ⊑ ∀★ ⟧ (Wl , Wr)`;
  * `＇ Xl`: `tag Xl`, at stage `n − 1` in `⌊ w ⌋`, relates `(Wl , Vr)`.
* **`⇒⊑⇒ p₁ p₂`:** for every `w′ ⊒ w` and every `Wl`, `Wr` with
  `𝒱⟦ p₁ ⟧ δ↑ w′ Wl Wr`:
  `ℰ⟦ p₂ ⟧ δ↑ w′ (Vl↑ · Wl) (Vr↑ · Wr)`.
* **`⇒⊑★ p₁ p₂`:** `Vr = Wr ⟨ (★⇒★) ! ⟩`, and the `⇒⊑⇒` clause on
  `p₁`, `p₂` relates `(Vl , Wr)`.  In `≻`, under `▷`.
* **`ι⊑★`:** `Vr = $ κ ⟨ ι ! ⟩` and `Vl = $ κ`.  In `≻`, under `▷`.
* **`∀⊑∀ p`:** for every `w′ ⊒ w`, types `T` and `T′`, and monotone,
  identity-closed `R`:
  `ℰ⟦ p ⟧ δ↑[0 ↦ (T , T′ , R)] w′ (Vl↑ ⦂∀ _ [ T ]) (Vr↑ ⦂∀ _ [ T′ ])`.
* **`∀⊑ p`** (`∀A ⊑ B`): for every `w′ ⊒ w`, type `T` and relation `R`:
  `ℰ⟦ p ⟧ δ↑[0 ↦ (T , R)] w′ (Vl↑ ⦂∀ _ [ T ]) Vr↑`.  In `≻`:
  * `R` ranges over guarded relations `▷ R′`;
  * when `B = ★`, the extension is strict.
* **`∀★⊑★` and `∀⊑★ p`:** `Vr = Wr ⟨ ∀★ ! ⟩`, and the `∀⊑∀` clause
  (with a `dead` variable for `∀⊑★`) relates `(Vl , Wr)`.  In `≻`,
  under `▷`.
* **`bot-elim`, `bot⊑★`:** empty, because no closed value has type
  `∀X.X`.

Two side conditions:

* **Identity-closed `R`.**  If `R` relates `(V , V′)`, then
  `V ⟨ refl∼ T ⟩` and `V′ ⟨ refl∼ T′ ⟩` are related by the expression
  relation at `R`.
  * The cast lemma under `∀ᶜ` needs this: `β-∀` substitutes `refl∼ T`
    for `id (＇ X)` (`Consistency.agda`, `_[_]ᶜ`).
  * The fundamental lemma instantiates `R = 𝒱⟦ q ⟧`, which is
    identity-closed by the identity-cast lemma.
* **Well-founded.**
  * The recursion is structural in `p`, except at the `★⊑★` grounds
    `★⇒★` and `∀★`, which go to stage `n − 1`.
  * The function and `∀` clauses reach `ℰ`, which reaches `𝒱` on a
    subterm of `p` at a stage `n′ ≤ n`.
  * So the order is lexicographic in `(n , p)`.  Section 6.10 gives the
    Agda encoding.

### 6.6 The guard convention for `≻`

**Rule.**  In `≻`, every relation whose right type is `★` is guarded:
its stage-`n` content depends only on stage `n − 1`.

**Why.**  In `≻` the left's steps are not counted.  Left-only
operations happen at precisions whose right type is `★`, and they leave
the right side unchanged: a left-only projection `?X`, a reveal, or an
instantiation.  So they must take a related pair at stage `n` to a
related pair at stage `n`.

**Checked on paper:** the `gen` example of the old note's Section 6.
* Left `(f ⟨ gen (X! ↦ ?X) ⟩) [C]` against right `f : ★ → ★`, related
  by `∀⊑` and `•⊑`, with `q : C ⊑ ★`.
* The left creates a left-only `Xl` and chooses `tag Xl = R′`, where
  `R′` is the guarded core of `R = 𝒱≻⟦ q ⟧ = ▷ R′`.  The leaf of `X`
  is `R` (validity in `≻`).
* An argument related at the leaf, in stage `n`, is tagged by the left
  alone with `X!`.  The `★⊑★` clause at stage `n` reads `tag Xl` at
  `n − 1`, that is `R′` at `n − 1`, which is `R` at `n`: the same.  No
  step was needed.
* `f` runs on both sides (the right's steps lower the stage).  The
  left's `?X` turns the `★⊑★` relation at some `m` back into the leaf
  at `m`, again without a step.  The left's reveal leaves the leaf
  unchanged.
* If `f` returns some other `★` value, the left's `?X` blames, which
  `ℰ≻` allows.

**`R = 𝒱≻⟦ q ⟧` is guarded for every `q : T ⊑ ★`**, case by case:
* `★⊑★`: every ground reads stage `n − 1`; constants have no content;
* `ι⊑★`, `⇒⊑★`, `∀★⊑★`, `∀⊑★`: guarded by Section 6.5;
* `X⊑★`: the leaf is guarded by validity, or quantified guarded;
* `∀⊑` into `★`: strict extension, by Section 6.5;
* `bot⊑★`: empty.

**In `≺`** nothing extra is needed.  Left-only operations are counted
there, and right-only operations (a right `inst` while the left stays
`∀`) are not counted but need no guard, because `≺` lets the right
take any number of steps.

### 6.7 The expression relations

* `ℰ≺ₙ⟦ p ⟧ δ w Ml Mr` holds when one of these does:
  * `Ml` takes `n` steps (it runs out);
  * `Ml` reaches `blame` in fewer than `n` steps;
  * `Ml` reaches a value `Vl` in `k ≤ n` steps and `Mr` reaches a value
    `Vr` in any number of steps, and there is a world
    `w′ : W (n − k)` with `w′ ⊒ w`, whose stores and embeddings are
    those of the two reductions, such that `𝒱≺ₙ₋ₖ⟦ p ⟧ δ↑ w′ Vl Vr`.
* `ℰ≻ₙ` is the mirror, with two differences:
  * it counts the right's steps;
  * `Ml` reaching `blame` in *any* number of steps is always allowed.
* A right `blame` is allowed in neither relation unless the left also
  blames.
* At stage `0` both relations hold trivially, because the counted side
  has taken zero steps.

### 6.8 The theorems

* **Fundamental lemma.**  Let `Φ ∣ γ ⊢ M ⊑ M′ ⦂ A ⊑ A′ ∶ p`.  Then for
  every direction, stage `n`, world `w`, valid store-variable-kind `δ`
  and pair of closing substitutions related at `γ`:

      ℰᵈₙ⟦ p ⟧ δ w (M closed on the left) (M′ closed on the right)

  Here "closed" means renamed by `δl` (or `δr`), then substituted.
* **The dynamic gradual guarantee** for closed programs.  Instantiate
  at `Φ = []`, `γ = []`, the empty world, and every `n`:
  * `ℰ≺ₙ` for `n` larger than the left's step count: if the left
    reduces to a value, the right reduces to a related value;
  * `ℰ≻ₙ` the same way: if the right reduces to a value, the left
    reduces to a related value or to `blame`.

  The two divergence clauses are the contrapositives.  Source programs
  reach this through `elaboration-preserves-precision`
  (`LR/Meta.agda`).  Whether the divergence clauses need determinism
  of reduction is still to be checked.

### 6.9 Lemmas, in dependency order

1. **Worlds:** restriction composes; extension is reflexive and
   transitive.
2. **Monotonicity:** `𝒱` and `ℰ` are Kripke-monotone (including
   downward closure in the stage), given monotone leaf and tag
   relations.
3. **Expression lemmas:**
   * values are expressions;
   * backward reduction, with stage bookkeeping;
   * the bind lemma for evaluation contexts.
4. **Uniqueness** of two-context precision derivations, and the
   **substitution lemma**:
   `𝒱⟦ p ⟧ δ[0 ↦ (T , T′ , 𝒱⟦ q ⟧ δ)] = 𝒱⟦ r ⟧ δ` for the
   `r : A [ T ] ⊑ B [ T′ ]` that `•⊑•` carries.
5. **Conversions.**  A reveal turns a store-variable entry into a
   substitution entry; a conceal turns it back.  This is the two-sided
   conversion lemma of the old note's Section 7, with one-sided
   variants.
6. **The identity-cast lemma** (`refl∼ T` is related to the identity).
7. **The cast lemma** (cast monotonicity, old note Section 8a, cases
   1–8), with the world-change lemma (old note Section 8b) as its
   `∀ᶜ`/`inst` and `∀ᶜ`/`gen` cases.
8. **Compatibility lemmas** for each rule of `LR.CastPrecision`.
9. **The fundamental lemma**, then the guarantee.

### 6.10 The Agda encoding

* **Staged worlds**, by mutual recursion on the stage:

      W n          = Σ ΔL ΔR . (TyVar ΔL → Tags n)
      Tags zero    = ⊤
      Tags (suc n) = Tags n × Rel n
      Rel n        = (w : W n) → Term (ΔL w) → Term (ΔR w) → Set

  The calls are `W n → Tags n` and `Tags (suc n) → W n`, `Tags n`.
  Every cycle drops the stage.
* **The relations.**  `𝒱` and `ℰ` are mutual, by lexicographic
  recursion on the stage and the derivation.
  * `ℰ`'s future world lives at a stage `n′` given with a proof of
    `n′ ≤′ n`.
  * A helper defined by recursion on that proof calls `𝒱` at `n` (on
    a smaller derivation) for `≤′-refl`, and steps down the stage for
    `≤′-step`.
  * So every call is structural.
* **Directions** are a parameter `d`.  The clauses that differ are the
  `▷` guards of Section 6.5 and the step-counting side in `ℰ`.

### 6.11 Revision during mechanization: descriptors, not semantic relations

Found when writing the definitions in Agda.  It supersedes Sections 6.1
and 6.3, the staged worlds of 6.10, and the semantic `R` of the `∀`
clauses in 6.5.  The mechanized definitions are in `LR/Desc.agda`,
`LR/World.agda` and `LR/Relation.agda`, and they pass `--safe`,
including the termination check.

**The obstacle.**  The `∀` clauses quantify over relations, and the
fundamental lemma instantiates them with `𝒱⟦ q ⟧`.
* A relation valued in `Set`, quantified inside a definition of type
  `Set`, lands in `Set₁`.  So `𝒱⟦ q ⟧` is not one of the relations
  quantified over.
* PolyGν's proof is on paper, in set theory, where this does not arise.
* Agda with `--safe` has no impredicative universe to put the relations
  in.  Worlds that hold semantic relations about worlds would have the
  same problem.

**The fix: quantify over syntax, interpret below the stage.**
* **Descriptors** (`LR.Desc`).  A descriptor is a two-context precision
  derivation with an environment.
  * The environment gives each left variable an *entry*: a nonempty
    list of left seals, a list of right seals, and a descriptor for the
    contents.
  * Descriptors are first-order syntax in `Set`.
  * They express everything the old note's descriptors did (`◁σ`,
    `▷σ′`, `tag`), for example the case-6 leaf `seals σ [] [β′, α′] q₀`.
* **The `∀` clauses quantify over descriptors.**  The new variable's
  leaf is *semantic*: the clause builds it from the descriptor, by calls
  at stages below the clause's own, and it is empty at the stages above.
  It is never read there, because the counted side steps before the body
  is compared.  Empty rather than trivial keeps the relation downward
  closed in the stage.
* **Interpretations** give each left variable either:
  * a syntactic entry, read on demand: the program's store variables,
    and the variables inside descriptors;
  * a semantic leaf: a type application's bound variable after its
    reveal.
* **Worlds are unstaged** (`LR.World`).  A world has the two store sizes
  and a *tag descriptor* per left store variable: the right tag
  variable, if the right tags too, and an entry for the payloads.
  `World : Set`.
* **Leaves are store-relative.**  A semantic leaf built in one world is
  read in a later one through the embeddings of the stores (`RelΩ`).

**Well-foundedness** (the order Agda's termination checker accepts):
* Every entry has a left seal.  So it is read one stage down, or, in
  `≻` with no right seal (a left-only variable), by `G` at the same
  stage *after peeling the left term*.
* `G` (`≻` at a precision whose right type is `★`) reads stage `n − 1`,
  except through tags and entries, which peel the left term.  So the
  same-stage cycles among `G`, `star`, `entry` and the peeling functions
  shrink the left term.
* Within one stage, `𝒱` recurses on the precision derivation.  The
  generic expression closure `ℰᵍ` takes the value relation as an
  argument, so these calls are visible to the checker.
* The semantic leaves and the stage-bounded helpers (`𝒱≤`, `𝒱<`, `G≤`,
  `starAt`) recurse on `≤′` proofs.

**What stays the same:**
* the clauses of Section 6.5, except the type of `R`;
* the guard convention of Section 6.6, where `G` is the guarded
  relation;
* the expression relations of 6.7, the theorems of 6.8 and the lemma
  list of 6.9.

**Identity closure** is now a lemma about descriptors (lemma 6), not a
side condition of the `∀` clauses.  Quantifying over every descriptor
only strengthens the clauses.

## 7. Mechanization status and next steps

**Done** (all checked with `--safe` through `All.agda`):

| file | content |
|---|---|
| `LR/Steps.agda` | counted reduction `M —→^ k [ χs ] N`; the store embedding of a reduction |
| `LR/Desc.agda` | descriptors, entries, tags; their types; renaming |
| `LR/World.agda` | worlds, extension, store-relative relations `RelΩ` |
| `LR/Relation.agda` | interpretations; `𝒱`, `G`, the `★` relation, entries; `ℰᵍ` and `ℰ`, in both directions |
| `proof/LR/WorldProps.agda` | renaming laws for descriptors and tags; extension is reflexive and transitive |
| `proof/TermRename.agda` | `renameᵗᵐ π (renameᵗᵐ η M) ≡ renameᵗᵐ (π ∘↪ η) M` and `renameᵗᵐ id↪ᵗ M ≡ M`, without funext |
| `proof/LR/InterpProps.agda` | equivalence of interpretations `≈ᴵ`; transport along `⊒-refl` and `⊒-trans`; `𝒱`, `G` and `ℰ` respect `≈ᴵ` |

**Renaming terms: how it is done.**
* Mode environments are vectors, `Env∼ Δ = Vec Var∼ Δ`, read with
  `μ ‼ X`, so terms are first-order data.  The only functions left in
  a cast are the `B ≢ ★` arguments of `inst` and `gen`, and these are
  definitionally equal because the library's `⊥` is proof irrelevant.
* Embeddings are canonical: `empty : zero ↪ᵗ zero`, and the embedding
  of the empty context into `Δ` is `ε↪ᵗ`, all skips.  It used to be
  `empty : zero ↪ᵗ Δ`, so `empty` and `skip empty` were two embeddings
  `0 ↪ᵗ 1` with the same action, and the laws failed on the nose:
  `skip empty ∘↪ empty = empty`, so `τ ∘↪ id↪ᵗ ≢ τ`, and renamed
  environments disagreed (`[X∼X]` against `[★∼X∼★]`).  With canonical
  embeddings `∘↪` is associative with unit `id↪ᵗ` (`proof/LR/WorldProps`).
* Casts with different endpoint types are compared by packing each with
  its endpoints (`⟪ c ⟫`) and using `_≡_`, at one fixed environment;
  no heterogeneous equality.  The gate evidence (`Ground`, `NonStar`,
  `NonVar`, `_∈ᵗ_`, `_⊢_∼★`, `_⊢★∼_`) is unique, so it does not matter
  which proof each side carries.

**Next, in order:**
**Interpretations: how it is done.**
* `δ ≈ᴵ δ′`: the types agree pointwise; entry leaves are equal; semantic
  leaves imply each other at every stage, world and pair of embeddings.
* `(δ ↑ᴵ e) ↑ᴵ e′ ≈ᴵ δ ↑ᴵ ⊒-trans e′ e` and `δ ↑ᴵ ⊒-refl w ≈ᴵ δ`.  The
  semantic leaves need associativity and right unit of `∘↪`, which is
  why embeddings had to be canonical.
* `𝒱-resp` and its helpers: one mutual induction mirroring `𝒱` and `G`,
  on the precision derivation and the stage.  Function arguments flip
  the equivalence (`≈ᴵ-sym`).  `ℰᵍ-map` shows the expression closure
  is monotone in its value relation.

1. **Kripke monotonicity** of `𝒱`, `G`, `star`, the entries and `ℰᵍ`,
   including downward closure in the stage.
   * The semantic leaves are empty above their bound, so they are
     downward closed.
   * The hypothesis is that leaves are monotone.  Descriptor-built
     leaves are, by the lemma itself, so this is a mutual induction.
2. **Expression lemmas** (Section 6.9, item 3), then items 4–9:
   * uniqueness of precision and the substitution lemma;
   * conversions;
   * identity casts;
   * the cast lemma, with the world-change lemma;
   * compatibility lemmas;
   * the fundamental lemma;
   * the guarantee.

**Not yet checked against the definitions** (they were checked on paper
against Section 6.5, before the switch to descriptors):
* the fundamental lemma's `Λ` cases;
* the shared type application;
* the cast lemma's cases 4–8.

The descriptor version should not change them, because every leaf the
paper proofs use is a descriptor (Section 6.11).
