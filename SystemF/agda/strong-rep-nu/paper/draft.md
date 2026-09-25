# Why strong-rep-nu looks the way it does — a brainstorm

Draft, 2026-09-25.  A ranked list of the design decisions in
`SystemF/agda/strong-rep-nu/`, each paired with the example that forces
it.  The intended reader knows System F and has been told one goal:
**color preservation**.  Everything else should follow from that goal
plus a small number of examples.

Notation is the named presentation of `notes/notes.md`: `X, Y, Z` are
type variables, `α, β, γ` representation variables, `Ξ` the store,
`↓X` / `↥X` the `unbind` / `bind` changes of a boundary scope.  Traces
marked *rendered* were produced by `scripts/render_term.sh` from
`Examples.agda`, not transcribed from de Bruijn indices.  Plain System F
traces are written by hand; they have no indices to get wrong.

---

## 0. The starting point: System F, and the goal

**The goal (Jeremy, 2026-09-04, `notes/DECISIONS.md`):** *"the color of
a non-boundary term should never change during reduction."*  Color a
subterm by the set of type variables it can see.  Reduction may move
subterms around, but a moved subterm keeps its color; only boundary
syntax may say anything new about scope.  The theorem is
`ColorPreservation.agda`:
`ScopeMapPreservation` (`names Δ₂ ≡ map ρ (names Δ₁)` at every residual
position) and its corollary `ColorPreservation` (the size of the scope
map is preserved).

**System F fails it twice, once for each β-rule.**

*Type β recolors the body by deleting a variable.*

    (ΛX. λx:X. x) [ℕ] · 7
      → (λx:ℕ. x) · 7                 λx:X.x was colored {X}; now colored {}
      → 7

The body used to be read with `X` in scope, holding an `X`.  After the
step there is no `X` anywhere: the representation `ℕ` was written into
the body.  The body now *knows* `X = ℕ`, which is exactly what
parametricity says it must not know.

*Term β recolors the argument by adding variables.*

    (λx:ℕ. ΛY. λy:ℕ. x) · 7
      → ΛY. λy:ℕ. 7                   7 was colored {}; now colored {Y}

The argument was authored where `Y` did not exist and now sits under
`ΛY`.  Harmless for `7`, but for a polymorphic argument it is the same
failure one level up (Decision 4).

[TODO: We're going to ignore color for contants, so we should replace
the 7 in the example with a slightly larger term, perhaps an identity 
function on nat.]

The rest of the list is what it takes to repair these two recolorings
without losing type safety.

---

## The ranked list

Ranked by how much of the calculus each decision explains.  Every entry
has an **example**, **what goes wrong without the decision**, **what the
calculus does**, and **where to look**.

### 1. Type application does not substitute; it installs a boundary

The single decision the rest serves.  `ν X:=A · (ΛX.V) ⟨ c ⟩` does not
compute `V[X:=A]`.  It allocates a store cell `α := R` for `A`'s
representation `R`, keeps `V` as it is, and wraps it in a **boundary**
`V ⟪ ↥X , c ⟫` that makes `X` a live name for `α` inside.

**Example: the baseline** (§1a, `P₀`; rendered, `showRun 0 5 P₀-⊢`):

    Ξ = []         ((ν X:=ℕ · (ΛY. λx:Y. x) ⟨ seal X ↦ unseal X ⟩) · 7)
      --[Nu-Λ]-->
    Ξ = [α := ℕ]   (((λx:X. x) ⟪ ↥X , seal X ↦ unseal X ⟫) · 7)
      --[Peel]-->
    Ξ = [α := ℕ]   (((λx:X. x) · (7 ⟪ ↓X , seal X ⟫)) ⟪ ↥X , unseal X ⟫)
      --[Beta]-->
    Ξ = [α := ℕ]   ((7 ⟪ ↓X , seal X ⟫) ⟪ ↥X , unseal X ⟫)
      --[Merge]-->
    Ξ = [α := ℕ]   (7 ⟪ ↥X , ↓X , id ℕ ⟫)
      --[Drop]-->
    Ξ = [α := ℕ]   7

**Against System F:** `λx:X. x` keeps its color `{X}` through the whole
run.  The identity function never sees `ℕ`: `7` enters it sealed as an
`X` and leaves it unsealed as an `ℕ`.  That is parametricity *enforced
at run time*, which is where "strong" in Strong System F comes from
(`Design.md` §1).

**Where:** `Reduction.agda` `Nu-Λ`; `notes/notes.md` "Reduction".

### 2. A boundary carries a *conversion*, and crossings go inward through the dual

A boundary relates two types, the interior type (read inside) and the
exterior type (read outside), by an explicit **conversion**, built leaf
by leaf: `seal X` (the interior sees the representation, the exterior
sees the name), `unseal X` (the reverse), `c ↦ d`, `∀X.c`, and `id`.
When a function wrapped in a boundary is applied, the argument
**crosses** inward, wrapped in the **dual** scope with the domain
conversion, and the result stays wrapped in the codomain conversion
(`Peel`).

**Example:** the `Peel` step of §1a above.  `7 : ℕ` must become an `X`
inside, so it gets `⟪ ↓X , seal X ⟫`: the dual `↓X` of `↥X`, with the
domain half `seal X`.  The answer gets `unseal X` outside.

**Without it (history):** a boundary that recorded just "the interior is
the exterior with `X := A`" and read *one* type through two
substitutions.  The v2 survey found 61 of 195 configurations where the
term did not determine the relationship (`notes/BoundarySurvey.md`,
`DesignPoints.md` D35).  An explicit conversion is what closes them.

**Sub-decisions, each with its own example:**

* **Crossings are inward only.**  An earlier `Merge ⊕` re-expressed an
  inner boundary *outward* across a conceal, which is the inverse of a
  substitution and therefore relational.  The v1 gauntlet (§9g)
  exhibited a reachable nesting with no flat form at all
  (`DesignPoints.md` D24–D25).  `Peel` only ever moves things *in*.
* **No polarity index.**  Conversions were first polarized (`↦` flips on
  domains).  The pushed `seal ↦ seal` of `TyPeelR` typed at *neither*
  polarity (`DECISIONS.md` "RULING: polarity dropped", 2026-09-06).  The
  boundary's frames already say, per variable, which side sees what.

### 3. A boundary scope is a list of changes, and an unbind masks instead of dropping

A boundary carries a **sequence** `Θ` of changes, `↓X` (unbind) and
`↥X` (bind), and its interior is **computed from the exterior at the
boundary's current position**.  An unbind deletes one name and keeps
every other one, including names bound *after* `X`.

**Example: the pre-boundary counterexample** (Jeremy's trace; `Design.md`
§1; §5a is today's version):

    (ΛX. λf:(∀Z.Z→Z). ΛY. f [Y]) [ℕ] · (ΛZ. λz:Z. z)

**Without it:** the pre-boundary design had one wrapper per variable,
`M ↑[X:=A]` / `M ↓[X:=A]`.  A conceal's interior was `Γ ↓ X`, the
exterior *truncated* at `X`, with everything bound after `X` dropped.
Its elimination rule `TyWrapCncl` pushed the type argument into the
concealed body.  After four steps the conceal sits under the later
`ΛY`, its interior is `(Y , X:=ℕ) ↓ X = ∅`, and the pushed `[Y]` must
type at `∅ ⊢ Y`.  The fourth term has no type at all.

**Two lessons, and together they are what a boundary is:**
1. **Mask, don't drop.**  `↓X` deletes `X` and nothing else.  The
   variables bound between the boundary's birth and its current position
   stay nameable.
2. **Never push a type argument into a concealed body.**  Record it as a
   new `bind` instead.  A boundary then has to carry a bind and an
   unbind at the same time, so it is a *list*.

**What the calculus does with the same program:** §5a runs it (value
restriction applied, Decision 7) to a value at `∀Y. ℕ ⇒ Y ⇒ Y`; see the
trace in Decision 4.

**A later instance of the same lesson, "move the unbinds, don't drop
them":** the scope move `Θ₁ ⋉ Θ₂` (`DesignPoints.md` D45), and the
`dual` that dropped `bind` entries and so let an **ill-typed** redex step
to a **well-typed** contractum (Jeremy's tightness test,
`DesignPoints.md` D47; `strong/` `proof/DualTightness`).  That makes
three times the design died of dropping something.  Candidate slogan:
*nothing may be dropped*.

### 4. Frame-exact term substitution

Substituting a value `W : A` for `x` under a `ΛY` wraps it in that
binder's dual, `W ⟪ ↓Y , id A ⟫`.  The value arrives in the frame it was
born in.  This is `_[_∶_]ᵐ` (`TermSubst.agda`), and why `Beta` carries
the argument type.

**Example:** §5a, the `Beta` step (rendered, `showRun 0 20 E₀-⊢`; the
renderer reuses letters across binders, so `X′` is simply the argument's
own bound variable):

    Ξ = [α := ℕ]
    (((λx:(∀Y. Y⇒Y). ΛY. λy:ℕ. ν Z:=Y · x ⟨ seal Z ↦ unseal Z ⟩)
        · ((ΛX′. λx:X′. x) ⟪ ↓X , ∀Y. id Y ↦ id Y ⟫))
      ⟪ ↥X , ∀Y. id ℕ ↦ (id Y ↦ id Y) ⟫)
      --[Beta]-->
    Ξ = [α := ℕ]
    ((ΛY. λx:ℕ. ν Z:=Y ·
        (((ΛX′. λy:X′. y) ⟪ ↓X , ∀Y. id Y ↦ id Y ⟫)
           ⟪ ↓Y , ∀Z. id Z ↦ id Z ⟫)
        ⟨ seal Z ↦ unseal Z ⟩)
      ⟪ ↥X , ∀Y. id ℕ ↦ (id Y ↦ id Y) ⟫)          -- VALUE

The argument was born under `↓X` and before `ΛY`.  It lands under
`ΛY`, but inside `⟪ ↓Y , … ⟫`, so its color is still `{}`: it sees
neither `X` (masked by its own crossing) nor `Y` (masked by the
substitution).

**Without it:** the second recoloring of §0.  Jeremy found it by reading
exactly this trace: "On the fourth step, is there a missing −Y in the
boundary around the ΛZ?" (`DECISIONS.md`, "Frame-exact Beta",
2026-09-08).  Before the repair every other rule was frame-exact and
`Beta` alone let a moved value gain a variable.

**Cost:** a numeral crossing a `Λ` picks up an `id ℕ` layer, removed by
one `Drop` (or merged away).

### 5. Two universes: type variables are lexical, representation variables are storage

A type context is a pair `Ξ ∣ Γ`: a store `Ξ` of representation cells
(`α` abstract, or `α := R`), and a **name map** `Γ` listing the live type
variables and which `α` each one names.  An unbind deletes a *name*; it
never touches a representation.  The relation `Γ ⊢ A ~ R`, which is
renaming through `Γ` (`proof/SameRenaming.agda`), connects the two.

**Example 5a: the crossing does not rename** (§10, `Examples.agda`,
checked by `refl`; rendered, ``showTmIn 1 (Nsub [ Wsub ∶ ` 0 ]ᵐ)``).
Substituting `W = 7 ⟪ seal X ⟫` for `x` in `ΛY. x` gives

    ΛY. ((7 ⟪ seal X ⟫) ⟪ ↓Y , id X ⟫)

The image's `seal X` is *unchanged*.  In the one-universe design the same crossing
renamed it (`seal 0` became `seal 1` in de Bruijn), because a type
variable was also a storage slot and a new `Λ` slot shifted it.

**Example 5b: one representation, several names over time** (the Merge
run excerpt in `notes/notes.md`, from `S₀`; rendered):

    Ξ = [α := ℕ , β := γ , γ := ℕ]
    (((((7 ⟪ ↓Z , seal Z ⟫) ⟪ ↓X , id Z ⟫) ⟪ ↥X , ↓Y , seal Y ⟫)
        ⟪ ↥Y , unseal Y ⟫) ⟪ ↥Z , unseal Z ⟫)

`β := γ` is an **alias** cell: its stored representation is the
representation *variable* `γ`, which `Z` names.  `↥Y` gives `β` a name
in one frame, `↓Y` takes it away in another, and the cell never moves.

**Why it matters for the goal:** color becomes a first-class object.  A
position's color is literally its name map `names Δ`.  Because every move
except the allocation is representation-only, ordinary positions never
shift, and `ScopeMapPreservation` can say `names Δ₂ ≡ map ρ (names Δ₁)`.
The one-universe v7 theorem had to count a push/pop balance instead
(`DECISIONS.md` 2026-09-21, "COLOR PRESERVATION is RESTATED").

**Where:** `Ctx.agda`; `strong-rep-var/notes/PLAN.md` "Goal" (the two
roles of a type variable, split).

### 6. A representation is stored once and cited by name

A conversion never contains a representation: `seal X` carries the name
`X`, and its representation is found through the context (the lookup
square `Δ ∋ X := A`).  The store holds each representation exactly once.

**Without it (history, the biggest single refutation):** v1's combined
boundary *copied* a variable's representation into every boundary that
mentioned it.  On 2026-09-05 both progress and preservation were
machine-refuted in the same hour, and the survey found that *every*
typability loss in the corpus was a failed copy: a representation copied
into a context that could not spell it (`BoundarySurvey.md` F1–F12;
`DesignSpace.md` "The through line").  Each era-B patch (`Reversal`, the
ambient dual, unfolding, `cnc⋆`, x-licenses, `SkelEq`) was killed by a
program that made the copy impossible one more way (`bad`, `bad₂`, `P`,
`E`, `E★`, …).  The fix was to remove the copy instead of repairing it.

**Example (the soundness gate, `proof/Adversary.agda`):** at
`Ξ ∣ Γ = (α) ∣ (X ↦ α)`, where `α` is abstract,

    7 ⟪ ↓X , seal X ⟫ : X          is refused (¬⊢adv)

because `seal X` must cite a *represented* binder and `α` has no
representation.  At `X ↦ α`, `α := ∀Z.Z⇒Z`, the same term is refused
because `7 : ℕ` cannot spell `α`'s representation (`¬⊢bad`).  With one
stored copy there are not two spellings to disagree.  A candidate
example for the paper: *you cannot forge an `X` from an `ℕ` unless `X`
is bound to `ℕ`.*

### 7. The value restriction: `ΛX.N` requires `N` to be a value, and there is no `ξ-Λ`

Nothing reduces under a type binder.

**Why:** it makes every redex's context the **ambient** one.  With
`ξ-Λ`, an allocation under a `Λ` would mint a cell whose representation
mentions the `Λ`'s own abstract variable, onto a context the `Λ`'s
siblings do not share.  With the restriction, "allocate at the top and
shift everyone else" means something (`RepStoreSketch.md`, "Why
experiment 1 had to come first").  It is the prerequisite for
Decision 8.

**Cost, on examples:** 10 of the 21 closed programs of the corpus were
rejected (`DECISIONS.md` 2026-09-21).  Jeremy's recipe repairs them: add
a dummy `λ` to make the body a value, and apply it.

    (ΛZ. x) [ℕ]      becomes      ((ΛZ. λy:ℕ. x) [ℕ]) · 0

§5a shows the other side of the cost: the program *stops* at a value
`ΛY. …` that System F would also stop at, instead of reducing under the
binder.

### 8. A global store, with each step reporting its allocation

The store `Ξ` is ambient.  `ν` allocates `α := R` on it, a step returns
the change it made (`δ = none | new R`), and the congruences shift the
redex's *siblings* by that one allocation.  A boundary changes names
only: `reps Δᵢ ≡ reps Δ ≡ reps Δᶜ`.

**Without it (strong-rep-var):** each boundary carried its own block of
representation bindings, pushed onto the context on the way *into* that
boundary.  A representation variable was then an index relative to the
enclosing boundaries, and every rule that moved a subterm across a
boundary had to re-index it (`renᴹ²`, `underRepBinds`, `SameTyExt`,
`RepWeakenTyping`).

**Example:** in the §1a trace the store `Ξ = [α := ℕ]` sits *outside* the
term, and `Peel` moves `7` into `⟪ ↓X , seal X ⟫` verbatim.  Before the
store, that crossing needed the bind-block weakening `RepWeakenTyping`.

**Not the rejected "global Σ-store" (D33→D34):** that stored the whole
context and lost lexical unbinding.  This one stores only the
representations, and unbinding stays lexical in `Γ`: `Ξ` says *what* a
representation is, and `Γ` says *whether* this position may name it.

### 9. `ν` replaces type application; the compiler writes the reveal

The run-time language has no `L [A]`.  Plain System F is a separate
source language, and `compile` translates `L [A]` (with `L : ∀X.C`) to
`ν X:=A · ⟦L⟧ ⟨ revealₓ(C) ⟩`.

**Why:** before `ν`, `TyBeta` minted the conversion `reveal X B` at run
time, which needed the annotation `B` on `L [B, A]`.  Its partner
`TyPeelR-Λ`, for a `∀`-value already under a boundary, had to **fuse**
the crossed conversion with the reveal (`instReveal`).  With the
conversion written at compile time, `Nu-⟪Λ⟫` can *stack* the crossed
conversion under `ν`'s own and leave the fusion to `Merge`.  Every
reveal in a run is one the compiler wrote.

**Example:** §1b, `((ΛX. λf:(∀Y. Y⇒𝔹). f[X]) [𝔹] · (ΛZ. λz:Z. true)) ·
false`: two `ν`s, both written by the compiler (`NuSketch.md` Rule 2).
§3 shows `Nu-⟪Λ⟫` with two store cells.

**Side benefit:** a clean compiler-correctness story.  `compile-⊢`,
`compile-closed` and `compile-safe` hold, and `SourceExamples.agda`
checks by `refl` that the twenty source programs compile to the corpus.
**Example for the paper:** `compile-⊢` needs every term-context type to be
well-formed.  At `Γₜ = x : ∀Y.Z` with `Z` out of scope, `x [ℕ]` has a
source typing but its `ν` has none.

### 10. One boundary per value, and `Merge` composes conversions

A value carries at most one boundary.  A boundary directly over a
value's boundary is a redex of `Merge`, which concatenates the two
scopes and **composes** the two conversions (`Δ ⊢ c₁ ⨟ c₂`).

**Without it:** boundaries piled up ("towers, not merges", the v2 law).
Special rules handled particular pairs (`CancelR` for `seal X` under
`unseal X`, `IdPush` for `id X` under `unseal X`), and `Nu-⟪⟫` pushed a
`ν` inward past towers.  The stack census over the 19 compiled runs
found up to **11** stacked pairs in one state (run V), and `CancelR` plus
`IdPush` made up 22 of V's 49 steps (`MergeSketch.md`).

**After it:** at most two stacked pairs in any state, V drops from 49
steps to 19, `CancelR`, `IdPush` and `Nu-⟪⟫` are deleted, and the rule
count falls to ten.

**Example:** the Merge excerpt in Decision 5b.  Its five steps each show
one clause of composition: absorbing an identity, *chaining* two seals
(which exists only because of the alias cell `β := γ`), cancelling the
last seal of a chain, `seal Z ⨟ unseal Z = id ℕ` read off the store, and
`Drop`.

**Why this is not v1's merge coming back:** v1's `⊕` merged by
substituting representations into representations, which is the copying
disease.  `Merge` composes *name-carrying* conversions at the merged
frame, and reads a representation only where `seal Z` meets `unseal Z`,
by lookup (`repOf`).

### 11. Conversions are tight normal forms, in three sorts

    g ::= id A | c ↦ d | ∀X.c                 middle
    t ::= g | seal X | t ; seal X             tail   (left-associated seal chain)
    c ::= t | unseal X | unseal X ; c         conversion (right-associated unseal chain)

These come with `NoCancel` (no `unseal X` directly before a bare
`seal X`) and non-identity chains only.

**Why:** composition must return *the* result, so that reduction stays
deterministic (`det`), and the value classification must be syntactic.
Inert tails are values and the one active tail, `id` at a base type, is
removed by `Drop`.  Without `NoCancel`, `unseal X ; seal X` would be a
second spelling of an identity at `X`.

**Example:** step 3 of the Merge excerpt, `(seal Z ; seal Y) ⨟ unseal Y =
seal Z`, which is only well defined because chains associate as above.

### 12. Hygiene: one live name per representation variable, and `WfCtx`

A well-formed context has no representation variable with two live
names (`Unique (names Δ)`).  Preservation takes `WfCtx Δ`.

**Example (the counterexample to premise-free preservation,
`notes/notes.md` "Metatheory"):** at `Ξ = (α := ℕ)`,
`Γ = (X ↦ α, Y ↦ α)`, the redex `(λx:ℕ. ΛZ. λy:ℕ. x) · 0` types (it
mentions neither `X` nor `Y`), but its frame-exact contractum
`ΛZ. λy:ℕ. (0 ⟪ ↓Z , id ℕ ⟫)` mints a boundary whose well-formedness
demands uniqueness.  With names this is ordinary alpha-hygiene.  With
duplicates, `X` and `Y` would both spell `α`, and `≈` would not
determine a spelling (`same-target-unique` needs `Unique`).

---

## Examples still to find or render

* A **single running example** that exercises Decisions 1–5 at once.
  §5a is the candidate (it *is* the pre-boundary counterexample), but its
  trace is long.  Check whether a shorter program shows mask-not-drop and
  frame-exact `Beta` together.
* A **color-preservation picture**: the §1a and §5a traces colored by
  scope map (standing preference: colored trace artifacts for scope and
  boundary material).  `notes/ColorPreservationProbe.agda` has a checked
  three-step run to start from.
* For each **"without"** claim, the same example run under the retired
  rule, from `strong/`, `strong-rep-var/` or `strong-rep-store/` (all
  still build), so that each decision is shown on one example with and
  without it.
* A **parametricity example** for Decision 6 that a reader recognises,
  e.g. a `∀X. X ⇒ X` that tries to return `7`.  The calculus refuses the
  boundary, not the program, so the example has to be built by hand
  (§9 of `Examples.agda` builds boundaries at non-empty ambients).

## Open questions for the draft

* **Ordering.** Is the list ranked by *explanatory power* (as here) or
  by *narrative order* (the order a reader needs them, which would put
  7–8 before 9–10)?
* **Scope of history.** How much of the refuted-designs history
  (pre-boundary, v1 copies, towers) belongs in the paper, versus a
  one-line "we tried X; it fails on example E"?
* **Decisions 7 and 8.** Are the value restriction and the global store
  design *decisions*, or engineering that makes the metatheory
  tractable?  They are motivated by the mechanization more than by the
  goal.
