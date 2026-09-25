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

### Where strong-rep-nu sits in the literature

Abbreviations used below (full list at the end):
**STA** = Grossman, Morrisett & Zdancewic, *Syntactic Type Abstraction*
(TOPLAS 2000); **Principals** = its ICFP'99 precursor; **BfA** = Ahmed,
Findler, Siek & Wadler, *Blame for All* (POPL 2011); **λB** = Ahmed,
Jamner, Siek & Wadler, *Theorems for Free for Free* (ICFP 2017);
**F_C** = Igarashi, Sekiyama & Igarashi, *On Polymorphic Gradual
Typing* (ICFP 2017), the blame calculus of System F_G; **GSF** =
Labrada, Toro & Tanter, *Gradual System F* (JACM 2022); **λC∀mp /
λS∀mp** = Igarashi, Ozaki, Sekiyama & Tanabe, *Space-Efficient
Polymorphic Gradual Typing, Mostly Parametric* (PLDI 2024); **λN** =
Rossberg, *Generativity and Dynamic Opacity for Abstract Types* (PPDP
2003); **PolyGν** = New, Jamner & Ahmed, *Graduality and Parametricity:
Together Again for the First Time* (POPL 2020); **New's thesis** = Max
S. New, *A Semantic Foundation for Sound Gradual Typing* (PhD thesis,
Northeastern, 2020), whose Chapter 10 is the revised PolyGν and its cast
calculus PolyCν.

Everything below was checked against the text of the paper named,
except where a row says *(from memory)*.

**Type application, calculus by calculus:**

| calculus | type application | where the instantiation lives | is `X` replaced in the body? |
|---|---|---|---|
| System F | `(ΛX.M)[A] → M[X:=A]` | nowhere | yes, by `A` |
| STA §5.2 | `[∀1]`: `⟨{Δ}, (Λα.eᵢ)[τ]⟩ → ⟨{Δ} ⊎ᵢ {α=τ}, {τ/α}ᵢ eᵢ⟩` | global knowledge, per agent | yes, but only in `i`-colored subterms |
| λN | ordinary substitution; `Nγ≈τ.e` generates names separately | local binder, floats outward (scope extrusion) | yes |
| BfA | `(TYBETA)`: `(ΛX.v)A → νX:=A. v` | local `ν` binder, immobile | **no**, but `NUWRAP` substitutes `A` into `λ` annotations as `ν` moves inward |
| λB | `Σ ▷ (ΛX.v)[B] → Σ,α:=B ▷ (v[α/X] : A[α/X] =+α⇒ A[B/X])` | global store `Σ` | yes, by a fresh name `α` |
| F_C | `Σ ▷ (ΛX.w)A → Σ, X≔A ▷ w` | global store, keyed by `X` itself | no (`X` becomes a global name) |
| GSF | `Σ ⊳ (ΛX.t)[T] → Σ,α:=T ⊳ t[α/X]`, plus outer evidence | global store | yes, by `α` |
| λC∀mp | `R_Tybeta_C`: `…(M⟨c⟩)[X:=α]⟨coerce⁺_α(Aₙ[X:=α])⟩`; at `★`, substitutes `★` | global store | yes, by `α` (or `★`) |
| PolyGν | `M{X ≅ A}`: brings `X ≅ A` into the *context*, with explicit `seal_X`/`unseal_X` terms | lexical, exported "inside-out" to the continuation | no (in the source) |
| PolyCν (New's thesis, Fig. 10.11) | `let x = M{X≅B}; N`, ANF: `X ≅ B` is bound in the continuation `N`; at run time `Σ, σ:A`, and `σ` is substituted for the bound variables | lexical in the source, global store `Σ` at run time | yes, by a fresh case `σ` |
| **strong-rep-nu** | `Nu-Λ`: `νX:=A · (ΛX.V) ⟨c⟩ → V ⟪ ↥X , c ⟫ ∣ new α:=R` | global store for `α := R`; `X ↦ α` in the lexical name map | **no** |

**The framing this suggests for the paper.**
- **What everyone shares.** Since BfA, every sealing calculus agrees
  that type application must not write the representation into the
  body.
- **Where they differ from us.** Almost all of them still *rename* the
  body, to a global type name `α`. That changes its color: the body was
  read with `X` in scope and is now read with a store name it never
  bound.
- **The two exceptions.** BfA's local `ν` and PolyGν's lexical
  `X ≅ A` keep `X`. BfA pays with `NUWRAP`'s annotation substitution and
  reduction under `Λ`; PolyGν pays with programmer-written seals.
- **Convergence.** On three axes strong-rep-nu *moved toward* this
  literature during its own development:
  - the global store (Decision 8: λB, F_C, GSF, λC∀mp);
  - the value restriction (Decision 7: λB §2.4);
  - one boundary per value with merging (Decision 10: STA `[8]`, λS∀mp).
- **What is left.** The decisions with no counterpart in any of these
  papers are 3, 4 and 5 (mask-not-drop scopes, frame-exact `Beta`, and
  the two universes). These are exactly the decisions color
  preservation forces. That is a clean story: *strong-rep-nu is the
  λB/STA design, minus the renaming.*

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

**Prior work.**
- **BfA is the origin of this decision.** Its `(TYBETA)` is
  `(ΛX.v)A → νX:=A. v`, and its erasure `(νX:=A.t)° = t°[X:=A]` (BfA
  Prop. 1) says outright that `ν` is a *delayed* type substitution.
  Strong-rep-nu's boundary is BfA's `ν` made explicit:
  - it carries a conversion, where BfA's static casts are the implicit,
    non-syntax-directed typing rules `(REVEAL)`/`(CONCEAL)`;
  - it never moves outward.

  BfA's own binders are also immobile ("our type bindings are
  immobile, that is, there is no scope extrusion", §1). The contrast is
  with λN, whose `N`-binders float outward.
- **Everyone since BfA renames.** λB, GSF, λC∀mp and the λB-style rules
  PolyG reviews all replace `X` by a fresh `α`. On §1a, λB gives
  `Σ,α:=ℕ ▷ ((λx:α. x) : α⇒α =+α⇒ ℕ⇒ℕ) 7`. The identity function now
  reads `α`, a name from the store, where it used to read its own
  binder `X`. Worth showing side by side with the strong-rep-nu trace
  above.
- **STA avoids the problem by coloring.** `[∀1]` substitutes `{τ/α}ᵢ`
  only into `i`-colored subterms, so a `j`-colored interior keeps the
  abstract `α` (STA p.1072). But abstraction is then only as strong as
  the coloring. Under the one-color translation, "type application
  still substitutes a type for a type variable" (p.1074). Strong-rep-nu
  installs a boundary at every instantiation, with no coloring needed.
- **Color is STA's word.** STA's agents are "principals"/"colors"
  (p.1039, fn. 1). The design law, "the color of a non-boundary term
  never changes", can be read as STA's colored substitution taken to
  its limit, where no subterm is ever substituted into.

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

**Prior work.**
- **The word "conversion" is λB's.** λB's conversions `=+α⇒` / `=−α⇒`
  are what BfA called static casts. λC∀mp calls them concealment `α⁻`
  and revelation `α⁺`, and says they "correspond to static casts in
  [BfA], conversions in [λB], and sealing/unsealing operations in [New
  et al. 2020]" (λC∀mp §3). λN's coercions `{e}⁺_γ` / `{e}⁻_γ` are the
  earliest version seen here.
- **`reveal`/`mkId` are type-directed coercion generation.**
  Strong-rep-nu's `revealₓ(C)` and `mkId` are λN's Fig. 3
  `{e : τ′}^±_{γ≈τ}` ("coercion polarity is inverted for function
  arguments"), λB's conversion inserted by type application, and
  λC∀mp's `coerce^±_α`.
- **Where strong-rep-nu differs: names, not store names.** Its `seal X`
  names a *lexical type variable*, and the representation is found
  through the name map. Every calculus above seals with a *store name*
  `α`.
- **`Peel` is the standard wrapped-function rule.** It is λB's rule (9),
  `(v : A→B ⇒ A′→B′) v′ → v (v′ : A′ ⇒ A) : B ⇒ B′`, which λB takes from
  Siek & Wadler's space-efficient function casts (λB §2.4). It is also
  λC∀mp's `R_Wrap_C`. What is new is the frame: the argument crosses
  under `dual Θ`, where STA reverses the agent list, `rev(ℓ)` in its
  `[9]`.
- **Polarity.** λB negates the label on the domain, and λN inverts
  coercion polarity. Strong-rep-nu dropped its polarity index because
  the frame records direction per variable. That is a real difference
  worth one sentence.

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

**Prior work.**
- **STA also needs order.** Its three-agent counterexample (p.1048)
  shows that nested embeddings must be flattened to an *ordered* agent
  list `ℓ`, since a set loses "that agent `i` must have exported the
  integer at type `t` before `j` could export it at type `s`".
  Strong-rep-nu's change list `Θ` is the same kind of object, and
  `Merge`'s `Θ₂ ++ Θ₁` is STA's list append in `[8]`.
- **But STA has no notion of out of scope.** Its `Θ` is used only for
  freshness in `[∀intro]` ("Θ is unused by the new version of the old
  rules", p.1072). Abstraction there is by *opacity* (`t ∉ Dom(δᵢ)`)
  only; strong-rep-nu has opacity *and* unnameability.
  `notes/TypeAbstractionComparison.md` §2 and §11 have the details;
  that note predates the store and `Merge`.
- **Mask-not-drop has no counterpart that I found.** The global-store
  calculi (λB, F_C, GSF, λC∀mp) have no lexical scope to drop from.
  BfA's local bindings are the only other design where a binding sits at
  a position.

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

**Prior work.**
- **No counterpart that I found.** Every calculus above uses ordinary
  capture-avoiding substitution for term `β`.
- **Closest analogue: STA's brackets travel with the value.** A
  substituted embedding `⌈v̂ⱼ⌉` keeps its bracket, and so its color.
  STA never checks scope, however: `[∀2]` moves an embedding under a
  `Λ` "discharged by α-freshness alone" (`TypeAbstractionComparison.md`
  §4).
- **A second analogue: BfA's `NUWRAP`.** It moves a `ν` under a `λ` and
  *substitutes* into that `λ`'s annotation (`λy:B[X:=A]`). That is the
  opposite repair, recoloring the moved binder instead of wrapping the
  moved value.
- **Suggested claim for the paper:** frame-exact substitution is new.

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

**Prior work.**
- **The two roles are already separated in λB.** λC∀mp notes that "type
  names and variables are distinguished in λC∀mp (following Ahmed et al.
  [2017])": a type variable `X` is lexical and a type name `α` lives in
  `Σ`.
- **The difference is how they are connected.** Those calculi connect
  the two universes by *substituting* `α` for `X`. Strong-rep-nu keeps
  both and connects them with a *name map* `X ↦ α`, which boundaries
  edit with `↓X` / `↥X`. As far as I found, that map is new.
- **F_C is the one-universe design with a global store.** It keys the
  store by `X` itself (`Σ, X≔A`, with `X` definitionally equal to `A`),
  which is the one-universe design strong-rep-var replaced.
- **GSF has alias chains too.** An evidence type name `αβ^Int` records
  "that α is bound to β, which is itself bound to Int" (GSF §7.2). These
  are the alias cells of Example 5b (`β := γ`), and in both calculi they
  are what makes chains of seals possible.
- **Terminology clash *(from memory)*.** "Representation" also names
  the run-time type representations of intensional polymorphism
  (Crary, Weirich & Morrisett, ICFP 1998). Strong-rep-nu's
  representations are types in the store, never terms. Say so once.

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

**Prior work.**
- **The soundness gate is λN's scoping rule.** λN types `{e}⁺_γ` only
  when `γ≈τ ∈ Γ`: "coercions are only available within the lexical
  scope of the corresponding type generator, thus the transition across
  abstraction boundaries can only be triggered from within the
  abstraction" (§3.2). `conv-seal`'s `Δ ∋ X := A` is the same rule,
  resolved through the name map.
- **Explicit conversions vs. equality modulo the store.** F_C and GSF
  make a store name *equal* to its binding (F_C: "X is definitionally
  equal to A"; GSF: "a type name α is considered equal to its associated
  type in the store"), and BfA's `(REVEAL)`/`(CONCEAL)` are
  non-syntax-directed. Strong-rep-nu, like λB and λC∀mp, has no such
  equality: every crossing is an explicit conversion. That is what
  keeps conversions syntactic normal forms (Decision 11) and reduction
  deterministic.
- **STA's per-agent knowledge `δᵢ` is a set of copies.** Def. 3.1's
  *compatibility* ("if `t ∈ Dom(δᵢ) ∩ Dom(δⱼ)` then `δᵢ(t) = δⱼ(t)`") is
  precisely the "copies agree" invariant whose failure killed v1. Worth
  a sentence: STA maintains it by construction in a monotone registry,
  while v1 had to maintain it across boundaries that move.

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

**Prior work.**
- **λB made exactly this move, for exactly this reason.** λB §2.4 calls
  BfA "topsy turvy" because it has to reduce under `Λ`: BfA wanted the
  value restriction (§5.2) but could not have it, because `(NUTYWRAP)`
  and `(GENERALIZE)` push non-values under a `Λ`. λB's fix is to make
  casts to `∀` values and apply them at type application. "With the
  removal of evaluation under type abstractions, we are free to
  immediately place generated names in a global store, forgoing the use
  of ν binders."
- **So Decisions 7 → 8 are λB's argument, rediscovered.** Cite it.
- **Others with value-restricted `Λ`.** F_C's values are `ΛX::G. w`.
  STA's `Λα. eᵢ` is a primval with no reduction under it.

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

**Prior work.**
- **The global store is the standard choice.** λB, F_C (which follows
  λB), GSF, λC∀mp, PolyG and Neis, Dreyer & Rossberg's `new`
  *(from memory)* all use a global store `Σ`.
- **BfA explains why a global store needs Decision 7.** Its §5.5 example
  `let f = ΛX.(ΛY.s)X in (f I, f B)` shows that under reduction under
  `Λ`, "`Y` should really get two different bindings", which a global
  list cannot give.
- **λN considered a store and rejected it.** It chose π-calculus-style
  scope extrusion: "we also considered … an explicit type store or heap
  as in the λν-calculus, but that choice would produce a more
  complicated system" (fn. 4).
- **STA's `{Δ}` is a monotone global knowledge base.**
- **The difference is what the store holds.** Everyone else stores
  *names*. Strong-rep-nu stores only *representations* and keeps names
  lexical. That resolves the D33 fork (`DesignSpace.md`, "a global
  Σ-store, NOT taken — lexical scope is needed for unbind blocking") by
  splitting it in two.
- **De Bruijn bookkeeping.** Reporting the allocation `δ` from each step
  and shifting siblings is how a de Bruijn development spells "`α`
  fresh". It is not a design point for the paper.

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

**Prior work.**
- **New's thesis is where the ν form comes from.** Chapter 10 states
  the problem this decision solves. With System F's syntax, an
  instantiation actually uses "a fresh type α that is merely isomorphic
  to B, not the same as it", and "this results in the need for
  type-directed sealing to mask the difference" (§10.1).
  - PolyGν's answer is an ANF-restricted instantiation,
    `let x = M{X≅B}; N`. There, "the continuation N now has an explicit
    isomorphism in scope, sealX : B → X and unsealX : X → B, allows it
    to manually seal and unseal inputs and outputs of x as necessary".
    The POPL paper uses an "inside-out" binding instead.
  - `ν X:=A · L ⟨c⟩` is that form with the continuation cut down to a
    *conversion*. `X` is bound in `c` and nowhere else, and the sealing
    and unsealing are the leaves `seal X` / `unseal X` of `c`, where
    PolyGν has terms.
  - `compile` then does, once and at compile time, the type-directed
    sealing that λB performs at run time and PolyGν leaves to the
    programmer: `⟦L[A]⟧ = ν X:=A · ⟦L⟧ ⟨revealₓ(C)⟩`.
  - Suggested one-line claim: *strong-rep-nu's ν is PolyGν's
    instantiation, with the continuation specialized to a conversion
    and the sealing written by the compiler.*
- **PolyCν's `∀ν` casts accumulate.** They build a stack of casts on the
  `Λν` (`Λν{X.([B⊑↕], M)}`), applied at instantiation. That is the same
  "casts to ∀ are values, eliminated at type application" discipline as
  λB and `Nu-⟪Λ⟫`.
- **Where PolyCν differs.** Its instantiation still substitutes a fresh
  case `σ` for the bound variables (`M[σ/X]`, `N[σ/Y]`), so it recolors,
  like λB.
- **The syntax.** `ν X:=A · L ⟨c⟩` takes its shape from the repo's
  GTPLC (`ν A · L •⟨ c ⟩`). BfA's `νX:=A. t` and λN's `Nγ≈τ. e` are the
  binder ancestors.
- **Who writes the reveal.** In λB, λC∀mp and λN the reveal conversion
  is generated by the *type-application rule*, at run time (`=+α⇒`,
  `coerce⁺_α`, `{e:τ}^±`). In PolyGν the *programmer* writes `seal_X` /
  `unseal_X`, and `M{X ≅ A}` exports `X ≅ A` to the continuation.
  PolyG's argument is that type-directed sealing is the source of
  graduality failures.
- **Strong-rep-nu sits between.** The conversion is explicit and
  arbitrary (`⊢ν` accepts any `c` whose types line up, as in PolyGν),
  but it is written by the *compiler*, and `X` is bound in `c` only, not
  exported.
- **`Nu-⟪Λ⟫` has a direct precedent.** λB's third type-application rule
  is `Σ ▷ (v : ∀X.A =ϕ⇒ ∀X.A′)[B] → Σ,α:=B ▷ ((v[α] : A[α/X] =ϕ⇒
  A′[α/X]) : A′[α/X] =+α⇒ A′[B/X])`. It moves the inner conversion
  inside and stacks the reveal outside, which is `Nu-⟪Λ⟫`'s stacked
  contractum. λC∀mp's `R_Tybeta_C` fuses a whole sequence of `∀`
  coercions instead.

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

**Prior work.**
- **The invariant is the space-efficiency one.** λS∀mp states it
  exactly: "a value is wrapped by at most one coercion and the hole in
  a frame never appears under coercion applications" (§4.2), after
  Herman, Tomb & Flanagan and Siek, Thiemann & Wadler's normal-form
  coercions.
- **The cancellation rules are old.** `Merge`'s `seal Z ⨟ unseal Z`
  clause is λN's `{{e}⁺_γ}⁻_γ → e`, λB's "two mirror image conversions
  … reduce to the identity", λC∀mp's `R_Remove_C`
  (`V⟨α⁻⟩⟨α⁺⟩ → V`), and GSF's consistent-transitivity rule `(unsl)`.
- **Composition-based merging is GSF's style.** GSF combines evidence
  at every step, and it is the closest relative in *how* `Merge` works.
- **STA's `[8]` merges too**, with an ordered list, but keeps one type
  annotation instead of composing.
- **An open question to raise.** Ozaki, Sekiyama & Igarashi (Scheme
  2021, cited by λC∀mp) show that polymorphic coercion calculi can
  build unbounded sequences `⟨α₁!⟩⋯⟨αₙ!⟩` that no composition shrinks.
  Strong-rep-nu's analogue is the seal chain `t ; seal X ; seal Y` built
  through alias cells. Is the chain length bounded, for example by the
  alias depth of the store? Without `★` it plausibly is, but it is
  unproved.

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

**Prior work.**
- **The three sorts line up with λS∀mp's schema.** λS∀mp's coercions
  follow `(G₁?p ;)? (⊥p | (g (; G₂!)?))`: an optional projection, a
  ground middle, and an optional injection. Strong-rep-nu's
  `c ::= unseal X ; c`, `g`, `t ::= t ; seal X` have the same layout,
  with **unseals in the projection position and seals in the injection
  position**. Two differences are worth stating:
  - chains are possible here (several seals in a row, through aliases),
    where `★` admits only one tag;
  - λS∀mp *drops* concealment and revelation from its normal forms
    ("as we detail later, concealment and revelation make it
    complicated to discuss space efficiency formally; thus, they are
    implicit in λS∀mp", §4). Strong-rep-nu keeps seals and unseals
    explicit in the normal form, which is a small contribution.
- **Lineage in the repo.** The three sorts come from GTLC's
  Siek–Thiemann–Wadler normal forms, with GTPLC's chain association
  (`MergeSketch.md`).

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

**Prior work.** Distinct names are the standard side condition
everywhere: BfA's implicit `X ∉ Γ`, GSF's "a type name store is
well-formed if all type names are distinct", STA's global α-conversion.
Strong-rep-nu's twist is that uniqueness is about *representation
variables* (at most one live name each), which only exists because of
Decision 5.

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

## Related work beyond the named papers

Found by the literature search, or cited by the papers above. Marked
**(read)** where I checked the text this session, and **(not read)**
otherwise.

**Directly relevant; should be cited:**
- *Theorems for Free for Free* (Ahmed, Jamner, Siek & Wadler, ICFP 2017)
  **(read)**. λB is the source of the word "conversion", of the value
  restriction plus global store argument (Decisions 7–8), and of the
  `Nu-⟪Λ⟫` shape (Decision 9). Arguably closer to strong-rep-nu than BfA.
- *Generativity and Dynamic Opacity for Abstract Types* (Rossberg, PPDP
  2003) **(read)**: λN's coercions, lexical-scope gate and
  type-directed coercion generation (Decisions 2, 6).
  - It also has a ready-made **color-preservation counterexample**:
    `P ≡ (Λα. λx:α. {x : α}⁻_{γ≈τ}) γ` has type `γ → γ`, but its
    β-contractum `λx:γ. {x : γ}⁻_{γ≈τ}` has type `γ → τ` (§3.2).
  - Substituting into a coercion's annotation changes its meaning, which
    is Decision 1 in one line. λN repairs it with "unsealed types";
    strong-rep-nu never substitutes into a conversion.
- *Graduality and Parametricity: Together Again for the First Time*
  (New, Jamner & Ahmed, POPL 2020) **(read, in part)**: explicit
  `seal_X` / `unseal_X`, and the inside-out `X ≅ A` binding (Decision 9).
- *A Semantic Foundation for Sound Gradual Typing* (Max S. New, PhD
  thesis, Northeastern 2020) **(read: Chapter 10, §§10.1–10.4)**. It
  motivates the ANF instantiation `let x = M{X≅B}; N` from which the ν
  form descends, and gives PolyCν's operational semantics (Fig. 10.11).
  This is the right citation for *why* type application is compiled to
  `ν` (Decision 9). The rest of the thesis (embedding–projection pairs,
  graduality) is background for the gradual follow-ups, not this paper.
  PDF: `maxsnew.com/docs/dissertation.pdf`.
- *Principals in Programming Languages* (Zdancewic, Grossman &
  Morrisett, ICFP 1999) **(read, previously; `notes/Zdancewic-embeddings.md`)**:
  colored embeddings, the origin of "color".
- *Parametric Polymorphism through Run-Time Sealing, or, Theorems for
  Low, Low Prices!* (Matthews & Ahmed, ESOP 2008) **(not read)**.
  Multi-language *boundaries* between System F and an untyped language,
  with seals. Boundary terms are its central construct, so it is likely
  the closest precedent for `M ⟪ Θ , c ⟫` as a *term*. PDF:
  `ccs.neu.edu/home/amal/papers/parpolyseal.pdf`.
- *Operational Semantics for Multi-Language Programs* (Matthews &
  Findler, POPL 2007) **(not read)**: the boundary construct itself.
- *Non-Parametric Parametricity* (Neis, Dreyer & Rossberg, ICFP 2009 /
  JFP 2011) **(not read)**: `new X ≈ A in e` with a global store σ, the
  store BfA §5.5 contrasts itself with.
- *Is Space-Efficient Polymorphic Gradual Typing Possible?* (Ozaki,
  Sekiyama & Igarashi, Scheme 2021) **(not read; cited by λC∀mp)**: the
  impossibility result behind the seal-chain question in Decision 11.
- *Blame and Coercion: Together Again for the First Time* (Siek,
  Thiemann & Wadler, PLDI 2015) and *Space-Efficient Gradual Typing*
  (Herman, Tomb & Flanagan, TFP 2007 / HOSC 2010) **(not read)**: normal
  forms and "one coercion per value" (Decisions 10–11).
- *Parameterized Cast Calculi and Reusable Meta-theory for Gradually
  Typed Lambda Calculi* (Siek & Chen, JFP 2021) **(read, previously;
  `notes/ParameterizedCastCalculi.md`)**.

**Gradual-parametricity papers you may want in a survey paragraph (not read):**
- *Gradual Parametricity, Revisited* (Toro, Labrada & Tanter, POPL 2019);
- *Plausible Sealing for Gradual Parametricity* (Labrada, Toro, Tanter &
  Devriese, OOPSLA 2022);
- *Consistent Subtyping for All* (Xie, Bi & Oliveira, ESOP 2018): the
  "separate gradual typing from polymorphism" policy that λC∀mp and
  PolyG follow;
- *Parametricity versus the Universal Type* (Devriese, Patrignani &
  Piessens, POPL 2018).

**Background on sealing (not read):**
- Morris, *Protection in Programming Languages* (CACM 1973);
- Pierce & Sumii, *Relating Cryptography and Polymorphism* (2000);
- Sumii & Pierce, *A Bisimulation for Dynamic Sealing* (POPL 2004);
- Guha, Matthews, Findler & Krishnamurthi, *Relationally-Parametric
  Polymorphic Contracts* (DLS 2007);
- Abadi, Cardelli, Pierce & Rémy, *Dynamic Typing in Polymorphic
  Languages* (JFP 1995).

**Adjacent areas the paper should at least name (from memory):**
- **Explicit substitutions** (Abadi, Cardelli, Curien & Lévy, λσ, 1991).
  A boundary is a type substitution that is never pushed through, and
  BfA's erasure `(νX:=A.t)° = t°[X:=A]` makes the analogy exact.
  - Consequence: strong-rep-nu should probably prove the corresponding
    **erasure theorem** into System F. BfA (Prop. 1) and STA (Lemma 5.8,
    Thm 5.10) both have one; strong-rep-nu does not.
- **Residual theory** (Lévy's labelled λ-calculus; Huet & Lévy). The
  `Residuals` relation behind `ScopeMapPreservation` is a residual
  tracing, and naming it as such would help readers.
- **Name generation** (Odersky's λν, POPL 1994; Pitts & Stark's
  ν-calculus, 1993), for the `ν` binder and fresh allocation.
- **Intensional polymorphism** (Harper & Morrisett, POPL 1995; Crary,
  Weirich & Morrisett, ICFP 1998), for the terminology clash on
  "representation".

**Not obtained / not needed:** nothing on your list was missing. The two
papers that were not in the repo (*On Polymorphic Gradual Typing* and
*Space-Efficient …*) and *Gradual System F* were downloaded to the
scratchpad from the authors' pages and arXiv.

## Open questions for the draft

* **Which relative leads the related-work section?** λB (*Theorems for
  Free for Free*) now looks at least as close as STA: conversions,
  value restriction plus store, and the `Nu-⟪Λ⟫` shape. STA is closest
  on *color* and ordered merging. One option is to lead with STA for the
  goal and λB for the mechanism.
* **An erasure theorem.** Should strong-rep-nu prove one before the
  paper, since BfA and STA both have one?

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
