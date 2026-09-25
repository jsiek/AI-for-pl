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

    (λf:ℕ⇒ℕ. ΛY. λy:ℕ. f) · (λz:ℕ. z)
      → ΛY. λy:ℕ. (λz:ℕ. z)           λz:ℕ.z was colored {}; now colored {Y}

The argument `λz:ℕ. z` was authored where `Y` did not exist and now
sits under `ΛY`, so it is read with `Y` in scope.  (Constants have no
color worth tracking, so the example uses the smallest term that does:
a function, whose annotation is read in a scope.)  Nothing goes wrong
for this argument, whose annotation `ℕ` mentions no variable, but for
a polymorphic argument it is the same failure one level up
(Decision 5).

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
| Matthews & Ahmed (ESOP'08) | ordinary substitution in the ML term, but a *boundary* annotation receives the sealed instance `⟨α; τ⟩` instead of `τ` (§3, `sl(η, κ)`) | on boundary annotations only | yes in terms; boundaries remember `α` |
| Neis, Dreyer & Rossberg (JFP'11) | `(RINST)`: `σ;(λα.e)τ ↪ σ;e[τ/α]`; names come separately from `new α≈τ in e`, `(RNEW)`: `σ, α≈τ` | global type store `σ` | yes |
| BfA | `(TYBETA)`: `(ΛX.v)A → νX:=A. v` | local `ν` binder, immobile | **no**, but `NUWRAP` substitutes `A` into `λ` annotations as `ν` moves inward |
| λB | `Σ ▷ (ΛX.v)[B] → Σ,α:=B ▷ (v[α/X] : A[α/X] =+α⇒ A[B/X])` | global store `Σ` | yes, by a fresh name `α` |
| F_C | `Σ ▷ (ΛX.w)A → Σ, X≔A ▷ w` | global store, keyed by `X` itself | no (`X` becomes a global name) |
| GSF (and its conference version, Toro et al. POPL'19) | `Σ ⊳ (ΛX.t)[T] → Σ,α:=T ⊳ t[α/X]`, plus outer evidence | global store | yes, by `α` |
| Funky (Labrada et al. OOPSLA'22) | `(RappG)`: `(ε(ΛX.t) :: ∀X.G)[F] → (schm(ε) t :: G)[F/X]`, instantiation only at base and variable types | *no store*: each unknown type carries an instantiation environment `?^{X:F}` | yes, by `F` |
| λC∀mp | `R_Tybeta_C`: `…(M⟨c⟩)[X:=α]⟨coerce⁺_α(Aₙ[X:=α])⟩`; at `★`, substitutes `★` | global store | yes, by `α` (or `★`) |
| PolyGν | `M{X ≅ A}`: brings `X ≅ A` into the *context*, with explicit `seal_X`/`unseal_X` terms | lexical, exported "inside-out" to the continuation | no (in the source) |
| PolyCν (New's thesis, Fig. 10.11) | `let x = M{X≅B}; N`, ANF: `X ≅ B` is bound in the continuation `N`; at run time `Σ, σ:A`, and `σ` is substituted for the bound variables | lexical in the source, global store `Σ` at run time | yes, by a fresh case `σ` |
| **strong-rep-nu** | `TyBeta`: `νX:=A · (ΛX.V) ⟨c⟩ → V ⟪ ↥X , c ⟫ ∣ new α:=R` | global store for `α := R`; `X ↦ α` in the lexical name map | **no** |

**The framing this suggests for the paper.**

Lead: the related-work discussion is organized around two papers.
**STA** for the goal (agents as colors, colored substitution, and the
ordered history of crossings), and **λB** for the mechanism (conversions,
the value restriction plus a global store, and the `∀`-conversion rule
that `TyWrap` follows). The other calculi are placed relative to these
two.

Tone: strong-rep-nu is built on this line of work, and the draft should
say so plainly. For each decision it records what we take from whom
(**Builds on**) and what we add (**New here**). The prior calculi were
designed for parametricity, blame, graduality or space efficiency, not
for color preservation. Where they substitute a name into a body, that
is the right choice for their goals, and our difference comes from
asking for a stronger syntactic invariant, not from a flaw in theirs.

- **What we inherit.** Since BfA, the sealing calculi agree that type
  application must not write the representation into the body. They
  generate a fresh name (BfA's `ν`, λN's `N`, Neis et al.'s `new`, the
  global stores of λB, F_C, GSF and λC∀mp), and they mediate between the
  name and its representation with conversions (λN's coercions, BfA's
  static casts, λB's conversions, PolyGν's seals). Strong-rep-nu's
  boundaries, `seal`/`unseal`, crossings, cancellation, value
  restriction, global store and merging all have direct ancestors in
  these papers, cited per decision below.
- **What color preservation adds.** To keep a body's color, `X` itself
  must stay in the body. Most of these calculi replace `X` by the fresh
  name `α`, which is harmless for parametricity but changes which
  variables the body is read with. And since their store names may
  appear in types anywhere, each allocation also adds `α` to the color
  of every other subterm. BfA's `ν` and PolyGν's `X ≅ A` keep
  `X`, but there the type variable *is* the name: one sort does both
  jobs.
- **The new piece: representation variables reached through a name
  map.** Strong-rep-nu separates the two jobs, as λB already separates
  type variables from type names. It then connects them by a *lexical
  name map* `X ↦ α`, which boundaries edit with `↓X` / `↥X`, instead of
  by substitution. The name map is what lets the body keep `X`, lets one
  representation be named differently in different frames (alias cells),
  and turns color into the checkable equation of `ScopeMapPreservation`.
  - The nearest relatives are Funky's instantiation environments
    `?^{X:F}` and Matthews & Ahmed's sealed annotations `⟨α; τ⟩`, both
    of which pair a lexical label with what it denotes. Neither has a
    store variable behind a name map. I found nothing closer, but that
    is a search result, not a proof of novelty.
- **Convergence.** On three axes strong-rep-nu *moved toward* this
  literature during its own development, and gained from doing so:
  - the global store (Decision 8: λB, F_C, GSF, λC∀mp);
  - the value restriction (Decision 7: λB §2.4);
  - one boundary per value with merging (Decision 10: STA `[8]`, λS∀mp).
- **What is new.** Decisions 2, 3 and 5 have no counterpart I found, and
  they are the decisions color preservation forces. The heart of it is
  Decisions 2 and 3, which had to go together:
  - **Decision 2, the driving decision:** boundary scopes are change
    lists in which `↥X` is a *binder* for type variables and `↓X` ends a
    scope. Every type variable therefore has a lexical binder at every
    point of a run, and every rule moves or inverts binders instead of
    substituting.
  - **Decision 3, forced by Decision 2:** once boundaries bind and
    unbind type variables, a representation must outlive the name that
    denotes it (after `↓X`) and be reachable by different names in
    different frames (`↥X` naming an existing cell). So type variables
    and representations become two universes, connected by a name map.
  - **Decision 5:** frame-exact `Beta`, the same binder principle
    applied to term substitution.

  In one sentence: *strong-rep-nu takes the λB/STA design and adds
  binding boundaries and a name map, so that type application no
  longer needs to rename.*

---

## The design decisions, in narrative order

In the order a reader needs them: the boundary (1), what it binds (2–3),
how values cross it (4–5), how the store and names are kept (6–8), the
run-time language that results (9–11), and how it relates back to
System F (12).  Every entry has an
**example**, with its reduction steps shown; **what goes wrong without
the decision**, in one line of history; **what the calculus does**; and
**where to look**, followed by **Builds on** / **New here**.

### 1. Type application does not substitute; it installs a boundary

The single decision the rest serves.  `ν X:=A · (ΛX.V) ⟨ c ⟩` does not
compute `V[X:=A]`.  It allocates a store cell `α := R` for `A`'s
representation `R`, keeps `V` as it is, and wraps it in a **boundary**
`V ⟪ ↥X , c ⟫` that makes `X` a live name for `α` inside.

**Example: the baseline** (§1a, `P₀`; rendered, `showRun 0 5 P₀-⊢`):

    Ξ = []         ((ν X:=ℕ · (ΛY. λx:Y. x) ⟨ seal X ↦ unseal X ⟩) · 7)
      --[TyBeta]-->
    Ξ = [α := ℕ]   (((λx:X. x) ⟪ ↥X , seal X ↦ unseal X ⟫) · 7)
      --[Wrap]-->
    Ξ = [α := ℕ]   (((λx:X. x) · (7 ⟪ ↓X , seal X ⟫)) ⟪ ↥X , unseal X ⟫)
      --[Beta]-->
    Ξ = [α := ℕ]   ((7 ⟪ ↓X , seal X ⟫) ⟪ ↥X , unseal X ⟫)
      --[Merge]-->
    Ξ = [α := ℕ]   (7 ⟪ ↥X , ↓X , id ℕ ⟫)
      --[Id]-->
    Ξ = [α := ℕ]   7

**Against System F:** `λx:X. x` keeps its color `{X}` through the whole
run.  The identity function never sees `ℕ`: `7` enters it sealed as an
`X` and leaves it unsealed as an `ℕ`.  That is parametricity *enforced
at run time*, which is where "strong" in Strong System F comes from
(`Design.md` §1).

**Where:** `Reduction.agda` `TyBeta`; `notes/notes.md` "Reduction".

**Builds on.**
- **Blame for All introduced this decision.** Its `(TYBETA)`,
  `(ΛX.v)A → νX:=A. v`, is the first rule we know of that answers type
  application with a binding instead of a substitution. Its erasure
  `(νX:=A.t)° = t°[X:=A]` (Prop. 1) shows that `ν` is a delayed type
  substitution. Strong-rep-nu's boundary is a direct descendant of BfA's
  `ν`: it keeps BfA's choice of immobile bindings ("our type bindings
  are immobile, that is, there is no scope extrusion", §1), and makes
  BfA's implicit static casts, the typing rules `(REVEAL)`/`(CONCEAL)`,
  into an explicit conversion.
- **Matthews & Ahmed first let a boundary remember what the body
  forgets.** Type application still substitutes into their ML terms,
  but "we can no longer directly substitute types for free type
  variables on boundary annotations". A boundary annotation receives a
  sealed instance `⟨α; τ⟩`, recording that the position "was abstract
  in the original program but has been substituted with a concrete
  type" (§3). Their observation that "the production of fresh names by
  capture-avoiding substitution corresponds exactly to the production
  of fresh seals" is a good epigraph for Decision 3.
- **λB, GSF and λC∀mp refine the idea with a global store** and a
  fresh name `α`. On §1a, λB gives
  `Σ,α:=ℕ ▷ ((λx:α. x) : α⇒α =+α⇒ ℕ⇒ℕ) 7`. That is exactly right for
  parametricity, and it is the semantics strong-rep-nu's store follows
  (Decision 8). Worth showing side by side with the strong-rep-nu trace
  above.
- **STA supplies the word and the idea of color.** STA's agents are
  "principals" or "colors" (p.1039, fn. 1), and its `[∀1]` substitutes
  `{τ/α}ᵢ` only into `i`-colored subterms, so a `j`-colored interior
  keeps the abstract `α` (p.1072). The design law, "the color of a
  non-boundary term never changes", is STA's colored substitution taken
  to its limit.
- **Plausible Sealing makes the scope argument from the parametricity
  side.** "In previous calculi, a seal α can continue to exist when the
  type variable X for which it was created goes out of scope" (§1). Its
  Funky answers with lexically scoped seals. That is the closest prior
  statement of the concern behind color preservation.

**New here.** Nothing is substituted at type application, not even a
fresh name. `X` stays in the body, and the boundary holds `X ↦ α := R`.
STA gets this effect only where the coloring (or its translation) puts
an agent boundary: under its one-color translation "type application
still substitutes a type for a type variable" (p.1074). Strong-rep-nu
installs a boundary at every instantiation, so no coloring is needed.

### 2. A boundary scope is a list of changes, and an unbind masks instead of dropping

A boundary carries a **sequence** `Θ` of changes, `↓X` (unbind) and
`↥X` (bind), and its interior is **computed from the exterior at the
boundary's current position**.  An unbind deletes one name and keeps
every other one, including names bound *after* `X`.

**Why this decision is central to color preservation: `↥X` is a
binder.**  A change list is best read as a *scope transformer*. It says
how the scope inside a boundary is obtained from the scope outside it,
one change at a time (`Boundary.agda` §3, `_⊢ⁱ_⇒_`):

    ↥X   binds the type variable X, for the boundary's interior, to a
         representation variable α that has no live name
    ↓X   ends the scope of X for the interior; α stays in the store

So `↥X` is a **binder for type variables**, on the same footing as
`ΛX` and `∀X`. The difference is what it binds to: `ΛX` introduces `X`
together with a *fresh, abstract* α, while `↥X` gives an *existing*
representation variable a name. `↓X` is its inverse, a binder's scope
coming to an end at a chosen position. That makes three kinds of
type-variable binder in strong-rep-nu (`∀X` in types, `ΛX` in terms,
`↥X` in boundary scopes), plus the `X` that `ν X:=A · L ⟨c⟩` binds in
`c`.

This is what turns color into a syntactic property. Every occurrence
of a type variable, at every point in a run, has a lexical binder, and
the color of a position is computed by walking from the root to that
position through the `Λ`s and boundary scopes on the way. That walk is
the frame judgment `Δ ⊢C C ⊣ Δ′` behind `ScopeMapPreservation`.
Reduction preserves color because each rule *moves a binder* or
*inserts its inverse*, and never substitutes. Each rule below has a
frame lemma saying its new frame reads back to the old scope:

- **`TyBeta`** replaces the `ΛX` binder by a `↥X` binder. In the named
  presentation, `ν X:=A · (ΛX.V) ⟨c⟩ → V ⟪ ↥X , c ⟫`. `V` is still read
  with `X` in scope, now bound by the boundary to the new cell α := R
  (`inst-interior`, `TyBeta-interior`).
- **`Wrap`** sends the argument into the interior under `dual Θ`, the
  inverse change list, so the argument is read in exactly the scope it
  came from (`dual-interior`: `Γ ⊢ⁱ Θ ⇒ Γᵢ → Γᵢ ⊢ⁱ dual Θ ⇒ Γ`).
- **`Beta`** wraps a value it substitutes under `ΛY` in `↓Y`, the
  inverse of the binder it crossed (Decision 5; `crossΛ-interior`).
- **`TyWrap`** reads the crossed scope `Θ` one binder in, under the new
  `↥X` (`liftᴮ-interior`).
- **`Merge`** concatenates the two scopes, which reads the inner frame
  after the outer, on the same store (`merged-interior`).

Without change lists there is nothing to move and nothing to invert,
and the only way to express a new scope is to substitute.

`↥X` also buys two things the other binders cannot express:
- **Re-naming an existing representation.** `⟪ ↓X , ↥Y ⟫` hides `X` and
  names the *same* α as `Y` for the interior: a boundary that
  α-converts. The alias chains of Example 3b (`↥X , ↓Y`) are built this
  way.
- **The conversion reads both sides.** The *conversion context* performs
  every `↥` and skips every `↓` (`conv-bind`, `conv-bind-live`), so a
  conversion can mention the names of both sides of the boundary.
  That is why `seal X` / `unseal X` can relate an interior `X` to an
  exterior representation.

**Why `↓X` is needed: one program, three calculi.**  Keeping `X` bound
in the body (instead of renaming it) has a price. Anything that later
*crosses into* that body must be readable without `X`, so the calculus
needs a way to end a scope, which is `↓X`. Here is the argument
`λn:ℕ. n` of §7a, `(ΛX. λx:X. x) [ℕ⇒ℕ] · (λn:ℕ. n) · 7`. It is written
outside `ΛX`, so its color is `{}`.

1. *Strong-rep-nu* (rendered, `showRun 0 4 A₀-⊢`; the renderer calls
   the argument `λx:ℕ. x`):

       (((λx:X. x) ⟪ ↥X , seal X ↦ unseal X ⟫) · (λn:ℕ. n)) · 7
         --[Wrap]-->
       (((λx:X. x) · ((λn:ℕ. n) ⟪ ↓X , seal X ⟫)) ⟪ ↥X , unseal X ⟫) · 7
         --[Beta]-->
       (((λn:ℕ. n) ⟪ ↓X , seal X ⟫) ⟪ ↥X , unseal X ⟫) · 7

   The body keeps `X`, bound by `↥X`. The argument now sits inside `↥X`,
   under its own `↓X`, and is read with color `{}` (`dual-interior`).

2. *Blame for All*: keeps the binder, but has no way to end its scope.
   This trace is derived from BfA's rules `(TYBETA)`,
   `νX:=A. (λy:B. t) → λy:B[X:=A]. (νX:=A. t)` `(NUWRAP)` and `(BETA)`;
   the paper does not print it.

       (ΛX. λx:X. x) (ℕ→ℕ) (λn:ℕ. n)
         → (νX:=ℕ→ℕ. λx:X. x) (λn:ℕ. n)        TYBETA
         → (λx:ℕ→ℕ. νX:=ℕ→ℕ. x) (λn:ℕ. n)      NUWRAP
         → νX:=ℕ→ℕ. (λn:ℕ. n)                  BETA

   The argument lands under `νX` and is read with `X` in scope, so its
   color goes from `{}` to `{X}`. BfA has no construct for "inside `ν`,
   but not for this subterm". `NUWRAP` also rewrote the annotation
   `X` to `ℕ→ℕ`, a type-β-style recoloring of the body.

3. *λB*, and likewise GSF and λC∀mp: renames. Derived from λB's rules:

       Σ ▷ (ΛX. λx:X. x)[ℕ⇒ℕ] (λn:ℕ. n)
         → Σ,α:=ℕ⇒ℕ ▷ ((λx:α. x) : α⇒α =+α⇒ (ℕ⇒ℕ)⇒(ℕ⇒ℕ)) (λn:ℕ. n)
         → … ((λx:α. x) ((λn:ℕ. n) : ℕ⇒ℕ =−α⇒ α)) : α =+α⇒ ℕ⇒ℕ

   A store name is a type variable here: `α` may appear in any type
   anywhere in the program (λB types terms at `Σ; Δ; Γ`, and GSF's
   well-formed types are those whose "type names [are] bound in a
   well-formed type name store").  So the color of a position includes
   the store names.  Allocating `α` recolors *every* subterm, whether or
   not it crosses anything:
   - the body goes from `{X}` to `{α}`: the same size, but it is read
     with a store name in place of its own binder;
   - the argument `λn:ℕ. n` goes from `{}` to `{α}`: it gains `α` just by
     existing after the allocation.

**The dichotomy.**

| design | body at type β | argument crossing in |
|---|---|---|
| rename `X` to a global store name (λB, GSF, λC∀mp) | recolored, `{X}` → `{α}` | recolored, gains `α` (every allocation recolors every subterm) |
| keep the binder, no unbinding change (BfA) | keeps `X` (but `NUWRAP` rewrites annotations) | recolored, gains `X` |
| keep the binder, and `↓X` (strong-rep-nu) | keeps `X` | keeps its color |

So `↓X` is exactly the price of not renaming, and it is the reason the
change list needs unbinds as well as binds.  Renaming does not escape
the problem either, once store names count as type variables: a global
store of names recolors everything at each allocation.  Strong-rep-nu's
store is just as global, but its representation variables never appear
in types (types mention only the lexical names of the name map), so an
allocation changes no color (Decisions 3 and 8). The same holds for term
substitution: frame-exact `Beta`'s `↓Y` ends `ΛY`'s scope for a value
planted under it (Decision 5).

**Machine-checked: without `↓U`, an ill-scoped argument gains a type.**
`notes/DualTightness.agda` (ported 2026-09-25 from
`strong/proof/DualTightness.agda`, Jeremy's tightness test of
2026-09-06) builds the smallest case:
- **The setup.** The exterior store has a cell `α := ℕ` but no live
  name for it, so `U` is out of scope. The boundary is `⟪ ↥U , … ⟫`,
  and the argument `W = λz:ℕ. (λy:U⇒U. z) · (λu:U. u)` names `U`.
- **The redex is ill typed** (`¬Redex`).
- **The real `Wrap` step** is computed by `Eval.step` (`wrap-steps`,
  by `refl`) and sends `W` in under `↓U`. That contractum is **refused**
  (`¬Contractum`): inside `↥U` and then `↓U`, the name map is empty again.
- **The same contractum without the `↓U`** (`Leaky`, `W` under the empty
  scope) is **well typed** (`⊢Leaky`). The argument has gained `U` by
  crossing a boundary.
- **A control:** an argument that does not name `U` types before and
  after the real step.

The original file recorded the one step in the design history driven by
an *ill*-typed program that gained a type: there, `dual` dropped the
inverse of an entry, which is exactly `Leaky`.

**STA has this for agents.** STA's `[9]` sends a function's argument
across with the reversed agent list `rev(ℓ)`, which returns it to its
own agent's color. That is an anti-binder for principals. Strong-rep-nu
adds the same thing for type variables.

**Example: the pre-boundary counterexample.**  We tried one wrapper per
variable, `M ↑[X:=A]` / `M ↓[X:=A]`, whose conceal interior *truncated*
the context at `X`.  It fails on Jeremy's program (`Design.md` §1), here
in its value-restricted form (Decision 7: the `ΛY` body gets a dummy
`λ_:ℕ`, and the program is continued with `[𝔹] · 0 · true` to reach it).
This is the program of §5a, `E₀ᴮ`:

    (((ΛX. λf:(∀Z.Z→Z). ΛY. λ_:ℕ. f [Y]) [ℕ] · (ΛZ. λz:Z. z)) [𝔹] · 0) · true

In the old design (rule names of that design; derived by hand from its
rules in `notes/old/notes-v1.md`, "Old per-variable design", which is no
longer mechanized; type annotations on wrappers omitted as in Jeremy's
original trace):

      (((ΛX. λf. ΛY. λ_:ℕ. f [Y]) [ℕ] · (ΛZ. λz:Z. z)) [𝔹] · 0) · true
    → TyBeta      ((((λf. ΛY. λ_. f [Y]) ↑[X:=ℕ]) · (ΛZ. λz. z)) [𝔹] · 0) · true
    → WrapReveal  ((((λf. ΛY. λ_. f [Y]) · (ΛZ. λz. z)↓[X:=ℕ]) ↑[X:=ℕ]) [𝔹] · 0) · true
    → Beta        (((ΛY. λ_. (ΛZ. λz. z)↓[X:=ℕ] [Y]) ↑[X:=ℕ]) [𝔹] · 0) · true
    → TyWrapRevl  ((((ΛY. λ_. (ΛZ. λz. z)↓[X:=ℕ] [Y]) [𝔹]) ↑[X:=ℕ]) · 0) · true
    → TyBeta      ((((λ_. (ΛZ. λz. z)↓[X:=ℕ] [Y]) ↑[Y:=𝔹]) ↑[X:=ℕ]) · 0) · true
    → WrapReveal  ((((λ_. …) ↑[Y:=𝔹]) · 0↓[X:=ℕ]) ↑[X:=ℕ]) · true
    → WrapReveal  (((((λ_. …) · 0↓[X:=ℕ]↓[Y:=𝔹]) ↑[Y:=𝔹]) ↑[X:=ℕ]) · true
    → Beta        ((((ΛZ. λz. z)↓[X:=ℕ] [Y]) ↑[Y:=𝔹]) ↑[X:=ℕ]) · true
    → TyWrapCncl  (((((ΛZ. λz. z) [Y]) ↓[X:=ℕ]) ↑[Y:=𝔹]) ↑[X:=ℕ]) · true   ← ill typed

The conceal now sits inside `↑[Y:=𝔹]`, whose `Y` was bound *after* `X`.
Its exterior is `Y:=𝔹, X:=ℕ` and its interior truncates at `X`,
`(Y:=𝔹, X:=ℕ) ↓ X = ∅`, so the pushed `[Y]` cannot type.  (The design
reduced under `Λ`, and Jeremy's original trace hit the same wall in four
steps.)  Two lessons, which together are what a boundary is: **mask,
don't drop** (`↓X` removes `X` and nothing else), and **never push a type
argument into a concealed body** (record it as a new `↥` instead).  A
boundary then carries binds and unbinds at once, so it is a list.

**The same program in strong-rep-nu** (rendered, `showRun 0 16 E₀ᴮ-⊢`,
lines wrapped; the renderer reuses letters across binders, so primed
names are the argument's own bound variables), sixteen steps to `true`:

    Ξ = []
    (((ν X:=𝔹 · ((ν Y:=ℕ · (ΛZ. (λx:(∀Y. (Y⇒Y)). (ΛX′. (λy:ℕ. (ν Y′:=X′ · x ⟨
      (seal Y′ ↦ unseal Y′) ⟩))))) ⟨ ((∀Y. (id Y ↦ id Y)) ↦ (∀Y. (id ℕ ↦ (id Y
      ↦ id Y)))) ⟩) · (ΛZ′. (λx:Z′. x))) ⟨ (id ℕ ↦ (seal X ↦ unseal X)) ⟩) ·
      0) · true)
      --[TyBeta]-->
    Ξ = [α := ℕ]
    (((ν Y:=𝔹 · (((λx:(∀Y. (Y⇒Y)). (ΛZ. (λy:ℕ. (ν X′:=Z · x ⟨ (seal X′ ↦
      unseal X′) ⟩)))) ⟪ ↥X , ((∀Y. (id Y ↦ id Y)) ↦ (∀Y. (id ℕ ↦ (id Y ↦ id
      Y)))) ⟫) · (ΛY′. (λx:Y′. x))) ⟨ (id ℕ ↦ (seal Y ↦ unseal Y)) ⟩) · 0) ·
      true)
      --[Wrap]-->
    Ξ = [α := ℕ]
    (((ν Y:=𝔹 · (((λx:(∀Y. (Y⇒Y)). (ΛZ. (λy:ℕ. (ν X′:=Z · x ⟨ (seal X′ ↦
      unseal X′) ⟩)))) · ((ΛY′. (λx:Y′. x)) ⟪ ↓X , (∀Y. (id Y ↦ id Y)) ⟫)) ⟪
      ↥X , (∀Y. (id ℕ ↦ (id Y ↦ id Y))) ⟫) ⟨ (id ℕ ↦ (seal Y ↦ unseal Y)) ⟩) ·
      0) · true)
      --[Beta]-->
    Ξ = [α := ℕ]
    (((ν Y:=𝔹 · ((ΛZ. (λx:ℕ. (ν X′:=Z · (((ΛY′. (λy:Y′. y)) ⟪ ↓X , (∀Y. (id Y
      ↦ id Y)) ⟫) ⟪ ↓Z , (∀Z. (id Z ↦ id Z)) ⟫) ⟨ (seal X′ ↦ unseal X′) ⟩))) ⟪
      ↥X , (∀Y. (id ℕ ↦ (id Y ↦ id Y))) ⟫) ⟨ (id ℕ ↦ (seal Y ↦ unseal Y)) ⟩) ·
      0) · true)
      --[TyWrap]-->
    Ξ = [α := 𝔹 , β := ℕ]
    (((((λx:ℕ. (ν Z:=X · (((ΛX′. (λy:X′. y)) ⟪ ↓Y , (∀Y. (id Y ↦ id Y)) ⟫) ⟪
      ↓X , (∀Z. (id Z ↦ id Z)) ⟫) ⟨ (seal Z ↦ unseal Z) ⟩)) ⟪ ↥Y , (id ℕ ↦ (id
      X ↦ id X)) ⟫) ⟪ ↥X , (id ℕ ↦ (seal X ↦ unseal X)) ⟫) · 0) · true)
      --[Merge]-->
    Ξ = [α := 𝔹 , β := ℕ]
    ((((λx:ℕ. (ν Z:=X · (((ΛX′. (λy:X′. y)) ⟪ ↓Y , (∀Y. (id Y ↦ id Y)) ⟫) ⟪ ↓X
      , (∀Z. (id Z ↦ id Z)) ⟫) ⟨ (seal Z ↦ unseal Z) ⟩)) ⟪ ↥X , ↥Y , (id ℕ ↦
      (seal X ↦ unseal X)) ⟫) · 0) · true)
      --[Wrap]-->
    Ξ = [α := 𝔹 , β := ℕ]
    ((((λx:ℕ. (ν Z:=X · (((ΛX′. (λy:X′. y)) ⟪ ↓Y , (∀Y. (id Y ↦ id Y)) ⟫) ⟪ ↓X
      , (∀Z. (id Z ↦ id Z)) ⟫) ⟨ (seal Z ↦ unseal Z) ⟩)) · (0 ⟪ ↓Y , ↓X , id ℕ
      ⟫)) ⟪ ↥X , ↥Y , (seal X ↦ unseal X) ⟫) · true)
      --[Id]-->
    Ξ = [α := 𝔹 , β := ℕ]
    ((((λx:ℕ. (ν Z:=X · (((ΛX′. (λy:X′. y)) ⟪ ↓Y , (∀Y. (id Y ↦ id Y)) ⟫) ⟪ ↓X
      , (∀Z. (id Z ↦ id Z)) ⟫) ⟨ (seal Z ↦ unseal Z) ⟩)) · 0) ⟪ ↥X , ↥Y ,
      (seal X ↦ unseal X) ⟫) · true)
      --[Beta]-->
    Ξ = [α := 𝔹 , β := ℕ]
    (((ν Z:=X · (((ΛX′. (λx:X′. x)) ⟪ ↓Y , (∀Y. (id Y ↦ id Y)) ⟫) ⟪ ↓X , (∀Z.
      (id Z ↦ id Z)) ⟫) ⟨ (seal Z ↦ unseal Z) ⟩) ⟪ ↥X , ↥Y , (seal X ↦ unseal
      X) ⟫) · true)
      --[Merge]-->
    Ξ = [α := 𝔹 , β := ℕ]
    (((ν Z:=X · ((ΛX′. (λx:X′. x)) ⟪ ↓X , ↓Y , (∀Z. (id Z ↦ id Z)) ⟫) ⟨ (seal
      Z ↦ unseal Z) ⟩) ⟪ ↥X , ↥Y , (seal X ↦ unseal X) ⟫) · true)
      --[TyWrap]-->
    Ξ = [α := β , β := 𝔹 , γ := ℕ]
    (((((λx:X. x) ⟪ ↓Y , ↓Z , (id X ↦ id X) ⟫) ⟪ ↥X , (seal X ↦ unseal X) ⟫) ⟪
      ↥Y , ↥Z , (seal Y ↦ unseal Y) ⟫) · true)
      --[Merge]-->
    Ξ = [α := β , β := 𝔹 , γ := ℕ]
    ((((λx:X. x) ⟪ ↥X , ↓Y , ↓Z , (seal X ↦ unseal X) ⟫) ⟪ ↥Y , ↥Z , (seal Y ↦
      unseal Y) ⟫) · true)
      --[Merge]-->
    Ξ = [α := β , β := 𝔹 , γ := ℕ]
    (((λx:X. x) ⟪ ↥Y , ↥Z , ↥X , ↓Y , ↓Z , ((seal Y ; seal X) ↦ (unseal X ;
      unseal Y)) ⟫) · true)
      --[Wrap]-->
    Ξ = [α := β , β := 𝔹 , γ := ℕ]
    (((λx:X. x) · (true ⟪ ↥Z , ↥Y , ↓X , ↓Z , ↓Y , seal Y ; seal X ⟫)) ⟪ ↥Y ,
      ↥Z , ↥X , ↓Y , ↓Z , unseal X ; unseal Y ⟫)
      --[Beta]-->
    Ξ = [α := β , β := 𝔹 , γ := ℕ]
    ((true ⟪ ↥Z , ↥Y , ↓X , ↓Z , ↓Y , seal Y ; seal X ⟫) ⟪ ↥Y , ↥Z , ↥X , ↓Y ,
      ↓Z , unseal X ; unseal Y ⟫)
      --[Merge]-->
    Ξ = [α := β , β := 𝔹 , γ := ℕ]
    (true ⟪ ↥Y , ↥Z , ↥X , ↓Y , ↓Z , ↥Z , ↥Y , ↓X , ↓Z , ↓Y , id 𝔹 ⟫)
      --[Id]-->
    Ξ = [α := β , β := 𝔹 , γ := ℕ]
    true
      -- VALUE

Step 3 is the frame-exact `Beta` of Decision 5: the argument lands under
`ΛZ` inside its own `↓X` (from the crossing) and `↓Z` (from the
substitution).  Where the old design pushed `[Y]` into a concealed body,
here the two `TyWrap` steps (4 and 10) *bind* the instantiation as a new
`↥` and allocate a cell, the second one an alias (`α := β`).  The two
`Merge`s after the second `TyWrap` build the seal chain
`seal Y ; seal X` and the unseal chain `unseal X ; unseal Y` that carry
`true` across both instantiations.

Twice more the design died of dropping something: the scope move
(`DesignPoints.md` D45), and a `dual` that dropped the inverse of a `↥`
(D47; `notes/DualTightness.agda` above).  Candidate slogan: *nothing may be
dropped*.

**What this forces: Decision 3.**  A binder that does not allocate
(`↥X` names an existing α) and an anti-binder that keeps the store
(`↓X` ends `X`'s scope but α stays) only make sense if the thing named
and the name are different.  When a type variable is itself the storage
slot, ending its scope must either delete the slot (dropping, which this
decision rules out) or keep it hidden in place, and a new name for an
old slot has nothing to point at.  Decision 3 is the separation this
requires.

**Builds on.**
- **STA showed that the history of crossings must be an ordered list.**
  Its three-agent counterexample (p.1048) shows that nested embeddings
  flatten to an *ordered* agent list `ℓ`, since a set loses "that agent
  `i` must have exported the integer at type `t` before `j` could
  export it at type `s`". Strong-rep-nu's change list `Θ` is the same
  kind of object, and `Merge`'s `Θ₂ ++ Θ₁` is STA's list append in `[8]`.
- **BfA's local bindings sit at a position**, which is what makes a
  "mask here, keep the rest" discipline meaningful at all.

**New here.** This is one of the two most novel parts of strong-rep-nu,
with Decision 3, and the paper should present it as a contribution.
- **A binder that does not allocate, and an unbinder.** In the calculi
  above, the construct that binds a type name also creates it:
  - BfA's `νX:=A. t`, λN's `Nγ≈τ. e`, Neis et al.'s `new α≈τ in e` and
    PolyGν's `X ≅ A` each bind a name *and* its representation at one
    place;
  - the binding then scopes over the whole body;
  - none can end a name's scope partway through a term, or give an
    already existing representation a new name.

  `↥X` binds a name to an existing representation variable, which is
  possible only because names and representations are separate
  (Decision 3), and `↓X` ends a scope at a chosen position.
- **Color is read off the binders.** Because every type variable has a
  lexical binder at every point of a run, and every rule moves or
  inverts binders, color preservation is a statement about scopes. The
  proof is one frame lemma per rule, where a proof by substitution would
  have to reason about what each substitution did.
- **Unnameability as well as opacity.** STA's abstraction is by opacity
  (`t ∉ Dom(δᵢ)`), and its `Θ` is used only for freshness ("Θ is unused
  by the new version of the old rules", p.1072). A change list that
  masks one name and keeps the rest has no counterpart that I found.
  `notes/TypeAbstractionComparison.md` §§2, 11 compare the two in
  detail; that note predates the store and `Merge`.
- **A connection worth naming (from memory):** a change list is an
  explicit *context morphism* between the exterior and interior type
  contexts. The Agda relation was called `CtxMorph` until 2026-09-21.
  It is in the spirit of explicit substitutions (λσ's shift `↑` and lift
  `⇑`), but it acts on the type context and is never pushed into the
  term.

### 3. Two universes: type variables are lexical, representation variables are storage

**Forced by Decision 2.**  This decision came second and was forced by
the first.  Once a boundary's `↥X` binds and `↓X` unbinds type
variables, two things have to be expressible that a single universe of
type variables cannot express:
- **A representation that outlives its name.** After `↓X`, the interior
  cannot name `X`, but `X`'s representation must still exist: a
  conversion (`seal X` at the conversion context) and the frames outside
  still refer to it.
- **One representation under different names in different frames.**
  `↥Y` gives an *existing* representation a new name for an interior.

The `S₀` run of Example 3b shows both:
- **Names come and go around a fixed cell.** In the scope
  `⟪ ↥X , ↓Y , seal Y ⟫`, `↥X` names one cell for the interior while
  `↓Y` hides another, and neither cell moves.
- **A cell may be an alias.** The store holds `β := γ`: `β`'s
  representation is the representation *variable* `γ`, which `Z`
  names.

So the calculus needs something for names to *denote*, separate from
the names themselves (representation variables, in the store), and a
map connecting them that boundaries edit (the name map).

**Without it:** we tried one universe, in which a type variable was also
its storage slot and `↓X` hid the slot in place (the original `strong/`,
from which strong-rep-var split the two universes).  It works, but a
crossing renamed ordinary variables (Example 3a), and the color theorem
could only compare scope *sizes*, by a push/pop count, rather than
relate the name maps themselves (`ScopeMapPreservation`;
`DECISIONS.md`, 2026-09-21).

A type context is a pair `Ξ ∣ Γ`: a store `Ξ` of representation cells
(`α` abstract, or `α := R`), and a **name map** `Γ` listing the live type
variables and which `α` each one names.  An unbind deletes a *name*; it
never touches a representation.  The relation `Γ ⊢ A ~ R`, which is
renaming through `Γ` (`proof/SameRenaming.agda`), connects the two.

**Example 3a: the crossing does not rename** (§10, `Examples.agda`,
checked by `refl`; rendered, ``showTmIn 1 (Nsub [ Wsub ∶ ` 0 ]ᵐ)``,
with ``Nsub = Λ (ƛ ℕ ∙ ` 1)``).
Substituting `W = 7 ⟪ seal X ⟫` for `x` in `ΛY. λ_:ℕ. x` (value-restricted:
the `Λ` body is a `λ`) gives

    ΛY. λ_:ℕ. ((7 ⟪ seal X ⟫) ⟪ ↓Y , id X ⟫)

The image's `seal X` is *unchanged*.  In the one-universe design the same crossing
renamed it (`seal 0` became `seal 1` in de Bruijn), because a type
variable was also a storage slot and a new `Λ` slot shifted it.

**Example 3b: one representation, several names over time** (the Merge
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

**Builds on.**
- **λB already separates the two sorts.** λC∀mp notes that "type names
  and variables are distinguished in λC∀mp (following Ahmed et al.
  [2017])": a type variable `X` is lexical and a type name `α` lives in
  the store. Strong-rep-nu's two universes are this distinction.
- **Funky pairs a lexical label with what it denotes.** An unknown type
  carries an instantiation environment: "`?^{X:Int}` expresses that type
  variable X is in scope and instantiated to Int. … In the type
  `?^{X:X}`, the two occurrences of X play a different role: the first
  is merely a label, while the second is an actual occurrence of the
  type variable X" (§3). That is the name map's split between a lexical
  label and what it denotes.
- **Matthews & Ahmed's `⟨α; τ⟩`** pairs the abstract variable with its
  instance on a boundary annotation.
- **GSF's evidence type names record alias chains.** `αβ^Int` records
  "that α is bound to β, which is itself bound to Int" (GSF §7.2).
  These correspond to the alias cells of Example 3b (`β := γ`).
- **F_C keys its global store by `X` itself** (`Σ, X≔A`), a clean
  one-sort design with a store. Strong-rep-var started from the
  analogous one-universe design.

**New here.** How the two sorts are *connected*. λB, GSF and λC∀mp
connect them by substituting `α` for `X`. Funky updates its
environments by substitution (`?^{Y:X, X:X}[Int/X] = ?^{Y:Int,
X:Int}`), and they live on each `?` rather than in the context.
Strong-rep-nu connects the sorts by a lexical name map `X ↦ α` in the
type context, which boundaries edit and nothing substitutes. That is
what makes color the checkable equation of `ScopeMapPreservation`. I
found nothing closer, but that is a search result, not a proof of
novelty.

*Terminology (from memory).* "Representation" also names the run-time
type representations of intensional polymorphism (Crary, Weirich &
Morrisett, ICFP 1998). Strong-rep-nu's representations are types in the
store, never terms; say so once.

### 4. A boundary carries a coercion-style *conversion*, and crossings go inward through the dual

A boundary relates two types, the interior type (read inside) and the
exterior type (read outside), by an explicit **conversion**, built leaf
by leaf: `seal X` (the interior sees the representation, the exterior
sees the name), `unseal X` (the reverse), `c ↦ d`, `∀X.c`, and `id`.
When a function wrapped in a boundary is applied, the argument
**crosses** inward, wrapped in the **dual** scope with the domain
conversion, and the result stays wrapped in the codomain conversion
(`Wrap`).

**Coercions, not casts.**  The conversions are *coercions* in the sense
of coercion calculi: a small syntax of combinators with a typing
judgement `Δ ⊢ c ∶ A ⇝ B`, following the polymorphic coercion calculi of
Igarashi and colleagues (λC∀, Ozaki, Sekiyama & Igarashi, Scheme 2021;
λC∀mp, Igarashi, Ozaki, Sekiyama & Tanabe, PLDI 2024):

    λC∀        c, d ::= id_A | G! | G?p | c → d | c ; d | ∀X.c      Γ ⊢C c : A ⇝ B
    λC∀mp      … plus concealment α⁻ and revelation α⁺
    here       c, d ::= id A | c ↦ d | ∀X.c | seal X | unseal X     Δ ⊢ c ∶ A ⇝ B

The function coercion is contravariant in its domain in both
(`(Ct_Arrow)` there, `conv-fun` here), and `∀X.c` is `(Ct_Cabs)`.  What
differs:
- **No `★`.** There are no injections or projections; `seal X` and
  `unseal X` play the roles of `α⁻` and `α⁺`.
- **Names, not store names.** `seal X` names a lexical type variable,
  resolved through the name map (Decision 6), where `α⁻` names a store
  name.
- **No syntactic sequence.** Composition is a function on normal forms
  (Decision 10), as in λS's `s # t`, rather than a coercion `c ; d`.

The alternative was a *cast* between two types, `⟨A ⇒ B⟩`, as in BfA
and λB, or GSF's *evidence*.  A cast names only its two endpoints, so
it cannot say, leaf by leaf, which variable a position seals or
unseals, and a boundary's crossings need exactly that.  Coercions are
also what make normal forms and composition, and so `Merge`,
possible.

**Example:** the `Wrap` step of §1a above.  `7 : ℕ` must become an `X`
inside, so it gets `⟪ ↓X , seal X ⟫`: the dual `↓X` of `↥X`, with the
domain half `seal X`.  The answer gets `unseal X` outside.

**Without it:** we tried reading one type through two substitutions
instead of an explicit conversion; the survey found 61 of 195
configurations where the term did not determine the relationship
(`notes/BoundarySurvey.md`).

**Sub-decisions, each with its own example:**

* **Crossings are inward only.**  We tried re-expressing a boundary
  outward (v1's `Merge ⊕`); it fails on a reachable nesting that has no
  flat form (`DesignPoints.md` D24–D25).
* **No polarity index.**  We tried polarized conversions; the pushed
  `seal ↦ seal` of the old `TyPeelR` typed at neither polarity
  (`DECISIONS.md`, 2026-09-06).

**Builds on.**
- **The coercion calculi of Igarashi and colleagues** supply the
  grammar and the typing judgement (above): λC∀ (Ozaki, Sekiyama &
  Igarashi, Scheme 2021), and λC∀mp / λS∀mp (Igarashi, Ozaki, Sekiyama
  & Tanabe, PLDI 2024). Behind them are Henglein's coercions (1994) and
  Siek, Thiemann & Wadler's blame-aware coercion calculus λC/λS
  (PLDI 2015), which the repo's GTLC follows.
- **Conversions.** The name and the idea are λB's: `=+α⇒` / `=−α⇒`,
  which BfA called static casts. λC∀mp's concealment `α⁻` / revelation
  `α⁺` "correspond to static casts in [BfA], conversions in [λB], and
  sealing/unsealing operations in [New et al. 2020]" (λC∀mp §3). λN's
  coercions `{e}⁺_γ` / `{e}⁻_γ` are the earliest version in this list.
- **Generating conversions from types.** `revealₓ(C)` and `mkId` are
  λN's type-directed `{e : τ′}^±_{γ≈τ}` (Fig. 3; "coercion polarity is
  inverted for function arguments"), λB's conversion inserted at type
  application, and λC∀mp's `coerce^±_α`.
- **Boundaries as terms, and the reversal on arguments.** Matthews &
  Ahmed's `τMS e` / `SMτ e`, after Matthews & Findler's multi-language
  semantics (POPL 2007), are term-level boundaries, and "the direction
  of conversion reverses for function arguments" (§2). That is the
  ancestor of `Wrap`'s dual.
- **`Wrap` itself** is λB's rule (9),
  `(v : A→B ⇒ A′→B′) v′ → v (v′ : A′ ⇒ A) : B ⇒ B′`, which λB takes from
  Siek & Wadler's space-efficient function casts (λB §2.4). It is also
  λC∀mp's `R_Wrap_C`, and in spirit STA's `[9]`, which reverses the
  agent list with `rev(ℓ)`.

**New here.**
- **`seal X` names a lexical type variable**, and the representation is
  found through the name map. The calculi above seal with a store name
  `α`.
- **The argument crosses under `dual Θ`**, a change list that says
  exactly which names the argument may use.
- **No polarity index.** λB negates the label on the domain and λN
  inverts polarity. Strong-rep-nu's frames record direction per variable,
  so the conversion judgment needs no polarity (Decision 4's
  sub-point).

### 5. Frame-exact term substitution

Substituting a value `W : A` for `x` under a `ΛY` wraps it in that
binder's dual, `W ⟪ ↓Y , id A ⟫`.  The value arrives in the frame it was
born in.  This is `_[_∶_]ᵐ` (`TermSubst.agda`), and why `Beta` carries
the argument type.

**Example:** the `Beta` step of the §5a run (step 3 of the trace in
Decision 2), shown here on the uncontinued program `E₀`, where it ends
in a value (rendered, `showRun 0 20 E₀-⊢`):

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

**Without it:** the argument gains `Y`, the second recoloring of §0.
Jeremy spotted the missing `↓Y` in this very trace (`DECISIONS.md`,
2026-09-08).

**Cost:** a numeral crossing a `Λ` picks up an `id ℕ` layer, removed by
one `Id` (or merged away).

**Builds on.**
- **STA's brackets travel with the value.** A substituted embedding
  `⌈v̂ⱼ⌉` keeps its bracket, and with it its color, which is the same
  instinct as frame-exact substitution.
- **BfA's `NUWRAP` faces the same situation from the other side.** When
  a `ν` moves under a `λ`, it substitutes into that `λ`'s annotation
  (`λy:B[X:=A]`), keeping the moved binding consistent with its new
  surroundings.

**New here.** Wrapping the substituted value in the crossed binder's
dual, so the value arrives in its birth frame. All the calculi above
use ordinary capture-avoiding substitution for term `β`, which suits
their goals. Suggested claim for the paper: frame-exact substitution is
new.

### 6. A representation is stored once and cited by name

A conversion never contains a representation: `seal X` carries the name
`X`, and its representation is found through the context (the lookup
square `Δ ∋ X := A`).  The store holds each representation exactly once.

**Without it:** we tried copying a variable's representation into every
boundary that mentions it (v1).  Progress and preservation both failed,
and every typability loss in the survey was a copy the target context
could not spell (`notes/BoundarySurvey.md`).

**Example (the soundness gate, `proof/Adversary.agda`):** at
`Ξ ∣ Γ = (α) ∣ (X ↦ α)`, where `α` is abstract,

    7 ⟪ ↓X , seal X ⟫ : X          is refused (¬⊢adv)

because `seal X` must cite a *represented* binder and `α` has no
representation.  At `X ↦ α`, `α := ∀Z.Z⇒Z`, the same term is refused
because `7 : ℕ` cannot spell `α`'s representation (`¬⊢bad`).  With one
stored copy there are not two spellings to disagree.  A candidate
example for the paper: *you cannot forge an `X` from an `ℕ` unless `X`
is bound to `ℕ`.*

**Builds on.**
- **The soundness gate is λN's scoping rule.** λN types `{e}⁺_γ` only
  when `γ≈τ ∈ Γ`: "coercions are only available within the lexical
  scope of the corresponding type generator" (§3.2). `conv-seal`'s
  `Δ ∋ X := A` is the same rule, resolved through the name map.
- **Explicit conversions**, as in λB and λC∀mp, rather than an equality
  between a name and its binding. F_C ("X is definitionally equal to
  A"), GSF ("a type name α is considered equal to its associated type in
  the store") and Neis et al.'s G (α and τ are "equal as classifiers,
  but not as data", with no "explicit term-level type coercions") show
  how light the implicit alternative can be. The explicit choice is
  what lets conversions be syntactic normal forms (Decision 10) and
  keeps reduction deterministic.
- **STA's compatible knowledge.** Def. 3.1 requires agents' knowledge
  to agree where it overlaps ("if `t ∈ Dom(δᵢ) ∩ Dom(δⱼ)` then
  `δᵢ(t) = δⱼ(t)`"), which STA maintains by construction in a monotone
  registry. It is the same "copies agree" invariant strong-rep-nu's v1
  could not maintain once boundaries moved. Storing the representation
  once is how strong-rep-nu reaches STA's invariant with lexical names.

**New here.** The store is read through the name map. The dynamic
semantics consults it in one place only: `Merge` meeting `seal Z` with
`unseal Z`, where `repOf` writes the identity at `Z`'s representation.
Compare G, where "the representation types in the store are never
actually inspected by the dynamic semantics".

### 7. The value restriction: `ΛX.N` requires `N` to be a value, and there is no `ξ-Λ`

Nothing reduces under a type binder.

**Why:** it makes every redex's context the **ambient** one.  With
`ξ-Λ`, an allocation under a `Λ` would create a cell whose representation
mentions the `Λ`'s own abstract variable, onto a context the `Λ`'s
siblings do not share.  With the restriction, "allocate at the top and
shift everyone else" means something (`RepStoreSketch.md`, "Why
experiment 1 had to come first").  It is the prerequisite for
Decision 8.

**Cost, on examples:** 10 of the 21 closed programs of the corpus were
rejected (`DECISIONS.md` 2026-09-21).  Jeremy's recipe repairs them: add
a dummy `λ` to make the body a value, and apply it.

    (ΛZ. x) [ℕ]      becomes      ((ΛZ. λy:ℕ. x) [ℕ]) · 0

The §5a program in Decision 2 shows the other side of the cost: the
pre-boundary counterexample needs its `ΛY` body padded with `λ_:ℕ` and
the program continued with `[𝔹] · 0` before the interesting reduction
happens, because nothing reduces under the binder.

**Builds on.** This decision is λB's, and the paper should say so.
- λB §2.4 explains why BfA had to reduce under `Λ`: BfA wanted the value
  restriction (§5.2), but `(NUTYWRAP)` and `(GENERALIZE)` push non-values
  under a `Λ`.
- λB resolves it by making casts to `∀` values that are applied at type
  application: "With the removal of evaluation under type abstractions,
  we are free to immediately place generated names in a global store,
  forgoing the use of ν binders."
- Strong-rep-nu's Decisions 7 → 8 follow the same argument.
- Other value-restricted `Λ`s: F_C's values are `ΛX::G. w`, and STA's
  `Λα. eᵢ` is a primval with no reduction under it.

**New here.** Nothing beyond the recipe for rewriting programs whose
`Λ` bodies are not values, which is folklore.

### 8. A global store, with each step reporting its allocation

The store `Ξ` is ambient.  `ν` allocates `α := R` on it, a step returns
the change it made (`δ = none | new R`), and the congruences shift the
redex's *siblings* by that one allocation.  A boundary changes names
only: `reps Δᵢ ≡ reps Δ ≡ reps Δᶜ`.

**Without it:** we tried giving each boundary its own block of
representation bindings (strong-rep-var); every rule that moved a
subterm across a boundary then had to re-index it.

**Example:** in the §1a trace the store `Ξ = [α := ℕ]` sits *outside* the
term, and `Wrap` moves `7` into `⟪ ↓X , seal X ⟫` verbatim.  Before the
store, that crossing needed the bind-block weakening `RepWeakenTyping`.

It is not the global Σ-store rejected earlier (D33→D34), which stored
names too and lost lexical unbinding: here `Ξ` says *what* a
representation is, and `Γ` says *whether* this position may name it.

**Builds on.**
- **The global store is the standard design**: λB, F_C (following λB),
  GSF, λC∀mp, PolyG and Neis et al.'s G (`σ`, with freshness "achieved
  by α-renaming").
- **The case for it** is BfA §5.5, which shows why a global list of
  bindings needs the value restriction first (Decision 7). Its
  hypothetical reduction, with `s = (λx:X. λy:Y. x) : X→Y→X`, is
  deliberately *not* value-restricted (`ΛX.(ΛY.s)X` reduces under
  `ΛX`); that is its point, so it is quoted as is:

      ε;      let f = ΛX.(ΛY.s)X in (f I, f B)
      ↦ Y≈X;   let f = ΛX.s in (f I, f B)
      ↦ Y≈X;   ((ΛX.s) I, (ΛX.s) B)
      ↦ Y≈X, X≈I; (s, (ΛX.s) B)

  "We would like to α-rename the X in ΛX.s, but that would lose the
  connection with Y. Also, Y should really get two different
  bindings."
- **The alternatives:** λN's scope extrusion ("we also considered … an
  explicit type store or heap as in the λν-calculus, but that choice
  would produce a more complicated system", fn. 4), which G also names
  (§2.2, fn. 3), and STA's monotone global knowledge base `{Δ}`.
- **Plausible Sealing gives the reason to keep names lexical.** "Global
  seals have been shown to break equivalences that hold in System F
  [Devriese et al. 2018]", and earlier proofs therefore use "Kripke
  worlds containing semantic types for dynamically-allocated seals".
  Funky instead tracks semantic types "in a lexical environment, similar
  to traditional formulations of parametricity [Reynolds 1983]" (§1).

**New here.**
- **Allocation changes no color.** A representation variable never
  appears in a type: types mention only the lexical names of the name
  map. So allocating a cell, which in λB, GSF or λC∀mp would add a new
  type variable to the color of every subterm, changes no position's
  color here (Decision 2's worked example).
- **What the store holds.** It holds *representations* only, while
  names stay lexical in the name map. That combines the global store's
  simplicity with the lexical scoping Plausible Sealing argues for, and
  it resolves the D33 fork (`DesignSpace.md`, "a global Σ-store, NOT
  taken — lexical scope is needed for unbind blocking") by splitting it
  in two.
- **A conjecture to state.** With no `★` and no type case, a store cell
  can only be observed through a live name. So a Reynolds-style
  parametricity theorem, with relations indexed by the name map instead
  of a Kripke world, may be within reach.
- **Not a design point.** Reporting the allocation `δ` from each step and
  shifting siblings is how a de Bruijn development spells "`α` fresh".

### 9. `ν` replaces type application; the compiler writes the reveal

The run-time language has no `L [A]`.  Plain System F is a separate
source language, and `compile` translates `L [A]` (with `L : ∀X.C`) to
`ν X:=A · ⟦L⟧ ⟨ revealₓ(C) ⟩`.

**Why:** without it, type application had to create the reveal at run
time (which needed an annotation `B` on `L [B, A]`), and its
`∀`-over-a-boundary partner had to fuse two conversions.  With the reveal
written by the compiler, `TyWrap` stacks and `Merge` fuses.

**Example:** §1b, `((ΛX. λf:(∀Y. Y⇒𝔹). f[X]) [𝔹] · (ΛZ. λz:Z. true)) ·
false`, compiled to two `ν`s, both written by the compiler (rendered,
`showRun 0 9 K₀-⊢`):

    Ξ = []
    (((ν X:=𝔹 · (ΛY. (λx:(∀Y. (Y⇒𝔹)). (ν Z:=Y · x ⟨ (seal Z ↦ id 𝔹) ⟩)))
         ⟨ ((∀Y. (id Y ↦ id 𝔹)) ↦ (seal X ↦ id 𝔹)) ⟩)
      · (ΛX′. (λx:X′. true))) · false)
      --[TyBeta]-->
    Ξ = [α := 𝔹]
    ((((λx:(∀Y. (Y⇒𝔹)). (ν Y:=X · x ⟨ (seal Y ↦ id 𝔹) ⟩))
         ⟪ ↥X , ((∀Y. (id Y ↦ id 𝔹)) ↦ (seal X ↦ id 𝔹)) ⟫)
      · (ΛZ. (λx:Z. true))) · false)
      --[Wrap]-->
    Ξ = [α := 𝔹]
    ((((λx:(∀Y. (Y⇒𝔹)). (ν Y:=X · x ⟨ (seal Y ↦ id 𝔹) ⟩))
         · ((ΛZ. (λx:Z. true)) ⟪ ↓X , (∀Y. (id Y ↦ id 𝔹)) ⟫))
        ⟪ ↥X , (seal X ↦ id 𝔹) ⟫) · false)
      --[Beta]-->
    Ξ = [α := 𝔹]
    (((ν Y:=X · ((ΛZ. (λx:Z. true)) ⟪ ↓X , (∀Y. (id Y ↦ id 𝔹)) ⟫)
          ⟨ (seal Y ↦ id 𝔹) ⟩)
        ⟪ ↥X , (seal X ↦ id 𝔹) ⟫) · false)
      --[TyWrap]-->
    Ξ = [α := β , β := 𝔹]
    (((((λx:X. true) ⟪ ↓Y , (id X ↦ id 𝔹) ⟫)
          ⟪ ↥X , (seal X ↦ id 𝔹) ⟫)
        ⟪ ↥Y , (seal Y ↦ id 𝔹) ⟫) · false)
      --[Merge]-->
    Ξ = [α := β , β := 𝔹]
    ((((λx:X. true) ⟪ ↥X , ↓Y , (seal X ↦ id 𝔹) ⟫)
        ⟪ ↥Y , (seal Y ↦ id 𝔹) ⟫) · false)
      --[Merge]-->
    Ξ = [α := β , β := 𝔹]
    (((λx:X. true) ⟪ ↥Y , ↥X , ↓Y , ((seal Y ; seal X) ↦ id 𝔹) ⟫) · false)
      --[Wrap]-->
    Ξ = [α := β , β := 𝔹]
    (((λx:X. true) · (false ⟪ ↥Y , ↓X , ↓Y , seal Y ; seal X ⟫))
      ⟪ ↥Y , ↥X , ↓Y , id 𝔹 ⟫)
      --[Beta]-->
    Ξ = [α := β , β := 𝔹]
    (true ⟪ ↥Y , ↥X , ↓Y , id 𝔹 ⟫)
      --[Id]-->
    Ξ = [α := β , β := 𝔹]
    true
        -- VALUE

The inner `ν Y:=X · x ⟨…⟩` meets a `∀`-value under a boundary, so
`TyWrap` fires. It allocates the *alias* cell `α := β` (Decision 3),
stacks the crossed conversion under `ν`'s own, and the two `Merge`s fuse
the layers, chaining `seal Y ; seal X` through the alias.

**Side benefit:** a clean compiler-correctness story.  `compile-⊢`,
`compile-closed` and `compile-safe` hold, and `SourceExamples.agda`
checks by `refl` that the twenty source programs compile to the corpus.
**Example for the paper:** `compile-⊢` needs every term-context type to be
well-formed.  At `Γₜ = x : ∀Y.Z` with `Z` out of scope, `x [ℕ]` has a
source typing but its `ν` has none.

**Builds on.**
- **New's thesis is where the ν form comes from.** Chapter 10 identifies
  the problem this decision solves. With System F's syntax, an
  instantiation actually uses "a fresh type α that is merely isomorphic
  to B, not the same as it", and "this results in the need for
  type-directed sealing to mask the difference" (§10.1).
  - PolyGν's elegant answer is the ANF instantiation `let x = M{X≅B}; N`,
    in which "the continuation N now has an explicit isomorphism in
    scope … to manually seal and unseal inputs and outputs of x as
    necessary". The POPL paper uses an "inside-out" binding instead.
  - `ν X:=A · L ⟨c⟩` is PolyGν's instantiation with the continuation
    specialized to a *conversion*: `X` is bound in `c`, and sealing and
    unsealing are `c`'s leaves `seal X` / `unseal X`.
- **The shape of `TyWrap` is λB's.** λB's third type-application rule,
  `Σ ▷ (v : ∀X.A =ϕ⇒ ∀X.A′)[B] → Σ,α:=B ▷ ((v[α] : A[α/X] =ϕ⇒
  A′[α/X]) : A′[α/X] =+α⇒ A′[B/X])`, moves the inner conversion inside
  and stacks the reveal outside, which is `TyWrap`'s stacked contractum.
  PolyCν's `∀ν` casts accumulate on the `Λν` (`Λν{X.([B⊑↕], M)}`) and
  are applied at instantiation, the same discipline. λC∀mp's
  `R_Tybeta_C` fuses a whole sequence of `∀` coercions in one step.
- **Syntax.** `ν X:=A · L ⟨c⟩` takes its shape from the repo's GTPLC
  (`ν A · L •⟨ c ⟩`). BfA's `νX:=A. t` and λN's `Nγ≈τ. e` are the
  binder ancestors.
- **Neis, Dreyer & Rossberg map where generative translation is safe.**
  They show that giving every existential introduction a fresh name
  (`pack ⟨τ,e⟩ ↝ new α≈τ in pack ⟨α,e⟩`) exposes sharing: `let x =
  pack ⟨τ,v⟩ in ⟨x,x⟩` and `⟨pack ⟨τ,v⟩, pack ⟨τ,v⟩⟩` become
  distinguishable. Their type-directed `Wr±`, after Sumii & Pierce's
  "firewall" and "sandbox", is the fix (§5). `compile` uses only the
  `∀` half, `e τ ↝ new α≈τ in e α`, so their result is the guide for an
  `∃` extension.

**New here.** Who writes the reveal. In λB, λC∀mp and λN the
type-application rule generates it at run time. In PolyGν the
programmer writes it, which is PolyG's key to graduality. Strong-rep-nu
keeps PolyGν's explicit, arbitrary conversion (`⊢ν` accepts any `c`
whose types line up), and has the compiler write it once:
`⟦L[A]⟧ = ν X:=A · ⟦L⟧ ⟨revealₓ(C)⟩`.

### 10. One boundary per value: conversions are tight normal forms, and `Merge` composes them

This is one decision in two halves.  Conversions are kept in **normal
form**, in three sorts:

    g ::= id A | c ↦ d | ∀X.c                 middle
    t ::= g | seal X | t ; seal X             tail   (left-associated seal chain)
    c ::= t | unseal X | unseal X ; c         conversion (right-associated unseal chain)

These come with `NoCancel` (no `unseal X` directly before a bare
`seal X`) and non-identity chains only.

The normal forms exist *so that composition is easy to define*.
`Δ ⊢ c₁ ⨟ c₂` is a total function whose result is again a tight normal
form, defined by cases on the sorts: a seal chain meets an unseal chain
at the middle, `seal X` meets `unseal X` and cancels, and identities are
absorbed.  With composition in hand, a value carries **at most one
boundary**: a boundary directly over a value's boundary is a redex of
`Merge`, which concatenates the two scopes and **composes** the two
conversions (`Δ ⊢ c₁ ⨟ c₂`).

Tightness also keeps reduction deterministic (`det`) and makes the value
classification syntactic.  Inert tails are values, and the one active
tail, `id` at a base type, is removed by `Id`.  Without `NoCancel`,
`unseal X ; seal X` would be a second spelling of an identity at `X`, and
composition would have two answers.

**Without it:** we tried letting boundaries pile up, with special rules
for particular pairs (`CancelR`, `IdPush`); the census found up to 11
stacked pairs in one state, and run V took 49 steps (`MergeSketch.md`).

**After it:** at most two stacked pairs in any state, V drops from 49
steps to 19, `CancelR`, `IdPush` and `Nu-⟪⟫` are deleted, and the rule
count falls to ten.

**Example:** the tail of run `S₀` (Example 3b's program; rendered,
`showRun 0 15 S₀-⊢`, last five steps, all at the store
`Ξ = [α := ℕ , β := γ , γ := ℕ]`):

    (((((7 ⟪ ↓Z , seal Z ⟫) ⟪ ↓X , id Z ⟫) ⟪ ↥X , ↓Y , seal Y ⟫)
         ⟪ ↥Y , unseal Y ⟫) ⟪ ↥Z , unseal Z ⟫)
      --[Merge]-->
    ((((7 ⟪ ↓X , ↓Z , seal Z ⟫) ⟪ ↥X , ↓Y , seal Y ⟫) ⟪ ↥Y , unseal Y ⟫)
       ⟪ ↥Z , unseal Z ⟫)
      --[Merge]-->
    (((7 ⟪ ↥X , ↓Y , ↓X , ↓Z , seal Z ; seal Y ⟫) ⟪ ↥Y , unseal Y ⟫)
       ⟪ ↥Z , unseal Z ⟫)
      --[Merge]-->
    ((7 ⟪ ↥Y , ↥X , ↓Y , ↓X , ↓Z , seal Z ⟫) ⟪ ↥Z , unseal Z ⟫)
      --[Merge]-->
    (7 ⟪ ↥Z , ↥Y , ↥X , ↓Y , ↓X , ↓Z , id ℕ ⟫)
      --[Id]-->
    7

Each step shows one clause of composition:
1. `seal Z ⨟ id Z = seal Z`: an identity is absorbed.
2. `seal Z ⨟ seal Y = seal Z ; seal Y`: two seals *chain*, which is
   possible only because of the alias cell `β := γ`.
3. `(seal Z ; seal Y) ⨟ unseal Y = seal Z`: the last seal of the chain
   is cancelled.
4. `seal Z ⨟ unseal Z = id ℕ`: the identity at `Z`'s representation,
   read off the store.
5. `Id` removes the identity at a base type.

(Not v1's merge coming back: v1's `⊕` substituted representations into
representations, whereas `Merge` composes name-carrying conversions and
reads a representation only where `seal Z` meets `unseal Z`, by lookup.)

**Builds on.**
- **The normal forms.** The three sorts follow λS∀mp's (and Siek,
  Thiemann & Wadler's) space-efficient schema
  `(G₁?p ;)? (⊥p | (g (; G₂!)?))`: an optional projection, a ground
  middle, and an optional injection. Strong-rep-nu's `c ::= unseal X ; c`,
  `g` and `t ::= t ; seal X` have the same layout, with **unseals in the
  projection position and seals in the injection position**. The repo
  lineage is GTLC's normal forms with GTPLC's chain association
  (`MergeSketch.md`).
- **The invariant is the space-efficiency one.** λS∀mp states it
  exactly: "a value is wrapped by at most one coercion and the hole in a
  frame never appears under coercion applications" (§4.2), after
  Herman, Tomb & Flanagan and Siek, Thiemann & Wadler's normal-form
  coercions.
- **The cancellation rules are well established.** `Merge`'s
  `seal Z ⨟ unseal Z` clause is λN's `{{e}⁺_γ}⁻_γ → e`, λB's "two mirror
  image conversions … reduce to the identity", λC∀mp's `R_Remove_C`
  (`V⟨α⁻⟩⟨α⁺⟩ → V`), and GSF's consistent-transitivity rule `(unsl)`.
- **Composing at every step is GSF's style.** GSF combines evidence at
  every step, and is the closest relative in *how* `Merge` works.
- **STA's `[8]` merges nested embeddings** with an ordered list.

**New here.**
- Seals and unseals are part of the normal form. λS∀mp chose to leave
  concealment and revelation implicit, because "concealment and
  revelation make it complicated to discuss space efficiency formally"
  (§4).
- Chains of several seals are possible, through aliases, where `★`
  admits one tag.
- Composition of name-carrying conversions at a merged frame, keeping
  both scopes (`Θ₂ ++ Θ₁`).

**An open question, with a candidate answer.** Ozaki, Sekiyama &
Igarashi (Scheme 2021) prove that λC∀ is not space-efficient (Thm 6).
- Their witness is polymorphic recursion at `★`: `M = (fix f = ΛX.
  λx:X. f ★ (x⟨X!⟩)) ★ (0⟨Int!⟩)` reaches `0⟨Int!⟩⟨X₁!⟩⋯⟨Xₙ!⟩` with
  `Xᵢ := ★`, which no smaller coercion can replace (the paper states
  the reachable state, not the individual steps). They conjecture that
  forbidding `★` as a type argument restores space efficiency, which
  λC∀mp then develops.
- Strong-rep-nu has neither `★` nor recursion. But the role `Xᵢ := ★`
  plays there, a cell that lets one seal follow another, is played here
  by *alias* cells `β := α`, which is what seal chains `t ; seal X ;
  seal Y` are built from (Example 3b). A polymorphically recursive
  `f [X]` under `ΛX` would create a new alias cell per round.
- Conjecture: with `fix`, seal chains grow without bound and Ozaki et
  al.'s argument transfers. Without `fix`, every run terminates, so
  chains are bounded, but no bound is proved.

### 11. Hygiene: one live name per representation variable, and `WfCtx`

A well-formed context has no representation variable with two live
names (`Unique (names Δ)`).  Preservation takes `WfCtx Δ`.

**Example (the counterexample to premise-free preservation,
`notes/notes.md` "Metatheory"; rendered there):**

    Ξ = (α := ℕ),  Γ = (X ↦ α, Y ↦ α)
    (λx:ℕ. ΛZ. λy:ℕ. x) · 0
      --[Beta]-->
    ΛZ. λy:ℕ. (0 ⟪ ↓Z , id ℕ ⟫)

The redex types, because it mentions neither `X` nor `Y`.  Its
frame-exact contractum creates a boundary whose well-formedness demands
uniqueness, which the duplicate naming of `α` violates.  With names this is ordinary alpha-hygiene.  With
duplicates, `X` and `Y` would both spell `α`, and `≈` would not
determine a spelling (`same-target-unique` needs `Unique`).

**Builds on.** Distinct names are the standard side condition: BfA's
implicit `X ∉ Γ`, GSF's "a type name store is well-formed if all type
names are distinct", and STA's global α-conversion.

**New here.** Uniqueness is stated for *representation variables*
(each has at most one live name). That condition exists only because of
Decision 3.

---

### 12. Erasure: a run is a System F run with stutters

Strong-rep-nu is related back to plain System F by an **erasure**
`⌊M⌋_Δ`, a function of the context and the term (`Erasure.agda`):

    ⌊ΛX. N⌋_Δ          = ΛX. ⌊N⌋_under(X,α,Δ)
    ⌊νX:=A · L ⟨c⟩⌋_Δ  = ⌊L⌋_Δ [⌊A⌋_Δ]
    ⌊M ⟪ Θ , c ⟫⌋_Δ    = ⌊M⌋_inside(Δ,Θ)          conversions are dropped

A type variable erases to what it denotes. The name map takes it to a
representation variable, and the store resolves that, alias cells
included, to either a concrete type or a cell created by a `Λ`. Cells
created by a `Λ` become source type variables; there are `srcScope Ξ` of
them.

**Example:** the §1a run of Decision 1 and its erasure, state by state.
The erasures are computed by hand here; `P-rows` in
`notes/ErasureProbe.agda` checks the same classification by `refl`.

    run-time step          erasure of the new state
    ─────────────          ───────────────────────────────
    (start)                (ΛX. λx:X. x) [ℕ] · 7
      --[TyBeta]-->        (λx:ℕ. x) · 7                 one source step
      --[Wrap]-->          (λx:ℕ. x) · 7                 unchanged
      --[Beta]-->          7                             one source step
      --[Merge]-->         7                             unchanged
      --[Id]-->            7                             unchanged

The source run is `(ΛX. λx:X. x) [ℕ] · 7 ⟶ˢ (λx:ℕ. x) · 7 ⟶ˢ 7`. The
boundary machinery (`Wrap`, `Merge`, `Id`) is invisible after erasure.

**The theorems** (`ErasureTheorems.agda`, all proved, 2026-09-25):
- **Typing** (`erasure-typing`): if `WfCtx Δ` and `Δ ∣ Γₜ ⊢ M : A`,
  then `srcScope Ξ ∣ ⌊Γₜ⌋ ⊢ˢ ⌊M⌋ : ⌊A⌋`.
- **Simulation**, by rule:
  - a *stutter* (`Wrap`, `Merge`, `Id`, or a congruence around one)
    leaves the erasure unchanged (`erasure-stutter`);
  - every other step (`TyBeta`, `Beta`, `TyWrap`) is exactly one source
    step (`erasure-step`).

  Their consequences are `erasure-simulation`, `erasure-run` and
  `compiled-run-erases`: a compiled program's run erases to its own
  source run.
- **Reflection** (`erasure-reflection`): every source step of an
  erasure is matched by a run. Stutters terminate: a boundary weighs 1,
  an application weighs 3·(operator) + (operand) + 1, and `Wrap`,
  `Merge` and `Id` each strictly decrease the weight.
- **Compile then erase** (`erase-compile`): `⌊compile d⌋ = M`.

**Without it:** no theorem connects the calculus back to System F. The
boundaries could, for all the other theorems say, change a program's
result.

**Builds on.**
- **Blame for All's Prop. 1** is the model. Its erasure,
  `(νX:=A.t)° = t°[X:=A]`, preserves types, and "if s ⟼ s′ then either
  s° = s′° or s° ⟼ s′°". `erasure-simulation` is that statement for
  strong-rep-nu.
- **STA's erasure** (Lemma 5.8, Thm 5.10) is what licenses calling its
  embeddings "only a proof technique" (p.1054). Erasure does the same
  for strong-rep-nu's boundaries.

**New here.**
- **The split by rule.** Stutters are exactly `Wrap`, `Merge` and `Id`,
  and every other step is exactly one source step.
- **Reflection,** the converse, which Blame for All does not state.
- **Compile then erase is the identity.** Together with
  `compiled-run-erases`, this says that compiling System F to
  strong-rep-nu and running it is running System F, with the boundary
  steps interleaved.
- **Erasure through the name map and the store.** A type variable is
  resolved through its name and an alias chain, never by substitution
  at run time.

## Examples still to find or render

* A **single running example** that exercises Decisions 1–5 at once.
  §5a is the candidate (it *is* the pre-boundary counterexample, and its
  sixteen-step run is now shown in Decision 2), but its terms are wide.
  Check whether a smaller program shows mask-not-drop and frame-exact
  `Beta` together.
* A **color-preservation picture**: the §1a and §5a traces colored by
  scope map (standing preference: colored trace artifacts for scope and
  boundary material).  `notes/ColorPreservationProbe.agda` has a checked
  three-step run to start from.
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
  `TyWrap` shape (Decision 9). Arguably closer to strong-rep-nu than BfA.
- *Generativity and Dynamic Opacity for Abstract Types* (Rossberg, PPDP
  2003) **(read)**: λN's coercions, lexical-scope gate and
  type-directed coercion generation (Decisions 4, 6).
  - Rossberg identified, and solved, the effect behind Decision 1: once
    coercions are reduction rules, substituting into a coercion's
    annotation changes its meaning. His example is
    `P ≡ (Λα. λx:α. {x : α}⁻_{γ≈τ}) γ`, typed `γ → γ`, whose
    β-contractum `λx:γ. {x : γ}⁻_{γ≈τ}` is typed `γ → τ` (§3.2).
  - λN's solution is "unsealed types", which delay the substitution.
    Strong-rep-nu's is to never substitute into a conversion. The example
    is a good one to reuse in the paper, with credit.
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
  Low, Low Prices!* (Matthews & Ahmed, ESOP 2008) **(read, §§1–3)**.
  Term-level boundaries `τMS e` / `SMτ e` between System F and Scheme,
  reversing direction on function arguments (Decision 4). At type
  application, boundary annotations receive sealed instances `⟨α; τ⟩`
  while ML terms are substituted (Decision 1): the earliest "the
  boundary remembers the abstract variable" in this list. The text
  extraction is garbled; read the PDF.
- *Operational Semantics for Multi-Language Programs* (Matthews &
  Findler, POPL 2007) **(not read)**: the boundary construct itself.
- *Non-Parametric Parametricity* (Neis, Dreyer & Rossberg, ICFP 2009 /
  JFP 2011) **(read, §§2 and 5)**:
  - `new α≈τ in e` with a global type store `σ`, the store BfA §5.5
    contrasts itself with;
  - implicit isomorphism, "equal as classifiers, but not as data"
    (Decision 6);
  - the counterexample to naive generative translation, with the
    type-directed `Wr±` fix (Decision 9).
- *Is Space-Efficient Polymorphic Gradual Typing Possible?* (Ozaki,
  Sekiyama & Igarashi, Scheme 2021) **(read, §§1, 4–5)**: Theorem 6 and
  its polymorphic-recursion witness, behind the seal-chain conjecture in
  Decision 10.
- *Blame and Coercion: Together Again for the First Time* (Siek,
  Thiemann & Wadler, PLDI 2015) and *Space-Efficient Gradual Typing*
  (Herman, Tomb & Flanagan, TFP 2007 / HOSC 2010) **(not read)**: normal
  forms and "one coercion per value" (Decision 10).
- *Parameterized Cast Calculi and Reusable Meta-theory for Gradually
  Typed Lambda Calculi* (Siek & Chen, JFP 2021) **(read, previously;
  `notes/ParameterizedCastCalculi.md`)**.

**Gradual-parametricity papers for a survey paragraph:**
- *Gradual Parametricity, Revisited* (Toro, Labrada & Tanter, POPL 2019)
  **(read, §§1, 4–6)**: the conference version of GSF, with the same
  global type-name store and instantiation by substituting a fresh name.
  Its headline result, that the dynamic gradual guarantee is
  incompatible with parametricity, is gradual-specific; cite it alongside
  GSF rather than separately.
- *Plausible Sealing for Gradual Parametricity* (Labrada, Toro, Tanter &
  Devriese, OOPSLA 2022) **(read, §§1–3)**:
  - the only *lexically scoped* sealing in the gradual line (Funky);
  - its critique of global seals (Decisions 1 and 8);
  - its instantiation environments `?^{X:F}`, the nearest analogue of
    the name map (Decision 3);
  - its key lemmas are mechanized in Agda.
- The rest of this group is **not read**:
  - *Consistent Subtyping for All* (Xie, Bi & Oliveira, ESOP 2018): the
    "separate gradual typing from polymorphism" policy that λC∀mp and
    PolyG follow;
  - *Parametricity versus the Universal Type* (Devriese, Patrignani &
    Piessens, POPL 2018), the equivalence-breaking result Plausible
    Sealing cites against global seals.

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
  - Consequence, now done: strong-rep-nu has the corresponding **erasure
    theorem** into System F, as BfA (Prop. 1) and STA (Lemma 5.8, Thm
    5.10) do. It is Decision 12.
- **Residual theory** (Lévy's labelled λ-calculus; Huet & Lévy). The
  `Residuals` relation behind `ScopeMapPreservation` is a residual
  tracing, and naming it as such would help readers.
- **Name generation** (Odersky's λν, POPL 1994; Pitts & Stark's
  ν-calculus, 1993), for the `ν` binder and fresh allocation.
- **Intensional polymorphism** (Harper & Morrisett, POPL 1995; Crary,
  Weirich & Morrisett, ICFP 1998), for the terminology clash on
  "representation".

**Where the PDFs are:** every paper marked (read) above, and every
paper named in the abbreviation list, is in the repo-level `papers/`
directory (index: `papers/README.md`), including the five read on
2026-09-25: Matthews & Ahmed ESOP'08, Neis–Dreyer–Rossberg,
Ozaki et al. Scheme'21, *Gradual Parametricity, Revisited* and
*Plausible Sealing*.  Everything still marked (not read) has no PDF in
the repo.

## Resolved questions (Jeremy, 2026-09-25)

* **Ordering:** narrative order (this revision).
* **Related work:** lead with STA for color and λB for mechanism.
* **History:** the short form, one line of "we tried X; it fails on
  example E" per decision.
* **Decisions 7 and 8** (value restriction, global store) count as design
  decisions.
* **Erasure theorem:** statements reviewed and all proved; merged to `main`
  (2026-09-25).

## Open questions for the draft

None at the moment.
