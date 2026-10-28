# Single-entry boundaries — an on-paper sketch (2026-10-28)

Status: SKETCH, not mechanized.  Nothing here is checked in Agda; every
trace below is derived by hand unless it says otherwise.  The purpose is
to locate νF (`paper/main.tex`) in the design space by building its
nearest neighbour: the same calculus with every boundary restricted to
ONE scope entry, values allowed to be towers of boundaries, and no
`Merge`.  Call it **νF₁**.

Notation is the paper's, in Unicode: a boundary is `[ε] M ⟨c⟩`, a
nested tower `[ε₁] [ε₂] M ⟨c₂⟩ ⟨c₁⟩` lists its scopes outermost first
and its conversions innermost first, `−X` is `seal X`, `+X` is
`unseal X`, and `ν X:=A. (L X)⟨c⟩` is instantiation.

## 1. Why ask

νF has two features that go together:

* a boundary scope `δ` is a LIST of entries `+X^α` / `−X^α`, and
* `Merge` fuses `[δ₂] ([δ₁] U ⟨t₁⟩) ⟨c₁⟩` into `[δ₂ ++ δ₁] U ⟨d⟩` by
  composing the two conversions, so a value carries at most one
  boundary.

Their history is not a single argument.  The list form came first
(2026-09-03, design point D07 in `notes/DesignPoints.md`), as the repair
for the per-variable design's failure (D05, "Example 8, historical" in
`notes/old/notes-v1.md`): there a conceal TRUNCATED its context at `X`,
dropping every variable bound after `X`, and `TyWrapCncl` pushed a type
argument into such a truncated context.  `Merge` came later
(2026-09-24, `notes/MergeSketch.md`), to keep values one boundary deep.

νF no longer truncates: `−X^α` removes `X` and nothing else
(`−X(Δ)` in the paper's Figure "Context Operations"), and a type
argument is never pushed inward (it is recorded as `+X^α`).  So the
original reason for lists is gone, and the question is whether
single-entry boundaries, with everything else as in νF, are enough.

## 2. Syntax

Types, representation types and type contexts are the paper's,
unchanged:

    ι      ::=  Int | Bool
    A,B,C  ::=  X | ι | A → B | ∀X. A
    R,S    ::=  α | X | ι | R → S | ∀X. R
    Δ      ::=  [] | Δ, α | Δ, α:=R | Δ, X:=α

A **scope entry** replaces the scope list:

    ε  ::=  +X^α  |  −X^α

    −ε:   −(+X^α) = −X^α        −(−X^α) = +X^α

Conversions are ONE sort, with no chains:

    c,d  ::=  id(A) | c → d | ∀X. c | −X | +X

The paper's three sorts (middle, tail, conversion) and its chains
`t ; −X` and `+X ; c` exist because `Merge` composes conversions: the
compiler's `reveal`/`conceal` (`Conversion.agda` §4) write only bare
seals and unseals, and `⨟` is what builds a chain.  νF₁ has no `Merge`
and no rule that builds a conversion from pieces — Wrap and TyBeta give
a boundary a SUB-conversion (a domain, a codomain, a `∀` body), Cancel
and Id delete layers, and Reach writes identities — so no reachable term
has a chain, and the grammar drops them along with the simplifying
constructors `⨾`, `Id?` and `+X(t)`.  What is lost is expressiveness for
hand-written boundaries: `(c → d) ; −X` must be written as two layers.

Terms:

    L,M,N  ::=  k | op(M⃗) | x | λx:A. N | L M
              | ΛX. V | ν X:=A. (L X)⟨c⟩ | [ε] M ⟨c⟩

    Simples  U    ::=  k | λx:A. N | ΛX. V
    Inert    i    ::=  id(X) | c → d | ∀X. c | −X
    Values   V,W  ::=  U | [ε] V ⟨i⟩      if Tidy(ε, V, i)

`Tidy(ε, V, i)` excludes the one value-shaped redex of §4:

    Tidy(ε, V, i)  =  ¬ (V = [−ε] W ⟨i′⟩)                 (no Cancel pair)

So a value is a TOWER: a simple value under any number of inert
boundaries, no two adjacent ones inverse.

## 3. Type system

Interior, conversion context and coherence, specialised from the
paper's `δ(Δ)`, `δ⁺(Δ)` and `Δ ⊢ δ`:

    (+X^α)(Δ)  =  Δ, X:=α              (+X^α)⁺(Δ)  =  Δ, X:=α
    (−X^α)(Δ)  =  −X(Δ)                (−X^α)⁺(Δ)  =  Δ

    Δ ⊢ +X^α   if  α ∈ Δ,  X:=β ∉ Δ for every β,  Y:=α ∉ Δ for every Y
    Δ ⊢ −X^α   if  X:=α ∈ Δ

The conversion context is always the larger of the two sides: the
interior for a `+` entry, the exterior for a `−` entry.

**Conversions** `Δ ∣ ε ⊢ c : R ⇒ S` — the paper's rules with `δ := [ε]`:

    ───────────────────────── (id-ι)
    Δ ∣ ε ⊢ id(ι) : ι ⇒ ι

    X:=α ∈ Δ
    ───────────────────────── (id-X)
    Δ ∣ ε ⊢ id(X) : α ⇒ α

    Δ ∣ −ε ⊢ c : R′ ⇒ R      Δ ∣ ε ⊢ d : S ⇒ S′
    ──────────────────────────────────────────── (fun)
    Δ ∣ ε ⊢ c → d : R → S ⇒ R′ → S′

    Δ, α, X:=α ∣ ε ⊢ c : R[X↦α] ⇒ S[X↦α]          X, α ∉ Δ
    ──────────────────────────────────────────── (all)
    Δ ∣ ε ⊢ ∀X. c : ∀X. R ⇒ ∀X. S

    α:=Δ(A) ∈ Δ                             α:=Δ(A) ∈ Δ
    ─────────────────────────── (seal)      ─────────────────────────── (unseal)
    Δ ∣ −X^α ⊢ −X : Δ(A) ⇒ α                Δ ∣ +X^α ⊢ +X : α ⇒ Δ(A)


The changes from the paper: the premise `±X^α ∈ δ` becomes "the entry
IS `±X^α`", and the two chain rules (`seal-seq`, `unseal-seq`) are
gone.  In a domain the entry is inverted, so a
boundary `[+X^α]` may unseal `X` in covariant positions and seal it in
contravariant ones, and `[−X^α]` the other way round.

**Terms** `Δ ∣ Γ ⊢ M : A` — the paper's rules; the two that mention
scopes become:

    Δ ⊢ A    Δ ∣ Γ ⊢ L : ∀X. C    Δ′ ∣ +X^α ⊢ c : Δ′(C) ⇒ Δ(B)    Δ ⊢ B
    ──────────────────────────────────────────────────────────────── (ν)
    Δ ∣ Γ ⊢ ν X:=A. (L X)⟨c⟩ : B          where Δ′ = Δ, α:=Δ(A), X:=α

    Δ ⊢ ε    ε(Δ) ∣ [] ⊢ M : A    ε⁺(Δ) ∣ ε ⊢ c : ε(Δ)(A) ⇒ Δ(B)    Δ ⊢ B
    ──────────────────────────────────────────────────────────────── (boundary)
    Δ ∣ Γ ⊢ [ε] M ⟨c⟩ : B

(`ν` is unchanged: its scope was already the single entry `+X^α`.)

## 4. Reduction

Frames are the paper's, with `[ε] □ ⟨c⟩` in place of `[δ] □ ⟨c⟩`, and
`([ε] □ ⟨c⟩)(Δ) = ε(Δ)`.  A tower prefix is abbreviated
`[ε₁ … εₖ] M ⟨cₖ … c₁⟩` = `[ε₁] … [εₖ] M ⟨cₖ⟩ … ⟨c₁⟩`.

    Δ ⊢ op(V⃗)  ⟶  ⟦op⟧(V⃗)                                         (Delta)
    Δ ⊢ (λx:A. N) V  ⟶  N[x := V]                                   (Beta)

    Δ ⊢ [ε] V ⟨c → d⟩ W  ⟶  [ε] (V ([−ε] W ⟨c⟩)) ⟨d⟩                (Wrap)

    Δ ⊢ ν X:=A. (V X)⟨d⟩  ⟶  [+X^α] (V • X) ⟨d⟩   ⊣ α:=Δ(A)         (TyBeta)
        where  (ΛX. N) • X        =  N
               ([ε] V ⟨∀X. c⟩) • X  =  [ε] (V • X) ⟨c⟩

    Δ ⊢ [ε] k ⟨id(ι)⟩  ⟶  k                                          (Id)

    Δ ⊢ [ε] ([−ε] V ⟨c₁⟩) ⟨c₂⟩  ⟶  V                                 (Cancel)

    Δ ⊢ [+X^α] [ε₁ … εₖ] [−X^α] V ⟨−X⟩ ⟨id(X) … id(X)⟩ ⟨+X⟩
      ⟶ [+X^α] [ε₁ … εₖ] [−X^α] V ⟨Id(A)⟩ ⟨Id(A) … Id(A)⟩ ⟨Id(A)⟩       (Reach)
        if k ≥ 1, α:=R ∈ Δ, and Δᵢ ⊢ A with Δᵢ(A) = R for the outer
        layer's interior Δ₀ and every intermediate interior Δ₁ … Δₖ
        (Id(A) is the paper's identity at A)

    Δ ⊢ F[M]  ⟶  F[M′] ⊣ ξ      if F(Δ) ⊢ M ⟶ M′ ⊣ ξ                (ξ)

What each rule replaces in νF:

* **Wrap** and **TyBeta** are νF's, generalised to towers.  νF's Wrap
  needs a SIMPLE body and its TyWrap a `Λ` one level down; here the body
  is any value.  TyBeta absorbs TyWrap: `•` strips one `∀` from every
  layer of a `∀`-typed tower (an inert conversion with a `∀` target is
  `∀X. c`, so every layer has one).  Each layer's `∀`-binder is renamed
  to the fresh `X`; since `X` is fresh, no layer's entry mentions it,
  and `X` stays nameable through every layer.  (In de Bruijn form this
  is where the old `Nu-⟪⟫` needed an alias cell per layer and a
  respelled reveal — 2026-09-20 in `notes/DECISIONS.md`.  With names
  nothing moves.)
* **Id** is νF's.
* **Cancel** is new, and is what replaces `Merge` for inverse pairs.  It
  needs no composition at run time: see obligation O1.
* **Reach** is new: an unseal that meets its seal through `k` layers
  carrying `id(X)`.  Each intermediate layer's type changes from `X` to
  a spelling of `X`'s payload, so the premise asks that every
  intermediate interior can spell it.  A `+` layer always can (it only
  adds names, and a `+` entry cannot re-bind a name already in scope);
  a `−Y^β` layer can unless the payload needs `β`, the representation
  it hides.  One type `A` serves every layer (O4).  It needs `k ≥ 1`
  (at `k = 0` the two layers are a Cancel pair).

There is no `Merge`, no conversion composition `⨟`, and no chain.

**No rule removes a layer that is not an inverse pair or a constant's
identity.**  An earlier draft of this sketch had a rule `Hide`,
`[−Y^β] V ⟨c⟩ ⟶ V` for an identity `c`, so that Reach would only ever
cross `+` layers.  It was deleted because it breaks color preservation
(`ColorPreservation.agda`): every hole in `V` sat in `−Y(Δ′)` before the
step and in `Δ′` after it, so it gains `Y` — reduction changing which
type variables a subterm can see, which the design law forbids.  The
cost is the gap in O2.

## 5. Examples (hand-derived)

Store allocations are shown with `⊣`; every run is at the empty
context.

### 5a. `K` — §1b of `Examples.agda`

    ((ΛX. λf:∀Y. Y→Bool. f [X]) [Bool] (ΛZ. λz:Z. true)) false

νF: 9 steps (TyBeta, Wrap, Beta, TyWrap, Merge, Merge, Wrap, Beta, Id —
rendered by `showRun 0 9 K₀-⊢`).  νF₁: 11 steps.  After the TyBeta that
instantiates `f` (⊣ β:=α), the value is the tower

    [+X^α] [+Y^β] [−X^α] (λz:Y. true) ⟨id(Y) → id(Bool)⟩ ⟨−Y → id(Bool)⟩ ⟨−X → id(Bool)⟩

three Wraps send `false` in (the argument becomes
`[+X^α] [−Y^β] [−X^α] false ⟨−X⟩ ⟨−Y⟩ ⟨id(Y)⟩`), Beta discards it, and
three Ids peel `true ⟨id(Bool)⟩ ⟨id(Bool)⟩ ⟨id(Bool)⟩`.

### 5b. `K` returning its argument — a Cancel pair inside a tower

    ((ΛX. λf:∀Y. Y→Y. f [X]) [Bool] (ΛZ. λz:Z. z)) false        : Bool

νF: 11 steps, three Merges (rendered with `showRun` on a scratch
module; the last Merge produces
`[+X^α, +Y^β, −X^α, +X^α, −Y^β, −X^α] false ⟨id(Bool)⟩`).

νF₁, 11 steps.  The first eight are as in 5a (with `+Y`/`+X` codomains
in place of `id(Bool)`) and end at the six-layer tower

    [+X^α] [+Y^β] [−X^α] [+X^α] [−Y^β] [−X^α] false ⟨−X⟩ ⟨−Y⟩ ⟨id(Y)⟩ ⟨id(Y)⟩ ⟨+Y⟩ ⟨+X⟩

with interiors {X}, {X,Y}, {Y}, {X,Y}, {X}, ∅ (outermost first) and
store α:=Bool, β:=α.  Then

    → Cancel   (layers 3–4)    [+X^α] [+Y^β] [−Y^β] [−X^α] false ⟨−X⟩ ⟨−Y⟩ ⟨+Y⟩ ⟨+X⟩
    → Cancel   (layers 2–3)    [+X^α] [−X^α] false ⟨−X⟩ ⟨+X⟩
    → Cancel                   false

This is the run that motivated the sketch.  Without Cancel the term is
stuck: the unseal `+Y` (layer 2) must meet the seal `−Y` (layer 5), and
the obvious "cancel at a distance" contractum is ILL TYPED — it turns
layer 3's `id(Y)` into an identity at `Y`'s payload `X`, and layer 3
is `[−X^α]`, whose interior {Y} cannot name `X`.  Here a variable (`Y`)
is bound to another (`X`) that has gone out of scope, which is exactly
the case Reach's premise excludes: layer 3's interior cannot spell `Y`'s
payload, so Reach does not apply.  Cancel on layers 3–4 is what fires;
the layer-2 boundary's body is then not a value (it is not Tidy), so
`ξ` reaches it first.

### 5c. An unseal reaching its seal through a later reveal

    (ΛX. λx:X. (ΛY. λ_:Int. x) [Bool] 0) [Int] 3                : Int

νF: typed and run by `showRun` on a scratch module, 11 steps, three
Merges.  νF₁:

    → TyBeta ⊣ α:=Int   [+X^α] (λx:X. ν Y:=Bool. ((ΛY. λ_:Int. x) Y)⟨id(Int) → id(X)⟩ 0) ⟨−X → +X⟩ 3
    → Wrap              [+X^α] ((λx:X. …) ([−X^α] 3 ⟨−X⟩)) ⟨+X⟩
    → Beta              [+X^α] (ν Y:=Bool. ((ΛY. λ_:Int. [−X^α] 3 ⟨−X⟩) Y)⟨id(Int) → id(X)⟩ 0) ⟨+X⟩
    → TyBeta ⊣ β:=Bool  [+X^α] ([+Y^β] (λ_:Int. [−X^α] 3 ⟨−X⟩) ⟨id(Int) → id(X)⟩ 0) ⟨+X⟩
    → Wrap              [+X^α] [+Y^β] ((λ_:Int. …) ([−Y^β] 0 ⟨id(Int)⟩)) ⟨id(X)⟩ ⟨+X⟩
    → Id                [+X^α] [+Y^β] ((λ_:Int. [−X^α] 3 ⟨−X⟩) 0) ⟨id(X)⟩ ⟨+X⟩
    → Beta              [+X^α] [+Y^β] [−X^α] 3 ⟨−X⟩ ⟨id(X)⟩ ⟨+X⟩
    → Reach             [+X^α] [+Y^β] [−X^α] 3 ⟨id(Int)⟩ ⟨id(Int)⟩ ⟨id(Int)⟩
    → Id, Id, Id        3

11 steps.  The `[+Y^β] … ⟨id(X)⟩` layer cannot be dropped (its interior
is larger than its exterior, and the term beneath it may mention `Y`)
and cannot be crossed by pushing `+X` inward (its entry licenses only
`Y`), so some rule of Reach's kind is needed.  Its interior {X, Y} spells
`X`'s payload as `Int`.

## 6. Obligations (none discharged)

* **O1 — an inverse pair composes to an identity.**  For
  `[ε] ([−ε] V ⟨c₁⟩) ⟨c₂⟩` well typed, the composite of `c₁` and `c₂`
  is an identity, so the pair's interior type equals its exterior type
  and Cancel preserves types.  Argument: the pair's exterior and
  interior contexts have the same bindings, so the composite's two
  endpoint types do not mention `X` (for `[+X^α]` outside, the exterior
  cannot name `X`; for `[−X^α]` outside, both sides do and the two
  spellings agree); a normal conversion between `X`-free endpoints
  under a scope that licenses only `X` has no seal or unseal (every
  seal or unseal of `X` puts `X` at an endpoint, since there are no
  chains), so it is all `id` leaves, i.e. an identity.  To check:
  the `∀` case, and that the `[−X^α][+X^α]` order needs only exchange
  (the interior `−X(Δ), X:=α` reorders `Δ`).
* **O2 — THE GAP: an unseal blocked by a hiding layer.**  Reach does
  not apply to
  `[+X^α] [ε₁ … εₖ] [−X^α] V ⟨−X⟩ ⟨id(X) … id(X)⟩ ⟨+X⟩`
  when some εᵢ is `−Y^β`, `X`'s payload needs `β`, and the layer is not
  half of a Cancel pair.  No other rule applies either, so such a
  state is STUCK.  Either show it unreachable from a closed source
  program, or exhibit one — which would separate νF₁ from νF, whose
  `Merge` keeps the `−Y^β` entry in the merged scope and needs no
  spelling of the payload at that layer.  5b reaches the shape's
  ingredients (layer 3 is `[−X^α]` carrying `id(Y)`, and `Y`'s payload
  is `X`) but there the layer is half of a Cancel pair.
* **O3 — progress at an active top layer.**  The active conversions are
  `id(ι)` (Id) and `+X`.  For `[+X^α] V ⟨+X⟩`, `V` is a tower
  at type `X`; its top inert conversion has target `X`, so it is
  `−X` under `[−X^α]` (Cancel), or `id(X)` under some `[±Y^β]`,
  `Y ≠ X` (a `±X` layer cannot carry `id(X)`: `+X` would make `X`
  unnameable outside, `−X` inside).  Walking down, every layer to the
  seal carries `id(X)`, and Reach applies unless a `−Y` layer cannot
  spell the payload — the gap O2.  This case analysis is the whole
  progress argument for unseals.
* **O4 — Reach preserves types, with ONE type `A`.**  After the step
  every layer from the inner `[−X^α]` out to the outer `[+X^α]` has
  interior and exterior type spelling `R`, so each `Id(A)` types at
  `R ⇒ R`; the outer layer's exterior type is `A` read in `Δ`, which
  is legitimate because `R`, a payload of `α`, does not contain `α`,
  so `A` does not mention `X`.  Why one `A` suffices: coherence gives
  each representation variable at most one name in a context; a `+`
  layer cannot re-bind a name already in scope, so it renames nothing
  `A` uses; and a `−` layer that removed a name `A` uses would make
  `R` unspellable there, failing the premise.  So whenever the premise
  holds, every layer spells `R` the same way.
* **O5 — determinism.**  Reach requires `k ≥ 1`; Cancel takes `k = 0`.
  A Cancel pair strictly inside a Reach redex makes the enclosing
  layer's body a non-value, so the Reach redex is not one (its layers
  must be values) until the pair is gone.
* **O6 — TyBeta on towers.**  `V • X` is well typed at the new interior:
  each layer's conversion `∀X. c` was checked with `X` bound by its own
  `∀` (rule `all`) and is now checked with `X` bound by the outer
  `+X^α`.  Needs: the representation variable of the `∀` rule and `α`
  play the same role for `c`, which is the substitution lemma the paper
  already relies on for TyWrap.
* **O7 — color preservation.**  `ColorPreservation.agda`'s statement
  should transfer rule by rule.  Wrap and TyBeta make νF's moves.
  Reach and Id change conversions only (Id's body is a constant, with no
  holes).  Cancel with `[+X^α]` outside leaves `V` at `−X(Δ, X:=α) = Δ`
  on both sides of the step; with `[−X^α]` outside, `V` moves from
  `−X(Δ), X:=α` to `Δ`, the same names in another order — fine for the
  length form, and for the positional `ScopeMapPreservation` it needs
  the reordering (which matters only in de Bruijn form).

## 7. Where this puts νF in the design space

The axes, with the points that have been built or sketched:

| point | entries per boundary | merging | what a hide does | payloads | instantiation |
|---|---|---|---|---|---|
| D02 per-variable wrappers (2026-09-01) | one | Cancel, Drop, Commute | truncates the context at `X` | copied types | pushes the type argument in (`TyWrapCncl`) |
| D07 v1 combined boundary (2026-09-03) | list | `⊕` | truncates at the deepest conceal | copied types | records it as a reveal |
| strong-rep-nu before 2026-09-24 | list | `CancelR`, `IdPush` (stacks otherwise) | does not truncate (D34 onward) | representation variables | records it |
| **νF** (`paper/main.tex`) | list | `Merge` (one boundary per value) | removes `X` only | representation variables | records it |
| **νF₁** (this sketch) | one | `Cancel`, `Reach` (towers) | removes `X` only | representation variables | records it |

D02 failed because of its truncation and its instantiation rule, not
because it had one entry per boundary (`notes/old/notes-v1.md`,
"Example 8, historical").  νF₁ keeps νF's answers to both and changes
only the entry count, so it isolates what lists and `Merge` buy:

* **For νF:** values are one boundary deep, so canonical forms, Wrap and
  TyWrap look at one boundary; runs are shorter (5a: 9 against 11); a
  seal chain records a path through several variables (`−X ; −Y`) in
  one conversion.
* **For νF₁:** no composition at run time, no chains, and each
  permission check is "the entry is `±X^α`"; the conversion context is
  one side of the boundary, never a union.  The price is two
  tower-tidying rules, one of them non-local (Reach), a progress
  argument (O3) that walks down a tower, and the gap O2.
* **Color preservation is where lists earn their keep.**  Under the
  design law a layer may disappear only if no hole beneath it would see
  a different set of names.  With one entry per boundary that leaves
  inverse pairs (Cancel) and constants (Id); every other hiding layer
  stays in the tower for good, and an unseal that must pass one whose
  interior cannot spell the payload is stuck (O2).  νF's `Merge` never
  deletes an entry, so it can fuse such a layer into its neighbours
  without changing any hole's scope.

Other points the axes suggest, not sketched: one entry per boundary
with merge-on-construction (`notes/MergeSketch.md`, question 2, option
M2); lists without any merging (stacks of multi-entry boundaries, the
pre-`Merge` calculus but with Cancel and Reach in place of `CancelR`
and `IdPush`).

## 8. Next steps

1. Run the corpus and the stress programs through a νF₁ evaluator (a
   checker for `Tidy` towers and the rules of §4), looking for a stuck
   state — the cheapest test of O2 and O3.
2. If none is stuck, prove O1 on paper, then decide whether to
   mechanize.
