# Single-entry boundaries — an on-paper sketch (2026-10-28)

Status: SKETCH, not mechanized.  Nothing here is checked in Agda; every
trace below is derived by hand unless it says otherwise.  §6 proves the
obligations on paper, except O2 (open); proving O1 refuted one order of
the first Cancel rule, which now carries a premise.  The rule set is
MINIMAL for progress: Cancel only for `[−X^α] [+X^α]` pairs, and Reach
from `k = 0` (§4).  The purpose is
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

    Tidy(ε, V, i)  =  ¬ ([ε] V ⟨i⟩ is a Cancel redex)

So a value is a TOWER: a simple value under any number of inert
boundaries, with no `[−X^α] [+X^α]` pair that Cancel would remove.  A
`[+X^α] [−X^α]` pair is never a redex, and a `[−X^α] [+X^α]` pair whose
interior and exterior types differ is not one either (§6, O1); both may
sit inside a value.

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

    Δ ⊢ [−X^α] ([+X^α] V ⟨c₁⟩) ⟨c₂⟩  ⟶  V                           (Cancel)
        if [+X^α] V ⟨c₁⟩ is a value and the pair's interior and
        exterior types agree: Δ₂(A) = Δ(B), where Δ₂ = −X(Δ), X:=α,
        V : A, and the redex : B

    Δ ⊢ [+X^α] [ε₁ … εₖ] [−X^α] V ⟨−X⟩ ⟨id(X) … id(X)⟩ ⟨+X⟩
      ⟶ [+X^α] [ε₁ … εₖ] [−X^α] V ⟨Id(A)⟩ ⟨Id(A) … Id(A)⟩ ⟨Id(A)⟩       (Reach)
        if k ≥ 0, the tower under the outer layer is a value, α:=R ∈ Δ,
        and Δᵢ ⊢ A with Δᵢ(A) = R for the outer layer's interior Δ₀
        and every intermediate interior Δ₁ … Δₖ
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
* **Cancel** is new: it removes a `[−X^α] [+X^α]` pair whose two
  sides have the same type, with no composition at run time.  Only this
  order is needed, and only for progress: in 5b such a pair blocks
  Reach.  The pair's conversions may compose to an unseal rather than
  an identity, hence the types-agree premise (O1, example 5d).  The
  other order, `[+X^α] [−X^α]`, would be sound without a premise (O1's
  lemma) but progress never needs it: an unseal directly over its seal
  is Reach with `k = 0`, and any other such pair is a value.
* **Reach** is new: an unseal that meets its seal through `k` layers
  carrying `id(X)`.  Each intermediate layer's type changes from `X` to
  a spelling of `X`'s payload, so the premise asks that every
  intermediate interior can spell it.  A `+` layer always can (it only
  adds names, and a `+` entry cannot re-bind a name already in scope);
  a `−Y^β` layer can unless the payload needs `β`, the representation
  it hides.  One type `A` serves every layer (O4).  At `k = 0` the
  premise always holds, since the seal's source is already spelled in
  `Δ`; the step keeps both layers with identity conversions, which Id
  later peels at a base type.

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

νF₁, 15 steps.  The first eight are as in 5a (with `+Y`/`+X` codomains
in place of `id(Bool)`) and end at the six-layer tower

    [+X^α] [+Y^β] [−X^α] [+X^α] [−Y^β] [−X^α] false ⟨−X⟩ ⟨−Y⟩ ⟨id(Y)⟩ ⟨id(Y)⟩ ⟨+Y⟩ ⟨+X⟩

with interiors {X}, {X,Y}, {Y}, {X,Y}, {X}, ∅ (outermost first) and
store α:=Bool, β:=α.  Then

    → Cancel        (layers 3–4)   [+X^α] [+Y^β] [−Y^β] [−X^α] false ⟨−X⟩ ⟨−Y⟩ ⟨+Y⟩ ⟨+X⟩
    → Reach, k = 0  (layers 2–3)   [+X^α] [+Y^β] [−Y^β] [−X^α] false ⟨−X⟩ ⟨id(X)⟩ ⟨id(X)⟩ ⟨+X⟩
    → Reach, k = 2  (layers 1–4)   [+X^α] [+Y^β] [−Y^β] [−X^α] false ⟨id(Bool)⟩ ⟨id(Bool)⟩ ⟨id(Bool)⟩ ⟨id(Bool)⟩
    → Id × 4                       false

The `k = 2` Reach crosses `[+Y^β]` (interior {X, Y}) and `[−Y^β]`
(interior {X}); both spell `X`'s payload as `Bool`.

This is the run that motivated the sketch.  Without Cancel the term is
stuck: the unseal `+Y` (layer 2) must meet the seal `−Y` (layer 5), and
the obvious "cancel at a distance" contractum is ILL TYPED — it turns
layer 3's `id(Y)` into an identity at `Y`'s payload `X`, and layer 3
is `[−X^α]`, whose interior {Y} cannot name `X`.  Here a variable (`Y`)
is bound to another (`X`) that has gone out of scope, which is exactly
the case Reach's premise excludes: layer 3's interior cannot spell `Y`'s
payload, so Reach does not apply.  Cancel on layers 3–4 is what fires
(their types agree: `Y` on both sides); the layer-2 boundary's body is
then not a value (it is not Tidy), so `ξ` reaches it first.  This is why
progress needs the `[−X^α] [+X^α]` order of Cancel.

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

### 5d. An inverse pair that must NOT cancel

    ((ΛX. λx:X. λg:(Int→X)→(Int→Int). g (λn:Int. x)) [Int] 5 (λh:Int→Int. h)) 0     : Int

νF: 14 steps, three Merges (rendered with `showRun` on a scratch
module).  Its seventh state is the tower

    [+X^α] [−X^α] [+X^α] (λn:Int. W) ⟨id(Int) → +X⟩ ⟨id(Int) → id(Int)⟩ ⟨id(Int) → id(Int)⟩ 0

with `W = [−X^α] 5 ⟨−X⟩` and α:=Int — the same in νF₁, whose first
seven steps (TyBeta, Wrap, Beta, Wrap, Beta, Wrap, Beta) match νF's.
Layers 2–3 are a `[−X^α] [+X^α]` pair: the inner value has type
`Int → X`, the pair's exterior type is `Int → Int`, and its conversions
compose to `id(Int) → +X`.  νF's first Merge turns layers 2–3 into ONE
boundary with scope `[−X^α, +X^α]` and conversion `id(Int) → +X`.

With Cancel WITHOUT the types-agree premise, layers 2–3 are a redex,
so layer 2's boundary is not a value and ξ reduces it first, to
`[+X^α] (λn:Int. W) ⟨id(Int) → id(Int)⟩`: a body of type `Int → X`
under a conversion whose source is `Int → Int` — ill typed (O1).

With the premise, the whole tower is a value (layers 1–2 are a
`[+X^α] [−X^α]` pair, which is never a redex), and the run finishes in
19 steps:

    → Wrap, Id          0 crosses layer 1; its [−X^α] 0 ⟨id(Int)⟩ wrapper drops
    → Wrap, Id          … layer 2
    → Wrap, Id          … layer 3, whose codomain is +X
    → Beta              [+X^α] [−X^α] [+X^α] [−X^α] 5 ⟨−X⟩ ⟨+X⟩ ⟨id(Int)⟩ ⟨id(Int)⟩
    → Reach, k = 0      [+X^α] [−X^α] [+X^α] [−X^α] 5 ⟨id(Int)⟩ ⟨id(Int)⟩ ⟨id(Int)⟩ ⟨id(Int)⟩
    → Id × 4            5

## 6. Obligations, proved on paper (2026-10-28)

Summary.  O1 and O3–O7 are proved below for the minimal rule set of
§4.  Proving O1 found that a `[−X^α] [+X^α]` pair can compose to an
unseal, which is why Cancel carries a premise.  O2 is a reachability
question and stays open.  Everything here is by hand.

### 6.0 Conventions and supporting lemmas

A context is **well named** if each name `X` has at most one binding
`X:=α` and each representation variable `α` is named by at most one
`X`.  Runtime contexts are well named, and the type system keeps them
so:

* **L1 (scopes keep contexts well named).**  If `Δ` is well named and
  `Δ ⊢ ε`, then `ε(Δ)` and `ε⁺(Δ)` are well named.  For `+X^α`,
  coherence says neither `X` nor `α` is named in `Δ`; for `−X^α`, a
  binding is removed.  The `all` and `Λ` rules add `X:=α` with both
  fresh.
* **L2 (spelling is injective).**  If `Γ` is well named, `Γ ⊢ A`,
  `Γ ⊢ B` and `Γ(A) = Γ(B)`, then `A = B` (up to renaming of bound
  variables).  Induction on `A`: at a variable, the two names denote the
  same representation and `Γ` names it once; the other cases are
  structural (under `∀X`, `X` is unnamed and maps to itself).
  Consequently a representation type `R` has at most one SPELLING in a
  well-named `Γ`, written `sp_Γ(R)` when it exists.
* **L3 (exchange).**  Typing depends on a context's name bindings only
  through the map `X ↦ α`, so moving a binding `X:=α` to another
  position (keeping it after the entry that allocates `α`) preserves
  every judgement.
* **L4 (refinement and renaming).**  Replacing an abstract `α` by
  `α:=R`, or renaming a representation variable to a fresh one,
  preserves every judgement.  No rule needs `α` to be abstract; `seal`
  and `unseal` need a payload, so adding one only enables them.
* **L5 (identity).**  If `Γ ⊢ A` then `Γ ∣ ε ⊢ Id(A) : Γ(A) ⇒ Γ(A)` for
  either entry `ε`.  `Id(A)` contains no seal or unseal; at `∀X. A` the
  `all` rule's body context `Γ, α′, X:=α′` spells `A` as
  `Γ(∀X.A)`'s body with `X ↦ α′`.
* **L6 (canonical forms).**  An inert conversion's target is a
  representation variable (`id(X)`, `−X`), an arrow (`c → d`) or a `∀`
  (`∀X. c`); never a base type.  A simple value has a base, arrow or
  `∀` type.  Hence, for a value `V` with `Γ ⊢ V : A`:
  * `A = ι`: `V` is a constant;
  * `A = A₁ → A₂`: `V` is a `λ`, or a tower whose top conversion is
    `c → d`;
  * `A = ∀X. C`: `V` is a `Λ`, or a tower whose top conversion is
    `∀X. c` over a value of `∀` type (by induction every layer has a
    `∀` conversion, so `V • X` is defined);
  * `A = X` with `X:=α ∈ Γ`: `V` is a tower whose top conversion has
    target `α` — `id(X)`, or `−X` under the entry `−X^α` (the only
    name for `α` in a well-named context is `X`).

### O1 — Cancel preserves types (proved, given its premise)

**Proof.**  Redex `[−X^α] ([+X^α] V ⟨c₁⟩) ⟨c₂⟩ : B` at `Δ`, with
`X:=α ∈ Δ`.  The outer interior is `−X(Δ)`; the inner layer's interior
is `Δ₂ = −X(Δ), X:=α`, and `Δ₂ ⊢ V : A`.  `Δ₂` has the same name map
as `Δ` (only the position of `X:=α` differs), so L3 gives
`Δ ⊢ V : A` and `Δ₂(A) = Δ(A)`.  The premise `Δ₂(A) = Δ(B)` then gives
`Δ(A) = Δ(B)`, and L2 gives `A = B`.  So the contractum `V` has type
`B` at `Δ`.  ∎

**Why the premise.**  Without it the step is not type-preserving.  `V`
sits where `X` is named, so its type may mention `X`, and the two
conversions need not compose to an identity.  Counterexample, reached
from a closed program (5d):

    [−X^α] ([+X^α] (λn:Int. W) ⟨id(Int) → +X⟩) ⟨id(Int) → id(Int)⟩

with `W = [−X^α] 5 ⟨−X⟩`.  The inner value has type `Int → X`; the
pair's exterior type is `Int → Int`; the conversions compose to
`id(Int) → +X`, an unseal.  Cancelling gives a term of the wrong type.
A pair that fails the premise is not a redex and may sit in a value
(Tidy, §2).  What νF does instead is visible in its run of 5d: `Merge`
produces the scope `[−X^α, +X^α]` with conversion `id(Int) → +X` — a
boundary that hides `X` and reveals it again in ONE scope.  A single
entry cannot say that, so νF₁ keeps both layers.

**The other order, `[+X^α] [−X^α]`, is not in the rule set.**  It
would be sound with no premise, by the following lemma, but progress
does not need it (O3).

**Lemma (inverse pair).**  Let `ε` be `+X^α` or `−X^α`.  If
`Γ ∣ ε ⊢ c₁ : R ⇒ T` and `Γ ∣ −ε ⊢ c₂ : T ⇒ S`, and `α` occurs free in
neither `R` nor `S`, then `R = S`.

*Proof.*  Induction on `c₁`, by cases on `T`.
* `T = ι`.  `c₁` has target `ι`: `id(ι)`, or `+X` (with source `α`,
  excluded).  So `R = ι`.  Symmetrically `c₂` is `id(ι)` or `−X` (target
  `α`, excluded), so `S = ι`.
* `T = α`.  `c₁` is `id(X)` (then `R = α`, excluded) or `−X`, which
  needs `ε = −X^α` and gives `R = P` where `α:=P`.  Then `−ε = +X^α`,
  and `c₂` is `id(X)` (`S = α`, excluded) or `+X`, giving `S = P`.
* `T = γ ≠ α`.  Only `id(Y)` with `Y:=γ` has target or source `γ` (a
  seal or unseal mentions `α`), so `R = γ = S`.
* `T = T₁ → T₂`.  `c₁` is a function conversion (`+X` has source `α`):
  `c₁ = a₁ → b₁` with `Γ ∣ −ε ⊢ a₁ : T₁ ⇒ R₁` and
  `Γ ∣ ε ⊢ b₁ : R₂ ⇒ T₂`.  Likewise `c₂ = a₂ → b₂` with
  `Γ ∣ ε ⊢ a₂ : S₁ ⇒ T₁` and `Γ ∣ −ε ⊢ b₂ : T₂ ⇒ S₂`.  The IH on
  `(a₂, a₁)` — the same lemma with the roles of the pair swapped —
  gives `S₁ = R₁`, and on `(b₁, b₂)` gives `R₂ = S₂`.
* `T = ∀Z. T′`.  Both are `∀Z.` conversions, checked in
  `Γ, α′, Z:=α′` with `α′ ≠ α` fresh; the IH gives the bodies equal
  after `Z ↦ α′`, hence `R = S`.  ∎

For `[+X^α] ([−X^α] V ⟨c₁⟩) ⟨c₂⟩ : B` at `Δ`: the inner interior is
`−X(Δ, X:=α) = Δ`, both conversions are checked in `Δ, X:=α`, and `A`,
`B` are spelled in `Δ`, which does not name `α`; the lemma gives
`Δ(A) = Δ(B)`.  In the other order the lemma's hypothesis fails —
`A` is spelled where `X` names `α` — which is exactly the
counterexample above.

### O2 — the gap: an unseal blocked by a hiding layer (OPEN)

Reach does not apply to
`[+X^α] [ε₁ … εₖ] [−X^α] V ⟨−X⟩ ⟨id(X) … id(X)⟩ ⟨+X⟩` when some
`εᵢ = −Y^β` hides a representation `β` that `X`'s payload needs, and
the layer is not half of a Cancel pair.  By O3 nothing else applies, so
such a state is stuck.  This is not a property of single reduction
steps but of reachable terms, so it needs an invariant or a
counterexample.  What is known:

* **Where hiding layers come from.**  A `−Y^β` layer is created only by
  Wrap, as the argument wrapper directly inside a `+Y^β` layer (or,
  in the de Bruijn development, by `crossΛᴹ` when Beta substitutes
  under a `Λ`).  TyBeta can later put a NEW `+Z` layer outside an
  existing `−Y` layer, which is how 5b's layer 3 (`[−X^α]` carrying
  `id(Y)`, with `Y`'s payload `X`) arises.
* **Why 5b is not stuck.**  The values of type `Y` inside layer 3 are
  the function's arguments, and each entered through layer 3's domain
  wearing the dual layer `[+X^α] … ⟨id(Y)⟩`.  When such a value leaves
  through layer 3's codomain, the two layers meet as a `[−X^α][+X^α]`
  pair whose types agree (`Y` and `Y`), and Cancel removes them before
  Reach is needed.
* **Conjectured invariant.**  Inside a `[−Y^β]` layer, every value
  whose type needs `β` carries, beneath only layers that themselves
  cancel, the `[+Y^β]` wrapper it received on entering — because code
  inside the layer cannot create such a value (it cannot name `β`).  If
  true, every hiding layer that O2 would need to cross is half of a
  Cancel pair by the time the unseal reaches it.  The step that needs
  care is TyBeta, which inserts `+` layers into the middle of a tower.

### O3 — progress (proved, modulo the gap O2)

**Claim.**  If `Δ ∣ [] ⊢ M : A` with `Δ` well named, then `M` is a
value, or `M` steps, or `M` contains an O2 configuration in evaluation
position.

*Proof.*  Induction on the typing derivation; the frames are the
evaluation positions, so by the IH an immediate subterm in a frame is a
value or steps (ξ) or is stuck at O2.  Remaining cases, all subterms
values:
* `op(V⃗)`: Delta, by L6 (base-typed values are constants).
* `V W`: by L6, `V` is `λ` (Beta) or a tower with top `c → d` (Wrap).
* `ν X:=A. (V X)⟨d⟩`: by L6, `V • X` is defined; TyBeta allocates
  `α:=Δ(A)` (`Δ ⊢ A` is a premise of `ν`).
* `[ε] V ⟨c⟩`.  If `c` is inert, the term is a value unless it is a
  Cancel redex.  Otherwise `c` is active: `id(ι)` or `+X` (the only
  conversions with no inert form; there are no chains).
  * `id(ι)`: `V` has base type, so by L6 it is a constant — Id.
  * `+X`, so `ε = +X^α`, and `V` is a value at type `X` in
    `Δ₀ = Δ, X:=α`.  By L6 its top layer carries `−X` under `−X^α` —
    Reach with `k = 0`, whose premise always holds (the seal's source
    is spelled in `−X(Δ₀) = Δ`, part of `Δ₀`) — or `id(X)` under some
    `εᵢ`.  That `εᵢ` is not `±X^α` (`+X^α` needs `X` unnamed outside;
    under `−X^α` the interior has no name for `α`, so no interior type
    has rep `α`), so it is `±Y^β` with `Y ≠ X`, and `X` still names
    `α` in its interior.  Repeat on the body.  The walk ends, because
    the bottom of a tower is simple and no simple value has a variable
    type, at a layer carrying `−X` under `−X^α`.  This is exactly
    Reach's left-hand side.  The walk may pass `[+Z^γ] [−Z^γ]` pairs
    (values, which Reach crosses like any other layers), but no
    `[−Z^γ] [+Z^γ]` pair: both of its layers carry `id(X)`, so its
    types agree and it is a Cancel redex, not part of a value.  Reach
    fires if every intermediate interior spells `X`'s payload;
    otherwise this is O2.  ∎

    **Which rules progress uses.**  Cancel appears in this proof only
    through Tidy: it clears `[−Z^γ] [+Z^γ]` pairs from the walk.  That
    is necessary — in 5b layer 3 is `[−X^α]` with interior {Y}, which
    cannot spell `Y`'s payload `X`, so Reach cannot cross it, and
    after any unsealing the type between layers 3 and 4 would be that
    payload, so no rule could keep the pair either.  The other order is
    not used: an unseal over its seal is Reach with `k = 0`.

### O4 — Reach preserves types (proved)

Write the redex's layers from the outside: `[+X^α]` at exterior `Δ`
with interior `Δ₀ = Δ, X:=α`; `εᵢ` with exterior `Δᵢ₋₁` and interior
`Δᵢ` (`1 ≤ i ≤ k`); `[−X^α]` with exterior `Δₖ` and interior
`Δₖ₊₁ = −X(Δₖ)`.  By the redex's typing: `Δₖ₊₁ ⊢ V : A_V` with
`Δₖ₊₁(A_V) = R` where `α:=R` (rule `seal`); every intermediate type is
`X`; and the whole term has type `B` with `Δ(B) = R` (rule `unseal`).
The premise gives `A` with `Δᵢ ⊢ A` and `Δᵢ(A) = R` for `0 ≤ i ≤ k`.

* Inner layer: body `V : A_V`; conversion `Id(A)` in context `Δₖ`
  types at `R ⇒ R` (L5), which is `Δₖ₊₁(A_V) ⇒ Δₖ(A)`; exterior type
  `A`, well formed in `Δₖ`.
* Layer `i`: body of type `A`; conversion context `εᵢ⁺(Δᵢ₋₁)` is the
  larger of `Δᵢ₋₁` and `Δᵢ`, so it spells `A`, and `Id(A)` types at
  `R ⇒ R = Δᵢ(A) ⇒ Δᵢ₋₁(A)` (L5); exterior type `A`, well formed in
  `Δᵢ₋₁`.
* Outer layer: body of type `A` in `Δ₀`; `Id(A)` types at
  `R ⇒ R = Δ₀(A) ⇒ Δ(B)`, so the exterior type is still `B`.

The store and `V` are untouched.  **One `A` suffices:** by L2 each
`Δᵢ` has at most one spelling of `R`.  The spellings agree because a
representation variable of `R` keeps its name down the tower: a `+`
layer cannot re-bind a name already in scope or name an `α` already
named (L1), and a `−` layer that removed the name of a representation
variable of `R` would leave its interior without a spelling, failing
the premise.  ∎

### O5 — determinism (proved, up to the choice of fresh `α`)

**Values do not step.**  A simple value has no frame position that
reduces (no ξ under `λ` or `Λ`).  A tower `[ε] V ⟨i⟩` has an inert
`i`, so Id (needs `id(ι)`) and Reach (needs `+X` on top) do not apply,
and Tidy excludes Cancel; its body is a value, by induction.

**At most one rule at the root.**  The left-hand sides are pairwise
disjoint: Delta (`op`), Beta (application of a `λ`), Wrap (application
of a boundary), TyBeta (`ν`), and on boundaries: Id (body a constant,
conversion `id(ι)`), Cancel (outer entry `−X^α`, body a value boundary
with entry `+X^α`), Reach (outer entry `+X^α`, conversion `+X`, the
tower beneath a value).  Id and Cancel differ on the body (constant
versus boundary); Id and Reach on the conversion (`id(ι)` versus
`+X`); Cancel and Reach on the sign of the outer entry.

**At most one frame decomposition.**  Every rule's left-hand side has
values in all its frame positions, and values do not step, so ξ and a
root rule never both apply; within ξ, the frames are the paper's
left-to-right order.  TyBeta's `α` is any fresh variable; results agree
up to renaming it (L4).  ∎

### O6 — TyBeta on towers preserves types (proved)

**Lemma (instantiation).**  If `Γ ⊢ V : ∀X. C` for a value `V`, `Γ` well
named, and `X`, `α` fresh, then for any `P`,
`Γ, α:=P, X:=α ⊢ V • X : C`.

*Proof.*  Induction on `V` (L6: a `Λ` or a tower of `∀` layers).
* `V = ΛX. N`: the `Λ` rule gives `Γ, α′, X:=α′ ⊢ N : C`; rename `α′`
  to `α` and refine it to `α:=P` (L4).
* `V = [ε] V′ ⟨∀X. c⟩`, with `ε(Γ) ⊢ V′ : ∀X. C′` (the `all` rule's
  source is a `∀`, and L2 fixes its spelling) and
  `ε⁺(Γ), α′, X:=α′ ∣ ε ⊢ c : ε(Γ)(C′)[X↦α′] ⇒ Γ(C)[X↦α′]`.  Let
  `Γ″ = Γ, α:=P, X:=α`.  Coherence `Γ″ ⊢ ε`: for `+Y^β`, `Y ≠ X` and
  `β ≠ α` by freshness; for `−Y^β`, `Y:=β ∈ Γ`.  Since `ε` touches
  only `Y`, `ε(Γ″) = ε(Γ), α:=P, X:=α` up to L3, so the IH types
  `V′ • X : C′` there; and `ε⁺(Γ″)` is the `all` premise's context
  with `α′` renamed and refined (L4), where `[X↦α′]` becomes reading
  `X` through `X:=α`.  So `Γ″ ⊢ [ε] (V′ • X) ⟨c⟩ : C`.  ∎

**TyBeta.**  The redex `ν X:=A. (V X)⟨d⟩ : B` at `Δ` has `Δ ⊢ V : ∀X. C`
and `Δ′ ∣ +X^α ⊢ d : Δ′(C) ⇒ Δ(B)` with `Δ′ = Δ, α:=Δ(A), X:=α`.  After
the step the context is `Δ⁺ = Δ, α:=Δ(A)`.  `Δ⁺ ⊢ +X^α` holds (`α`
allocated, `X` and `α` unnamed), its interior is `Δ′`, the lemma (with
`P = Δ(A)`) gives `Δ′ ⊢ V • X : C`, `d` is unchanged, and
`Δ⁺(B) = Δ(B)`.  So `[+X^α] (V • X) ⟨d⟩ : B` at `Δ⁺`.  ∎

### O7 — color preservation (proved, with one inherited caveat)

The color of a hole is the name map of its context (`Residual.agda`
§2); residuals are as in `Residual.agda` §5, with the redex's own nodes
consumed.  Rule by rule, a residual hole's map before and after:

* **Wrap.**  Holes in `V` stay at `ε(Δ)`.  Holes in `W` move from `Δ`
  to `(−ε)(ε(Δ))`: for `+X^α`, `−X(Δ, X:=α) = Δ`; for `−X^α`,
  `−X(Δ), X:=α`, the same map (positions differ only in de Bruijn
  form — the same situation as νF's Wrap).
* **TyBeta.**  Holes in `V` keep their maps up to renaming the `Λ`'s
  (and each layer's `all`) bound representation to the allocated `α`
  — the residual's ρ, as for νF's TyWrap.
* **Id.**  The constant is consumed with its boundary (no residual), as
  in νF.
* **Cancel.**  `V`'s holes move from `−X(Δ), X:=α` to `Δ` — the same
  map.
* **Reach.**  No layer moves; conversions only.  Every hole keeps its
  context.
* **Beta.**  Holes of `N` keep their contexts.  The CAVEAT: an argument
  copy substituted under a `Λ` inside `N` sees that `Λ`'s variable.
  The Agda's Beta wraps such a copy in a hiding boundary (`crossΛᴹ`,
  `TermSubst.agda`) so its map is unchanged; the paper's named
  `N[x := V]` does not.  νF₁ inherits whichever νF adopts, and in the
  `crossΛᴹ` form those hiding layers are among the ones Reach crosses
  (O2).

So νF₁ satisfies the color law exactly when νF does; deleting Hide
(§4) is what made that true.  ∎

## 7. Where this puts νF in the design space

The axes, with the points that have been built or sketched:

| point | entries per boundary | merging | what a hide does | payloads | instantiation |
|---|---|---|---|---|---|
| D02 per-variable wrappers (2026-09-01) | one | Cancel, Drop, Commute | truncates the context at `X` | copied types | pushes the type argument in (`TyWrapCncl`) |
| D07 v1 combined boundary (2026-09-03) | list | `⊕` | truncates at the deepest conceal | copied types | records it as a reveal |
| strong-rep-nu before 2026-09-24 | list | `CancelR`, `IdPush` (stacks otherwise) | does not truncate (D34 onward) | representation variables | records it |
| **νF** (`paper/main.tex`) | list | `Merge` (one boundary per value) | removes `X` only | representation variables | records it |
| **νF₁** (this sketch) | one | `Cancel` (`[−X][+X]` only), `Reach` (towers) | removes `X` only | representation variables | records it |

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
  argument (O3) that walks down a tower, longer runs (5b: 15 against
  11; 5d: 19 against 14), identity layers left in values at non-base
  types, and the gap O2.
* **One scope can hide and reveal the same variable.**  νF's run of
  5d builds `[−X^α, +X^α] (λn:Int. W) ⟨id(Int) → +X⟩`: hide `X`, then
  reveal it again, with a conversion that unseals.  With one entry per
  boundary that is two layers that cannot cancel each other, and they
  stay in the value until the run ends.
* **Color preservation is where lists earn their keep.**  Under the
  design law a layer may disappear only if no hole beneath it would see
  a different set of names.  With one entry per boundary that leaves
  `[−X^α] [+X^α]` pairs with agreeing types (Cancel) and constants
  (Id); every other hiding layer
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

1. Settle O2: run the corpus and the stress programs through a νF₁
   evaluator (a checker for `Tidy` towers and the rules of §4), looking
   for a stuck state, and try to prove the conjectured invariant.
2. If O2 holds, decide whether to mechanize; the proofs of §6 are the
   plan (L1–L6, then O1, O3–O7).
