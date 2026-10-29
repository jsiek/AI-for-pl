# Single-entry boundaries — an on-paper sketch (2026-10-28)

Status: SKETCH, not mechanized.  Nothing here is checked in Agda; every
trace below is derived by hand unless it says otherwise.  The purpose is
to locate νF (`paper/main.tex`) in the design space by building its
nearest neighbour: the same calculus with every boundary restricted to
ONE scope entry, values allowed to be towers of boundaries, and no
`Merge`.  Call it **νF₁**.

This is the fourth version of the sketch (§9 has the history).  Two
choices distinguish it from νF beyond the entry count:

* **Runtime types are representation types.**  Terms are typed at the
  paper's representation types `R`; named types `A` survive only where a
  programmer writes them (annotations).  This is what makes progress
  hold: the earlier version, with named runtime types, admitted a
  well-typed stuck term (§5e).
* **`id` carries no type.**  One identity conversion, `id : R ⇒ R` for
  every `R`, so the reduction rules never have to spell a type.

With both, the rule set is Delta, Beta, Wrap, TyBeta, Id and two new
rules, **Cancel** and its special case **Cancel-□**, with no premise.  §6 proves progress, preservation,
determinism and color preservation on paper, with no open obligation
of its own (one inherited caveat, Beta under `Λ`, and one design
question, abstraction, are recorded).

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

Named types are the paper's; they are what annotations are written in.
Runtime types are the paper's representation types:

    ι      ::=  Int | Bool
    A,B,C  ::=  X | ι | A → B | ∀X. A                 named types (annotations)
    R,S,T  ::=  α | X | ι | R → S | ∀X. R             runtime types (X bound by an enclosing ∀)
    Δ      ::=  [] | Δ, α^X | Δ, α^X:=R | Δ, X:=α     (an allocation records its name X)

A **scope entry** replaces the scope list:

    ε  ::=  +X^α  |  −X^α

    −ε:   −(+X^α) = −X^α        −(−X^α) = +X^α

Conversions are ONE sort.  `id` carries no type, and there are no
chains:

    c,d  ::=  id | c → d | ∀X. c | −X | +X

The paper's three sorts (middle, tail, conversion) and its chains
`t ; −X` and `+X ; c` exist because `Merge` composes conversions: the
compiler's `reveal`/`conceal` (`Conversion.agda` §4) write only bare
seals and unseals, and `⨟` is what builds a chain.  νF₁ has no `Merge`
and no rule that builds a conversion from pieces — Wrap and TyBeta give
a boundary a SUB-conversion (a domain, a codomain, a `∀` body), Id
deletes a layer, and Cancel writes `id` — so no reachable term has a
chain.  What is lost is expressiveness for hand-written boundaries:
`(c → d) ; −X` must be written as two layers.  The compiler's identity
leaves `id(Y)` and `id(ι)` become `id`; whether structural identities
such as `id → id` should also collapse to `id` (a smart constructor) is
left open — the rules below accept either.

Terms:

    L,M,N  ::=  k | op(M⃗) | x | λx:A. N | L M
              | ΛX. V | ν X:=A. (L X)⟨c⟩ | [ε] M ⟨c⟩

    Simples  U    ::=  k | λx:A. N | ΛX. V
    Values   V,W  ::=  U | [ε] V ⟨i⟩
    Inert    i    ::=  c → d | ∀X. c | −X | id      (id only over a non-constant)

**Identity towers** are stacks of layers that all carry `id`, with a
hole at the bottom; `I[M]` plugs `M` into the hole:

    I  ::=  □  |  [ε] I ⟨id⟩

So a value is a TOWER: a simple value under any number of boundaries
with inert conversions.  There is no side condition on adjacent layers:
the one rule that removes a pair of layers, Cancel-□, needs an active
unseal on top (§4).  `[ε] k ⟨id⟩` is the one active form with an `id`,
and Id removes it.

## 3. Type system

Interior, conversion context and coherence, specialised from the
paper's `δ(Δ)`, `δ⁺(Δ)` and `Δ ⊢ δ`:

    (+X^α)(Δ)  =  Δ, X:=α              (+X^α)⁺(Δ)  =  Δ, X:=α
    (−X^α)(Δ)  =  −X(Δ)                (−X^α)⁺(Δ)  =  Δ

    Δ ⊢ +X^α   if  α ∈ Δ,  X:=β ∉ Δ for every β,  Y:=α ∉ Δ for every Y
    Δ ⊢ −X^α   if  X:=α ∈ Δ

and, for both, the NAMING CONDITION: `α`'s allocation records the name
`X` (`α^X ∈ Δ`).  A representation variable has one name for its whole
life, so it can be hidden and revealed again, but only under that name;
two names never denote one representation variable, even at different
times.  Names are fresh at allocation (TyBeta renames the `Λ`'s binder
to a fresh `X`), so the condition costs nothing for compiled programs
(§6, L1).

A scope changes only NAME bindings; the representation variables, and
so the meaning of every runtime type, are the same on both sides.

**Well-formed runtime types** `Δ ⊢ R`: every free representation
variable of `R` is allocated in `Δ` (abstract or with a payload).  A
runtime type need not be nameable: it may mention a representation
variable that no name in scope denotes.

**Conversions** `Δ ∣ ε ⊢ c : R ⇒ S`:

    Δ ⊢ R
    ───────────────────── (id)
    Δ ∣ ε ⊢ id : R ⇒ R

    Δ ∣ −ε ⊢ c : R′ ⇒ R      Δ ∣ ε ⊢ d : S ⇒ S′
    ──────────────────────────────────────────── (fun)
    Δ ∣ ε ⊢ c → d : R → S ⇒ R′ → S′

    Δ, α^X, X:=α ∣ ε ⊢ c : R[X↦α] ⇒ S[X↦α]        X, α ∉ Δ
    ──────────────────────────────────────────── (all)
    Δ ∣ ε ⊢ ∀X. c : ∀X. R ⇒ ∀X. S

    α^X:=P ∈ Δ                              α^X:=P ∈ Δ
    ─────────────────────────── (seal)      ─────────────────────────── (unseal)
    Δ ∣ −X^α ⊢ −X : P ⇒ α                   Δ ∣ +X^α ⊢ +X : α ⇒ P

In a domain the entry is inverted, so a boundary `[+X^α]` may unseal
`X` in covariant positions and seal it in contravariant ones, and
`[−X^α]` the other way round.  The changes from the paper: the premise
`±X^α ∈ δ` becomes "the entry IS `±X^α`"; `id` is untyped; seal and
unseal read the payload `P` directly rather than through a spelling;
the chain rules are gone.

**Terms** `Δ ∣ Γ ⊢ M : R`, with `Γ` mapping term variables to runtime
types:

    ─────────── (const, k : ι)      ───────────────── (var)
    Δ ∣ Γ ⊢ k : ι                   Δ ∣ Γ ⊢ x : Γ(x)

    Δ ⊢ A     Δ ∣ Γ, x:Δ(A) ⊢ N : S
    ──────────────────────────────── (lam)        an annotation means Δ(A)
    Δ ∣ Γ ⊢ λx:A. N : Δ(A) → S

    Δ ∣ Γ ⊢ L : R → S     Δ ∣ Γ ⊢ M : R
    ──────────────────────────────────── (app)    R compared syntactically
    Δ ∣ Γ ⊢ L M : S

    Δ, α^X, X:=α ∣ Γ ⊢ V : R    X, α ∉ Δ
    ──────────────────────────────────── (Lam)
    Δ ∣ Γ ⊢ ΛX. V : ∀X. R[α ↦ X]

    Δ ⊢ A    Δ ∣ Γ ⊢ L : ∀X. R    Δ′ ∣ +X^α ⊢ c : R[X ↦ α] ⇒ S    Δ ⊢ S
    ───────────────────────────────────────────────────────────────── (ν)
    Δ ∣ Γ ⊢ ν X:=A. (L X)⟨c⟩ : S       where Δ′ = Δ, α^X:=Δ(A), X:=α;  X, α ∉ Δ

    Δ ⊢ ε    ε(Δ) ∣ [] ⊢ M : R    ε⁺(Δ) ∣ ε ⊢ c : R ⇒ S
    ──────────────────────────────────────────────────── (boundary)
    Δ ∣ Γ ⊢ [ε] M ⟨c⟩ : S

(`Δ ⊢ S` in `ν` keeps `α` out of the result type.)  The boundary rule
asks for no named type on either side: the interior and exterior types
are runtime types, and a scope does not change what they mean.

Names keep two jobs: an annotation `λx:A` is read through the current
name map, and a scope entry `±X^α` decides which names a subterm may
write (color) and which representation variable a boundary may seal or
unseal (permission).

## 4. Reduction

Frames are the paper's, with `[ε] □ ⟨c⟩` in place of `[δ] □ ⟨c⟩`, and
`([ε] □ ⟨c⟩)(Δ) = ε(Δ)`.  A tower prefix is abbreviated
`[ε₁ … εₖ] M ⟨cₖ … c₁⟩` = `[ε₁] … [εₖ] M ⟨cₖ⟩ … ⟨c₁⟩`.

    Δ ⊢ op(V⃗)  ⟶  ⟦op⟧(V⃗)                                         (Delta)
    Δ ⊢ (λx:A. N) V  ⟶  N[x := V]                                   (Beta)

    Δ ⊢ [ε] V ⟨c → d⟩ W  ⟶  [ε] (V ([−ε] W ⟨c⟩)) ⟨d⟩                (Wrap)
    Δ ⊢ [ε] V ⟨id⟩ W     ⟶  [ε] (V ([−ε] W ⟨id⟩)) ⟨id⟩              (Wrap-id)

    Δ ⊢ ν X:=A. (V X)⟨d⟩  ⟶  [+X^α] (V • X) ⟨d⟩   ⊣ α^X:=Δ(A)       (TyBeta)
        where  (ΛX. N) • X          =  N
               ([ε] V ⟨∀X. c⟩) • X  =  [ε] (V • X) ⟨c⟩
               ([ε] V ⟨id⟩) • X     =  [ε] (V • X) ⟨id⟩

    Δ ⊢ [ε] k ⟨id⟩  ⟶  k                                             (Id)

    Δ ⊢ [+X^α] I[[−X^α] V ⟨−X⟩] ⟨+X⟩  ⟶  [+X^α] I[[−X^α] V ⟨id⟩] ⟨id⟩    (Cancel)
        if I ≠ □ and I[[−X^α] V ⟨−X⟩] is a value

    Δ ⊢ [+X^α] ([−X^α] V ⟨−X⟩) ⟨+X⟩  ⟶  V                              (Cancel-□)

    Δ ⊢ F[M]  ⟶  F[M′] ⊣ ξ      if F(Δ) ⊢ M ⟶ M′ ⊣ ξ                (ξ)

What each rule does, against νF:

* **Wrap** and **TyBeta** are νF's, generalised to towers: νF's Wrap
  needs a SIMPLE body and its TyWrap a `Λ` one level down; here the body
  is any value.  Wrap-id and the third clause of `•` treat an untyped
  `id` at a function or `∀` type as `id → id` and `∀X. id`.  TyBeta
  absorbs TyWrap: `•` strips one `∀` from every layer of a `∀`-typed
  tower.  Each layer's `∀`-binder is renamed to the fresh `X`; since
  `X` is fresh, no layer's entry mentions it, and `X` stays nameable
  through every layer.
* **Id** is νF's, for the untyped `id`: it fires only over a constant,
  which typing puts at a base type.
* **Cancel** is new: an unseal `+X` meets its seal `−X` through an
  identity tower `I`.  Only the two ends change, both to `id`; `I` is
  copied unchanged, because its layers carry the untyped `id` both
  before the step (at `α`) and after it (at `α`'s payload).  The types
  inside `I` become the payload, which need not be nameable at an
  intermediate layer, and does not have to be (runtime types).  No layer
  moves.  The naming condition makes the seal's name the unseal's name,
  `X`; `I` may contain layers whose entry is `−X^α` or `+X^α` (5b's
  second Cancel crosses both).  The hole of `I` is at the FIRST layer
  below the unseal that does not carry `id`, so a redex has one
  decomposition (O6).  (Earlier drafts called this rule Reach, and used
  the name Cancel for removing an adjacent inverse pair; that rule is
  called PairCancel here.)
* **Cancel-□** is Cancel with an empty `I`: the seal sits directly under
  its unseal, and both layers go, leaving `V`.  It is color-safe where
  Hide was not, because the two entries cancel exactly on the name map:
  `V`'s context is `−X(Δ, X:=α) = Δ` before the step and `Δ` after it.
  Cancel is restricted to `I ≠ □` so the two rules do not overlap.  Only
  this order of the pair is a redex: in `[−X^α] ([+X^α] V ⟨+X⟩) ⟨−X⟩`
  the inner unseal is active, so the inner boundary is not a value.  It
  saves the identity layers Cancel would leave, which Id cannot remove
  at a non-base type.

There is no `Merge`, no conversion composition and no chain.  The only
rules that remove layers are Id (one, over a constant) and Cancel-□
(an unseal and its seal).

**Two rules that are NOT here, and why** (§9 has the details):

* **Hide**, `[−Y^β] V ⟨id⟩ ⟶ V`, breaks color preservation: every hole
  in `V` would gain `Y`.
* **PairCancel**, removing an inverse pair `[−X^α] [+X^α]`, is not needed
  for progress once Cancel has no premise.  If added to shorten towers,
  it needs a premise that the pair's interior and exterior types agree:
  5d reaches a pair whose conversions compose to an unseal.

## 5. Examples (hand-derived)

Store allocations are shown with `⊣`; every run is at the empty
context unless it says otherwise.  Compiled conversions are written with
their identity leaves as `id` (structural identities such as `id → id`
are left as compiled).

### 5a. `K` — §1b of `Examples.agda`

    ((ΛX. λf:∀Y. Y→Bool. f [X]) [Bool] (ΛZ. λz:Z. true)) false

νF: 9 steps (TyBeta, Wrap, Beta, TyWrap, Merge, Merge, Wrap, Beta, Id —
rendered by `showRun 0 9 K₀-⊢`).  νF₁: 11 steps.  After the TyBeta that
instantiates `f` (⊣ β:=α), the value is the tower

    [+X^α] [+Y^β] [−X^α] (λz:Y. true) ⟨id → id⟩ ⟨−Y → id⟩ ⟨−X → id⟩

three Wraps send `false` in (the argument becomes
`[+X^α] [−Y^β] [−X^α] false ⟨−X⟩ ⟨−Y⟩ ⟨id⟩`), Beta discards it, and
three Ids peel `true ⟨id⟩ ⟨id⟩ ⟨id⟩`.

### 5b. `K` returning its argument — an unseal through a hiding layer

    ((ΛX. λf:∀Y. Y→Y. f [X]) [Bool] (ΛZ. λz:Z. z)) false        : Bool

νF: 11 steps, three Merges (rendered with `showRun` on a scratch
module; the last Merge produces
`[+X^α, +Y^β, −X^α, +X^α, −Y^β, −X^α] false ⟨id(Bool)⟩`).

νF₁, 16 steps.  The first eight are as in 5a (with `+Y`/`+X` codomains)
and end at the six-layer tower

    [+X^α] [+Y^β] [−X^α] [+X^α] [−Y^β] [−X^α] false ⟨−X⟩ ⟨−Y⟩ ⟨id⟩ ⟨id⟩ ⟨+Y⟩ ⟨+X⟩

with interiors {X}, {X,Y}, {Y}, {X,Y}, {X}, ∅ (outermost first) and
store α:=Bool, β:=α.  Then

    → Cancel, |I| = 2 (layers 2–5)  [+X^α] [+Y^β] [−X^α] [+X^α] [−Y^β] [−X^α] false ⟨−X⟩ ⟨id⟩ ⟨id⟩ ⟨id⟩ ⟨id⟩ ⟨+X⟩
    → Cancel, |I| = 4 (layers 1–6)  [+X^α] [+Y^β] [−X^α] [+X^α] [−Y^β] [−X^α] false ⟨id⟩ ⟨id⟩ ⟨id⟩ ⟨id⟩ ⟨id⟩ ⟨id⟩
    → Id × 6                       false

The first Cancel is the step the named-type versions could not take: it
crosses layer 3, `[−X^α]` with interior {Y}, and makes the type there
`Y`'s payload, `α` — which layer 3 cannot name.  As a runtime type that
is fine.

**The problem, concretely.**  Here is the first Cancel's contractum
again, layer by layer, with the type each layer's body would need:

| layer | entry | interior names | conversion after Cancel | body's type, named / runtime |
|---|---|---|---|---|
| 2 | `+Y^β` | {X:α, Y:β} | `id` | `X` / `α` |
| 3 | `−X^α` | {Y:β} | `id` | **none** / `α` |
| 4 | `+X^α` | {Y:β, X:α} | `id` | `X` / `α` |
| 5 | `−Y^β` | {X:α} | `id` (was `−Y`) | `X` / `α` |

Before the step, every type between layers 2 and 5 was `Y` (runtime
`β`); after it, each is `Y`'s payload `α`.  With NAMED runtime types
the boundary rule types layer 3 as

    {Y:β} ∣ [] ⊢ ([+X^α] …) : A      {X:α, Y:β} ∣ −X^α ⊢ id : {Y:β}(A) ⇒ α

so it needs a named type `A` with `{Y:β}(A) = α` — and `{Y:β}` has no
name for `α`, because layer 3 is exactly the boundary that hides `X`.
There is no such `A`, so the contractum has no derivation.  This is the
shape behind the trouble: `Y` is bound to `X` (β:=α), and the unseal of
`Y` has to carry `Y`'s payload through a layer where `X` is out of
scope.  The second version's premise refused the step; the first and
second versions got through 5b anyway with PairCancel on layers 3–4 (their
types agree), but 5e has no such pair and is stuck.  With runtime types
the rule asks only `{Y:β} ⊢ α`, which holds because `α` is allocated.

### 5c. An unseal reaching its seal through a later reveal

    (ΛX. λx:X. (ΛY. λ_:Int. x) [Bool] 0) [Int] 3                : Int

νF: typed and run by `showRun` on a scratch module, 11 steps, three
Merges.  νF₁, 11 steps:

    → TyBeta ⊣ α:=Int   [+X^α] (λx:X. ν Y:=Bool. ((ΛY. λ_:Int. x) Y)⟨id → id⟩ 0) ⟨−X → +X⟩ 3
    → Wrap              [+X^α] ((λx:X. …) ([−X^α] 3 ⟨−X⟩)) ⟨+X⟩
    → Beta              [+X^α] (ν Y:=Bool. ((ΛY. λ_:Int. [−X^α] 3 ⟨−X⟩) Y)⟨id → id⟩ 0) ⟨+X⟩
    → TyBeta ⊣ β:=Bool  [+X^α] ([+Y^β] (λ_:Int. [−X^α] 3 ⟨−X⟩) ⟨id → id⟩ 0) ⟨+X⟩
    → Wrap              [+X^α] [+Y^β] ((λ_:Int. …) ([−Y^β] 0 ⟨id⟩)) ⟨id⟩ ⟨+X⟩
    → Id                [+X^α] [+Y^β] ((λ_:Int. [−X^α] 3 ⟨−X⟩) 0) ⟨id⟩ ⟨+X⟩
    → Beta              [+X^α] [+Y^β] [−X^α] 3 ⟨−X⟩ ⟨id⟩ ⟨+X⟩
    → Cancel, |I| = 1  [+X^α] [+Y^β] [−X^α] 3 ⟨id⟩ ⟨id⟩ ⟨id⟩
    → Id × 3            3

The `[+Y^β]` layer cannot be dropped (its interior is larger than its
exterior, and the term beneath it may mention `Y`) and cannot be
crossed by pushing `+X` inward (its entry licenses only `Y`), so a rule
of Cancel's kind is needed.

### 5d. An inverse pair whose conversions compose to an unseal

    ((ΛX. λx:X. λg:(Int→X)→(Int→Int). g (λn:Int. x)) [Int] 5 (λh:Int→Int. h)) 0     : Int

νF: 14 steps, three Merges (rendered with `showRun` on a scratch
module).  Its seventh state is the tower

    [+X^α] [−X^α] [+X^α] (λn:Int. W) ⟨id → +X⟩ ⟨id → id⟩ ⟨id → id⟩ 0

with `W = [−X^α] 5 ⟨−X⟩` and α:=Int — the same in νF₁, whose first
seven steps (TyBeta, Wrap, Beta, Wrap, Beta, Wrap, Beta) match νF's.
Layers 2–3 are a `[−X^α] [+X^α]` pair whose inner value has type
`Int → α` while the pair's exterior type is `Int → Int`: its
conversions compose to `id → +X`, an unseal, so removing the pair would
be ill typed.  νF's first Merge turns layers 2–3 into ONE boundary with
scope `[−X^α, +X^α]` and conversion `id → +X`.  In νF₁ the tower is a
value and the run finishes in 17 steps:

    → Wrap, Id          0 crosses layer 1; its [−X^α] 0 ⟨id⟩ wrapper drops
    → Wrap, Id          … layer 2
    → Wrap, Id          … layer 3, whose codomain is +X
    → Beta              [+X^α] [−X^α] [+X^α] [−X^α] 5 ⟨−X⟩ ⟨+X⟩ ⟨id⟩ ⟨id⟩
    → Cancel-□          [+X^α] [−X^α] 5 ⟨id⟩ ⟨id⟩
    → Id × 2            5

### 5e. A term that is stuck with named runtime types

At the store β^Y:=Int, γ^W:=Int, α^X:=β with one name, `Y:=β`:

    S  =  [+X^α] [−Y^β] [+W^γ] [+Y^β] [−X^α] V ⟨−X⟩ ⟨id⟩ ⟨id⟩ ⟨id⟩ ⟨+X⟩       V = [−Y^β] 3 ⟨−Y⟩

Interiors from the outside: {Y:β, X:α}, {X:α}, {X:α, W:γ},
{X:α, W:γ, Y:β}, {W:γ, Y:β}.  Every entry uses its variable's recorded
name, so `S` satisfies the naming condition.  Types: `V : β`; the seal
`−X : β ⇒ α`; the three `id` layers at `α`; the unseal `+X : α ⇒ β`; so
`S : β`.  (Wrap it as `[+Y^β] S ⟨+Y⟩ : Int` for a context with no names.)
This is a hand-written well-typed term, not one known to be reachable —
but progress is about every well-typed term.

With NAMED runtime types `S` is stuck.  Cancel would make the types
inside `I` the payload `β`, and `[−Y^β]`'s interior {X:α} and
`[+W^γ]`'s interior {X:α, W:γ} have no name for `β`; no other rule
applies.  (The hide `[−Y^β]` and its re-reveal `[+Y^β]` are not
adjacent, so not even a PairCancel would help.)  With runtime types:

    → Cancel             [+X^α] [−Y^β] [+W^γ] [+Y^β] [−X^α] V ⟨id⟩ ⟨id⟩ ⟨id⟩ ⟨id⟩ ⟨id⟩

a value of type `β`, whose `[−Y^β]` and `[+W^γ]` layers have interior
type `β`.

(The third version's stuck example hid `β` as `Y` and revealed it as
`Z`; the naming condition now rejects it.  The example above survives
the condition, which is why runtime types are still needed.)

## 6. Proofs, on paper

All by hand.  Type safety (progress, O2; preservation, O3–O5 and the
standard cases), determinism (O6) and color preservation (O7) are
proved for the rules of §4.  O1 relates the type system to the paper's
named one.  The caveat in O7 and the question in §6.8 are not
discharged.

### 6.0 Conventions and supporting lemmas

A context is **well named** if each name `X` has at most one binding
`X:=α` and each representation variable `α` is named by at most one
`X`.  Runtime contexts are well named, and the type system keeps them
so:

* **L1 (scopes keep contexts well named).**  If `Δ` is well named and
  `Δ ⊢ ε`, then `ε(Δ)` and `ε⁺(Δ)` are well named.  For `+X^α`,
  coherence says neither `X` nor `α` is named in `Δ`; for `−X^α`, a
  binding is removed.  The `all` and `Lam` rules add `X:=α` with both
  fresh.  Reduction keeps the naming condition: entries are created
  only by TyBeta (`+X^α` for the fresh `α^X` it allocates), by Wrap
  (`−ε`, the same name and variable as `ε`), and by `crossΛᴹ` in Beta
  (hiding a `Λ`'s own variable under its own binder name), and TyBeta's
  renaming of the `Λ`'s binder renames the hiding layers inside its
  body with it.
* **L2 (spelling is injective).**  If `Γ` is well named, `Γ ⊢ A`,
  `Γ ⊢ B` and `Γ(A) = Γ(B)`, then `A = B` (up to renaming of bound
  variables).  Induction on `A`: at a variable, the two names denote the
  same representation and `Γ` names it once; the other cases are
  structural.  (Used only by O1.)
* **L3 (exchange).**  Typing depends on a context's name bindings only
  through the map `X ↦ α`, so moving a binding `X:=α` (keeping it after
  the entry that allocates `α`) preserves every judgement.
* **L4 (refinement and renaming).**  Replacing an abstract `α` by
  `α:=P`, or renaming a representation variable to a fresh one,
  preserves every judgement.  No rule needs `α` abstract; `seal` and
  `unseal` need a payload, so adding one only enables them.
* **L5 (runtime types ignore scopes).**  `Δ ⊢ R` iff `ε(Δ) ⊢ R` iff
  `ε⁺(Δ) ⊢ R`: a scope entry changes name bindings only, and
  well-formedness of a runtime type looks only at representation
  variables.  So any `R` may be the type at any layer of a tower.
* **L6 (canonical forms).**  The inert conversions' targets are: `c → d`
  an arrow, `∀X. c` a `∀`, `−X` the variable `α` of its entry, `id` its
  own source.  A simple value has a base, arrow or `∀` type.  Hence, by
  induction on a value `V` with `Γ ⊢ V : R`:
  * `R = ι`: `V` is a constant (an `id` layer over a non-constant has
    the non-base type of its body);
  * `R = R₁ → R₂`: `V` is a `λ`, or a tower whose top conversion is
    `c → d` or `id`;
  * `R = ∀X. R′`: `V` is a `Λ`, or a tower whose top conversion is
    `∀X. c` or `id`, over a value of `∀` type, so `V • X` is defined;
  * `R = α`: `V` is a tower whose top conversion is `id` (over a value
    of type `α`) or `−X` under the entry `−X^α`, where `X` is `α`'s
    recorded name (naming condition).

### O1 — the named type system embeds (proved)

**Claim.**  If `Δ ∣ Γ ⊢ M : A` in the paper's named system (with this
sketch's single-entry scopes), then `Δ ∣ Δ(Γ) ⊢ M : Δ(A)` here.  In
particular a compiled closed source program at the empty context has
the runtime type `Δ(A) = A`, so type safety is stated as before.

*Proof.*  Induction on the derivation.  `λ`, application, constants and
variables are immediate.  `Λ`: the named rule types `V : A` under
`Δ, α, X:=α`, and `Δ(∀X. A)` is `∀X.` of that body's representation
with `α ↦ X`.  `ν`: the named premise `c : Δ′(C) ⇒ Δ(B)` is this
sketch's premise with `R = Δ(C)` and `S = Δ(B)`.  `boundary`: the named
premise `c : ε(Δ)(A) ⇒ Δ(B)` is this sketch's premise with `R = ε(Δ)(A)`
and `S = Δ(B)`.  Conversions: `id(ι)` and `id(X)` become `id`; `seal`
and `unseal` read `α:=Δ(A)` as `α:=P`.  ∎

The converse fails, by design: Cancel's contracta (5b's layer 3, 5e) have
runtime types that no context names.

### O2 — progress (proved)

**Claim.**  If `Δ ∣ [] ⊢ M : R` with `Δ` well named, then `M` is a value
or `M` steps.

*Proof.*  Induction on the typing derivation; the frames are the
evaluation positions, so by the IH an immediate subterm in a frame is a
value or steps (ξ).  Remaining cases, all subterms values:
* `op(V⃗)`: Delta, by L6 (base-typed values are constants).
* `V W`: by L6, `V` is a `λ` (Beta) or a tower with top `c → d` (Wrap)
  or `id` (Wrap-id).
* `ν X:=A. (V X)⟨d⟩`: by L6, `V • X` is defined; TyBeta allocates
  `α^X:=Δ(A)` (`Δ ⊢ A` is a premise of `ν`).
* `[ε] V ⟨c⟩`.  If `c` is inert the term is a value.  Otherwise `c` is
  `id` over a constant — Id — or `+X`.  For `+X`, `ε = +X^α` and `V` is
  a value of type `α` (rule `unseal`).  By L6 its top layer carries
  `−X` under `−X^α`, or `id` over a value of type `α`; repeat on the
  body.  The walk ends, because the bottom of a tower is simple and no
  simple value has a variable type, at a layer carrying `−X` under
  `−X^α`.  The layers passed form an identity tower `I`, so `V` is
  `I[[−X^α] V′ ⟨−X⟩]`, a value: Cancel-□'s left-hand side if `I = □`,
  Cancel's otherwise.  Neither has another premise, so one fires.  ∎

### O3 — Cancel preserves types (proved)

Redex `[+X^α] I[[−X^α] V ⟨−X⟩] ⟨+X⟩ : S` at `Δ`.  Let `α^X:=P ∈ Δ`.
By `unseal`, the outer layer's interior type is `α` and `S = P`.  By
induction on `I`, each of its layers carries `id` and has interior and
exterior type `α`.  By `seal`, `V : P` (the payload of `α` is unique).
In the contractum the seal layer's `id : P ⇒ P` gives it exterior type
`P`; by induction on `I`, each layer of `I`, unchanged, now has
interior and exterior type `P`, and its `id : P ⇒ P` is well formed at
that layer by L5; the outer layer's `id : P ⇒ P` gives exterior type
`P = S`.  The store, the scopes and `V` are unchanged.  ∎

**Cancel-□.**  Redex `[+X^α] ([−X^α] V ⟨−X⟩) ⟨+X⟩ : S` at `Δ`, with
`α^X:=P ∈ Δ`.  The outer interior is `Δ, X:=α`; the inner interior is
`−X(Δ, X:=α) = Δ`, since coherence of `+X^α` means `X` is unnamed in
`Δ`.  So `Δ ⊢ V : P` (rule `seal`), and `S = P` (rule `unseal`): the
contractum `V` has type `S` at `Δ`.  ∎

### O4 — Wrap preserves types (proved)

Redex `[ε] V ⟨c → d⟩ W : S′` at `Δ`, with `ε(Δ) ⊢ V : R → S`,
`ε⁺(Δ) ∣ −ε ⊢ c : R′ ⇒ R`, `ε⁺(Δ) ∣ ε ⊢ d : S ⇒ S′`, and `Δ ⊢ W : R′`.
The new layer `[−ε] W ⟨c⟩` sits at `ε(Δ)`:
* coherence: for `ε = +X^α`, `ε(Δ) ∋ X:=α`, so `−X^α` is coherent; for
  `ε = −X^α`, `X` and `α` are unnamed in `−X(Δ)` (L1), so `+X^α` is;
* its interior `(−ε)(ε(Δ))` is `Δ` (for `+X^α`) or `Δ` with `X:=α`
  moved (for `−X^α`), so `W : R′` there by L3;
* its conversion context `(−ε)⁺(ε(Δ))` is `ε⁺(Δ)` up to L3 (for `+X^α`
  both are `Δ, X:=α`; for `−X^α` both have `Δ`'s bindings), so
  `c : R′ ⇒ R` there.
So `[−ε] W ⟨c⟩ : R`, `V (…) : S`, and `[ε] (…) ⟨d⟩ : S′`.  Wrap-id is
the same with `c = d = id`, `R′ = R`, `S′ = S`.  ∎

### O5 — TyBeta on towers preserves types (proved)

**Lemma (instantiation).**  If `Γ ⊢ V : ∀X. R` for a value `V`, `Γ`
well named, and `X`, `α` fresh, then for any `P`,
`Γ, α^X:=P, X:=α ⊢ V • X : R[X ↦ α]`.

*Proof.*  Induction on `V` (L6: a `Λ`, or a tower whose layers carry
`∀X. c` or `id`).
* `V = ΛX. N`: the `Lam` rule gives `Γ, α′^X, X:=α′ ⊢ N : R[X ↦ α′]`;
  rename `α′` to `α` and refine it to `α^X:=P` (L4).
* `V = [ε] V′ ⟨∀X. c⟩`, with `ε(Γ) ⊢ V′ : ∀X. R″` and
  `ε⁺(Γ), α′^X, X:=α′ ∣ ε ⊢ c : R″[X↦α′] ⇒ R[X↦α′]`.  Let
  `Γ″ = Γ, α^X:=P, X:=α`.  Coherence `Γ″ ⊢ ε`: for `+Y^β`, `Y ≠ X` and
  `β ≠ α` by freshness; for `−Y^β`, `Y:=β ∈ Γ`.  Since `ε` touches
  only `Y`, `ε(Γ″) = ε(Γ), α^X:=P, X:=α` up to L3, so the IH types
  `V′ • X : R″[X↦α]` there; and `ε⁺(Γ″)` is the `all` premise's
  context with `α′` renamed and refined (L4).  So
  `Γ″ ⊢ [ε] (V′ • X) ⟨c⟩ : R[X↦α]`.
* `V = [ε] V′ ⟨id⟩`: as the previous case with `c = id` and
  `R″ = R`.  ∎

**TyBeta.**  The redex `ν X:=A. (V X)⟨d⟩ : S` at `Δ` has `Δ ⊢ V : ∀X. R`
and `Δ′ ∣ +X^α ⊢ d : R[X↦α] ⇒ S` with `Δ′ = Δ, α^X:=Δ(A), X:=α`.  After
the step the context is `Δ⁺ = Δ, α^X:=Δ(A)`.  `Δ⁺ ⊢ +X^α` holds (`α`
allocated, `X` and `α` unnamed), its interior is `Δ′`, the lemma (with
`P = Δ(A)`) gives `Δ′ ⊢ V • X : R[X↦α]`, `d` is unchanged, and
`Δ⁺ ⊢ S`.  So `[+X^α] (V • X) ⟨d⟩ : S` at `Δ⁺`.  ∎

**The standard cases.**  Delta: by the operator's type.  Id:
`[ε] k ⟨id⟩ : ι` and `k : ι`.  Beta: the substitution lemma, with the
caveat of O7 for a substitution under `Λ`.  ξ: the IH, at `F(Δ)`, and
weakening of the siblings by the allocated cell.

### O6 — determinism (proved, up to the choice of fresh `α`)

**Values do not step.**  A simple value has no frame position that
reduces (no ξ under `λ` or `Λ`).  A tower `[ε] V ⟨i⟩` has an inert `i`:
Id needs `id` over a constant, which is not inert, and Cancel needs `+X`
on top; its body is a value, by induction.

**At most one rule at the root.**  Delta (`op`), Beta (application of a
`λ`), Wrap and Wrap-id (application of a boundary, told apart by the
conversion), TyBeta (`ν`), Id (`id` over a constant), Cancel (`+X`
over a non-empty `I`) and Cancel-□ (`+X` directly over its seal) have
disjoint left-hand sides.

**Cancel decomposes one way.**  A Cancel redex is `[+X^α] M ⟨+X⟩` with
`M = I[[−X^α] V ⟨−X⟩]`.  `I` matches only layers that carry `id`, so
its hole is at the first layer of `M` whose conversion is not `id`;
that layer must be the seal.  So `I`, and with it the contractum, is
determined by `M`.  A deeper seal cannot be chosen instead, because the
first non-`id` layer would sit between it and the unseal.

**At most one frame decomposition.**  Every rule's left-hand side has
values in all its frame positions, and values do not step, so ξ and a
root rule never both apply; within ξ, the frames are the paper's
left-to-right order.  TyBeta's `α` is any fresh variable; results agree
up to renaming it (L4).  ∎

### O7 — color preservation (proved, with one inherited caveat)

The color of a hole is the name map of its context (`Residual.agda`
§2); residuals are as in `Residual.agda` §5, with the redex's own nodes
consumed.  Rule by rule, a residual hole's map before and after:

* **Wrap, Wrap-id.**  Holes in `V` stay at `ε(Δ)`.  Holes in `W` move
  from `Δ` to `(−ε)(ε(Δ))`: for `+X^α`, `−X(Δ, X:=α) = Δ`; for
  `−X^α`, `−X(Δ), X:=α`, the same map.
* **TyBeta.**  Holes in `V` keep their maps up to renaming the `Λ`'s
  (and each layer's `all`) bound representation to the allocated `α`
  — the residual's ρ, as for νF's TyWrap.
* **Id.**  The constant is consumed with its boundary, as in νF.
* **Cancel.**  No layer moves; conversions only.  Every hole keeps its
  context.
* **Cancel-□.**  `V`'s holes move from `−X(Δ, X:=α) = Δ` to `Δ`: the
  same map, on the nose.
* **Beta.**  Holes of `N` keep their contexts.  The CAVEAT: an argument
  copy substituted under a `Λ` inside `N` sees that `Λ`'s variable.
  The Agda's Beta wraps such a copy in a hiding boundary (`crossΛᴹ`,
  `TermSubst.agda`) so its map is unchanged; the paper's named
  `N[x := V]` does not.  νF₁ inherits whichever νF adopts; `crossΛᴹ`'s
  wrapper is a single entry `[unbind 0 0]`, so it fits as is.

So νF₁ satisfies the color law exactly when νF does.  ∎

### 6.8 Abstraction — a design question, not discharged

Runtime types may mention a representation variable that no name in
scope denotes (5b's layer 3, 5e's `[−Y^β]` layer).  The argument that
this does not leak: runtime types are compared syntactically, so `α`
and its payload `P` are different types; a value of type `α` inside a
region that hides `α`'s name can only pass through `id`; using it at
`P` needs an unseal, which needs a `+Z^α` entry in scope; and code in
the region cannot write `α` in an annotation.  This is the argument
for νF, but it is not proved here.  The design question is different:
Jeremy's 2026-09-04 ruling (W4 withdrawn in `notes/DECISIONS.md`)
wants a sealed value's context to hold only the names that existed when
it was sealed.  νF₁ keeps NAMES that tight; its TYPES are not.

## 7. Where this puts νF in the design space

The axes, with the points that have been built or sketched:

| point | entries per boundary | merging | what a hide does | payloads | runtime types | instantiation |
|---|---|---|---|---|---|---|
| D02 per-variable wrappers (2026-09-01) | one | Cancel, Drop, Commute | truncates the context at `X` | copied types | named | pushes the type argument in (`TyWrapCncl`) |
| D07 v1 combined boundary (2026-09-03) | list | `⊕` | truncates at the deepest conceal | copied types | named | records it as a reveal |
| strong-rep-nu before 2026-09-24 | list | `CancelR`, `IdPush` (stacks otherwise) | does not truncate (D34 onward) | representation variables | named | records it |
| **νF** (`paper/main.tex`) | list | `Merge` (one boundary per value) | removes `X` only | representation variables | named | records it |
| νF₁, third version (§9) | one | PairCancel, Cancel with a premise | removes `X` only | representation variables | named | records it — NOT type safe (5e) |
| **νF₁** (this sketch) | one | none; Cancel (towers) | removes `X` only | representation variables | representation types | records it |

D02 failed because of its truncation and its instantiation rule, not
because it had one entry per boundary (`notes/old/notes-v1.md`,
"Example 8, historical").  νF₁ keeps νF's answers to both and changes
the entry count, which isolates what lists and `Merge` buy:

* **For νF:** values are one boundary deep, so canonical forms, Wrap and
  TyWrap look at one boundary; runs are shorter (5a: 9 against 11; 5b:
  11 against 16; 5d: 14 against 17); a seal chain records a path
  through several variables (`−X ; −Y`) in one conversion; and every
  intermediate type has a NAME in its context.
* **For νF₁:** no composition, no chains, no respelling, and each
  permission check is "the entry is `±X^α`"; the rule set is Wrap,
  TyBeta, Id and Cancel.  The price is towers, a progress argument that
  walks down a tower, identity layers left in values at non-base
  types, and runtime types that mention unnamed representation
  variables (§6.8).
* **The deciding axis is runtime types.**  With named runtime types and
  the color law, single-entry boundaries are not type safe: 5e is
  well typed and stuck, and the repairs either break color (Hide) or
  reason about several scope entries at once (a non-local PairCancel —
  `Merge` in disguise).  Optional conversions typed as a run, the other
  idea tried, are exactly νF's multi-entry scope.  So under the color
  law: **named runtime types need multi-entry scopes and `Merge`;
  representation runtime types do not.**
* **One scope can hide and reveal the same variable.**  νF's run of 5d
  builds `[−X^α, +X^α] (λn:Int. W) ⟨id → +X⟩`.  With one entry per
  boundary that is two layers that stay in the value.

Other points the axes suggest, not sketched: one entry per boundary
with merge-on-construction (`notes/MergeSketch.md`, question 2, option
M2); lists without any merging; νF with representation runtime types
(it would keep `Merge` for depth-1 values but could drop the spelling
in composition).

## 8. Mechanization notes (de Bruijn)

From the current Agda's conventions (`Reduction.agda`, `TermSubst.agda`,
`Boundary.agda`): a cell is allocated at the head of the store, so
existing representation indices move up; entries `bind X β` /
`unbind X β` hold an ordinary position and a representation index.

* **TyBeta** lifts each layer's single entry (`liftᴮ`, as TyWrap does
  for its one scope today); conversions and the `Λ` body move verbatim,
  and the `Λ`'s representation slot becomes the new cell.  Siblings
  shift by `↑ᴹ[new R]` through ξ, as today.
* **Wrap** needs no respelling: an entry and its inverse cancel exactly
  on the name list (delete position `X`, re-insert at `X`, or the
  reverse), so the argument's context and the crossed conversion's
  context are unchanged.  νF's Wrap needs `respellᶜ` only because a
  multi-entry scope and its dual can order the names differently.
* **Cancel** is an inductive judgement over `I` (`[−X^α] V ⟨−X⟩` steps
  its conversion to `id`; `[ε] M ⟨id⟩` passes the step to `M`), and it
  writes untyped `id`: no spelling, no indices, nothing to shift.  With
  de Bruijn names the seal and the unseal are matched by comparing the
  entries' representation indices, since ordinary positions differ
  between layers; the naming condition makes that the same match as
  the named one.
* **Cancel-□** needs no shift: `bind X β` then `unbind X β` inserts and
  deletes at the same position, so `V`'s name list is the redex's.
* **Conversions contain no representation indices** (`id` is untyped;
  seals and unseals cite names), so `↑ᴹ` and `crossΛᴹ` stay out of
  conversions, as today.  Runtime types in the typing judgement carry
  representation indices, which the typing lemmas shift.

## 9. History of this sketch

Names below are the current ones: the drafts' Reach is **Cancel**, and
the drafts' Cancel (removing an adjacent inverse pair) is **PairCancel**.

1. **First version** (named runtime types): PairCancel for both orders of an
   inverse pair, Hide (`[−Y^β] V ⟨id⟩ ⟶ V`), and Cancel crossing only
   `+` layers.  **Hide was deleted** because it breaks color
   preservation: every hole in `V` gains `Y`.
2. **Second version:** Cancel generalised to cross `−` layers, with a
   premise that every intermediate interior can NAME the payload.
   Proving PairCancel type-preserving found that a `[−X^α] [+X^α]` pair can
   compose to an unseal (5d), so that order gained a types-agree
   premise; the other order is sound by the lemma below but unneeded
   (an unseal over its seal is Cancel with `k = 0`), so the minimal set
   kept PairCancel only for `[−X^α] [+X^α]`.
3. **Third version:** chains and annotated identities removed.  Progress
   was proved modulo one obligation, O2, at first treated as a
   reachability question.  But progress is about every well-typed
   term, and 5e is well typed and stuck: **progress was false**.
4. **This version:** runtime types are representation types and `id` is
   untyped.  Cancel loses its premise, progress holds (O2), and PairCancel
   is no longer needed.  Later in the same version: Cancel is stated with
   an identity-tower grammar `I` instead of ellipses, and a naming
   condition (each representation variable has one name for its whole
   life) lets the seal be written `−X`.  Restricting `id` to atomic
   types was considered and not taken: Cancel would then have to
   rewrite every layer of `I` to an identity at the payload.  Last,
   Cancel-□ removes an unseal and the seal directly under it, instead
   of leaving two identity layers (5d: 19 → 17 steps).

**Lemma (inverse pair), kept for reference.**  Let `ε` be `+X^α` or
`−X^α`.  If `Γ ∣ ε ⊢ c₁ : R ⇒ T` and `Γ ∣ −ε ⊢ c₂ : T ⇒ S`, and `α`
occurs free in neither `R` nor `S`, then `R = S`.  Induction on `c₁` by
cases on `T`: at `ι`, `γ ≠ α`, arrows and `∀` the two sides match
structurally; at `α`, `c₁` must be a seal (`ε = −X^α`, source `P`) and
`c₂` an unseal (target `P`), since an `id` would put `α` at an endpoint.
For `[+X^α] [−X^α]` the endpoints are spelled where `α` is unnamed, so
the lemma applies; for `[−X^α] [+X^α]` they need not be, and 5d shows
the conclusion fails.

## 10. Next steps

1. Run the corpus and the stress programs through a νF₁ evaluator, as a
   check of the hand proofs and to measure tower heights against νF's
   runs.
2. Decide the design question of §6.8.
3. If the point is worth keeping, mechanize: L1–L6, then O1–O7, with the
   de Bruijn plan of §8.
