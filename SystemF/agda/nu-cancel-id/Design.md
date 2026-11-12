# νF₁ᶜ — the design, with variables as names (2026-11-08)

This is the on-paper presentation of the calculus mechanized in this
directory, written in one piece.  It is the second version of the
experiment in `../strong-rep-nu/notes/CancelIdSketch.md` (§8 there).
That note keeps the history: why CancelId alone is stuck (§2), the
first version's Sink and why it needed runtime types (§§3–7, §8).  This
file restates the current design from scratch, with variables as names,
and says where each part lives in the Agda.

Status: type safety (progress and preservation), determinism and color
preservation are all CHECKED in Agda (§8).  Every example (§7) starts
from a System F program and runs to a value, and every run is checked
in Agda.

## 1. A first example

The program 5c instantiates `X` with `Int`, passes `3`, and inside
instantiates `Y` with `Bool` and returns the outer argument:

    (ΛX. λx:X. (ΛY. λ_:Int. x) [Bool] 0) [Int] 3                : Int

After elaboration (§6) and nine steps (§7) it reaches

    [+X^α] [+Y^β] [−X^α] 3 ⟨−X⟩ ⟨id⟩ ⟨+X⟩

* `[−X^α] 3 ⟨−X⟩` is `3` sealed as `X`: inside, `X` is hidden, and the
  conversion `−X` turns the payload `Int` into the variable `α`.
* `[+Y^β] … ⟨id⟩` is a reveal of `Y` carrying `id`, left by
  instantiating `ΛY`: the body's type `X` does not mention `Y`.
* `[+X^α] … ⟨+X⟩` is the unseal of `X`, from the outer instantiation.

The unseal has to meet its seal, and the `Y` layer is in the way.  The
design's answer is a local rule, Push, that moves the unseal through
the reveal:

    → Push      [+Y^β] ([+X^α] [−X^α] 3 ⟨−X⟩ ⟨+X⟩) ⟨id⟩
    → Cancel-□  [+Y^β] 3 ⟨id⟩
    → Id        3

Every intermediate term is typed at a NAMED type, the paper's: here
`Int` throughout, and inside the seal `X`.

## 2. Syntax

    ι        ::=  Int | Bool
    A,B,C    ::=  X | ι | A → B | ∀X. A                  named types
    P,R,S    ::=  α | X | ι | R → S | ∀X. R              runtime types
    Δ        ::=  ∅ | Δ, α^X | Δ, α^X:=P | Δ, X:=α       contexts
    ε        ::=  +X^α | −X^α                            scope entries
    c,d      ::=  id | c → d | ∀X. c | −X | +X           conversions

    L,M,N    ::=  k | x | λx:A. N | L M
               |  ΛX^α. N                                 type abstraction
               |  ν X:=A. (L X)⟨c⟩                        instantiation
               |  [ε] M ⟨c⟩                               boundary

* Named types are what terms are typed at.  Runtime types appear only
  in conversion typing and in payloads; a runtime `X` is bound by an
  enclosing runtime `∀X`.
* A context allocates representation variables, each with its NAME `X`
  recorded (`α^X` abstract, `α^X:=P` with a payload), and binds names
  to them (`X:=α`).
* A `Λ` binds a name and an abstract representation variable together.
  A source program writes `ΛX. N`, short for `ΛX^α. N` with `α` fresh;
  the variable is needed only when Beta copies a value under the `Λ`
  (§5).
* A boundary has ONE scope entry: `+X^α` reveals `α` under the name `X`
  in its body, `−X^α` hides it.  `−ε` swaps the sign.
* `id` carries no type.  `−X` seals and `+X` unseals the boundary's own
  variable, so a conversion never names a variable other than its
  boundary's.
* A nested tower is written outermost entry first and innermost
  conversion first: `[ε₁] [ε₂] M ⟨c₂⟩ ⟨c₁⟩`.

**The naming condition.**  A representation variable has one name for
its whole life: `α^X` may be named only as `X`.  It can be hidden and
revealed again, but never under another name, and names are fresh at
allocation.  Compiled programs meet it for free.

Agda (`Types.agda`, `Ctx.agda`, `Terms.agda`): named and runtime types
share one syntax `Ty`; `[ s , α ] M ⟨ c ⟩` is the boundary with sign
`s`; `ν_·_⟨_⟩` is instantiation; `Λ_` binds the name and the variable
as one de Bruijn index.  There are no primitive operators, so no Delta.

### Contexts as flags

Under the naming condition a context's name bindings are determined by
WHICH allocated variables are currently named: if `α^X` is named at
all, it is named `X`.  So the Agda represents a context as a store
(one payload or `abs` per variable) and, beside it, one Boolean flag
per variable, `true` when it is named.  A name is a de Bruijn index
that counts only the named variables, newest first (`_∋ⁿ_↦_`).  For
two variables, both named:

    flags  true ∷ true ∷ []        name 0 is variable 0, name 1 is variable 1

Inside `[−X^0]` the flags are `false ∷ true ∷ []`, and name 0 is
variable 1: what the outside writes as name 1, the inside writes as
name 0.  A scope entry sets one flag (`setFlag`).  This is
`strong`'s mask (D34, "mask, do not drop") with names counted over the
unmasked variables only; that count is what makes an allocation, whose
variable starts unnamed, move no name.

## 3. Type system

### Contexts, entries and spelling

The interior of an entry:

    (+X^α)(Δ)  =  Δ, X:=α
    (−X^α)(Δ)  =  Δ with X:=α removed

Coherence:

    Δ ⊢ +X^α   if  α^X is allocated in Δ and X is not bound in Δ
    Δ ⊢ −X^α   if  X:=α ∈ Δ

So a reveal needs its variable unnamed outside, a hide needs it named.
In flags: the flag of `α` outside is `false` for `+`, `true` for `−`,
and the interior flips it (`⊢[]`'s first premise, `interior`).

**Spelling** `Δ(A)` reads a named type as a runtime type, written
`Δ ⊢ A ⇝ R` in the Agda:

    Δ(X) = α   if X:=α ∈ Δ           Δ(ι) = ι
    Δ(A → B) = Δ(A) → Δ(B)           Δ(∀X. A) = ∀X. Δ′(A)

where `Δ′` reads `X` as the bound runtime `X`.  `Δ ⊢ A` means `Δ(A)` is
defined: every free name of `A` is bound in `Δ`.  Spelling is
injective on a well-named context (`⇝-inj`).

### Conversions

`Δ ∣ ε ⊢ c : R ⇒ S`, at runtime types.  Only the allocations of `Δ`
matter; a conversion never looks at names.

    ─────────────────────── (id)
    Δ ∣ ε ⊢ id : R ⇒ R

    Δ ∣ −ε ⊢ c : R′ ⇒ R      Δ ∣ ε ⊢ d : S ⇒ S′
    ──────────────────────────────────────────── (fun)
    Δ ∣ ε ⊢ c → d : R → S ⇒ R′ → S′

    Δ, β^Y ∣ ε ⊢ c : R[Y↦β] ⇒ S[Y↦β]        β fresh
    ──────────────────────────────────────────── (all)
    Δ ∣ ε ⊢ ∀Y. c : ∀Y. R ⇒ ∀Y. S

    α^X:=P ∈ Δ                              α^X:=P ∈ Δ
    ─────────────────────────── (seal)      ─────────────────────────── (unseal)
    Δ ∣ −X^α ⊢ −X : P ⇒ α                   Δ ∣ +X^α ⊢ +X : α ⇒ P

`id` has no premise: every type at a boundary is a spelling, so it is
well formed already.

### Terms

`Δ ∣ Γ ⊢ M : A`, with `Γ` mapping term variables to NAMED types.

    ─────────── (const, k : ι)      ───────────────── (var)
    Δ ∣ Γ ⊢ k : ι                   Δ ∣ Γ ⊢ x : Γ(x)

    Δ ⊢ A     Δ ∣ Γ, x:A ⊢ N : B
    ──────────────────────────── (lam)
    Δ ∣ Γ ⊢ λx:A. N : A → B

    Δ ∣ Γ ⊢ L : A → B     Δ ∣ Γ ⊢ M : A
    ──────────────────────────────────── (app)
    Δ ∣ Γ ⊢ L M : B

    Δ, α^X, X:=α ∣ Γ ⊢ N : C        X, α ∉ Δ
    ──────────────────────────────────────── (Lam)
    Δ ∣ Γ ⊢ ΛX^α. N : ∀X. C

    Δ ⊢ A    Δ ∣ Γ ⊢ L : ∀X. C    Δ ⊢ B
    Δ, α^X:=Δ(A) ∣ +X^α ⊢ c : (Δ, α^X:=Δ(A), X:=α)(C) ⇒ (Δ, α^X:=Δ(A))(B)
    ─────────────────────────────────────────────────────────────── (ν)
    Δ ∣ Γ ⊢ ν X:=A. (L X)⟨c⟩ : B                            X, α ∉ Δ

    Δ ⊢ ε    ε(Δ) ∣ ∅ ⊢ M : A    ε(Δ) ⊢ A    Δ ⊢ B
    Δ ∣ ε ⊢ c : ε(Δ)(A) ⇒ Δ(B)
    ──────────────────────────────────────────────── (boundary)
    Δ ∣ Γ ⊢ [ε] M ⟨c⟩ : B

* A boundary's body is term-closed, typed in the interior at a named
  type `A`.  Its result is a named type `B` in the exterior.  The
  conversion relates the two READINGS.  So a layer carrying `id` reads
  its two types as one runtime type, possibly through different names
  (in de Bruijn form, through different name positions).
* In `ν`, the conversion is typed where the new variable has its
  payload and is named `X`; the result `B` is read with the variable
  allocated but unnamed, which is TyBeta's exterior.  Since `B` is
  read in `Δ` plus an unnamed variable, it cannot mention `α`.
* `app` compares named types syntactically.

Agda: `_∣_,_⊢_⦂_⟹_` (conversions), `_∣_⊢_⦂_` (terms) in `Terms.agda`.

## 4. Values

    Values      V,W  ::=  k | F | S
    Functional  F    ::=  λx:A. N | ΛX^α. N
                       |  [ε] V ⟨c → d⟩ | [ε] V ⟨∀X. c⟩
                       |  [+X^α] F ⟨id⟩
                       |  [−X^α] F ⟨id⟩      unless F = [+X^α] F′ ⟨id⟩
    Sealed      S    ::=  [−X^α] V ⟨−X⟩  |  [+Z^γ] S ⟨id⟩

* A functional value has an arrow or `∀` type; a sealed value has a
  variable type; a constant has a base type.
* A sealed value is a seal under any number of REVEAL layers carrying
  `id`.  A hide carrying `id` over a sealed value is never a value
  (§5: Sink, Swap or CancelId fires).
* A hide over a reveal of the same variable, both `id`, is the
  CancelId redex, so it is excluded from the functional values.
* `ΛX^α. N` is a value for every body: there is no reduction under `Λ`.
* An `id` layer over a constant is not a value: Id removes it.

Agda: `Value`, `Fun`, `Sealed` in `Reduction.agda`.

## 5. Reduction

`Δ ⊢ M ⟶ N ⊣ ξ`, where `ξ` is the allocation, if any.

    Δ ⊢ (λx:A. N) V  ⟶  N[x := V]                                    (Beta)

    Δ ⊢ [ε] V ⟨c → d⟩ W  ⟶  [ε] (V ([−ε] W ⟨c⟩)) ⟨d⟩                 (Wrap)
    Δ ⊢ [ε] V ⟨id⟩ W     ⟶  [ε] (V ([−ε] W ⟨id⟩)) ⟨id⟩               (Wrap-id)

    Δ ⊢ ν X:=A. (V X)⟨d⟩  ⟶  [+X^α] (V • X^α) ⟨d⟩   ⊣ α^X:=Δ(A)      (TyBeta)
        α fresh, where
          (ΛX^β. N) • X^α          =  N[β ↦ α]
          ([ε] V ⟨∀Y. c⟩) • X^α    =  [ε] (V • X^α) ⟨c⟩
          ([ε] V ⟨id⟩) • X^α       =  [ε] (V • X^α) ⟨id⟩

    Δ ⊢ [ε] k ⟨id⟩  ⟶  k                                             (Id)

    Δ ⊢ [+X^α] ([−X^α] W ⟨−X⟩) ⟨+X⟩  ⟶  W                            (Cancel-□)
    Δ ⊢ [−X^α] ([+X^α] V ⟨id⟩) ⟨id⟩  ⟶  V                            (CancelId)
        if [+X^α] V ⟨id⟩ is a value

    Δ ⊢ [−Z^γ] ([−X^α] V ⟨−X⟩) ⟨id⟩  ⟶  [−X^α] ([−Z^γ] V ⟨id⟩) ⟨−X⟩  (Sink)
        if γ ≠ α
    Δ ⊢ [−Z^γ] ([+W^δ] S ⟨id⟩) ⟨id⟩  ⟶  [+W^δ] ([−Z^γ] S ⟨id⟩) ⟨id⟩  (Swap)
        if γ ≠ δ
    Δ ⊢ [+X^α] ([+Z^γ] S ⟨id⟩) ⟨+X⟩  ⟶  [+Z^γ] ([+X^α] S ⟨+X⟩) ⟨id⟩  (Push)

    Δ ⊢ E[M]  ⟶  E[M′] ⊣ ξ      if E(Δ) ⊢ M ⟶ M′ ⊣ ξ                 (ξ)
    E  ::=  □ M | V □ | ν X:=A. (□ X)⟨c⟩ | [ε] □ ⟨c⟩

with `V, W` values and `S` a sealed value.

* **Beta** substitutes a closed value.  A copy that crosses a
  `ΛY^β` is wrapped in a hide of the `Λ`'s own variable:

      (ΛY^β. N)[x := V]  =  ΛY^β. N[x := [−Y^β] V ⟨id⟩]

  so the copy's holes keep their name map (`V` was typed where `Y` is
  not named).  A boundary's body is term-closed, so substitution stops
  there.
* **Wrap** sends an argument through a boundary with the inverse entry;
  **TyBeta** allocates a variable for the instantiation, reveals it as
  `X` around the body, and strips one `∀` from every layer of a
  `∀`-typed tower.  The `Λ`'s abstract variable becomes the allocated
  one.
### Why each boundary rule

An unseal `[+X^α] V ⟨+X⟩` must reach the seal `[−X^α] W ⟨−X⟩` of its
own variable.  On the way, a run leaves `id` layers between the two,
and Id removes an `id` layer only over a constant.  The layers come
from three places:

* Beta's hide around a copy under `Λ` (5c);
* TyBeta's reveal `[+Y^β] … ⟨id⟩` when the instantiated body's type
  does not mention `Y` (5c, 5e);
* Wrap, which gives the argument the inverse of each layer's entry,
  with `id` where the layer's domain is `id` (5b, 5e).

Each boundary rule removes or crosses one kind of layer.  Each is
NEEDED: §7's examples are run with every rule, and removing any one
of the five rules leaves an example stuck at a well-typed term that is
not a value (`tools/ablate.py` reruns the examples without each rule
and prints where they stop).

* **Cancel-□**, `[+X^α] ([−X^α] W ⟨−X⟩) ⟨+X⟩ ⟶ W`: the unseal meets its
  seal and both layers go.  Every unseal ends this way (5b, 5c, 5d,
  5e).  Without it, 5d stops after 14 steps at
  `[+X^α] [−X^α] [+X^α] [−X^α] 5 ⟨−X⟩ ⟨+X⟩ ⟨id⟩ ⟨id⟩`.
* **CancelId**, `[−X^α] ([+X^α] V ⟨id⟩) ⟨id⟩ ⟶ V`: a hide directly over
  a reveal of the same variable.  5b creates the pair: the third Wrap
  puts `[+X^α] … ⟨id⟩` around the argument, and Beta returns it
  under the function's `[−X^α] … ⟨id⟩`.  Without it, 5b stops after 8
  steps at

      [+X^α] [+Y^β] [−X^α] [+X^α] [−Y^β] [−X^α] false
        ⟨−X⟩ ⟨−Y⟩ ⟨id⟩ ⟨id⟩ ⟨+Y⟩ ⟨+X⟩

  where the pair sits between the unseal of `Y` and its seal.  The
  value grammar excludes this left-hand side (§4), which is the
  experiment's starting point: the pair is not a value, so it must
  step.  5e needs it too, once Swap has brought the pair together.
* **Sink**, a hide moves below a seal of another variable.  5c's Beta
  copies `x`, the `X`-sealed `3`, under `ΛY`, so the copy is
  `[−Y^ζ] ([−X^α] 3 ⟨−X⟩) ⟨id⟩`, and after TyBeta it sits under the
  unseal of `X`.  Without Sink, 5c stops after 7 steps at
  `[+X^α] [+Y^β] [−Y^β] [−X^α] 3 ⟨−X⟩ ⟨id⟩ ⟨id⟩ ⟨+X⟩`.  The reveal of
  `Y` is ABOVE the hide, the order CancelId does not remove, and the
  hide blocks the unseal.  Sinking it puts it on the constant, where Id
  removes it.
  5e uses it twice to take a hide of `W` down to `false`.
* **Swap**, a hide moves below a reveal of another variable, over a
  sealed value.  In 5e the last Wrap gives the argument a hide of `W`
  over a reveal of `X`.  Without Swap, 5e stops after 9 steps with the
  argument `[−W^γ] [+X^α] [−Y^β] [−X^α] false ⟨−X⟩ ⟨−Y⟩ ⟨id⟩ ⟨id⟩`, which
  is not a value (a hide over a sealed value), so Beta cannot fire.
  Later, Swap moves the function's `[−X^α]` past `[+W^γ]` onto the
  `[+X^α]` it cancels with.
* **Push**, an unseal moves through a reveal of another variable.  5c's
  inner instantiation leaves `[+Y^β] … ⟨id⟩` between the unseal of `X`
  and its seal.  Without Push, 5c stops after 9 steps at
  `[+X^α] [+Y^β] [−X^α] 3 ⟨−X⟩ ⟨id⟩ ⟨+X⟩` (§1).  The reveal cannot be
  removed: its body may mention `Y`.  5e pushes two unseals through
  `[+W^γ]`.

**No reveal carrying `id` moves inward.**  Sink and Swap move a hide
inward; Push moves an unseal inward and the reveal it crosses outward.
Moving a hide inward is safe for names: every context between its old
and new position gains names.  The first version also sank reveals
carrying `id` below seals.  That could leave a layer whose type
no name denotes, which is why it needed runtime types
(`CancelIdSketch.md` §8, with 5b).  All five rules restore or keep the
name map exactly, so none needs a premise about names.  CancelId's one
side condition, that the reveal it removes is a value, is there for
determinism (§8).

Agda: `_⊢_⟶_∣_` in `Reduction.agda`; `crossΛ` is the hide around a
copy, `_•⟶_` is `•`, and `Alloc` is `ξ` (`new P` allocates an unnamed
variable at the head of the store, and the siblings of the redex
shift).

## 6. Elaboration from System F

A source program is plain System F over the same named types:

    L,M,N  ::=  k | x | λx:A. N | L M | ΛX. N | L [A]

Elaboration `⟦·⟧` is structural except at type application, which
becomes an instantiation:

    ⟦L [A]⟧  =  ν X:=A. (⟦L⟧ X)⟨reveal_X(C)⟩          where L : ∀X. C

The conversion unseals `X` where `C` runs covariantly and seals it where
`C` runs contravariantly; every other leaf is `id`:

    reveal_X(X)       =  +X                conceal_X(X)       =  −X
    reveal_X(Y)       =  id  (Y ≠ X)       conceal_X(Y)       =  id
    reveal_X(ι)       =  id                conceal_X(ι)       =  id
    reveal_X(A → B)   =  conceal_X(A) → reveal_X(B)
    conceal_X(A → B)  =  reveal_X(A) → conceal_X(B)
    reveal_X(∀Y. A)   =  ∀Y. reveal_X(A)
    conceal_X(∀Y. A)  =  ∀Y. conceal_X(A)

A compound identity stays structural: `reveal_Y(Int → X)` is
`id → id`.  A source `ΛX. N` elaborates to `ΛX^ζ. ⟦N⟧` with `ζ` fresh;
the examples write the variable only where Beta's hide mentions it.
This is `strong-rep-nu`'s `compile` (`Compile.agda`, `reveal 0 C`).
`nu-cancel-id` has no compiler in Agda, and `Examples.agda` gives the
elaborated terms directly.  `tools/nuc.py` implements this elaboration
together with the reduction rules of §5.

## 7. Examples

Each example gives the System F program, its elaboration, and the run
to a value.  Every run starts at the empty context; `⊣` shows an
allocation, and `where` names a subterm that the following lines
abbreviate.  Every run is checked in Agda (`Examples.agda`), and
preservation types each of its states.  The traces below are printed
by `tools/nuc.py`.  The Agda runs of 5a, 5d and 5e are generated from
the same interpreter by `tools/gen_examples.py`; 5b and 5c are written
by hand.

The boundary rules each example uses, with the number of times (§5,
"Why each boundary rule", says where each rule is needed):

| rule | 5a | 5b | 5c | 5d | 5e |
|---|---|---|---|---|---|
| Cancel-□ | | 2 | 1 | 1 | 2 |
| CancelId | | 1 | | | 1 |
| Sink | | | 1 | | 2 |
| Swap | | | | | 2 |
| Push | | | 1 | | 2 |

5a uses none: its sealed argument is discarded.

### 5a. `K`

The argument `f` ignores its argument, so the sealed `false` is
discarded (11 steps).

    ((ΛX. λf:(∀Y. Y → Bool). f [X]) [Bool] (ΛZ. λz:Z. true)) false
                                                                  : Bool
    ⇒ elaborate
    (ν X:=Bool. ((ΛX. F) X)⟨(∀Y. id → id) → (−X → id)⟩) G false
        where F = λf:(∀Y. Y → Bool). ν Y:=X. (f Y)⟨−Y → id⟩
              G = ΛZ. λz:Z. true
    → TyBeta    [+X^α] F ⟨(∀Y. id → id) → (−X → id)⟩ G false   ⊣ α^X:=Bool
    → Wrap      [+X^α] (F ([−X^α] G ⟨∀Y. id → id⟩)) ⟨−X → id⟩ false
    → Beta      [+X^α] (ν Y:=X. (([−X^α] G ⟨∀Y. id → id⟩) Y)⟨−Y → id⟩)
                  ⟨−X → id⟩ false
    → TyBeta    [+X^α] [+Y^β] [−X^α] (λz:Y. true) ⟨id → id⟩ ⟨−Y → id⟩
                  ⟨−X → id⟩ false                             ⊣ β^Y:=α
    → Wrap      [+X^α] ([+Y^β] [−X^α] (λz:Y. true) ⟨id → id⟩ ⟨−Y → id⟩
                          ([−X^α] false ⟨−X⟩)) ⟨id⟩
    → Wrap      [+X^α] [+Y^β] ([−X^α] (λz:Y. true) ⟨id → id⟩
                          ([−Y^β] [−X^α] false ⟨−X⟩ ⟨−Y⟩)) ⟨id⟩ ⟨id⟩
    → Wrap      [+X^α] [+Y^β] [−X^α] ((λz:Y. true)
                          ([+X^α] [−Y^β] [−X^α] false ⟨−X⟩ ⟨−Y⟩ ⟨id⟩))
                  ⟨id⟩ ⟨id⟩ ⟨id⟩
    → Beta      [+X^α] [+Y^β] [−X^α] true ⟨id⟩ ⟨id⟩ ⟨id⟩
    → Id        [+X^α] [+Y^β] true ⟨id⟩ ⟨id⟩
    → Id        [+X^α] true ⟨id⟩
    → Id        true

The second TyBeta runs inside `[+X^α]`, where `X` names `α`, so `Y:=X`
allocates `β` with payload `α`.  The third Wrap's argument is a reveal
over a sealed value, so it is a value.

### 5b. `K` returning its argument

The same program with `f` returning its argument, so the sealed `false`
comes back out through every layer (11 steps, as in νF; `run-5b`).

    ((ΛX. λf:(∀Y. Y → Y). f [X]) [Bool] (ΛZ. λz:Z. z)) false     : Bool
    ⇒ elaborate
    (ν X:=Bool. ((ΛX. F) X)⟨(∀Y. id → id) → (−X → +X)⟩) G false
        where F = λf:(∀Y. Y → Y). ν Y:=X. (f Y)⟨−Y → +Y⟩
              G = ΛZ. λz:Z. z
    → TyBeta    [+X^α] F ⟨(∀Y. id → id) → (−X → +X)⟩ G false   ⊣ α^X:=Bool
    → Wrap      [+X^α] (F ([−X^α] G ⟨∀Y. id → id⟩)) ⟨−X → +X⟩ false
    → Beta      [+X^α] (ν Y:=X. (([−X^α] G ⟨∀Y. id → id⟩) Y)⟨−Y → +Y⟩)
                  ⟨−X → +X⟩ false
    → TyBeta    [+X^α] [+Y^β] [−X^α] (λz:Y. z) ⟨id → id⟩ ⟨−Y → +Y⟩
                  ⟨−X → +X⟩ false                             ⊣ β^Y:=α
    → Wrap      [+X^α] ([+Y^β] [−X^α] (λz:Y. z) ⟨id → id⟩ ⟨−Y → +Y⟩
                          ([−X^α] false ⟨−X⟩)) ⟨+X⟩
    → Wrap      [+X^α] [+Y^β] ([−X^α] (λz:Y. z) ⟨id → id⟩
                          ([−Y^β] [−X^α] false ⟨−X⟩ ⟨−Y⟩)) ⟨+Y⟩ ⟨+X⟩
    → Wrap      [+X^α] [+Y^β] [−X^α] ((λz:Y. z)
                          ([+X^α] [−Y^β] [−X^α] false ⟨−X⟩ ⟨−Y⟩ ⟨id⟩))
                  ⟨id⟩ ⟨+Y⟩ ⟨+X⟩
    → Beta      [+X^α] [+Y^β] [−X^α] [+X^α] [−Y^β] [−X^α] false
                  ⟨−X⟩ ⟨−Y⟩ ⟨id⟩ ⟨id⟩ ⟨+Y⟩ ⟨+X⟩
    → CancelId  [+X^α] [+Y^β] [−Y^β] [−X^α] false ⟨−X⟩ ⟨−Y⟩ ⟨+Y⟩ ⟨+X⟩
    → Cancel-□  [+X^α] [−X^α] false ⟨−X⟩ ⟨+X⟩
    → Cancel-□  false

The hide `[−X^α]` that the function's tower puts over the result meets
the reveal `[+X^α]` that the third Wrap put around the argument, and
CancelId removes the pair.

### 5c. An unseal reaching its seal through a later reveal

The program of §1 (12 steps; `run-5c`).

    (ΛX. λx:X. (ΛY. λ_:Int. x) [Bool] 0) [Int] 3                 : Int
    ⇒ elaborate
    (ν X:=Int. ((ΛX. λx:X. B) X)⟨−X → +X⟩) 3
        where B = (ν Y:=Bool. ((ΛY. λ_:Int. x) Y)⟨id → id⟩) 0
    → TyBeta    [+X^α] (λx:X. B) ⟨−X → +X⟩ 3                  ⊣ α^X:=Int
    → Wrap      [+X^α] ((λx:X. B) ([−X^α] 3 ⟨−X⟩)) ⟨+X⟩
    → Beta      [+X^α] ((ν Y:=Bool. ((ΛY^ζ. λ_:Int. C) Y)⟨id → id⟩) 0)
                  ⟨+X⟩
                    where C = [−Y^ζ] [−X^α] 3 ⟨−X⟩ ⟨id⟩
    → TyBeta    [+X^α] ([+Y^β] (λ_:Int. C′) ⟨id → id⟩ 0) ⟨+X⟩  ⊣ β^Y:=Bool
                    where C′ = [−Y^β] [−X^α] 3 ⟨−X⟩ ⟨id⟩
    → Wrap      [+X^α] [+Y^β] ((λ_:Int. C′) ([−Y^β] 0 ⟨id⟩)) ⟨id⟩ ⟨+X⟩
    → Id        [+X^α] [+Y^β] ((λ_:Int. C′) 0) ⟨id⟩ ⟨+X⟩
    → Beta      [+X^α] [+Y^β] [−Y^β] [−X^α] 3 ⟨−X⟩ ⟨id⟩ ⟨id⟩ ⟨+X⟩
    → Sink      [+X^α] [+Y^β] [−X^α] [−Y^β] 3 ⟨id⟩ ⟨−X⟩ ⟨id⟩ ⟨+X⟩
    → Id        [+X^α] [+Y^β] [−X^α] 3 ⟨−X⟩ ⟨id⟩ ⟨+X⟩
    → Push      [+Y^β] [+X^α] [−X^α] 3 ⟨−X⟩ ⟨+X⟩ ⟨id⟩
    → Cancel-□  [+Y^β] 3 ⟨id⟩
    → Id        3

The hide `[−Y^ζ]` is Beta's wrapper for the copy of `x` under `ΛY`;
TyBeta turns `ζ` into the allocated `β`.  The hide sinks below the `X`
seal and Id removes it.  In the state after the second Beta, the hide
`[−Y^β]` reads its body's type `X` and its own type `X` as `α`.

### 5d. An inverse pair whose conversions compose to an unseal

(17 steps.)

    ((ΛX. λx:X. λg:(Int → X) → Int → Int. g (λn:Int. x)) [Int]
       5 (λh:Int → Int. h)) 0                                    : Int
    ⇒ elaborate
    (ν X:=Int. ((ΛX. F) X)⟨−X → d⟩) 5 H 0
        where F = λx:X. λg:(Int → X) → Int → Int. g (λn:Int. x)
              H = λh:Int → Int. h
              d = ((id → +X) → (id → id)) → (id → id)
    → TyBeta    [+X^α] F ⟨−X → d⟩ 5 H 0                       ⊣ α^X:=Int
    → Wrap      [+X^α] (F ([−X^α] 5 ⟨−X⟩)) ⟨d⟩ H 0
    → Beta      [+X^α] (λg:(Int → X) → Int → Int. g (λn:Int. W)) ⟨d⟩ H 0
                    where W = [−X^α] 5 ⟨−X⟩
    → Wrap      [+X^α] ((λg:(Int → X) → Int → Int. g (λn:Int. W))
                          ([−X^α] H ⟨(id → +X) → (id → id)⟩)) ⟨id → id⟩ 0
    → Beta      [+X^α] (([−X^α] H ⟨(id → +X) → (id → id)⟩) (λn:Int. W))
                  ⟨id → id⟩ 0
    → Wrap      [+X^α] [−X^α] (H ([+X^α] (λn:Int. W) ⟨id → +X⟩))
                  ⟨id → id⟩ ⟨id → id⟩ 0
    → Beta      [+X^α] [−X^α] [+X^α] (λn:Int. W) ⟨id → +X⟩ ⟨id → id⟩
                  ⟨id → id⟩ 0
    → Wrap      [+X^α] ([−X^α] [+X^α] (λn:Int. W) ⟨id → +X⟩ ⟨id → id⟩
                          ([−X^α] 0 ⟨id⟩)) ⟨id⟩
    → Id        [+X^α] ([−X^α] [+X^α] (λn:Int. W) ⟨id → +X⟩ ⟨id → id⟩ 0)
                  ⟨id⟩
    → Wrap      [+X^α] [−X^α] ([+X^α] (λn:Int. W) ⟨id → +X⟩
                          ([+X^α] 0 ⟨id⟩)) ⟨id⟩ ⟨id⟩
    → Id        [+X^α] [−X^α] ([+X^α] (λn:Int. W) ⟨id → +X⟩ 0) ⟨id⟩ ⟨id⟩
    → Wrap      [+X^α] [−X^α] [+X^α] ((λn:Int. W) ([−X^α] 0 ⟨id⟩))
                  ⟨+X⟩ ⟨id⟩ ⟨id⟩
    → Id        [+X^α] [−X^α] [+X^α] ((λn:Int. W) 0) ⟨+X⟩ ⟨id⟩ ⟨id⟩
    → Beta      [+X^α] [−X^α] [+X^α] [−X^α] 5 ⟨−X⟩ ⟨+X⟩ ⟨id⟩ ⟨id⟩
    → Cancel-□  [+X^α] [−X^α] 5 ⟨id⟩ ⟨id⟩
    → Id        [+X^α] 5 ⟨id⟩
    → Id        5

After the third Beta, the layers `[−X^α] [+X^α]` carry `id → id` and
`id → +X`, not `id`, so CancelId does not apply.  Their conversions
compose to an unseal, so removing them would be ill typed.  The tower
is a functional value, and the three Wraps take `0` through it.

### 5e. A hide and its re-reveal separated by another reveal

5b with an argument that instantiates a type of its own: `G`'s body
applies `ΛW` to `Bool`, which leaves a reveal `[+W^γ]` beneath the
function's hide `[−X^α]` (21 steps).

    ((ΛX. λf:(∀Y. Y → Y). f [X]) [Bool]
       (ΛZ. (ΛW. λz:Z. z) [Bool])) false                         : Bool
    ⇒ elaborate
    (ν X:=Bool. ((ΛX. F) X)⟨(∀Y. id → id) → (−X → +X)⟩) G false
        where F = λf:(∀Y. Y → Y). ν Y:=X. (f Y)⟨−Y → +Y⟩
              G = ΛZ. ν W:=Bool. ((ΛW. λz:Z. z) W)⟨id → id⟩
    → TyBeta    [+X^α] F ⟨(∀Y. id → id) → (−X → +X)⟩ G false   ⊣ α^X:=Bool
    → Wrap      [+X^α] (F ([−X^α] G ⟨∀Y. id → id⟩)) ⟨−X → +X⟩ false
    → Beta      [+X^α] (ν Y:=X. (([−X^α] G ⟨∀Y. id → id⟩) Y)⟨−Y → +Y⟩)
                  ⟨−X → +X⟩ false
    → TyBeta    [+X^α] [+Y^β] [−X^α] (ν W:=Bool. ((ΛW. I) W)⟨id → id⟩)
                  ⟨id → id⟩ ⟨−Y → +Y⟩ ⟨−X → +X⟩ false         ⊣ β^Y:=α
                    where I = λz:Y. z
    → TyBeta    [+X^α] [+Y^β] [−X^α] [+W^γ] I ⟨id → id⟩ ⟨id → id⟩
                  ⟨−Y → +Y⟩ ⟨−X → +X⟩ false                 ⊣ γ^W:=Bool
    → Wrap      [+X^α] ([+Y^β] [−X^α] [+W^γ] I ⟨id → id⟩ ⟨id → id⟩
                          ⟨−Y → +Y⟩ ([−X^α] false ⟨−X⟩)) ⟨+X⟩
    → Wrap      [+X^α] [+Y^β] ([−X^α] [+W^γ] I ⟨id → id⟩ ⟨id → id⟩
                          ([−Y^β] [−X^α] false ⟨−X⟩ ⟨−Y⟩)) ⟨+Y⟩ ⟨+X⟩
    → Wrap      [+X^α] [+Y^β] [−X^α] ([+W^γ] I ⟨id → id⟩
                          ([+X^α] [−Y^β] [−X^α] false ⟨−X⟩ ⟨−Y⟩ ⟨id⟩))
                  ⟨id⟩ ⟨+Y⟩ ⟨+X⟩
    → Wrap      E[[−W^γ] [+X^α] [−Y^β] [−X^α] false ⟨−X⟩ ⟨−Y⟩ ⟨id⟩ ⟨id⟩]
                    where E = [+X^α] [+Y^β] [−X^α] [+W^γ] (I □)
                                ⟨id⟩ ⟨id⟩ ⟨+Y⟩ ⟨+X⟩
    → Swap      E[[+X^α] [−W^γ] [−Y^β] [−X^α] false ⟨−X⟩ ⟨−Y⟩ ⟨id⟩ ⟨id⟩]
    → Sink      E[[+X^α] [−Y^β] [−W^γ] [−X^α] false ⟨−X⟩ ⟨id⟩ ⟨−Y⟩ ⟨id⟩]
    → Sink      E[[+X^α] [−Y^β] [−X^α] [−W^γ] false ⟨id⟩ ⟨−X⟩ ⟨−Y⟩ ⟨id⟩]
    → Id        E[[+X^α] [−Y^β] [−X^α] false ⟨−X⟩ ⟨−Y⟩ ⟨id⟩]
    → Beta      [+X^α] [+Y^β] [−X^α] [+W^γ] [+X^α] [−Y^β] [−X^α] false
                  ⟨−X⟩ ⟨−Y⟩ ⟨id⟩ ⟨id⟩ ⟨id⟩ ⟨+Y⟩ ⟨+X⟩
    → Swap      [+X^α] [+Y^β] [+W^γ] [−X^α] [+X^α] [−Y^β] [−X^α] false
                  ⟨−X⟩ ⟨−Y⟩ ⟨id⟩ ⟨id⟩ ⟨id⟩ ⟨+Y⟩ ⟨+X⟩
    → CancelId  [+X^α] [+Y^β] [+W^γ] [−Y^β] [−X^α] false
                  ⟨−X⟩ ⟨−Y⟩ ⟨id⟩ ⟨+Y⟩ ⟨+X⟩
    → Push      [+X^α] [+W^γ] [+Y^β] [−Y^β] [−X^α] false
                  ⟨−X⟩ ⟨−Y⟩ ⟨+Y⟩ ⟨id⟩ ⟨+X⟩
    → Cancel-□  [+X^α] [+W^γ] [−X^α] false ⟨−X⟩ ⟨id⟩ ⟨+X⟩
    → Push      [+W^γ] [+X^α] [−X^α] false ⟨−X⟩ ⟨+X⟩ ⟨id⟩
    → Cancel-□  [+W^γ] false ⟨id⟩
    → Id        false

* **The third TyBeta** fires inside the function's tower.  `Λ` bodies
  do not reduce, so `G`'s body waits until the second TyBeta strips
  `ΛZ` and exposes it.
* **The last Wrap** passes the argument through `[+W^γ]`, which
  gives it a hide of `W` over a reveal of `X`: not a value.  Swap,
  two Sinks and Id move that hide down to `false` and remove it.
* **After the second Beta**, the hide `[−X^α]` and its re-reveal
  `[+X^α]` are separated by `[+W^γ]`.  This is the shape of the
  hand-written 5e in `SingleEntrySketch.md`, which was stuck with named
  types under the old Cancel.  Swap brings the pair together and
  CancelId removes it.  Push then carries each unseal through
  `[+W^γ]` to its seal.

## 8. Metatheory

**Progress** (checked: `Progress.agda`, `proof/Progress.agda`).  A
well-typed closed term is a value or steps.  Canonical forms, at named
types: a value of base type is a constant; of arrow or `∀` type is
functional; of variable type is sealed.  For a boundary over a value:

* An unseal `[+X^α] V ⟨+X⟩` has a body whose type reads as `α` with `X`
  named, so `V` is sealed.  If `V` is a seal, its variable is `α` and
  Cancel-□ fires; if `V` is a reveal over a sealed value, Push fires.
* An `id` layer over a constant: Id.  A reveal over a functional or
  sealed value: a value.  A hide over a functional value: a value, or
  CancelId.  A hide over a sealed value: Sink (over a seal of another
  variable), Swap (over a reveal of another variable) or CancelId (over
  a reveal of its own); a hide of `X` directly over `X`'s seal is
  incoherent, since `X` is not named inside the hide.

**Preservation** (checked: `Preservation.agda`, `proof/Preservation.agda`).
If `Δ ∣ ∅ ⊢ M : A` and `Δ ⊢ M ⟶ N ⊣ ξ`, then `Δ, ξ ∣ ∅ ⊢ N : A`,
with the new variable unnamed.

* **CancelId, Cancel-□.**  The two entries restore the exterior name
  map exactly.  The body's type and the result type spell the same
  runtime type there (`id`; or the seal and unseal of one payload), and
  spelling is injective, so they are the same named type.
* **Sink, Swap, Push.**  Entries on different variables commute, so the
  moved body keeps its context.  The moved layer's new exterior has
  every name of the context its type was read in before, so the type
  can be re-read there.  For Push, the reveal's type changes from `X` to
  the unseal's result `B`, which is named in the unseal's exterior, and
  both of the reveal's new contexts contain it.
* **TyBeta.**  The `Λ`'s abstract variable becomes the allocated one,
  with its payload; refining an abstract variable preserves typing.
* **Beta.**  Substitution; a copy under `Λ` is typed through its hide.
* **Allocation inside a frame.**  The siblings are weakened by an
  unnamed variable, which moves no name.

**Determinism** (checked: `Determinism.agda`,
`proof/Determinism.agda`).  If `Δ ⊢ M ⟶ N₁ ⊣ ξ₁` and
`Δ ⊢ M ⟶ N₂ ⊣ ξ₂`, then `N₁ = N₂` and `ξ₁ = ξ₂`; no typing is needed.
Values do not step, and the left-hand sides are disjoint: Sink needs a
seal under the hide, Swap a reveal of another variable, CancelId a
reveal of the same one; Push needs a reveal under an unseal, Cancel-□ a
seal.  Swap and Push need a SEALED body, so a hide over a reveal over a
functional value stays a value.  TyBeta's payload is the spelling of
`A`, which is a function, and its fresh variable is unique up to
renaming (in the Agda it is always index 0).

CancelId's side condition is what makes the left-hand sides disjoint
from the ξ rule.  Over a constant, `[−X^α] ([+X^α] k ⟨id⟩) ⟨id⟩` would
otherwise step both by CancelId, to `k`, and by Id under the hide, to
`[−X^α] k ⟨id⟩`.  With the condition only the second applies, and Id
then gives `k` as well.  No example needs CancelId over a constant;
progress applies it only over functional and sealed values.

**Color** (checked: `ColorPreservation.agda`,
`proof/ColorPreservation.agda`; residuals in `Residual.agda`).  A
position is a hole `C` with the node `M` in it.  Its COLOR is its name
map: under the naming condition that is the list of variables named at
the hole, newest first, since name `X` denotes the `X`-th of them.  A
step moves a position to its RESIDUALS.  The nodes the redex consumes
have none: its own layers, and Id's constant.  The theorem: if
`Δ ∣ ∅ ⊢ L : A` and a run from `L` to `L′`, ending at `Δ′`, takes
`(C , M)` to `(D , N)`, then the name map at `D` in `Δ′` is the name
map at `C` in `Δ` with each variable renamed by the residual's `ρ`.  So
the number of names in scope is unchanged.  `ρ` is the identity,
except in two places, where it shifts variables past one that was
inserted below them:

* a sibling of an allocation (the new variable is unnamed);
* a copy that Beta's hide carries under a `Λ`.  The hide unnames the
  `Λ`'s variable, so the copy sees the same names as before, each one
  shifted past it.

Residuals are real positions: `L = C[M]` and `L′ = D[N]`
(`residuals-sound`).  Rule by rule:

* **Sink, Swap and Push** commute entries for different variables, so
  the moved body's map is unchanged.  Push needs no premise: an unseal
  and a reveal of the same variable set the same flag.
* **CancelId and Cancel-□** restore the exterior map exactly, and so do
  Wrap's two entries on the argument.  This is where typing is used:
  the redex's variable already has, outside, the flag that the second
  entry sets.  That is coherence.
* **TyBeta**: the allocated variable, revealed, takes the place of the
  variable the `Λ` named, so the body's map is unchanged.  Each layer
  of a `∀`-typed tower moves past it.
* **Beta**: the body keeps its frames, since substitution stops at
  boundaries.  A copy under `k` `Λ`s is wrapped in `k` hides.  The
  map moves past each hidden variable, which is the renaming above.

## 9. Against earlier designs

* **νF₁** (`SingleEntrySketch.md`) has the same single-entry
  boundaries, but its Cancel walks an unseal down an identity tower in
  one non-local step and leaves layers whose types have no name, so it
  types terms at runtime types.  Here the local rules keep every type
  named.
* **Push** is close to D39's `IdPush`, which also moved the unseal
  inward but created an identity at a looked-up type.  Here `id` is
  untyped, so Push has no premise.
* **CancelId** is the sketch's PairCancel restricted to two `id`s,
  where the types agree by construction.
* **Sink** is D02's `Commute`, restricted to a hide over a seal.
