# νF₁ᶜ — the design, with variables as names (2026-11-08)

This is the on-paper presentation of the calculus mechanized in this
directory, written in one piece.  It is the second version of the
experiment in `../strong-rep-nu/notes/CancelIdSketch.md` (§8 there).
That note keeps the history: why CancelId alone is stuck (§2), the
first version's Sink and why it needed runtime types (§§3–7, §8).  This
file restates the current design from scratch, with variables as names,
and says where each part lives in the Agda.

Status: type safety (progress and preservation) is CHECKED in Agda.
Determinism and color preservation are argued on paper only (§7).
Examples 5b and 5c are checked; 5a, 5d and 5e are hand-derived.

## 1. A first example

The program 5c instantiates `X` with `Int`, passes `3`, and inside
instantiates `Y` with `Bool` and returns the outer argument:

    (ΛX. λx:X. (ΛY. λ_:Int. x) [Bool] 0) [Int] 3                : Int

After nine steps (§6) it reaches

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

    Δ ⊢ A     Δ ∣ Γ, x:A ⊢ N : B           Δ ∣ Γ ⊢ L : A → B     Δ ∣ Γ ⊢ M : A
    ───────────────────────── (lam)        ──────────────────────────────── (app)
    Δ ∣ Γ ⊢ λx:A. N : A → B                Δ ∣ Γ ⊢ L M : B

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

    Δ ⊢ (λx:A. N) V  ⟶  N[x := V]                                      (Beta)

    Δ ⊢ [ε] V ⟨c → d⟩ W  ⟶  [ε] (V ([−ε] W ⟨c⟩)) ⟨d⟩                   (Wrap)
    Δ ⊢ [ε] V ⟨id⟩ W     ⟶  [ε] (V ([−ε] W ⟨id⟩)) ⟨id⟩                 (Wrap-id)

    Δ ⊢ ν X:=A. (V X)⟨d⟩  ⟶  [+X^α] (V • X^α) ⟨d⟩   ⊣ α^X:=Δ(A)        (TyBeta)
        α fresh, where
          (ΛX^β. N) • X^α          =  N[β ↦ α]
          ([ε] V ⟨∀Y. c⟩) • X^α    =  [ε] (V • X^α) ⟨c⟩
          ([ε] V ⟨id⟩) • X^α       =  [ε] (V • X^α) ⟨id⟩

    Δ ⊢ [ε] k ⟨id⟩  ⟶  k                                                (Id)

    Δ ⊢ [+X^α] ([−X^α] W ⟨−X⟩) ⟨+X⟩  ⟶  W                              (Cancel-□)
    Δ ⊢ [−X^α] ([+X^α] V ⟨id⟩) ⟨id⟩  ⟶  V                              (CancelId)

    Δ ⊢ [−Z^γ] ([−X^α] V ⟨−X⟩) ⟨id⟩  ⟶  [−X^α] ([−Z^γ] V ⟨id⟩) ⟨−X⟩    (Sink, γ ≠ α)
    Δ ⊢ [−Z^γ] ([+W^δ] S ⟨id⟩) ⟨id⟩  ⟶  [+W^δ] ([−Z^γ] S ⟨id⟩) ⟨id⟩    (Swap, γ ≠ δ)
    Δ ⊢ [+X^α] ([+Z^γ] S ⟨id⟩) ⟨+X⟩  ⟶  [+Z^γ] ([+X^α] S ⟨+X⟩) ⟨id⟩    (Push)

    Δ ⊢ E[M]  ⟶  E[M′] ⊣ ξ      if E(Δ) ⊢ M ⟶ M′ ⊣ ξ                  (ξ)
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
* **Cancel-□** is an unseal meeting its seal: both layers go.
  **CancelId** removes a hide directly over a reveal of the same
  variable, both carrying `id`.  Both restore the exterior name map
  exactly, so they need no premise.
* **Sink and Swap** move a HIDE inward: below a seal of another
  variable, or below a reveal of another variable over a sealed value.
  **Push** moves an UNSEAL inward through a reveal of another variable.
  Between them, every `id` layer between an unseal and its seal is
  moved out of the way or cancelled.
* Only hides move inward.  Moving a hide inward is safe for names:
  every context between its old and new position gains names.  A
  reveal moving inward could leave a layer whose type no name denotes;
  that is why the first version needed runtime types
  (`CancelIdSketch.md` §8).

Agda: `_⊢_⟶_∣_` in `Reduction.agda`; `crossΛ` is the hide around a
copy, `_•⟶_` is `•`, and `Alloc` is `ξ` (`new P` allocates an unnamed
variable at the head of the store, and the siblings of the redex
shift).

## 6. Examples

Every run is at the empty context; `⊣` shows an allocation.

**5c** (12 steps; checked as `run-5c` in `Examples.agda`):

    ν X:=Int. ((ΛX. λx:X. B) X)⟨−X → +X⟩ 3
        where B = ν Y:=Bool. ((ΛY. λ_:Int. x) Y)⟨id → id⟩ 0
    → TyBeta    [+X^α] (λx:X. B) ⟨−X → +X⟩ 3                     ⊣ α^X:=Int
    → Wrap      [+X^α] ((λx:X. B) ([−X^α] 3 ⟨−X⟩)) ⟨+X⟩
    → Beta      [+X^α] (ν Y:=Bool. ((ΛY^γ. λ_:Int. C) Y)⟨id → id⟩ 0) ⟨+X⟩
                    where C = [−Y^γ] ([−X^α] 3 ⟨−X⟩) ⟨id⟩
    → TyBeta    [+X^α] ([+Y^β] (λ_:Int. C′) ⟨id → id⟩ 0) ⟨+X⟩     ⊣ β^Y:=Bool
                    where C′ = [−Y^β] ([−X^α] 3 ⟨−X⟩) ⟨id⟩
    → Wrap      [+X^α] [+Y^β] ((λ_:Int. C′) ([−Y^β] 0 ⟨id⟩)) ⟨id⟩ ⟨+X⟩
    → Id        [+X^α] [+Y^β] ((λ_:Int. C′) 0) ⟨id⟩ ⟨+X⟩
    → Beta      [+X^α] [+Y^β] [−Y^β] [−X^α] 3 ⟨−X⟩ ⟨id⟩ ⟨id⟩ ⟨+X⟩
    → Sink      [+X^α] [+Y^β] [−X^α] [−Y^β] 3 ⟨id⟩ ⟨−X⟩ ⟨id⟩ ⟨+X⟩
    → Id        [+X^α] [+Y^β] [−X^α] 3 ⟨−X⟩ ⟨id⟩ ⟨+X⟩
    → Push      [+Y^β] ([+X^α] [−X^α] 3 ⟨−X⟩ ⟨+X⟩) ⟨id⟩
    → Cancel-□  [+Y^β] 3 ⟨id⟩
    → Id        3

The hide `[−Y^β]` is Beta's wrapper for the copy of `x` under `ΛY`; it
sinks below the `X` seal and Id removes it.  Typing the state after
Beta: inside `[+X^α] [+Y^β]` both names are bound, and the hide
`[−Y^β]` reads its body's type `X` and its own type `X` as `α`.

**5b**, `K` returning its argument (11 steps, as in νF; checked as
`run-5b`):

    ν X:=Bool. ((ΛX. F) X)⟨(∀Y. id → id) → (−X → +X)⟩ (ΛZ. λz:Z. z) false
        where F = λf:(∀Y. Y → Y). ν Y:=X. (f Y)⟨−Y → +Y⟩
    → TyBeta    [+X^α] F ⟨(∀Y. id → id) → (−X → +X)⟩ G false      ⊣ α^X:=Bool
                    where G = ΛZ. λz:Z. z
    → Wrap      [+X^α] (F ([−X^α] G ⟨∀Y. id → id⟩)) ⟨−X → +X⟩ false
    → Beta      [+X^α] (ν Y:=X. ([−X^α] G ⟨∀Y. id → id⟩ Y)⟨−Y → +Y⟩)
                  ⟨−X → +X⟩ false
    → TyBeta    [+X^α] ([+Y^β] ([−X^α] (λz:Y. z) ⟨id → id⟩) ⟨−Y → +Y⟩)
                  ⟨−X → +X⟩ false                                  ⊣ β^Y:=α
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

The third Wrap's argument `[+X^α] (Y-sealed) ⟨id⟩` is a value (a reveal
over a sealed value), and the hide that Beta puts over it cancels with
it.

**5e** (hand-derived), at `β^Y:=Int, γ^W:=Int, α^X:=β` with `Y:=β`
bound, and `V = [−Y^β] 3 ⟨−Y⟩`:

    [+X^α] [−Y^β] [+W^γ] [+Y^β] [−X^α] V ⟨−X⟩ ⟨id⟩ ⟨id⟩ ⟨id⟩ ⟨+X⟩
    → Swap      [+X^α] [+W^γ] [−Y^β] [+Y^β] [−X^α] V ⟨−X⟩ ⟨id⟩ ⟨id⟩ ⟨id⟩ ⟨+X⟩
    → CancelId  [+X^α] [+W^γ] [−X^α] V ⟨−X⟩ ⟨id⟩ ⟨+X⟩
    → Push      [+W^γ] ([+X^α] [−X^α] V ⟨−X⟩ ⟨+X⟩) ⟨id⟩
    → Cancel-□  [+W^γ] ([−Y^β] 3 ⟨−Y⟩) ⟨id⟩                     : Y

The result is a sealed value: a reveal over a seal.

**5a** (`K`, hand-derived) takes 11 steps: the third Wrap's argument is
a value, Beta discards it, and three Ids finish.  **5d** (hand-derived)
takes 17, as in `SingleEntrySketch.md`.

## 7. Metatheory

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

**Determinism** (on paper).  The left-hand sides are disjoint: Sink
needs a seal under the hide, Swap a reveal of another variable,
CancelId a reveal of the same one; Push needs a reveal under an unseal,
Cancel-□ a seal.  Swap and Push need a SEALED body, so a hide over a
reveal over a functional value stays a value.  TyBeta's fresh variable
is unique up to renaming (in the Agda it is always index 0).

**Color** (on paper).  Sink, Swap and Push commute entries for
different variables, so a moved body's name map is unchanged; CancelId
and Cancel-□ restore the exterior map exactly.  Beta's hide under `Λ`
keeps the copy's map.

## 8. Against earlier designs

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
