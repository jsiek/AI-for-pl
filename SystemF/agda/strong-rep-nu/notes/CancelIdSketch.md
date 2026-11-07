# CancelId in place of Cancel — an experiment on νF₁ (2026-11-06)

Status: SKETCH, on paper, not mechanized.  It modifies νF₁
(`notes/SingleEntrySketch.md`, "the sketch" below) and uses its
notation, its type system (§3 there, unchanged) and its lemmas L1–L6.
Call the variant **νF₁ᶜ**.

## 1. The question

The sketch's Cancel walks an unseal down an identity tower `I` to its
seal and rewrites both ends to `id`.  The experiment replaces it with a
local rule that removes a hide directly over a re-reveal of the same
variable:

    Δ ⊢ [−X^α] ([+X^α] V ⟨id⟩) ⟨id⟩  ⟶  V                           (CancelId)

and changes the value grammar so that this left-hand side is not a
value.  Cancel-□ (`[+X^α] ([−X^α] V ⟨−X⟩) ⟨+X⟩ ⟶ V`) stays: it is how
an unseal meets its seal.  The question is whether progress can be
proved.

**Answer: not with CancelId alone, but yes with one more local rule.**
With CancelId and Cancel-□ as the only rules for towers, a closed
program reaches a stuck term (§2).  The repair is a rule, **Sink**, that
moves an identity layer for another variable below a seal (§3).  With
it, a value of variable type is a seal, possibly under one re-reveal of
its own name, and progress holds (§4).  Preservation, color
preservation and determinism also hold (§4).  The price is that Sink
commutes two scope entries, which in de Bruijn form needs a renaming of
the moved body (§6).

## 2. CancelId alone is not enough

The unseal in `[+X^α] V ⟨+X⟩` needs its body `V : α` to be the seal
`[−X^α] W ⟨−X⟩`.  An identity layer for ANOTHER variable can sit
between them, and CancelId cannot remove it, because CancelId removes
only a `[−Z][+Z]` pair for one `Z`.  The sketch's 5c reaches such a
term:

    (ΛX. λx:X. (ΛY. λ_:Int. x) [Bool] 0) [Int] 3                : Int

After seven steps, the same as the sketch's:

    [+X^α] [+Y^β] [−X^α] 3 ⟨−X⟩ ⟨id⟩ ⟨+X⟩

The `[+Y^β]` layer comes from instantiating `ΛY` and carries `id`,
because the body's result type `X` does not mention `Y`.  The term is
well typed, it is not a value (the outer unseal is active), and no rule
applies.  Cancel-□ needs the seal directly under the unseal, and
CancelId needs a `−X` layer over a `+X` layer.  A value grammar cannot
help by itself: excluding `[+Y^β] ([−X^α] 3 ⟨−X⟩) ⟨id⟩` from the values
makes the term stuck one level down instead.

Two more well-typed terms that are stuck under CancelId alone:

* `[+X^α] [+W^γ] [−W^γ] [−X^α] V ⟨−X⟩ ⟨id⟩ ⟨id⟩ ⟨+X⟩` with `W`
  unnamed.  The pair is `+W` over `−W`, the order CancelId does not
  remove.
* The sketch's 5e: `[+X^α] [−Y^β] [+W^γ] [+Y^β] [−X^α] V ⟨−X⟩ ⟨id⟩
  ⟨id⟩ ⟨id⟩ ⟨+X⟩`.  The `−Y … +Y` pair is not adjacent.

## 3. νF₁ᶜ

### Syntax

Types, contexts, scope entries, conversions and terms are the sketch's.
Values are split by what their type can be:

    Values      V,W  ::=  k | F | S
    Functional  F    ::=  λx:A. N | ΛX. V
                       |  [ε] V ⟨c → d⟩ | [ε] V ⟨∀X. c⟩
                       |  [ε] F ⟨id⟩      unless ε = −X^α and F = [+X^α] F′ ⟨id⟩
    Sealed      S    ::=  H[V]

    Seal heads  H    ::=  [−X^α] □ ⟨−X⟩  |  [+X^α] ([−X^α] □ ⟨−X⟩) ⟨id⟩

A seal head `H` belongs to ONE name, `X`.  The second form is a sealed
value under a re-reveal of its own name.  In 5a and 5b below, Wrap
crosses a `[−X^α]` layer with an `id` domain and wraps a `Y`-sealed
argument in `[+X^α] … ⟨id⟩`; Sink then moves that layer onto the `X`
seal inside, building this head.

So an `id` layer is a value only over a functional value, and never as
the outer half of a CancelId pair.  An `id` layer over a constant or
over a sealed value is active.

### Reduction

The sketch's Delta, Beta, Wrap, Wrap-id, TyBeta and Id are unchanged,
and so is Cancel-□.  Cancel is removed.  Two rules are new:

    Δ ⊢ [−X^α] ([+X^α] V ⟨id⟩) ⟨id⟩  ⟶  V                          (CancelId)

    Δ ⊢ [ε] H[V] ⟨id⟩  ⟶  H[[ε] V ⟨id⟩]                             (Sink)
        if ε's name is not H's name

CancelId is the user's rule.  The two layers cancel exactly on the name
map: `V`'s context is `+X(−X(Δ))`, which is `Δ` with `X:=α` moved
(L3).  It fires at every type, with any value `V`.

Sink moves an identity layer for another variable `Z` below `H`.
Entries for different names commute on the name map, and the naming
condition makes their representation variables different too.  So `V`'s
context and the head's coherence are unchanged up to L3.  After the
step, `[ε] V ⟨id⟩` is a value, or the step continues: Id if `V` is a
constant, Sink again if `V` is sealed, CancelId if `V` is an `id` layer
for `Z`'s inverse.

What happens to an `id` layer `[ε] M ⟨id⟩` over a value `M`:

| `M` | `ε` | step |
|---|---|---|
| constant | any | Id |
| functional, not `[+X^α] F′ ⟨id⟩` under `ε = −X^α` | any | none (a value) |
| `[+X^α] F′ ⟨id⟩` | `−X^α` | CancelId |
| `[−X^α] W ⟨−X⟩` | `+X^α` | none (a value: the second seal head) |
| `[−X^α] W ⟨−X⟩` | `−X^α` | impossible (incoherent: `X` is not named inside `−X^α`) |
| `[+X^α] ([−X^α] W ⟨−X⟩) ⟨id⟩` | `−X^α` | CancelId |
| `[+X^α] ([−X^α] W ⟨−X⟩) ⟨id⟩` | `+X^α` | impossible (incoherent: `X` is already named) |
| `H[W]` | names `Z ≠ X` | Sink |

## 4. Proofs, on paper

### Canonical forms (replaces the sketch's L6)

By induction on a value `V` with `Γ ⊢ V : R`:

* a constant has a base type;
* a functional value has an arrow or `∀` type: `[ε] F ⟨id⟩` has `F`'s
  type;
* a sealed value has a variable type: `H[W] : α` when `H` belongs to
  `X` and `α^X` (naming condition).

So `R = ι` gives a constant, `R → S` and `∀X. R` give a functional
value (and the sketch's Wrap, Wrap-id and `•` cover every functional
form), and `R = α` gives a sealed value whose head belongs to `α`'s
recorded name.

### Progress (proved)

**Claim.**  If `Δ ∣ [] ⊢ M : R` with `Δ` well named, then `M` is a
value or `M` steps.

*Proof.*  As in the sketch's O2 except for boundaries.  Take
`[ε] V ⟨c⟩` with `V` a value.

* `c` is `c₁ → c₂`, `∀X. c′` or `−X`: a value (for `−X`, typing forces
  `ε = −X^α`, so it is the first seal head).
* `c = id`: the table in §3.  Every row is a value, a step, or
  impossible by coherence.
* `c = +X`: then `ε = +X^α` and `V : α` at `Γ = ε(Δ)`, where `X:=α`.
  By canonical forms `V = H[W]` with `H` belonging to `X`.  The second
  seal head starts with a `[+X^α]` layer, which is incoherent at `Γ`
  because `X` is named there.  So `H = [−X^α] □ ⟨−X⟩`, and Cancel-□
  fires.  ∎

No walk down a tower is needed: an unseal's body is its seal or the
term steps inside it.

### Preservation (proved for the new rules)

**CancelId.**  The redex `[−X^α] ([+X^α] V ⟨id⟩) ⟨id⟩ : R` at `Δ`, with
`X:=α ∈ Δ`.  Both `id`s have type `R ⇒ R`, so `V : R` at
`+X(−X(Δ))`, which is `Δ` with `X:=α` moved.  By L3, `V : R` at `Δ`.  ∎

**Sink, first head.**  The redex `[ε] ([−X^α] V ⟨−X⟩) ⟨id⟩ : α` at
`Δ`, with `ε` for `Z ≠ X`, `α^X:=P` and `V : P` at `−X(ε(Δ))`.  Then
`X:=α ∈ Δ`, because `−X^α` is coherent at `ε(Δ)` and `ε` does not touch
`X`.  The contractum `[−X^α] ([ε] V ⟨id⟩) ⟨−X⟩`:

* `−X^α` is coherent at `Δ`;
* `ε` is coherent at `−X(Δ)`.  For `+Z^γ`, `Z` and `γ` are unnamed in
  `Δ`, so in `−X(Δ)` too.  For `−Z^γ`, `Z:=γ` is in `Δ`, so in `−X(Δ)`.
* `V : P` at `ε(−X(Δ))`, which is `−X(ε(Δ))` up to L3;
* `id : P ⇒ P` (L5), and the seal `−X : P ⇒ α` reads the store, which
  is unchanged.

So the contractum has type `α`.  ∎

**Sink, second head.**  The redex
`[ε] ([+X^α] ([−X^α] V ⟨−X⟩) ⟨id⟩) ⟨id⟩ : α`.  The two `X` layers
cancel on the name map, so `V` sits at `ε(Δ)` before and after up to
L3.  Coherence of `+X^α` at `Δ` follows from its coherence at `ε(Δ)`.
`γ ≠ α` holds by the naming condition, since `α`'s name is `X` and
`γ`'s is `Z`.  The rest is as for the first head.  ∎

The other rules' cases are the sketch's O4, O5 and the standard cases.
Cancel-□ is the sketch's O3, second part.

### Color preservation (proved, with the sketch's caveat)

* **CancelId.**  `V`'s holes move from `+X(−X(Δ))` to `Δ`: the same
  map.
* **Sink.**  `V`'s holes move from the head's interior over `ε(Δ)` to
  `ε` of the head's interior over `Δ`.  The two scopes touch different
  names, so this is the same map.

The color law in the Agda (`ColorPreservation.agda`) is positional: a
hole's scope map is the LIST `names Δ`, and it must be equal on the
nose, with ρ renaming representation variables only.  Sink allocates
nothing, so ρ is the identity, and the redex's own boundaries are
consumed; the residual positions are the holes inside `V`.  It is
enough that `V`'s name list is the same list before and after.  Entries
are positional (`Boundary.agda`): `bind j α` inserts at position `j`,
`unbind i α` deletes position `i`.  Let `L = names Δ`; `X` and `Z` sit
at different positions throughout.

* **`ε = bind j γ` (a `+Z`), first head `unbind i α`.**  Before, `V`
  is at `delete i (insert j L)`.  The contractum's seal acts first, at
  `Δ`, with index `i′`, and the moved bind second, with index `j′`.  If
  `j < i`: `i′ = i − 1`, `j′ = j`, and `insert j (delete (i−1) L) =
  delete i (insert j L)`.  If `j > i`: `i′ = i`, `j′ = j − 1`, and
  `insert (j−1) (delete i L) = delete i (insert j L)`.
* **`ε = unbind j γ` (a `−Z`), first head.**  Both sides delete the same
  two distinct elements of `L`; each index is read in the list it acts
  on.
* **Second head, `bind k α` then `unbind k α`.**  Before, `V` is at
  `delete k (insert k (ε L)) = ε L`.  After, the head acts at `Δ` with
  `X`'s position `k′` in `L`, and `ε`, with its index unchanged, acts on
  `delete k′ (insert k′ L) = L`: `V` is at `ε L` again.

So `V` moves verbatim and keeps its name list.  This fixes what the
contractum must be: the two entries are RE-INDEXED (`i′`, `j′`, `k′`),
and the seal's conversion `−X`, which cites `X` by its position in the
seal's conversion context (`ε(Δ)` before, `Δ` after), is re-indexed
from `i` to `i′`.  The moved `id` is untyped and cites nothing.

The other rules are as in the sketch's O7, including the Beta-under-`Λ`
caveat.

### Determinism (proved, up to the choice of fresh `α`)

**Values do not step.**  The value grammar has no CancelId or Sink
left-hand side: an `id` layer over a sealed value is a value only in
the second seal head, where the layer's name is the head's own and its
entry is `+X^α`.

**At most one rule at the root.**  CancelId needs `−X^α` over `+X^α`,
and Sink needs a different name.  Id needs a constant directly under
the layer.  `H` is determined by the term: its first form is a layer
carrying `−X`, and its second form is a `+X^α` layer carrying `id` over
that seal.

**Termination of the administrative steps.**  Each Sink lowers one
`id` layer past one seal, and CancelId and Id remove layers.  So these
three rules cannot run forever on their own: count, for each `id`
layer, the seals below it.

## 5. The examples, rerun

Store allocations as in the sketch; hand-derived.

**5a (`K`).**  The third Wrap crosses the `[−X^α]` layer with an `id`
domain.  The argument it builds, `[+X^α] [−Y^β] [−X^α] false ⟨−X⟩
⟨−Y⟩ ⟨id⟩`, is now active: Sink moves the `[+X^α]` layer below `−Y`,
giving `[−Y^β] [+X^α] [−X^α] false ⟨−X⟩ ⟨id⟩ ⟨−Y⟩`, a value.  Beta
then discards it, and three Ids finish.  The run takes 12 steps, against
11 in νF₁ and 9 in νF.

**5b (`K` returning its argument).**  The first seven steps are the
sketch's.  Then:

    → Wrap      [+X^α] [+Y^β] [−X^α] ((λz:Y. z)
                                       ([+X^α] [−Y^β] [−X^α] false ⟨−X⟩ ⟨−Y⟩ ⟨id⟩))
                  ⟨id⟩ ⟨+Y⟩ ⟨+X⟩
    → Sink      [+X^α] [+Y^β] [−X^α] ((λz:Y. z)
                                       ([−Y^β] [+X^α] [−X^α] false ⟨−X⟩ ⟨id⟩ ⟨−Y⟩))
                  ⟨id⟩ ⟨+Y⟩ ⟨+X⟩
    → Beta      [+X^α] [+Y^β] [−X^α] [−Y^β] [+X^α] [−X^α] false ⟨−X⟩ ⟨id⟩ ⟨−Y⟩ ⟨id⟩ ⟨+Y⟩ ⟨+X⟩
    → Sink      [+X^α] [+Y^β] [−Y^β] [−X^α] [+X^α] [−X^α] false ⟨−X⟩ ⟨id⟩ ⟨id⟩ ⟨−Y⟩ ⟨+Y⟩ ⟨+X⟩
    → CancelId  [+X^α] [+Y^β] [−Y^β] [−X^α] false ⟨−X⟩ ⟨−Y⟩ ⟨+Y⟩ ⟨+X⟩
    → Cancel-□  [+X^α] [−X^α] false ⟨−X⟩ ⟨+X⟩
    → Cancel-□  false

The run takes 13 steps, against 16 in νF₁ and 11 in νF.  The second
Sink is the layer that blocked the named-type versions: `[−X^α]` hides
`X` over a `Y`-sealed value.  Here it sinks below the `Y` seal, onto the
`X` re-reveal the first Sink put there, and the pair cancels.  Under the
`Y` seal, the second seal head `[+X^α] [−X^α] false ⟨−X⟩ ⟨id⟩` has type
`α` in a context where `X` is hidden: a type no name denotes, as in the
sketch (§7, point 1).

**5c.**  The stuck term of §2 now steps:

    → Sink      [+X^α] [−X^α] [+Y^β] 3 ⟨id⟩ ⟨−X⟩ ⟨+X⟩
    → Id        [+X^α] [−X^α] 3 ⟨−X⟩ ⟨+X⟩
    → Cancel-□  3

The run takes 10 steps, against 11 in νF₁.

**5d.**  Unchanged from the sketch, 17 steps: its unseal already sits
directly on its seal (Cancel-□), and its other `id` layers are over
constants or functions.

**5e** (at β^Y:=Int, γ^W:=Int, α^X:=β, with name `Y:=β`):

    S₀ = [+X^α] [−Y^β] [+W^γ] [+Y^β] [−X^α] [−Y^β] 3 ⟨−Y⟩ ⟨−X⟩ ⟨id⟩ ⟨id⟩ ⟨id⟩ ⟨+X⟩
    → Sink      [+X^α] [−Y^β] [+W^γ] [−X^α] [+Y^β] [−Y^β] 3 ⟨−Y⟩ ⟨id⟩ ⟨−X⟩ ⟨id⟩ ⟨id⟩ ⟨+X⟩
    → Sink      [+X^α] [−Y^β] [−X^α] [+W^γ] [+Y^β] [−Y^β] 3 ⟨−Y⟩ ⟨id⟩ ⟨id⟩ ⟨−X⟩ ⟨id⟩ ⟨+X⟩
    → Sink      [+X^α] [−Y^β] [−X^α] [+Y^β] [−Y^β] [+W^γ] 3 ⟨id⟩ ⟨−Y⟩ ⟨id⟩ ⟨−X⟩ ⟨id⟩ ⟨+X⟩
    → Id        [+X^α] [−Y^β] [−X^α] [+Y^β] [−Y^β] 3 ⟨−Y⟩ ⟨id⟩ ⟨−X⟩ ⟨id⟩ ⟨+X⟩
    → Sink      [+X^α] [−X^α] [−Y^β] [+Y^β] [−Y^β] 3 ⟨−Y⟩ ⟨id⟩ ⟨id⟩ ⟨−X⟩ ⟨+X⟩
    → CancelId  [+X^α] [−X^α] [−Y^β] 3 ⟨−Y⟩ ⟨−X⟩ ⟨+X⟩
    → Cancel-□  [−Y^β] 3 ⟨−Y⟩

The third Sink uses the second seal head (`[+Y^β] [−Y^β] □ ⟨−Y⟩ ⟨id⟩`).
The term ends as the value `[−Y^β] 3 ⟨−Y⟩ : β`.

## 6. Against earlier designs

* **D02, the per-variable wrappers** (`notes/DesignPoints.md`;
  `notes/old/notes-v1.md`, "Old per-variable design") had `Cancel`
  (`V ↓[X] ↑[X] ⟶ V`, a reveal over its own conceal: Cancel-□), `Drop`
  (remove a reveal over a conceal of another variable, if the variable
  does not occur), and `Commute`.  `Commute` was rejected statically when
  conceal markers were tightened (D04), and it died with D02.  Sink is
  a `Commute` restricted to an `id` layer over a seal head.  D02 failed
  for its truncating conceal and its `TyWrapCncl`, not for these rules
  (sketch §1), and νF₁ᶜ keeps neither.
* **`IdPush`** (D39, ruled 2026-09-05, later retired with `⊕` regrown)
  moved the ACTIVE unseal inward through an `id` layer, swapping the two
  conversions.  Sink moves the `id` layer instead and leaves the unseal
  in place.  `IdPush` needed an owner-lookup premise to spell the
  identity it created at a looked-up type.  Sink creates no conversion;
  the untyped `id` it moves is the one already there.
* **The sketch's PairCancel** removed `[−X^α] [+X^α]` at any
  conversions and needed a types-agree premise (5d).  CancelId is
  PairCancel restricted to two `id`s, where the types agree by
  construction, so it needs no premise.
* **The sketch's Cancel** did Sink's work in one non-local step: it
  rewrote the two ends and left the tower `I` in place.  νF₁ᶜ trades it
  for local steps that remove `I` layer by layer: by Sink and Id when
  the layer reaches a constant, by CancelId when it meets its inverse.

## 7. Open points

1. **Named runtime types do not suffice.**  No νF₁ᶜ rule rewrites a
   type inside a layer that stays, as the sketch's Cancel did.  But the
   second seal head `[+X^α] ([−X^α] W ⟨−X⟩) ⟨id⟩` has type `α` in a
   context where `X`, `α`'s only name, is hidden, so no named type
   describes it.  5a and 5b both build one.  So νF₁ᶜ keeps the sketch's
   representation runtime types, and with them the sketch's §6.8
   abstraction question.
2. **De Bruijn cost of Sink.**  In the sketch, Wrap and Cancel-□ need no
   respelling, because an entry and its inverse cancel at one position.
   Sink swaps entries for two different names.  The moved body `V` does
   NOT need a renaming: with re-indexed entries its name list is the
   same list (§4, color).  The cost is index arithmetic on the two
   entries and on the seal's conversion, of the kind TyWrap's `liftᴮ`
   does.  (An earlier draft of this note said `V` needed a swap
   renaming; that would also have broken the positional color law.)
   The mechanization (`../nu-cancel-id/`) avoids even that: it keeps
   one named flag per cell instead of a list of name positions (the
   naming condition makes the two equivalent), so an entry carries only
   its cell, and Sink re-indexes nothing.
3. **Tower height.**  Sink and CancelId shorten towers that Cancel left
   behind (5b ends at `false` with no Ids), but every hide and re-reveal
   pair now costs a Sink per seal it crosses.
