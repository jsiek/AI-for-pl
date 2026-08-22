# GTSFImp Alternative Semantics — Shift-Free Reduction

This document records the design settled in discussion on the PR (2026-08-21/22).
It replaces the earlier candidate menu. The checked `alt.*` core and its
statement-level bookkeeping revisions are recorded below. Notation follows the
live development
([`Types.agda`](../Types.agda), [`Conversion.agda`](../Conversion.agda),
[`CastTerms.agda`](../CastTerms.agda), [`Reduction.agda`](../Reduction.agda)).

## Goal

Remove all shifting of terms during reduction. In the live calculus every
allocation step renames terms:

- `β-inst`, `β-gen`, `β-reveal-∀`, `β-conceal-∀` shift the exposed value
  (`⇑ᵗᵐ V`, an O(|V|) traversal);
- every ξ-frame rule shifts the untouched sibling (`M′ ≡ χ ▷ᵀ M`);
- consistency evidence in frames is transported (`c′ ≡ χ ▷ᶜ c`), and
  `β-inst` shifts its closed evidence (`↑ᶜ (c [ ★ /0 ]ᶜ)`).

All of these exist because the fresh type variable is bound at de Bruijn
index `0` of the ambient context, so `bind` re-indexes everything.
Shifting up by 1 is the special case of inserting a slot at position `0`;
the design generalizes to inserting or removing a slot at an arbitrary
position, and then arranges that the *ambient* context never needs a slot
inserted at all.

## Two classes of type variable

**Store names** `α` live in a global, append-only type store
`Σ : StoreCtx → Set`-style, mapping each name to its representation type.
Allocation (`bind`) extends this store and nothing else. Because the store
is append-only and store names are not de Bruijn indices of terms or
types, allocation re-indexes nothing.

**Scoped variables** `X` are the de Bruijn indices of `Ty Δ` and
`Term Δ`, introduced only by binders: `∀`/`Λ` as before, and now the
reveal/conceal nodes. Scoped variables are term-local; which scoped
variables exist at a subterm is controlled entirely by the binders above
it, never by allocation.

A reveal/conceal node carries an **anchor**: the store name `α` its
scoped variable is connected to. One store name may anchor many
reveal/conceal nodes — `β-reveal-⇒` splits one boundary into two, and
disconnected regions of the same allocation arise when values escape
(see the escape example below). The typing context therefore tracks, for
each in-scope crossing variable, its anchor; the store lookup at the
anchor supplies the representation type that the node's conversion is
checked against.

## Reveal is a binder, conceal is an anti-binder

The term grammar replaces the live same-context conversion forms
`M ↑ c` and `M ↓ c` with anchored crossing forms:

```text
M, N ::= …                        -- all other forms as in CastTerms.agda
       | ƛ A ˙ N                    -- lambda, annotated by its domain
       | M ↑[ X ≔ α ] c           -- reveal: binds slot X, anchored at α
       | M ↓[ X ≔ α ] c           -- conceal: anti-binds slot X, anchored at α
```

The dot in `ƛ A ˙ N` distinguishes the domain annotation from the body;
the annotation is syntax and the `⊢ƛ` rule requires it to be the domain of the
resulting arrow type.

Beside its conversion, a node carries two pieces of data: the **slot
position** `X` — the de Bruijn position being removed from (reveal) or
inserted into (conceal) scope; a genuine binder position, since an
all-identity delimiter conversion does not determine it — and the
**anchor** `α`, the store name the slot is connected to. Store names are
drawn from the append-only store; the typing rule's lookup premise is
their only well-formedness check. In the intrinsic syntax the
constructors cross the context index:

```agda
_↑[_≔_]_ : Term (suc Δ) → (X : TyVar (suc Δ)) → (α : Name)
  → Conv↑ (suc Δ) A (wkᵗ X B) → Term Δ                    -- binder
_↓[_≔_]_ : Term Δ → (X : TyVar (suc Δ)) → (α : Name)
  → Conv↓ (suc Δ) (wkᵗ X A) B → Term (suc Δ)              -- anti-binder
```

with `wkᵗ X = renameᵗ (punchIn X)` the type-level slot insertion;
shift-by-1 is the slot `X = 0`. A reveal *binds* its scoped variable over
its subterm: inside, `X` is in scope; outside, the node's type is `X`-free.
A conceal is the dual hole: its subterm lives *outside* the scope of `X`
even though the node sits inside it. Both interiors are term-closed. Displays
later in this document abbreviate `↑[ X ≔ α ] c` to `↑ c ⟨α⟩` when the slot
is `0` or clear from context.

Typing, with `α ⦂ R ∈ Σ` the anchor's store entry and the context
recording the connection `X ≔ α`:

```agda
⊢conceal : {c : Conv↓ (suc Δ) (wkᵗ X A) B}
  → α ⦂ R ∈ Σ
  → c pivot-strict at X, representations at R
  → ⟨ Δ , Σ , ∅ ⟩ ⊢ M ⦂ A                     -- closed and X-free
    -----------------------------------------------------------
  → ⟨ suc Δ [X ≔ α] , Σ , Γ′ ⟩ ⊢ M ↓[ X ≔ α ] c ⦂ B

⊢reveal : {c : Conv↑ (suc Δ) A (wkᵗ X B)}
  → α ⦂ R ∈ Σ
  → c pivot-strict at X, representations at R
  → ⟨ suc Δ [X ≔ α] , Σ , ∅ ⟩ ⊢ M ⦂ A
    -----------------------------------------------------------
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ↑[ X ≔ α ] c ⦂ B        -- result leaves X's scope
```

Here `Γ` and `Γ′` are arbitrary. The crossing changes the scoped-type context
and classifier but does not transport a surrounding term context into its
interior.

**Pivot strictness.** The conversion under a crossing node mentions at
most one scoped variable — the node's own `X` — at `seal X`/`unseal X`
leaves; every other leaf is an identity. This is what makes the rules
well-formed: it forces the outer endpoint to be an image of `wkᵗ X`, so
the term on the far side can live in the context without `X`. There is
no `Maybe` pivot and no `PivotJoin`: the anchor is node data, so a
conversion whose leaves are all identities (a pure *delimiter*) still
names its variable. This closes, in the syntax itself, the
retype-an-identity-at-any-pivot loophole that the DGG's version-2
imprecision rules had to close externally
([`Rationale.md`](../Rationale.md), "Identity reveals").

## Reachability invariant: crossing interiors are closed

Every reveal or conceal interior reachable from a closed compiled program is
typed in the empty term context. The typing rules above bake this invariant
into all well-typed syntax, rather than asking substitution and preservation
to recover it after the fact.

The reachability argument is an induction on evaluation. In the base case,
compilation emits no crossing nodes. For the step case, reduction mints a
crossing only at an evaluation position; evaluation positions in a closed
program are term-closed because evaluation never descends beneath a term
binder. Ordinary call-by-value substitution deposits only closed values beneath
binders, so it cannot introduce a free term variable into an existing crossing
interior. Finally, reduction never grows the ambient scoped-type context: a
closed source program and every program reachable from it remain `Term 0`.
Runtime packages created by crossings are therefore term-closed. Packages that
escape a local crossing have ambient types in `Ty 0` and are type-closed; their
representation types are type-closed through the global store as well.

**Identities are atomic.** `id↑`/`id↓` are restricted to `Atom` types
(`＇Y`, `‵ι`, `★`), matching the consistency layer's `id : Atom A → …`.
Conversions are then structural down to atoms. The generators
`〖_,_↑_〗`/`makeConceal` already conform — they recurse through `⇒`/`∀`
unconditionally and emit identities only at atomic leaves. Consequences:

- a delimiter at `A ⇒ B` is necessarily `id↓ A ↦↑ id↑ B`, which the
  existing `β-reveal-⇒` splits at application — no new commuting rules
  for composite delimiters;
- "mentions the pivot" is a plain syntactic property of the leaf set;
- inversion never faces an identity of arbitrary shape.

## Delimiters persist; `id-reveal` drops at base types only

The live rules `id-reveal`/`id-conceal` discard identity wrappers
unconditionally. In this design an identity-conversion reveal anchored
at `α` is the closing delimiter of its region, and the drop rule is
restricted to base atoms, where the canonical inhabitants are constants
and a constant inhabits every context:

```agda
id-reveal : ($ κ) ↑ id↑ (‵ ι) ⟨α⟩ —→ $ κ
```

No premise, no strengthening operation. (An earlier draft guarded the
drop with a "pivot does not occur in the value" strengthening premise
at every atom; that makes value-hood at `★` undecidable by pattern —
a delimited `★`-value would be a value or a redex depending on a
term-level occurrence check — and the drop rule would overlap with the
projection-merge rule below. Base-only drop keeps `Value`, progress,
and determinism syntax-directed.)

At `★` and at foreign variables `＇Y` a delimiter is always a value;
delimiter spines on `★`-values are consumed by elimination, never by
garbage collection. An `id`-conceal never drops at any type — its
subterm lives in the smaller context — and is consumed only by
`conceal-reveal` cancellation at its matching reveal. When a projection
meets a `★`-delimiter, it commutes into the region to meet the tag:

```agda
(V ↑ id↑ ★ ⟨α⟩) ⟨ ？ H ⟩ —→ (V ⟨ ？ H ⟩′) ↑ id↑ … ⟨α⟩
```

with tag comparison by **anchor equality**: two regions anchored at the
same `α` may have different scoped names for the same allocation, and
the tag/untag rules compare anchors, not scoped indices. This is the
same-anchor *merge* — the one genuinely new rule family.

## Reduction never shifts

The reduction judgment becomes

```text
Σ ∣ M —→ Σ′ ∣ M′        M, M′ : Term Δ,  Σ′ = Σ or Σ, α ⦂ R
```

with the ambient `Δ` fixed across every step. What dissolves from
[`Reduction.agda`](../Reduction.agda): `StoreChange`'s action on terms
and evidence (`applyTerm`/`▷ᵀ`, `applyConsistency`/`▷ᶜ`,
`applyBody`/`▷ᵇ`, and their `▶` iterations), all ξ-frame shift premises,
every `⇑ᵗᵐ`, and the `↑ᶜ` on `β-inst`'s closed evidence — its endpoints
are `X`-free, so it sits outside the reveal at ambient `Δ` unchanged.

Sketch of `β-inst` (slot at `0`, anchors written `⟨α⟩`):

```text
Σ ∣ V ⟨ (inst c) B≢★ ⟩ —→ Σ, α ⦂ ★ ∣
  ((V ↓ δ∀ ⟨α⟩) ⦂∀ … [ ＇ 0 ]) ↑ 〖 0 , ★ ↑ A 〗⟨α⟩ ⟨ c [ ★ /0 ]ᶜ ⟩
```

`V` enters the region through an anti-binder delimiter `δ∀` (structural,
all-atomic-identity, anchored at `α`), is type-applied at the scoped
variable, revealed through the generated conversion (binder, closing the
region), and cast by the *unshifted* closed evidence. The composition
properties hold on the existing rules: `β-reveal-⇒` sends
`(V ↑ (c ↦↑ d)⟨α⟩) · W` to `(V · (W ↓ c ⟨α⟩)) ↑ d ⟨α⟩`, which pairs the
binder with a fresh anti-binder so all context indices line up, and
`conceal-reveal` cancellation `(V ↓ seal ⟨α⟩) ↑ unseal ⟨α⟩ —→ V` has both
sides at ambient `Δ`.

## Why escapees must stay live: the re-entry example

Sealed-and-tagged values escape their region through positive-`★`
channels: with `B = ＇X ⇒ ★`, applying the generalized dynamic identity
yields the free-floating package `(7 ↓ seal ⟨α⟩) ⟨ tag ⟨α⟩ ⟩ ⦂ ★` after
the region's delimiter would (in the live calculus) be erased by
`id-reveal` — the delimiter restriction exists precisely to keep the
package closed.

Such packages are not dead. With

```text
B = ＇X ⇒ ((★ ⇒ ★) ⇒ ＇X)          W = ƛx. ƛj. j · x

(ƛh. h · 9 · (ƛu. (ƛw. u) · (h · 5 · (ƛv. u)))) · ((W ⟨ gen c ⟩) ⦂∀ B [ ℕ ])
```

the instantiation fires `β-gen` once (CBV argument), so both uses of `h`
share one allocation. The outer call leaks its tagged argument `t₉` to
user code through the identity-conversion `(★ ⇒ ★)` channel; the inner
sibling call `h · 5 · (ƛv. u)` routes the captured `t₉` to its own
positive-`＇X` exit, where the projection meets the tag — same
allocation, tags match, unseal returns `9`. The whole program reduces to
`$ 9` with no blame: an escaped package was consumed by a *different*
region of the same allocation. Hence: escapees keep their anchors, the
merge rule is by anchor equality, and no design may neuter or eagerly
blame an escaped package. (When the generalized type has no positive
occurrence of the bound variable, no projection site exists and packages
are inert forever — ordinary uninspected `★` values.)

A mechanized `—↠` derivation of this program in the *live* calculus is
queued as a baseline probe; if the trace does not hold as claimed, the
design motivation needs revisiting before the new calculus is built.

## Open bookkeeping (expected mechanization friction)

- **`β-inst` binder/slot exchange.** Reusing the `inst` body `A`
  verbatim inside the region relies on the pun between the consistency
  binder and the slot position; the exact de Bruijn exchange between the
  `∀`-binder and the inserted slot inside `δ∀` needs to be worked out in
  Agda, and slot positions other than `0` appear as soon as regions
  nest.
- **Conceal orientation cases.** The anti-binder form covers values
  entering a region; whether any rule still needs a same-context conceal
  (or reveal) is to be discovered by the mechanization, not assumed.
- **Store monotonicity.** The one new lemma obligation: typing is
  preserved under store extension (`Σ ⊆ Σ′`) — a lookup lemma, not a
  term traversal.
- **`GenSafe` and value forms.** `RevealValue`/`ConcealValue` gain the
  atomic-delimiter cases (`★` and `＇Y` delimiters are always values;
  base delimiters never are); `GenSafe`'s interaction with anchored
  suspended casts needs restating.
- **Delimiters at foreign variables.** A reveal delimiter at `＇Y` is
  eliminated by commuting past `Y`'s consuming unseal — a node-local
  reveal-past-reveal swap that renumbers the two slot positions; the
  exact rule shape is to be settled in Agda.
- **Blame.** `tag-untag-bad` compares anchors; blame across regions of
  distinct allocations must still be derivable through the merge rule.

## Mechanization notes

The following are the statement-level resolutions and deviations in the first
`alt.*` core.  They are recorded here as revised statements so later work does
not accidentally rely on the prose sketch where the checked Agda interface is
different.

### The store length is explicit in typing contexts

The checked context record is

```agda
⟨ Δ , n , κ , Σ , Γ ⟩
```

where `Σ : Store n` and `κ : TyVar Δ → Binding n`.  The extra displayed `n`
is the index needed by Agda to make the existential store length available to
the dependent projections `κᵉ` and `Σᵉ`; it adds no semantic component.

`Binding n` contains either `∀-bound` or `anchored α` with `α : Fin n`.
The raw stable name carried by terms is a natural number.  A premise
`α ⦂ R ∈ Σ` resolves that raw name to the corresponding `Fin n` used in the
classifier.

### Reduction carries the scoped-variable classifier

The checked one-step judgment is

```agda
Σ ∣ κ ⊢ M —→[ χ ] M′
```

with `M M′ : Term Δ`, `Σ : Store n`,
`κ : TyVar Δ → Binding n`, and `χ : StoreΔ n n′`.  This refines the sketched
`Σ ∣ M —→ Σ′ ∣ M′`: reduction needs `κ` both to translate an allocating type
argument to a name-scoped store representation and to compare variable tags by
anchor.  If `χ = bind R`, the next multi-step premise uses the pointwise
weakening of `κ` from `Fin n` to `Fin (suc n)`; terms are unchanged.

### Representation transport is relational

The checked crossing premises are, for the lookup `p : α ⦂ R ∈ Σ`,

```agda
Reps↑ (BindingRel (κᵉ (cross-ctx Γ X p))) R c
Reps↓ (BindingRel (κᵉ (cross-ctx Γ X p))) R c
```

respectively.  `Transport` is structural on types.  An anchored scoped
variable transports to its anchor name, a type-local `∀` variable transports
to the corresponding type-local variable, and a `∀-bound` entry in `κ` has no
transport constructor.  Under a conversion `∀`, both the variable relation
and `R` are weakened once.  Thus every `seal` or `unseal` representation is
checked against the current weakened store entry without defining a partial
transport function.

### Ordinary lambda beta uses substitution that stops at crossings

Lambdas carry their domain type, and the checked single substitution is

```agda
_[_] : Term Δ → Term Δ → Term Δ
β : Value V → Σ ∣ κ ⊢ (ƛ A ˙ N) · V —→[ keep ] N [ V ]
```

The implementation generalizes internally to substitution at an arbitrary
term index.  Under `ƛ`, that index is incremented and `V` is weakened only by
the term-variable renaming `rename suc`.  Under `Λ`, the replacement is
weakened across that existing lexical type binder; this is unrelated to store
allocation, and no allocation or evaluation-frame rule traverses a term.

Substitution stops at both crossing nodes:

```agda
(M ↑[ X ≔ α ] c) [ V ] = M ↑[ X ≔ α ] c
(M ↓[ X ≔ α ] c) [ V ] = M ↓[ X ≔ α ] c
```

This is sound directly from the closed-interior premises of `⊢reveal` and
`⊢conceal`: a variable supplied by an enclosing lambda cannot occur free below
either node. Constants and `blame` are unchanged, and every other constructor
is traversed structurally. The lambda domain annotation is retained by design
because it remains useful for typing inversion, not because substitution needs
to track the type.

### `β-Λ` and `β-gen` take an endpoint-correct exit conversion

The checked allocation rules are

```agda
β-Λ :
  Value V → Transport (BindingRel κ) A R →
  Σ ∣ κ ⊢ (Λ V) ⦂∀ B [ A ] —→[ bind R ]
    V ↑[ 0 ≔ n ] d
```

where `d : Conv↑ (suc Δ) B (wkᵗ 0 (B [ A ]ᵗ))`, and

```agda
β-gen :
  Value V → (A ≢ ★) → GenSafe c →
  Transport (BindingRel κ) C R →
  Σ ∣ κ ⊢ (V ⟨ gen c ⟩) ⦂∀ B [ C ] —→[ bind R ]
    (((V ↓[ 0 ≔ n ] δ↓ (⇑ᵗ A)) ⟨ c ⟩)
      ↑[ 0 ≔ n ] d)
```

where `d : Conv↑ (suc Δ) B (wkᵗ 0 (B [ C ]ᵗ))`.  This makes the entry
anti-binder and exit reveal explicit and performs no term renaming.  The
literal generator `〖 0 , ⇑ᵗ C ↑ B 〗` computes the extensionally equal target
`replaceTy 0 (⇑ᵗ C) B`; that target is not definitionally equal to
`wkᵗ 0 (B [ C ]ᵗ)`, especially under nested `∀`.  A future endpoint theorem
can replace the supplied `d` by the literal generator without changing the
term or store behavior.

### Three allocation rules remain omitted

There are currently no `β-inst`, `β-reveal-∀`, or `β-conceal-∀`
constructors.  In `β-inst`, the body of the source `∀` uses slot `0` for its
type binder, while the freshly entered region also uses crossing slot `0`.
After the entry anti-binder, these are two distinct slots and the body must be
transported across their exchange before it can be type-applied at the region
variable.  The same exchange appears when type application crosses a
structural `∀` reveal or conceal.  Neither `Types` nor the settled term syntax
provides this typed exchange, and choosing an order silently changes the
displayed rule.  The three rules are therefore omitted pending an explicit
exchange statement.

### Tag cancellation uses an explicit anchor relation

The checked tag rules replace syntactic ground equality and inequality by

```agda
TagMatch κ G H
TagMismatch κ G H
```

For variable grounds, `TagMatch` requires both classifier entries to be
`anchored α` for the same `α`; `TagMismatch` requires distinct anchors.  Base,
function, and universal ground tags retain their structural comparison.  This
is the statement needed for two distinct scoped names anchored at one
allocation to cancel.

The projection-into-`★`-delimiter merge rule remains deferred exactly as
allowed in the task; its intended location is marked in `alt.Reduction`.
