# GTSFImp Alternative Semantics — Shift-Free Reduction

This document records the checked alternative core settled in discussion on
the PR (2026-08-21/22). Notation follows the live development where the
alternative does not deliberately differ.

## Goal

Remove all shifting of terms during reduction. In the live calculus every
allocation step renames terms, every allocating ξ-frame shifts its untouched
sibling, and consistency and conversion evidence must move with the term.
Those traversals exist because allocation adds a de Bruijn type slot to the
ambient context.

The alternative separates runtime store names from lexically scoped type
variables. Allocation extends only an append-only store, while reveal and
conceal nodes manage scoped slots locally. The ambient type context of a
reduction step therefore stays fixed.

## Two classes of type variable

**Store names** `α` live in a global append-only `Store n`. A store entry is a
representation type scoped by earlier store names. Allocation extends this
store and nothing else, so it reindexes no term or scoped type.

**Scoped variables** `X` are the de Bruijn indices of `Ty Δ` and `Term Δ`.
They are introduced by `∀`/`Λ` and by reveal/conceal crossings. A crossing
carries an anchor `α`, connecting its scoped pivot to a store entry. Several
crossings may use one anchor.

The checked typing context is

```agda
⟨ Δ , n , κ , Σ , Γ ⟩
```

where `Σ : Store n` and `κ : TyVar Δ → Binding n`. A binding is either
`∀-bound` or `anchored α`. The explicit `n` lets Agda expose the indices of
`κ` and `Σ`; it adds no semantic component.

## Raw conversion shapes

Conversions carry only their structural direction. They contain no type
context, endpoint, pivot, representation, store name, or leaf data.

```agda
mutual
  data Reveal : Set where
    unseal : Reveal
    _↦↑_   : Conceal → Reveal → Reveal
    `∀↑_   : Reveal → Reveal
    id↑    : Reveal

  data Conceal : Set where
    seal  : Conceal
    _↦↓_  : Reveal → Conceal → Conceal
    `∀↓_  : Conceal → Conceal
    id↓   : Conceal
```

Endpoints and the old `PivotStrict` and `Reps` obligations are subsumed by
one self-contained typing judgment per direction:

```agda
⊢↑[ X ⦂ R′ ] c ⦂ A ↝ B
⊢↓[ X ⦂ R′ ] c ⦂ A ↝ B
```

Here `X : TyVar Δ` and `R′ A B : Ty Δ`. The representation `R′` is scoped in
the same context as the conversion endpoints. These judgments mention no
store, anchor, classifier, or transport relation.

Their rules are:

```agda
⊢unseal : ⊢↑[ X ⦂ R′ ] unseal ⦂ ＇ X ↝ R′
⊢seal   : ⊢↓[ X ⦂ R′ ] seal ⦂ R′ ↝ ＇ X

⊢↑-⇒ : ⊢↓[ X ⦂ R′ ] c ⦂ A′ ↝ A
      → ⊢↑[ X ⦂ R′ ] d ⦂ B ↝ B′
      → ⊢↑[ X ⦂ R′ ] c ↦↑ d ⦂ A ⇒ B ↝ A′ ⇒ B′

⊢↓-⇒ : ⊢↑[ X ⦂ R′ ] c ⦂ A′ ↝ A
      → ⊢↓[ X ⦂ R′ ] d ⦂ B ↝ B′
      → ⊢↓[ X ⦂ R′ ] c ↦↓ d ⦂ A ⇒ B ↝ A′ ⇒ B′

⊢↑-∀ : ⊢↑[ suc X ⦂ ⇑ᵗ R′ ] c ⦂ A ↝ B
      → ⊢↑[ X ⦂ R′ ] `∀↑ c ⦂ `∀ A ↝ `∀ B

⊢↓-∀ : ⊢↓[ suc X ⦂ ⇑ᵗ R′ ] c ⦂ A ↝ B
      → ⊢↓[ X ⦂ R′ ] `∀↓ c ⦂ `∀ A ↝ `∀ B

⊢id↑ : Atom A → ⊢↑[ X ⦂ R′ ] id↑ ⦂ A ↝ A
⊢id↓ : Atom A → ⊢↓[ X ⦂ R′ ] id↓ ⦂ A ↝ A
```

Thus `seal` and `unseal` are the only rules that can touch a variable, and
they can touch only the supplied pivot. Pivot strictness and representation
agreement are structural consequences of a conversion-typing derivation,
not separate predicates. Identities are restricted to atoms by their typing
rules rather than by syntax.

One passed-down `R′` also means that every `seal` or `unseal` leaf in one
conversion uses the same scoped representation, modulo weakening beneath
`∀`. A mixed-alias conversion, whose leaves use different scoped aliases of
one allocation, is deliberately untypeable. No reduction rule mints such a
shape. If the deferred merge rule eventually needs mixed aliases, that is the
point at which to revisit the restriction.

The generators are ordinary shape functions. For example,
`〖 X , R′ ↑ B 〗 : Reveal` recursively emits `unseal` exactly at `＇ X`, and
`makeConceal X R′ B : Conceal` is dual. Their endpoint facts are proofs:

```agda
generator-typed↑ :
  ⊢↑[ X ⦂ R′ ] 〖 X , R′ ↑ B 〗 ⦂ B ↝ replaceTy X R′ B

generator-typed↓ :
  ⊢↓[ X ⦂ R′ ] makeConceal X R′ B
    ⦂ replaceTy X R′ B ↝ B
```

The delimiters `δ↑ A` and `δ↓ A` likewise return shapes, with separate
`delimiter-typed↑` and `delimiter-typed↓` proofs.

## Reveal is a binder, conceal is an anti-binder

The term grammar contains anchored crossings with raw conversions:

```agda
_↑[_≔_]_ : Term (suc Δ) → TyVar (suc Δ) → Name → Reveal → Term Δ
_↓[_≔_]_ : Term Δ → TyVar (suc Δ) → Name → Conceal → Term (suc Δ)
```

A reveal binds slot `X` over its interior and removes that slot outside. A
conceal is the dual hole: its interior is outside the scope of `X`, while the
whole node is inside. Both interiors are closed in the term-variable context.
The explicit slot remains necessary because an all-identity delimiter does
not determine a pivot.

Let `p : α ⦂ R ∈ Σ` be the anchor lookup. The checked rules have exactly one
node-level transport premise and one conversion-typing premise:

```agda
⊢reveal :
  (p : α ⦂ R ∈ Σ)
  → Transport (BindingRel (κ (cross-ctx Γ X p))) R′ R
  → ⊢↑[ X ⦂ R′ ] c ⦂ A ↝ wkᵗ X B
  → cross-ctx Γ X p ⊢ M ⦂ A
  → Γ ⊢ M ↑[ X ≔ α ] c ⦂ B

⊢conceal :
  (p : α ⦂ R ∈ Σ)
  → Transport (BindingRel (κ (cross-ctx Γ X p))) R′ R
  → ⊢↓[ X ⦂ R′ ] c ⦂ wkᵗ X A ↝ B
  → ⟨ Δ , n , κ , Σ , [] ⟩ ⊢ M ⦂ A
  → ⟨ suc Δ , n , κ (cross-ctx Γ X p) , Σ , Γ′ ⟩
      ⊢ M ↓[ X ≔ α ] c ⦂ B
```

The displays abbreviate the record projections used in Agda. `κ` occurs only
in the node-level `BindingRel` transport (and in allocation-rule transport),
never in conversion typing.

`Transport` is relational and structural on types. An anchored scoped
variable maps to its anchor name, a type-local `∀` variable maps to the
corresponding store-local variable through `LiftRel`, and a `∀-bound` entry in
`κ` has no `BindingRel` constructor.

## Reachability invariant: crossing interiors are closed

Every reveal or conceal interior reachable from a closed compiled program is
typed in the empty term context. The typing rules above bake this invariant
into all well-typed syntax, rather than asking substitution and preservation
to recover it after the fact.

The reachability argument is an induction on evaluation. In the base case,
compilation emits no crossing nodes. For the step case, reduction mints a
crossing only at an evaluation position; evaluation positions in a closed
program are term-closed because evaluation never descends beneath a term
binder. Ordinary call-by-value substitution deposits only closed values
beneath binders, so it cannot introduce a free term variable into an existing
crossing interior. Finally, reduction never grows the ambient scoped-type
context: a closed source program and every program reachable from it remain
`Term 0`. Runtime packages created by crossings are therefore term-closed.
Packages that escape a local crossing have ambient types in `Ty 0` and are
type-closed; their representation types are type-closed through the global
store as well.

Term substitution consequently stops at both crossing nodes. Type-context
weakening still renumbers the explicit crossing slots, but leaves each raw
conversion shape unchanged.

## Canonical interiors and delimiter values

Raw identity shapes do not record the atom at which they are used. Valuehood
therefore follows the interior's positive syntax rather than a negative type
or occurrence test.

`CanonicalInterior V` has three shapes:

- a tagged value `W ⟨ (idᵍ G) ! ⟩`;
- a sealed value `W ↓[ X ≔ α ] seal`;
- an identity reveal delimiter `W ↑[ X ≔ α ] id↑` whose own interior is
  canonical.

Each base case carries the needed `Value W` evidence. Consequently it also
entails `Value V`. On well-typed terms, these are exactly the canonical
interiors at `★` and at scoped variables; constants at base types are absent.

The mutually defined `RevealValue` and `ConcealValue` gates are:

- arrow and `∀` reveal/conceal shapes preserve an interior value;
- `seal` concealments preserve an interior value;
- an `id↓` concealment is a value only around a `CanonicalInterior`;
- an `id↑` reveal is a value only around a `CanonicalInterior`;
- `unseal` reveals are never values.

Typing turns the positive syntax check into the intended atom distinction. An
identity concealment at `★` or a foreign variable is a value whenever its
interior is a value; an identity concealment around a base constant is not.
An identity reveal delimiter is a value exactly around a tag, a seal, or a
further valid delimiter, and never around a base constant or an identity
concealment. Hence none of the following redexes is also a value.

## Delimiter and cancellation rules

The base drops are symmetric and raw:

```agda
id-reveal  : ($ κ₀) ↑[ X ≔ α ] id↑ —→[ keep ] $ κ₀
id-conceal : ($ κ₀) ↓[ X ≔ α ] id↓ —→[ keep ] $ κ₀
```

Non-base identity cancellation is deliberately loose in node data:

```agda
id-cancel :
  CanonicalInterior V
  → (V ↓[ X ≔ α ] id↓) ↑[ Y ≔ β ] id↑ —→[ keep ] V
```

Using the positive `CanonicalInterior` refinement of `Value V` makes
`id-cancel` disjoint from both constant drop rules without putting types back
into raw syntax. Typed instances are precisely the non-base atomic cases.

Seal/unseal cancellation is also loose:

```agda
conceal-reveal :
  Value V
  → (V ↓[ X ≔ α ] seal) ↑[ Y ≔ β ] unseal —→[ keep ] V
```

Typing inversion forces `X = Y` and `α = β`: the conceal produces `＇ X`,
the reveal consumes `＇ Y` in the same scoped context, and classifier
agreement at that slot identifies the anchors. Preservation may extract those
equalities; reduction does not carry them.

The loose `id-cancel` formulation is intentionally open for review if
`Bindings` becomes a first-order `Vec`. In that representation,
mismatched-insertion classifier coincidences may make loose mismatched nodes
typeable at `★` or foreign atoms. This task does not choose the future rule.

## Syntactic tag comparison

Tag cancellation follows the live calculus and compares ground types
syntactically. There are no `TagMatch` or `TagMismatch` relations and the
classifier does not appear in either rule:

```agda
tag-untag :
  Value V
  → V ⟨ (idᵍ G) ! ⟩ ⟨ ？ (idᵍ G) ⟩ —→[ keep ] V

tag-untag-bad :
  Value V
  → G ≢ H
  → V ⟨ (idᵍ G) ! ⟩ ⟨ ？ (idᵍ H) ⟩ —→[ keep ] blame
```

Cross-region behavior that cannot be expressed by syntactic tag equality
belongs to the still-deferred merge rule, not to tag comparison.

## Reduction never shifts

The checked one-step judgment is

```agda
Σ ∣ κ ⊢ M —→[ χ ] M′
```

where `χ` is `keep` or `bind R`. If a step allocates, the next multi-step
premise weakens only `κ` and the store; `M` and `M′` remain in the same scoped
type context. Evaluation frames never traverse an untouched sibling.

Allocation rules now carry literal raw generator shapes. In particular,

```agda
β-Λ :
  Value V
  → Transport (BindingRel κ) A R
  → (Λ V) ⦂∀ B [ A ] —→[ bind R ]
      V ↑[ 0 ≔ n ] 〖 0 , ⇑ᵗ A ↑ B 〗

β-gen :
  Value V
  → A ≢ ★
  → GenSafe c
  → Transport (BindingRel κ) C R
  → (V ⟨ gen c ⟩) ⦂∀ B [ C ] —→[ bind R ]
      ((V ↓[ 0 ≔ n ] δ↓ (⇑ᵗ A)) ⟨ c ⟩)
        ↑[ 0 ≔ n ] 〖 0 , ⇑ᵗ C ↑ B 〗
```

There is no endpoint-correct conversion parameter to choose, so the earlier
nondeterministic deviation has dissolved. `alt.GeneratorEndpoint` retains the
pure type theorem

```agda
replaceTy 0 (⇑ᵗ C) B ≡ ⇑ᵗ (B [ C ]ᵗ)
```

and uses it to transport `generator-typed↑` to the endpoint required by
preservation. This evidence is proof infrastructure, not rule data.

## Deferred forall allocation rules and exchange

`β-inst`, `β-reveal-∀`, and `β-conceal-∀` are still absent from
`_—→[_]_`. Their proposed raw redexes and contracta, plus typing validations,
live in `alt.Exchange` pending user sign-off.

The two newest scoped slots are exchanged only in types and classifiers. Raw
conversion shapes mention no variables, so conversion-level `swap↑`/`swap↓`
functions have vanished. Opening a structural `∀` transports only the
conversion-typing endpoint proof; the shape is unchanged. All three proposed
contracta use literal generator shapes.

The two nested-crossing validations still take `BindingsExtensionality`
explicitly. Inserting the fresh crossing before the old crossing and inserting
the old crossing after the fresh one are pointwise equal functions, but Agda
needs this restricted extensionality principle to turn that fact into context
equality. No postulate is introduced.

The validations also expose the node-level `Transport` evidence needed after
store weakening and crossing exchange. General transport-weakening lemmas are
not yet part of the alt core; preservation may later derive these premises
from the allocating rule's original transport proof.

## Mechanization notes

- `Binding`, `Bindings`, `BindingRel`, `LiftRel`, and `Transport` remain in
  `alt.Terms`. `alt.Conversion` imports only `Types`.
- Conversion renaming, endpoint indices, `PivotStrict↑/↓`, and `Reps↑/↓` have
  been deleted. Type-context weakening changes crossing slots but reuses the
  raw shape verbatim.
- Ordinary lambda beta uses structural single substitution. Substitution
  stops at crossings because their interiors are typed in the empty term
  context.
- `RevealValue`, `ConcealValue`, `Value`, and `CanonicalInterior` are mutually
  defined so the progress gates are positive and syntax-directed.
- Reduction still carries `κ` to step under anchored crossings and to state
  allocation `Transport` premises. Tag rules do not inspect it.
- The projection-into-`★`-delimiter merge rule remains deferred. Its intended
  location is marked in `alt.Reduction`.
- Refactoring `Bindings` to `Vec` remains a separate pending decision.
- No `β-inst`, `β-reveal-∀`, or `β-conceal-∀` constructor has been added to
  reduction; only their checked statements remain in `alt.Exchange`.
