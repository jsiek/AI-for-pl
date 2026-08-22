# GTSFImp Alternative Semantics — Shift-Free Reduction

This document records the design settled in discussion on the PR (2026-08-21/22).
It replaces the earlier candidate menu. Status: design statements agreed,
mechanization not yet started; expect bookkeeping revisions once Agda pushes
back. Notation follows the live development
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

The crossing constructors change the term's context index:

```agda
_↑_ : Term (suc Δ) → Conv↑ (suc Δ) A B → Term Δ      -- binder
_↓_ : Term Δ → Conv↓ (suc Δ) A B → Term (suc Δ)      -- anti-binder
```

A reveal *binds* its scoped variable over its subterm: inside, `X` is in
scope; outside, the node's type is `X`-free. A conceal is the dual hole:
its subterm lives *outside* the scope of `X` even though the node sits
inside it. (The rules below are written with the slot at position `0`
for readability; the mechanization takes an arbitrary slot position
`X : TyVar (suc Δ)`, with `wkᵗ X = renameᵗ (punchIn X)` the induced
type-level slot insertion, `wkᶜ X` the same on term contexts, and the
node's typing quantifying over the position. Shift-by-1 is `X = 0`.)

Typing, with `α ⦂ R ∈ Σ` the anchor's store entry and the context
recording the connection `X ≔ α`:

```agda
⊢conceal : {c : Conv↓ (suc Δ) (wkᵗ X A) B}
  → α ⦂ R ∈ Σ
  → c pivot-strict at X, representations at R
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A                     -- M unshifted, X-free
    -----------------------------------------------------
  → ⟨ suc Δ [X ≔ α] , Σ , wkᶜ X Γ ⟩ ⊢ M ↓ c ⦂ B

⊢reveal : {c : Conv↑ (suc Δ) A (wkᵗ X B)}
  → α ⦂ R ∈ Σ
  → c pivot-strict at X, representations at R
  → ⟨ suc Δ [X ≔ α] , Σ , wkᶜ X Γ ⟩ ⊢ M ⦂ A
    -----------------------------------------------------
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ↑ c ⦂ B                 -- result leaves X's scope
```

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

## Delimiters persist; `id-reveal` is restricted

The live rules `id-reveal`/`id-conceal` discard identity wrappers
unconditionally. In this design an identity-conversion reveal anchored
at `α` is the closing delimiter of its region and must not be discarded
while `X`-mentioning syntax lives beneath it. The rules become:

```agda
id-reveal : Value V
  → V ≡ insertᵗᵐ X V₀            -- pivot does not occur in the value
    ------------------------------
  → V ↑ id↑ a ⟨α⟩ —→ V₀
```

and dually for `id-conceal`. At base atoms the premise is always
satisfiable (the value inside is a constant), so delimiters never pile
up on first-order data. At `★` the delimiter is a value when the premise
fails; the projection then commutes into the region to meet the tag:

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
  atomic-delimiter cases; `GenSafe`'s interaction with anchored
  suspended casts needs restating.
- **Blame.** `tag-untag-bad` compares anchors; blame across regions of
  distinct allocations must still be derivable through the merge rule.
