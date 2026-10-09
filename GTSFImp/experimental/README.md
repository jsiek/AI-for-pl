# Leaf-local contextual coercion experiment

This experiment tests the context-switching presentation of `β-inst` without
changing the live GTSFImp development.

## Raw coercions and leaf-local typing

[`ContextualCoercion.agda`](ContextualCoercion.agda) separates raw `Coercion`
syntax from its typing judgment. The raw constructors cover the live
consistency constructors and add two specialized leaves:

- `inst-out X` represents the instantiation-bound cast from `X` to `★`;
- `inst-in X` represents the instantiation-bound cast from `★` to `X`.

The raw `id`, `inst c`, and `gen c` constructors carry no endpoint types.
Their endpoint types occur in the typing derivation, not in the raw syntax.

A `CastCtx` entry records the live consistency mode and, for an
instantiation-bound variable, whether allocation is `pending` or `active`.
The phase affects only the two specialized typing rules:

```agda
⊢inst-out-pending : κ X ≡ inst-out-bound pending
  → κ ⊢ inst-out X ∶ ＇ X ⇒ ★

⊢inst-out-active : κ X ≡ inst-out-bound active
  → κ ⊢ inst-out X ∶ ★ ⇒ ★

⊢inst-in-pending : κ X ≡ inst-in-bound pending
  → κ ⊢ inst-in X ∶ ★ ⇒ ＇ X

⊢inst-in-active : κ X ≡ inst-in-bound active
  → κ ⊢ inst-in X ∶ ★ ⇒ ★
```

The rules for identity, arrows, universals, injection, projection,
instantiation, generalization, and the two bottom cases use their ordinary
endpoint indices; there is no recursive `interpret` operation in the typing
relation.

The generic injection and projection rules require `GenericGround κ G`.
For a variable ground `＇ X`, that evidence can be constructed only when
`κ X` is `ordinary`. Consequently, when `X` is instantiation-bound, the raw
generic identity injection and projection at `X` are not typable: the boundary
must be represented by `inst-out X` or `inst-in X`.

## Correspondence with consistency

The phase-forgetting map is

```agda
toEnv∼ : CastCtx Δ → Env∼ Δ
```

and it commutes with `flipᵐ`, `extᵐ`, `instᵐ`, and `genᵐ`. Every
contextual coercion typing derivation erases to live consistency at its
actual endpoints:

```agda
coercion→consistency :
  κ ⊢ c ∶ A ⇒ B
  → toEnv∼ κ ⊢ A ∼ B
```

The reverse theorem applies to a `PendingCtx`, whose entries are ordinary or
instantiation-bound at the pending phase:

```agda
consistency→coercion :
  PendingCtx κ
  → toEnv∼ κ ⊢ A ∼ B
  → Σ[ c ∈ Coercion Δ ] (κ ⊢ c ∶ A ⇒ B)
```

In the variable-ground injection and projection cases, the proof inspects the
corresponding `CastCtx` entry. An ordinary entry produces generic `_!` or `？_`
syntax; an instantiation-bound entry produces `inst-out` or `inst-in`.
`consistency→fromEnv∼-coercion` and
`fromEnv∼-coercion→consistency` state the resulting equivalence for an
arbitrary live `Env∼` embedded by `fromEnv∼`.

## `β-inst` and phase activation

[`ContextualBetaInst.agda`](ContextualBetaInst.agda) adds experimental term
wrappers and reduction. Cast contexts occur only in `⊢cast`, not in `Term`.
The same raw body coercion is used before and after allocation.

[`ContextualCoercionActivation.agda`](ContextualCoercionActivation.agda)
proves that every well-typed pending instantiation body admits the required
active typing:

```agda
activate-newest-typing :
  pending0 ⊢ c ∶ A ⇒ ⇑ᵗ B
  → active0 ⊢ c ∶ replaceTy zero ★ A ⇒ ⇑ᵗ B
```

The proof is by induction on contextual coercion typing. It reuses the live
occurrence, shifting, and type-replacement lemmas to carry the phase change
through arrows, universals, nested `inst`, and nested `gen`. The raw coercion
is unchanged throughout.

The experimental `β-inst` takes the pending body typing as a premise, derives
the active typing using `activate-newest-typing`, and retains the generated
reveal conversion

```agda
↑ 〖 zero , ★ ↑ A 〗
```

and then applies the actively typed, unchanged raw coercion `c`. The theorem
`β-inst-preservation` proves preservation across the `bind ★` store change.
The identity example checks the characteristic phase change:

```agda
pending0 ⊢ inst-in zero ↦ inst-out zero
  ∶ (X ⇒ X) ⇒ (★ ⇒ ★)

active0 ⊢ inst-in zero ↦ inst-out zero
  ∶ (★ ⇒ ★) ⇒ (★ ⇒ ★)
```

At runtime, either specialized leaf lowers to the unannotated `id`.

## Nested-generalization regression

The [checked regression](ContextualActivationRegression.agda) retains the
former nested-`gen` counterexample. In named-variable notation, its pending
body has the following shape, where `X` is bound by the enclosing `inst` and
`Y` is bound by `gen`:

```agda
gen (inst-in X ↦ ？ id)
```

It is typable from `X ⇒ ★` to `∀ Y. ★ ⇒ Y`. Consequently the outer
`inst` source is non-variable and contains `X`, while its target is non-`★`;
all existing `inst` side conditions hold. The enclosing variable is also
forced through `inst-in`, exactly as intended.

After activation, `body-active` checks that the same raw body is typable from
`★ ⇒ ★` to the same target. This is precisely the case that failed when
raw `gen` stored its source annotation. Removing the endpoint annotations
from both `gen` and `inst` eliminates that obstruction.

The experiment does not replace the live consistency relation, evaluator, or
full type-safety development.
