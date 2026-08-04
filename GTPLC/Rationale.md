# GTPLC Design Rationale

This document records why GTPLC makes design choices that are not evident
from the definitions alone. Each rationale has a stable explicit anchor so
that the Agda source can link directly to it.

## Contents

- [Keep eager checks outside `gen` and `inst`](#gen-inst-side-conditions)
- [Use canonical association for seal and unseal sequences](#canonical-sequence-association)

<a id="gen-inst-side-conditions"></a>
## Keep eager checks outside `gen` and `inst`

### Decision

The `gen` narrowing rule and the `inst` widening rule require all three of
the following endpoint conditions:

```agda
NonVar A
zero ∈ᵗ A
B ≢ ★
```

For narrowing, the body of `gen` has judgment

```agda
genᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ⦂ ⇑ᵗ B ⊒ A
```

The first two conditions force `A` to be headed by either `_ ⇒ _` or
`` `∀ ``: `NonVar A` rules out a variable, while an occurrence of `zero`
rules out base types and `★`. The last condition makes `⇑ᵗ B` non-dynamic.
Consequently, inversion of the body derivation rules out an eager root
projection (`untag` or `untag-seq`). Its root must instead be a function,
universal, or nested `gen` coercion, each of which takes a value to a value.
This is the type-indexed GTPLC counterpart of GTSF's `GenSafe` grammar.

This restriction does not prohibit projections at arbitrary depth. A
projection may occur inside a function or universal coercion, where the
surrounding structural coercion ensures that it runs at the corresponding
elimination rather than being delayed by `gen` itself.

The widening rule for `inst` is dual. Its body has judgment

```agda
instᵈ μ ∣ suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ ⊢ c ⦂ A ⊑ ⇑ᵗ B
```

Here `NonVar A` and `zero ∈ᵗ A` force the source to be headed by `_ ⇒ _`
or `` `∀ ``, and `B ≢ ★` makes the target non-dynamic. Inversion therefore
rules out an eager root tag (`tag` or `tag-seq`) underneath `inst`. The
remaining roots are function, universal, or nested `inst` coercions. This is
the counterpart of GTSF's `InstSafe` grammar.

### Why the restriction is operationally necessary

`gen c` is inert regardless of the shape of `c`. Therefore
`V ⟨ gen c ⟩` is a value, and `c` is not run until that polymorphic value
is instantiated. If the narrowing rule admitted `B = ★`, it could place an
eager function projection underneath `gen`:

```text
V ⟨ gen ((★⇒★ ？) ︔ c) ⟩
```

For a dynamically tagged non-function `V`, this term is still a value. The
projection that should report blame has been delayed by generalization. That
delay breaks the reduction/imprecision synchronization required by the
dynamic gradual guarantee.

The normalized coercion keeps the projection outside `gen`.

Diagram:

    V ⟨ (★⇒★ ？) ︔ gen c ⟩
    |
    v
    V ⟨ ★⇒★ ？ ⟩ ⟨ gen c ⟩

The projection is now performed immediately and reports blame before the
inert `gen` can delay it. The `B ≢ ★` premise makes this factorization the
only admissible normal form for the dynamic endpoint. Dually, widening from
a polymorphic type to `★` uses

```text
inst c ︔ (★⇒★ !)
```

so that the function tag remains outside `inst` rather than being hidden in
its body.

The corresponding explicit safe grammars are documented in
[`GTSF/NarrowWiden.agda`][gtsf-narrow-widen]. The repaired mismatch example
in [`GenSafeMismatchBlameRegression.agda`][mismatch-regression] checks that
compilation produces the factored coercions and that both sides report blame
for a mismatched dynamic tag.

[gtsf-narrow-widen]: ../GTSF/NarrowWiden.agda
[mismatch-regression]: ../GTSF/proof/Compilation/GenSafeMismatchBlameRegression.agda

<a id="canonical-sequence-association"></a>
## Use canonical association for seal and unseal sequences

### Decision

Seal chains in narrowing associate to the left, while unseal chains in
widening associate to the right. Thus the canonical forms are

```agda
((G ？) ︔ seal X) ︔ seal Y
unseal X ︔ (unseal Y ︔ (G !))
```

and not

```agda
(G ？) ︔ (seal X ︔ seal Y)
(unseal X ︔ unseal Y) ︔ (G !)
```

The merged narrowing and widening judgments enforce this distinction with
endpoint-shape premises. The `untag-seq` constructor requires `NonVar B`, so
it cannot place an untag outside a sequence whose final target is a sealed
type variable. Such a sequence must instead be extended by `seal-seq`.
Dually, `tag-seq` requires `NonVar A`, so it cannot place a tag outside a
sequence whose initial source is an unsealed type variable. Such a sequence
must instead be extended by `unseal-seq`.

### Why the restriction is necessary

For a concrete example, take the context, store, and mode environment

```agda
Δ₂ = suc (suc zero)

Σ₂ =
  (zero , ＇ (suc zero)) ∷
  (suc zero , ‵ `ℕ) ∷ []

μ-seal X = seal-or-id
```

The store is recursively well formed:

```agda
wfΣ₁ = store-bind store-empty wfBase refl
wfΣ₂ = store-bind wfΣ₁ (wfVar z<s) refl
```

Thus `zero` is represented by the older variable `suc zero`, which in turn
is represented by `ℕ`. Before the endpoint-shape premises were added, the
following two narrowing judgments both held:

```agda
μ-seal ∣ Δ₂ ∣ Σ₂
  ⊢ (((‵ `ℕ) ？) ︔ seal (suc zero)) ︔ seal zero
    ⦂ ★ ⊒ ＇ zero

μ-seal ∣ Δ₂ ∣ Σ₂
  ⊢ ((‵ `ℕ) ？) ︔ (seal (suc zero) ︔ seal zero)
    ⦂ ★ ⊒ ＇ zero
```

The first is canonical. It is built by applying `seal-seq` twice. The second
would require `untag-seq` with final target `＇ zero`, but its new premise
would be `NonVar (＇ zero)`, which has no constructor.

The dual ambiguity was

```agda
μ-seal ∣ Δ₂ ∣ Σ₂
  ⊢ unseal zero ︔ (unseal (suc zero) ︔ ((‵ `ℕ) !))
    ⦂ ＇ zero ⊑ ★

μ-seal ∣ Δ₂ ∣ Σ₂
  ⊢ (unseal zero ︔ unseal (suc zero)) ︔ ((‵ `ℕ) !)
    ⦂ ＇ zero ⊑ ★
```

Here the first is canonical and is built by applying `unseal-seq` twice. The
second would require `tag-seq` with initial source `＇ zero`, but its new
premise would be `NonVar (＇ zero)`.

Because `_︔_` is a syntax constructor rather than an associative operation
modulo equality, each noncanonical coercion is propositionally unequal to its
canonical counterpart. Narrowing and widening therefore were not determined
by their endpoints, mode environment, and well-formed store.

The separate GTSF normal-form grammar prevented this overlap with its strict
cross-narrowing and strict cross-widening categories. The endpoint-shape
premises are the corresponding invariant for GTPLC's merged grammar and type
system. They keep every judgment index in constructor form; normalization by
the smart wrappers happens in their proof definitions rather than through a
composition function in a constructor conclusion.
