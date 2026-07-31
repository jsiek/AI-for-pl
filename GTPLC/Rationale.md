# GTPLC Design Rationale

This document records why GTPLC makes design choices that are not evident
from the definitions alone. Each rationale has a stable explicit anchor so
that the Agda source can link directly to it.

## Contents

- [Keep eager checks outside `gen` and `inst`](#gen-inst-side-conditions)

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
