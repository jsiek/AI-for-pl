# GTPLC Design Notes

## Coercion-indexed narrowing and widening

GTPLC represents type imprecision with two mutually defined judgments:

```agda
Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ B ⊣ Δᴿ
Φ ∣ Δᴸ ⊢ c ⦂ A ⊒ B ⊣ Δᴿ
```

The first is widening and the second is narrowing. Both are indexed directly
by the coercion `c`.

This replaces the earlier factorization into three layers:

1. raw `Narrowing c` and `Widening c` grammar predicates;
2. separate `NonId`, `GenSafe`, and `InstSafe` grammar predicates;
3. an imprecision judgment indexed by a proof of one of those predicates.

The separate grammar duplicated information already determined by the
imprecision endpoints. It also made composition proceed indirectly: first
compose raw grammar witnesses using a partial, fuel-indexed function, then
prove that well-typed operands make the partial result total, erase the
typing derivations to shape derivations, and reconstruct a typed result.

In the coercion-indexed design, one derivation simultaneously establishes
the imprecision relation, endpoint well-formedness, and the permitted normal
form of its coercion.

## Identity and non-identity side conditions

Identity is determined from endpoint types instead of a positive `NonId`
grammar. The smart wrappers compare types using `_≟Ty_`.

For widening into `★`, a relation ending at the function ground type is
wrapped as follows:

```agda
wrap-tag⇒ : ∀ {c Φ Δᴸ Δᴿ A}
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ (★ ⇒ ★) ⊣ Δᴿ
  → ∃[ d ] Φ ∣ Δᴸ ⊢ d ⦂ A ⊑ ★ ⊣ Δᴿ
```

If `A ≡ ★ ⇒ ★`, the result is the bare coercion `★⇒★ !`. Otherwise the
result is `c ︔ (★⇒★ !)` and its typing rule records
`A ≢ ★ ⇒ ★`.

Narrowing from `★` is dual:

```agda
wrap-untag⇒ : ∀ {c Φ Δᴸ Δᴿ B}
  → Φ ∣ Δᴸ ⊢ c ⦂ (★ ⇒ ★) ⊒ B ⊣ Δᴿ
  → ∃[ d ] Φ ∣ Δᴸ ⊢ d ⦂ ★ ⊒ B ⊣ Δᴿ
```

If `B ≡ ★ ⇒ ★`, the result is the bare coercion `★⇒★ ？`. Otherwise the
result is `(★⇒★ ？) ︔ c` and its typing rule records
`★ ⇒ ★ ≢ B`.

The polymorphic rules also need endpoint side conditions:

```agda
inst : ... → A ⊑ B → B ≢ ★ → (`∀ A) ⊑ B
gen  : ... → B ⊒ A → B ≢ ★ → B ⊒ (`∀ A)
```

These inequalities replace the relevant `InstSafe` and `GenSafe`
constraints. When the exposed endpoint is `★`, composition first constructs
a coercion to or from `★ ⇒ ★`, applies `inst` or `gen` at that non-dynamic
endpoint, and then uses `wrap-tag⇒` or `wrap-untag⇒`. Thus the normalized
coercion retains the required function tag or projection.

## Composition

Composition operates directly on typed derivations. The public narrowing
theorem has the form

```agda
narrowing-composition-total : ∀ {c d Φ Δᴸ Δᴿ A B C}
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⊒ B ⊣ Δᴿ
  → idᵢ Δᴿ ∣ Δᴿ ⊢ d ⦂ B ⊒ C ⊣ Δᴿ
  → Σ[ r ∈ Coercion ] Φ ∣ Δᴸ ⊢ r ⦂ A ⊒ C ⊣ Δᴿ
```

Widening composition is dual, with the identity imprecision context on its
left operand. The internal `composeⁿ` and `composeʷ` functions construct the
result coercion and its typing derivation together.

Removing the intermediate grammar makes the recursive calls structurally
visible to Agda. The composition definitions therefore need neither
`Maybe`, explicit fuel, a termination pragma, shape erasure, nor a separate
proof that the raw result is well typed.

## Size and tradeoff

Before removing the comparison implementation, the two developments had
the following line counts:

| Development | Relation and grammar | Composition proof | Total |
|---|---:|---:|---:|
| Grammar-indexed | 1,051 | 4,427 | 5,478 |
| Coercion-indexed | 287 | 1,166 | 1,453 |

The coercion-indexed development is 4,025 lines, approximately 73.5%,
smaller.

The main tradeoff is that narrowing and widening are no longer reusable as
untyped predicates over raw coercions. Their normal-form constraints are
available only together with imprecision typing. GTPLC accepts that
tradeoff because its consumers require typed coercions, and the combined
judgment gives composition a substantially smaller trusted interface.

The coercion-indexed design is the canonical GTPLC design.





