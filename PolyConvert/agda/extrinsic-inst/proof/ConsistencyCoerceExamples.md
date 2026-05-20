# `coerce` Context Examples

This note works through a few raw `coerce` shapes.  Write `P` for `plain`
and `N` for `ν-bound`.  The notation

- `L(D)` is the mode context needed to type the left imprecision witness
  `p⊒`.
- `R(D)` is the mode context needed to type the right imprecision witness
  `p⊑`.

For `coerce D` with midpoint `B`, the desired witnesses have types

```agda
0 ∣ L(D) ⊢ p⊒ ⦂ A ⊒ B
0 ∣ R(D) ⊢ p⊑ ⦂ B ⊑ C
```

The interesting clauses impose these local constraints:

- `∀-~-∀ D` needs `L(D) = P ∷ L₀` and `R(D) = P ∷ R₀`,
  then produces output contexts `L₀` and `R₀`.
- `∀-~-B D` needs `L(D) = P ∷ L₀` and `R(D) = N ∷ R₀`,
  then produces output contexts `L₀` and `R₀`.
- `A-~-∀ D` needs `L(D) = N ∷ L₀` and `R(D) = P ∷ R₀`,
  then produces output contexts `L₀` and `R₀`.

## Example 1. `∀-~-∀` over `X-~-X`

Derivation:

```agda
D₁ = ∀-~-∀ (X-~-X here)
```

Type shape:

```agda
[] ⊢ `∀ (＇ zero) ~ `∀ (＇ zero)
```

Raw imprecision:

```agda
B   = `∀ (＇ zero)
p⊒ = `∀A⊑∀B (X⊑X zero)
p⊑ = `∀A⊑∀B (X⊑X zero)
```

Mode requirements:

```text
inner L = P ∷ []
inner R = P ∷ []
outer L = []
outer R = []
```

This is the easy case: `∀-~-∀` sees `P` on both recursive outputs.

## Example 2. `∀-~-B` over `νX-~-★`

Derivation:

```agda
D₂ = ∀-~-B wf★ (νX-~-★ here)
```

Type shape:

```agda
[] ⊢ `∀ (＇ zero) ~ ★
```

Raw imprecision:

```agda
B   = `∀ (＇ zero)
p⊒ = `∀A⊑∀B (X⊑X zero)
p⊑ = `∀A⊑B ★ (X⊑★ zero)
```

Mode requirements:

```text
recursive L = P ∷ []
recursive R = N ∷ []
outer L     = []
outer R     = []
```

This is exactly the asymmetric split that `∀-~-B` needs.

## Example 3. `A-~-∀` over `★-~-νX`

Derivation:

```agda
D₃ = A-~-∀ wf★ (★-~-νX here)
```

Type shape:

```agda
[] ⊢ ★ ~ `∀ (＇ zero)
```

Raw imprecision:

```agda
B   = `∀ (＇ zero)
p⊒ = `∀A⊑B ★ (X⊑★ zero)
p⊑ = `∀A⊑∀B (X⊑X zero)
```

Mode requirements:

```text
recursive L = N ∷ []
recursive R = P ∷ []
outer L     = []
outer R     = []
```

This is the dual asymmetric split.

## Example 4. `∀-~-∀` around Example 2

Derivation:

```agda
D₄ = ∀-~-∀ (∀-~-B wf★ (νX-~-★ here))
```

Type shape:

```agda
[] ⊢ `∀ (`∀ (＇ zero)) ~ `∀ ★
```

Raw imprecision:

```agda
B   = `∀ (`∀ (＇ zero))
p⊒ = `∀A⊑∀B (`∀A⊑∀B (X⊑X zero))
p⊑ = `∀A⊑∀B (`∀A⊑B ★ (X⊑★ zero))
```

Mode requirements:

```text
inner-most L = P ∷ P ∷ []
inner-most R = N ∷ P ∷ []
middle L     = P ∷ []
middle R     = P ∷ []
outer L      = []
outer R      = []
```

This one still works.  The inner `∀-~-B` is under an outer `P`, so after
it strips its own binder, both middle outputs are headed by `P`, which is
what the surrounding `∀-~-∀` needs.

## Example 5. `∀-~-B` around `∀-~-∀`

Derivation shape:

```agda
D₅ =
  ∀-~-B wf∀★
    (∀-~-∀ (νX-~-★ (there here)))
```

Type shape:

```agda
[] ⊢ `∀ (`∀ (＇ (suc zero))) ~ `∀ ★
```

Raw imprecision wanted by the inner `∀-~-∀`:

```agda
p⊒ᵢ = `∀A⊑∀B (X⊑X (suc zero))
p⊑ᵢ = `∀A⊑∀B (X⊑★ (suc zero))
```

Mode requirements for the inner `∀-~-∀`:

```text
inner-most L = P ∷ N ∷ []
inner-most R = P ∷ N ∷ []
inner L      = N ∷ []
inner R      = N ∷ []
```

But the outer `∀-~-B` needs:

```text
recursive L = P ∷ []
recursive R = N ∷ []
```

The right side matches, but the left side does not.  The inner `∀-~-∀`
necessarily strips a `P` binder and leaves the surrounding `N` at the head
of its output context.  The outer `∀-~-B` wants that left output under `P`.

## Example 6. `A-~-∀` around `∀-~-∀`

Derivation shape:

```agda
D₆ =
  A-~-∀ wf∀X
    (∀-~-∀ (★-~-νX (there here)))
```

Type shape:

```agda
[] ⊢ `∀ ★ ~ `∀ (`∀ (＇ (suc zero)))
```

Raw imprecision wanted by the inner `∀-~-∀`:

```agda
p⊒ᵢ = `∀A⊑∀B (X⊑★ (suc zero))
p⊑ᵢ = `∀A⊑∀B (X⊑X (suc zero))
```

Mode requirements for the inner `∀-~-∀`:

```text
inner-most L = P ∷ N ∷ []
inner-most R = P ∷ N ∷ []
inner L      = N ∷ []
inner R      = N ∷ []
```

But the outer `A-~-∀` needs:

```text
recursive L = N ∷ []
recursive R = P ∷ []
```

The left side matches, but the right side does not.  This is the dual
failure to Example 5.

## Invariants Suggested By The Examples

The output contexts are not arbitrary witnesses.  They are synthesized by
the consistency derivation:

```text
L(∀-~-∀ D) requires L(D) = P ∷ L₀ and returns L₀
R(∀-~-∀ D) requires R(D) = P ∷ R₀ and returns R₀

L(∀-~-B D) requires L(D) = P ∷ L₀ and returns L₀
R(∀-~-B D) requires R(D) = N ∷ R₀ and returns R₀

L(A-~-∀ D) requires L(D) = N ∷ L₀ and returns L₀
R(A-~-∀ D) requires R(D) = P ∷ R₀ and returns R₀
```

Arrow composition only needs a join:

```text
L(⇒-~-⇒ D E) = join (L(D)) (L(E))
R(⇒-~-⇒ D E) = join (R(D)) (R(E))
```

The bad news is that Examples 5 and 6 show valid consistency derivations
whose synthesized recursive contexts do not match the enclosing rule's
required head mode.  So a total `coerce` theorem with the current raw
imprecision constructors likely needs more than existential output
contexts.  It needs either:

- a restriction on consistency derivations that rules out these nests,
- additional raw imprecision forms that can abstract over a `ν-bound` head
  where `⊑-∀` currently requires `plain`, or
- a different decomposition theorem that can change the midpoint/raw
  imprecision shape in the problematic nested cases.
