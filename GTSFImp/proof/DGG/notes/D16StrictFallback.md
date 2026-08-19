# D16 strict fallback record

Date: 2026-08-18

The strict form of `unmatchedTargetsDynamic` was tested at the live
target-`Λ` minting site before changing the invariant.  In
`spine-typed-Λ-child`, the child world is
`rightOnlyWorld W (＇ X)`.  Its newly allocated target entry is used directly
by both

`structural-reveal-typing B (Z∋ refl)`

and

`spine-typed-map-bindʷ (＇ X) refl typed`.

Thus the fresh target lookup must satisfy

$$
\mathsf{lookupStore}\;(\mathsf{storeBind}\;\Sigma^R\;(\mathord{\＇}X))\;0
  = \mathord{\＇}(\mathsf{suc}\;X),
$$

not `★`.  This is operational rather than a proof-only alias: the same site
maps the child spine through `bind (＇ X)` and transports its type with
`replace-zero-open B (＇ X)`.

## Strict flattening test

For the test, only the two child-world occurrences in
`spine-typed-Λ-child` were changed temporarily from
`rightOnlyWorld W (＇ X)` to `rightOnlyWorld W ★`; the conversion and spine
were deliberately left unchanged.  Agda 2.8 rejected
`structural-reveal-typing B (Z∋ refl)` with exit code 42:

> `(＇ Fin.suc X) != ★` when checking that `refl` has type
> `⇑ᵗ (＇ X) ≡ ⇑ᵗ ★`.

The source edit was then restored.  Flattening the entry would change the
instantiated endpoint from `B [ ＇ X ]ᵗ` to `B [ ★ ]ᵗ`, so it cannot
preserve this reduction/type derivation.

## Concrete `★`-then-`＇0` route

The concrete route occurs as

`rightOnlyWorld (rightOnlyWorld W ★) (＇ Fin.zero)`

with store changes `bind ★ ∷ bind (＇ Fin.zero) ∷ []`, notably in
`InstInversionDef`, `InstInversionProof`, `InstInversionLambdaProof`, and
`TargetBindLift`.  Its second entry is the same required variable-indirection
shape.  Here `＇ Fin.zero` points to the immediately preceding unmatched `★`
entry, so this route satisfies the chain-permissive fallback exactly.

Conclusion: the recorded live minting site genuinely requires variable
indirection.  D16 stage 1 must use the previously specified chain-permissive
fallback for unmatched target entries: a direct `★`, or a direct variable
whose target head is itself unmatched.

This does not validate the unrestricted generic `rightOnlyWorld W (＇ X)`
surface.  The fallback additionally requires old `X` to be unmatched, and
`spine-typed-Λ-child` plus the structural target `Λ`/conversion/`gen` sites do
not currently expose that fact.  Stage 1 therefore leaves the classification
as an explicit builder premise; stage 2 must either supply it at each caller
or redesign that generic allocation surface.
