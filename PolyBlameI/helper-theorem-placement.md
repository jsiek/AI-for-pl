# Helper Theorem Placement (Reminder)

When adding helper lemmas, place them by domain:

- `TypeSubst.agda`: type-level renaming/substitution lemmas (no term-level helpers).
- `Store.agda`: store-only structure/lookup/uniqueness lemmas (no term or imprecision proofs).
- `Imprecision.agda`: imprecision/reachability/freshness/same-drop helpers, and lemmas depending on those notions.
- `Reduction.agda`: reduction rules plus only reduction-specific glue.

Quick check before adding a helper to `Reduction.agda`:

1. If it mentions only types/renaming/substitution, move it to `TypeSubst.agda`.
2. If it mentions only stores/lookups/`Uniqueˢ`, move it to `Store.agda`.
3. If it mentions `FreshReachˢ`, `Reachˢ`, `SameDropˢ`, `replaceᵗ`, or `RenameSafeˢ`, move it to `Imprecision.agda`.
