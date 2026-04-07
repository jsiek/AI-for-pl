# Goal
Prove `subst-⇑ˢ-⇑ᵀ` in `Terms.agda` by discharging the two remaining cast-transport obligations and eliminate its postulate.

## Plan
- [x] 1. Add canonical cast helpers (`cast↑`, `cast↑-∋`) built from `substCtx-↑ᵗ` and `substᵗ-↑ᵗ`.
- [x] 2. Prove the variable-level coherence for lifted substitutions across the casted contexts.
- [x] 3. Lift that coherence to terms via `subst-substEqᶜ` to obtain the left transport equation.
- [ ] 4. Prove the right transport bridge (`cast↑ (substᵀ ↑ᵗ N) ≡ ⇑ᵀ N`). Partial progress: theorem now defined for `zero/true/false/suc/if/var`; remaining constructor postulates listed below.
- [x] 5. Prove `subst-⇑ˢ-⇑ᵀ` using the two transport equations plus `subᵀ-sub ↑ᵗ`.
- [x] 6. Re-check `Terms.agda` and `Parametricity.agda` and mark completion.

## Remaining Proof Obligations

`subst-⇑ˢ-⇑ᵀ` is now proved. Current unresolved obligation in `Terms.agda`:

```agda
substᵀ-shiftSubst-renameᵀ-core
```

`substᵀ-shiftSubst-renameᵀ` is now a proved wrapper that transports from any `ctx-coh` to canonical `shiftSubst-ctx-coh` via `uip-≡`, and then applies `substᵀ-shiftSubst-renameᵀ-core`.
`substᵀ-extsᵗ-⇑ᵀ` remains a specialization (`ξ = S_`, `ξ' = S_`) of this generalized path, so the statement is no longer hard-wired to `⇑ᵀ`.

## Postulates Introduced In This Phase
- `substᵀ-shiftSubst-renameᵀ-core` (in `Terms.agda`): canonical generalized shift/substitution commutation parameterized by renamings (`ξ`,`ξ'`) and type coherence (`ty-coh`), with context coherence derived by `shiftSubst-ctx-coh`.

## Generalized Setup Added
- Added `SubstWk` in `Terms.agda` to characterize when a type substitution behaves like a renaming, including closure under `extsᵗ/extᵗ`.
- Added derived equalities `SubstWk-varEq`, `SubstWk-typeEq`, `SubstWk-ctxEq` and transport `castWk`.
- Added generalized theorem statement `cast-substᵀ-renameᵀ` and specialization `cast↑-substᵀ↑ᵗ-generalized`.
- Next proof work should target this generalized theorem path for binder (`Λ`) compatibility.

## Failed Attempts / Pitfalls (Do Not Repeat)
- `cast↑-substᵀ↑ᵗ-case-nat` originally failed from a forward-reference issue: the helper tried to call `cast↑-substᵀ↑ᵗ` before it was in scope. Fix that by parameterizing helpers over IH equalities (`pL/pM/pN`) instead of calling the main theorem directly.
- Direct `rewrite`-style proofs for `cast↑-substᵀ↑ᵗ-ƛ` and `cast↑-substᵀ↑ᵗ-·` repeatedly triggered Agda's ill-typed with-abstraction errors (dependent rewrite over implicit “lhs” type/context indices).
- The same dependent-rewrite failure happened for `substᵀ-map↑ᵗ-⇑ˢ-coh` (especially the `Z` case) when rewriting with `substCtx-↑ᵗ`/`substᵗ-↑ᵗ`.
- `substᵀ-map↑ᵗ-⇑ˢ-coh` was discharged by avoiding dependent `rewrite` in the `Z` case; the successful path was explicit cast composition (`substEq-cancel-sym`, `cast-ctx-type-term`, `cast↑-substᵀ↑ᵗ`, `cast-substCtx-↑ᵗ-Z`, `⇑ˢ-castᵗ`).
- A detour through generic app-cast transport lemmas (`cast-app-type-term`, `cast-app-ctx-term`) led to an additional coherence subproblem: `substᵗ-↑ᵗ (A ⇒ B)` is not definitionally equal to `cong₂ _⇒_ (substᵗ-↑ᵗ A) (substᵗ-↑ᵗ B)`, so a nontrivial cast-coherence lemma is needed there.
- Practical guidance: avoid large dependent `rewrite` chains in these goals; prefer small transport lemmas with explicit equality arguments and compose via `trans`/`cong`.
- Attempting to prove `substᵀ-shiftSubst-renameᵀ` directly with recursive `rewrite` on `ctx-coh` in nontrivial constructors (`suc`, and expected similarly `case/if/ƛ/·`) triggered Agda's ill-typed with-abstraction issue again. This route is brittle because `ctx-coh` is an arbitrary proof argument and not definitionally aligned with constructor-specific context casts.
- A partial implementation with separate `Λ`/`∙` helper postulates compiled only after reverting the unfinished recursive body; this confirmed we should avoid ad-hoc constructor rewrites and instead introduce a cast-coherence layer that does not rely on rewriting by `ctx-coh`.

### New SCC-specific failures (`subᵀ-sub-Λ-body-Z-base`)
- Attempted to define `subᵀ-sub-Λ-body-Z-base τ σ = refl`. This fails because the two sides are not definitionally equal after normalization; they differ by nontrivial casts (`substCtx-extsᵗ-⇑ᶜ` transport), so `refl` cannot solve it.
- Attempted to define the base from fuel recursion:
  - `subᵀ-sub-Λ-body-Z-base τ σ = subᵀ-sub-Λ-body-fuel (suc zero) τ σ (` Z)`
  - This reintroduces the SCC and fails termination checking.
  - Reported cycle (do not re-attempt in this form): `substᵀ-map-⇑ˢ-fuel ... Z -> subᵀ-sub-Λ-body-fuel ... (` Z) -> coh -> substᵀ-map-⇑ˢ-fuel ... Z`.
- Also tried placing the definition outside the `mutual` (for forward-reference avoidance); Agda then rejects it because the pre-mutual declaration requires a definition before the block. So this placement does not solve the SCC issue.
- `subᵀ-sub-Λ-body-Z-base` is now defined (no longer a postulate) by canonicalizing both sides and using `substᵀ-extsᵗ-⇑ᵀ` at `M = σ Z`.

## Candidate Next Direction (Current)
- Prove `substᵀ-extsᵗ-⇑ᵀ` directly by induction on `M`, generalized enough to recurse under `Λ` (instantiate IH at `extsᵗ τ` for the body).
- Keep the proof outside the mixed SCC; do not reintroduce calls into `subᵀ-sub-Λ-body-fuel` / `substᵀ-map-⇑ˢ-fuel`.
