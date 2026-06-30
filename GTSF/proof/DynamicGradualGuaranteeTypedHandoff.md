# Typed DGG Handoff

## Goal

Continue the typed proof of the app-left DGG case:

`dynamicGradualGuarantee wfΣ okM σ⊒ (⊢· L⊢ M⊢) (⊢· L′⊢ M′⊢) qᶜ (·⊒· qᶜ L⊒L′ M⊒M′) (ξ-·₁ L′→N′ shiftM)`

The old right-`ν` counterexample is invalid under the typed statement because
its source term is not well typed.  Do not revive that route.

## Immediate Blocker

The recursive call on the left subterm needs typing for the function-shaped
coercion index:

`Δ ∣ srcStoreⁿ σ ⊢ p ↦ q ∶ᶜ A ⇒ B ⊒ A′ ⇒ B′`

The app case currently has only the result coercion typing `qᶜ`.  A temporary
probe confirmed that passing `qᶜ` to the recursive call fails before any frame
transport issues arise.

## Recommended Lemma

Add a reusable typing/index lemma for term narrowing.  A good general shape is:

if `Δ ⊢ σ ꞉ srcStoreⁿ σ ⊒ˢ Σ′`, a typed variable-context narrowing relates
source context `Γ` to target context `Γ′`, source typing gives
`Δ ∣ srcStoreⁿ σ ∣ Γ ⊢ M ⦂ A`, target typing gives
`Δ ∣ Σ′ ∣ Γ′ ⊢ M′ ⦂ B`, and
`Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p`, then
`Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B`.

This requires a real context-narrowing judgment for `γ`; it is a reusable
concept, not just an alias for one proof obligation.

## App Case Use

For `·⊒·`:

- Invert source and target application typing to get typings for `L`, `L′`,
  `M`, and `M′`.
- Apply the term-narrowing typing lemma to `L⊒L′` to obtain the missing
  `p ↦ q` coercion typing for the recursive DGG call.
- The argument relation can also justify the contravariant domain half:
  derive typing for `- p`, use `dualⁿ-flips-typingᵐ`, then combine that
  widening for `p` with `qᶜ` using `cast-fun`.

After the recursive call is available, the older frame obligations remain:

- preserve or expose the transported final index, rather than hiding it behind
  only `∃[ p′ ]`;
- transport `qᶜ` through the emitted store-change history;
- transport `M⊒M′` to relate `applyTerms χs M` and `applyTerm χ′ M′` under
  `combineStoreNrw π σ`.

## Constraints

- Do not add new postulates.
- Prefer existing algebra in `proof.NarrowWidenProperties`,
  `proof.CoercionProperties`, `proof.Catchup`, and
  `proof.TermNarrowingProperties`.
- For renaming/substitution induction, formulate lemmas over the parallel
  renaming and substitution functions first, then derive single-variable
  corollaries.
- Keep proof attempts recorded in `proof/DynamicGradualGuaranteeProofLog.md`.
