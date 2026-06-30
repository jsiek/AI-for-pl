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

## Refuted Lemma

The initially recommended reusable typing/index lemma for arbitrary term
narrowing is false.  The tempting shape was:

if `Δ ⊢ σ ꞉ srcStoreⁿ σ ⊒ˢ Σ′`, a typed variable-context narrowing relates
source context `Γ` to target context `Γ′`, source typing gives
`Δ ∣ srcStoreⁿ σ ∣ Γ ⊢ M ⦂ A`, target typing gives
`Δ ∣ Σ′ ∣ Γ′ ⊢ M′ ⦂ B`, and
`Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p`, then
`Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B`.

The checked counterexample is in
`proof.TermNarrowingTypingCounterexample`.  It uses:

`0 : ℕ`

`blame : ℕ`

`0 ⊒ blame ∶ id 𝔹`

The last relation is admitted by `⊒blame` using the independently well-typed
coercion `id 𝔹 ∶ᶜ 𝔹 ⊒ 𝔹`.  The proposed lemma would require
`id 𝔹 ∶ᶜ ℕ ⊒ ℕ`, which is impossible.

The branch now adds the missing context-narrowing judgment
`Δ ∣ Σ ⊢ γ ꞉ Γ ⊒ᵍ Γ′`, but that premise is not enough to make the exact
typing/index theorem true.

## Replacement Direction

Do not try to prove the refuted arbitrary theorem.  The next durable route is
one of:

- introduce a typed/well-indexed term-narrowing judgment whose constructors
  carry endpoint-aligned coercion typings by construction;
- strengthen the existing relation constructors so every stored coercion typing
  is tied to the source and target term typings;
- prove a restricted lemma for non-blame, non-arbitrary-index branches that is
  strong enough for the app-left case where the target function actually steps.

The first option is the cleanest for DGG: the induction hypothesis would expose
the function-shaped coercion typing for `L⊒L′` directly.

## App Case Use

For `·⊒·`:

- Invert source and target application typing to get typings for `L`, `L′`,
  `M`, and `M′`.
- Apply the typed/well-indexed term-narrowing invariant to `L⊒L′` to obtain
  the missing `p ↦ q` coercion typing for the recursive DGG call.
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
