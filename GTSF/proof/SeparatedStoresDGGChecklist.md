# Separated Stores DGG Checklist

## Working Policy

- Prioritize getting back to the DGG beta case and the `sim-beta` lemma.
- Work top-down where that clarifies the target proof shape.
- Let `catchup-lemmaˡ` remain unfinished while the DGG caller and simulation
  lemma surface are being shaped.
- Avoid new redundant postulates; use existing proof holes in modules that
  already allow unsolved metas while the proof is under construction.

## Progress Snapshot

- [x] Add explicit seal correspondence with `leftStore` and `rightStore`.
- [x] Add side-specific seal correspondence shifts.
- [x] Add the initial separated term narrowing relation.
- [x] Make separated term narrowing endpoint typing witnesses explicit
  constructor arguments.
- [x] Replace the separated endpoint-typing record with product-shaped
  evidence and pattern match on pairs at term-narrowing use sites.
- [x] Add left-side catchup store-change operations.
- [x] State `catchup-lemmaˡ` with the target term unchanged.
- [x] Add the new separated-store modules to `All.agda`.
- [x] Add the separated DGG beta proof surface to `All.agda`.

## Track A. Back To DGG Beta

- [x] Add a separated DGG theorem skeleton focused on application beta.
- [x] Add a full separated `dynamicGradualGuarantee` skeleton over the current
  separated term-narrowing relation.
- [x] Add a separated `sim-beta` statement.
- [x] Adapt the DGG beta case to call `catchup-lemmaˡ` sequentially.
- [x] Split the value-left beta caller case on `RuntimeOK R`.
- [x] Add an argument-first beta caller helper for runtime-active arguments.
- [x] Preserve the domain/argument relation across catchup.
- [x] Compose the `ready` and `tail` reductions in separated stores.
- [x] Identify the exact separated constructors needed by `sim-beta`.

Current named obligations in `proof.DynamicGradualGuaranteeSeparated`:

- `catchup-lemmaˡ`, `advance-left-term-narrowing`, and
  `advance-left-lambda-narrowing` now preserve source-side changes with
  `applyCoercions` and `applyTys`, while the target term/type stay fixed.
- The left-first and argument-first beta helpers now maintain the domain
  relation through catchup. Their `WR⊒V′` premises are obtained by rewriting
  `applyCoercions` through duality, so the argument reaches `sim-beta` at the
  dual of the caught-up function domain.
- `left-ready` now uses `·₁-↠` directly in the left-first helper
  `separated-dgg-beta-left-first`.
- `separated-dgg-beta` now cases on `RuntimeOK (L · R)`: the `ok-no` and
  `ok-·₁` cases provide `No• R` directly and call the left-first helper. The
  `ok-·₂` value-left case now cases again on `RuntimeOK R`; its `ok-no`
  subcase also calls the left-first helper, while the remaining subcases are
  routed through `separated-dgg-beta-right-first`.
- `separated-dgg-beta-left-first` now takes the exposed `RuntimeOK L` and
  `RuntimeOK R` facts directly. This removes the local runtime projection
  helpers from the beta caller and keeps both sequential catchups tied to the
  `RuntimeOK` cases chosen by `separated-dgg-beta`.
- `separated-dgg-beta-right-first` handles the value-left/runtime-argument
  path by catching up `R` first, advancing the already-value function relation
  across those left-side changes, and calling `sim-beta` with the resulting
  premises.
- `dynamicGradualGuarantee` in `proof.DynamicGradualGuaranteeSeparated` now
  gives the full theorem-shaped caller for the separated-store relation. Its
  result tracks a source-side sequence `χs`, the target one-step store change
  `χ′`, the advanced left namespace `ΔL′`, the advanced right namespace
  `ΔR′`, and the combined seal correspondence
  `applyRightChange χ′ (applyLeftChanges χs ρ)`.
- The pure application beta case of this full skeleton is wired to
  `separated-dgg-beta`. This is now the top-down caller that checks whether
  the `sim-beta` statement is usable by the full theorem.
- The application and primitive congruence cases already invoke the recursive
  `dynamicGradualGuarantee` call before their reconstruction holes, preserving
  the induction-hypothesis opportunity in the skeleton.
- The two target-cast constructors currently remain constructor-level holes in
  the full skeleton. Splitting their target reductions exhaustively requires
  first inverting the shape of the target cast coercion, because Agda cannot
  decide redexes like `β-id` under an unknown `- s`.
- `applyLeftChanges-++` is now available from `proof.CatchupSeparated`.
  Both beta caller helpers use it with `applyTyCtxs-++` and `↠-trans` to
  return a single composed source reduction after the call to `sim-beta`.
- `sim-beta-lambda` proves the direct lambda beta simulation shape, modulo the
  separated substitution lemma.
- `sim-beta` now has explicit coverage for the direct lambda case
  (`ƛ⊒ƛᵗ`) and the two remaining source-cast cases (`cast+⊒ᵗ`,
  `cast-⊒ᵗ`). Agda accepts this as exhaustive for the current separated
  relation.
- The source-cast cases now expose the recursive `sim-beta` call directly in
  each clause. In the `t = c ↦ d` branches, the argument cast is caught up
  first, the inner function relation is advanced across those left-side
  changes, and the recursive call uses the resulting value argument evidence.
  The argument-cast relation is now built at the call site from two explicit
  evidence holes. Those holes sit beside the `cast-fun c⊢ d⊢` typing
  information and the existing argument relation instead of being hidden behind
  reusable endpoint-projection lemmas.
- The final source-cast wrappers are now structurally present: each branch
  destructs the recursive `sim-beta` result, lifts the recursive tail reduction
  through the codomain cast, composes it with the `β-↦` head step and the
  argument-ready reduction, and returns the composed reduction.
- The source-cast branches still have two final codomain-correlation holes,
  one in each outer result-cast wrapper. The old reusable endpoint-projection
  helpers have been removed; the remaining holes now sit directly at the cast
  constructors where the relevant term/coercion typing information is in
  scope.
- `lambda-target-function-narrowing` now proves the direct `ƛ⊒ƛᵗ` case. Its
  two remaining source-cast cases invoke the recursive inversion immediately
  before the reconstruction hole, keeping the intended structural recursion
  visible.
- `advance-left-term-narrowing` now proves the zero-change base case by
  returning the existing relation directly. Its only remaining hole is the
  non-empty store-change case.
- `advance-left-lambda-narrowing` now proves the zero-change base case by
  returning the existing function relation directly. Its only remaining hole
  is the non-empty store-change case.
- `sim-beta` is temporarily marked `TERMINATING` while
  `lambda-target-function-narrowing` and `advance-left-lambda-narrowing` are
  still top-down holes. The recursive calls are on the intended inner function
  relation, but Agda cannot see that structural decrease through those
  placeholder surfaces yet.
- The source-cast cases are split on the source cast coercion `t`; the
  recursive `sim-beta` call appears only in the `t = c ↦ d` branch. The other
  coercion forms are now visible as separate cases to be ruled out or handled
  by their own typing/canonical-form facts.
- In each `t = c ↦ d` branch, the source `β-↦` head reduction is now explicit:
  `(V ⟨ - (c ↦ d) ⟩) · WR` steps to
  `(V · (WR ⟨ - c ⟩)) ⟨ - d ⟩`, and `(V ⟨ c ↦ d ⟩) · WR`
  steps to `(V · (WR ⟨ c ⟩)) ⟨ d ⟩`.
- The same branches now also have the argument-ready reductions lifted through
  the result cast with `cast-dual-↠` and `cast-↠`, respectively.
- Several non-function source-cast branches are now discharged by impossible
  `Value` patterns: `id`, sequencing, cast+ `gen`, and cast- `？`,
  `unseal`, and `inst`.
- `TermNarrowingSeparated` now has source/target typing extractors, so
  separated narrowing proofs can feed canonical-form lemmas.
- The endpoint typing witnesses in `TermNarrowingSeparated` are now explicit
  product-shaped constructor arguments. The `sim-beta` and separated DGG
  clauses pattern match through the pair and then expose the top typing
  constructor, such as `⊢⟨⟩` for source casts and `⊢ƛ` for target lambdas.
- The cast+ and cast- `∀` source-cast branches now use `canonical-⇒` plus
  impossible `FunView` equalities to discharge the function-type contradiction.
- The same canonical-form pattern now discharges cast+ `unseal` and `inst`,
  plus cast- tag, `seal`, and `gen` source-cast branches.
- The cast+ tag/untag source-cast branches are now split by the underlying
  type shape. The tag case is impossible by value evidence after dualizing to
  an untag; the untag case dualizes to an inert tag and is discharged by
  `canonical-⇒`.

## Track B. Term Narrowing Surface Needed By `sim-beta`

- [x] Add separated cast-left and cast-right constructors.
- [ ] Add separated `ν` and polymorphic constructors needed by catchup results.
- [ ] Add separated substitution narrowing for the beta body.
- [x] Remove the lightweight coercion-correlation records; separated
  constructors now carry explicit endpoint products.

The current full separated DGG skeleton ranges over the current
`TermNarrowingSeparated` relation. That relation still lacks the shared-store
constructors for `⊒Λᵗ`, `⊒⟨ν⟩ᵗ`, `α⊒αᵗ`, `⊒αᵗ`, `ν⊒νᵗ`, `⊒νᵗ`, and
`ν⊒ᵗ`, so the skeleton is full for the current separated relation but not yet
full-language complete.

The separated cast constructors currently carry explicit endpoint-product
evidence for the endpoint coercions. They intentionally leave the old
shared-store composition premises to the future two-sided coercion relation.

The separated substitution lemma is now stated as
`term-substitution-narrowingᶜ`; its proof is still a hole. The direct lambda
case is factored as `sim-beta-lambda` and already performs the one-step
`β` reduction.

## Track C. Catchup Proof

- [x] Add right-side store-change operations.
- [ ] Add a right catchup statement, if needed.
- [ ] Port catchup helper lemmas to separated stores.
- [ ] Prove `catchup-lemmaˡ`.
- [ ] Prove right catchup if needed by DGG.

Current catchup progress:

- `catchup-lemmaˡ` now splits first on `RuntimeOK`, exposing the recursive
  proof shape before introducing any named obligations. The remaining cases are
  the eight runtime constructors: `ok-no`, `ok-•`, `ok-·₁`, `ok-·₂`, `ok-ν`,
  `ok-⊕₁`, `ok-⊕₂`, and `ok-⟨⟩`.

## Track D. Migration And Cleanup

- [ ] Port the DGG theorem from shared `StoreNrw` to separated stores.
- [ ] Remove old shared-store-only beta scaffolding once the separated proof
  supersedes it.
- [ ] Decide whether old `StoreNrw` remains internal support or is deleted.
