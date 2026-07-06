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
- [x] Restore `proof.CatchupSeparated` and
  `proof.DynamicGradualGuaranteeSeparated` to `All.agda` (they had been
  commented out while `proof.DGGBetaCastSeparated` failed to check).
- [x] Repair `proof.DGGBetaCastSeparated`:
  `separated-dgg-beta-cast-value-shape` is marked `TERMINATING` (same
  catchup-projection recursion as `sim-beta`), the missing `⊒cast+ᵗ`
  inner-coercion branches for a function-shaped target cast are covered
  (`G !`, `seal`, and `gen` are refuted through their `tgt` equations
  against the arrow-typed cast; `id` and `_︔_` are explicit holes), and
  the source-cast `with`-groups have explicit fallback holes for the
  non-canonical inner-coercion shapes.

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
- The `⊒cast-ᵗ` target-step coverage is now split exhaustively, because its
  cast coercion is a raw index: `blame-⟨⟩`, `β-id`, and `tag-untag-bad` are
  proved (the latter blames, so `⊒blameᵗ` closes it), and `β-seq`, `β-inst`,
  `tag-untag-ok`, and `seal-unseal` are now four named relation holes with
  zero source steps. Only `⊒cast+ᵗ` retains a constructor-level catch-all:
  its target cast is `narrowing-dual t⊒`, and Agda cannot decide redexes
  like `β-id` or `blame-⟨⟩` under that projection without first matching the
  `t⊒` witness shape (adding a generic `blame-⟨⟩` clause for `⊒cast+ᵗ` fails
  with a stuck unification on `narrowing-dual`).
- The remaining `⊒cast-ᵗ` step holes need: a seq-component story for
  `β-seq` (an `∶ᶜ`-typed intermediate coercion to stack two `⊒cast-ᵗ`
  layers), a target-cast-stripping inversion for `tag-untag-ok` and
  `seal-unseal` (a right-side analogue of catchup), and separated `ν`
  constructors for `β-inst` (Track B).
- The theorem conclusion now tracks the endpoint types: it returns
  `(C ≡ applyTys χs A) × (D ≡ applyTy χ′ B)` alongside the final relation.
  Every completed clause proves these directly — the `β-id` clauses derive
  the target-type equation from the `src`/`tgt` components of the id-cast
  typing tuple, the `⊕` frames use `applyTys-ℕ`/`applyTy-ℕ`, and the
  `separated-⊕-δ` helpers were extended to return the equalities. Only the
  two beta helper delegation sites carry endpoint-tracking holes, pending
  the same extension through `separated-dgg-beta`/`separated-dgg-beta-cast`
  and `sim-beta`.
- Every ξ-frame reconstruction hole is still blocked on two structural
  gaps: (a) there is no right-side store-change transport surface (the
  mirror of the postulated `left-change-term-narrowing` family) to advance
  the untouched subterm across `applyRightChange χ′` / `applyTerm χ′`; and
  (b) the resulting *coercion* `r` has no link back to the input coercion.
  Coercion-index tracking (`r ≡ applyCoercion χ′ (applyCoercions χs p)`) is
  false — the `β-id` clauses return the inner relation at its `∶ᶜ`
  coercion, not the incoming index — so the application/`⊕` frames need
  either a coercion-conversion rule in the relation or `∶ᶜ` evidence in the
  conclusion, which `⊒cast+ᵗ` inner relations cannot supply.
- The coercion-recovery story is now: endpoint tracking + normal-form
  determinacy (`narrowing-determinedᵐ` in `proof.NarrowWidenProperties`)
  determine the result coercion from the endpoints, one mode env at a
  time. `nat-endpoints-id-coercionᶜ` in `proof.DGGPrimitiveSeparated`
  packages the recipe at `‵ ℕ ⊒ ‵ ℕ` (where `cast-id` types `id (‵ ℕ)` in
  every mode), and the three `ξ-⊕`-IH holes are closed with it. The
  application-frame analogue needs the transported function coercion typed
  in the *changed* stores (blocked on the right-side transport surface)
  and at the *same mode env* as the IH's existential coercion typing —
  either a cross-mode determinacy corollary for seal-variable-free
  endpoints or mode tracking through the theorem.
- The theorem no longer takes a separate coercion premise. The old
  `∶ᶜ` premise was inherited from the shared-store statement, was
  consumed only by the `⊒blameᵗ` reconstructions, and made the theorem
  stricter than the relation: recursive calls on the general-mode inner
  relations of `⊒cast+ᵗ` and `cast-⊒ᵗ` had no `∶ᶜ` evidence to supply.
  `⊒blameᵗ` now carries general-mode coercion evidence (matching the
  other cast-composed positions), the blame cases recover it from the
  relation via `typed-term-narrowing-coercion`, and the two former
  `target-cast-plus-inner-step-simulation` /
  `source-cast-minus-inner-simulation` holes are genuine recursive calls.
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

## Partial-port findings (cambridge25 comparison, 2026-07-05)

Comparing `TermNarrowingSeparated` against the cambridge25 term narrowing
rules (`γ ⊢ M ⊒ M′ : r`):

- Present: (⊒blame), (x⊒x), (λ⊒λ), (·⊒·), (Λ⊒Λ), (κ⊒κ), (⊕⊒⊕), and the
  four cast rules.
- Missing: (extend) and (split) — the seal-correspondence manipulation
  rules; parts of their role live in the `SealCorr`/`applyLeftChanges`
  machinery, but nobody has checked the machinery derives what the rules
  provide.  Also missing: (⊒Λ), (⊒⟨ν⟩), (α⊒α), (⊒α), (ν⊒ν), (⊒ν) — the
  Track B list below.
- Weakened: all four separated cast rules dropped the cambridge25
  composition side conditions (`s ⨾ q ≈ r`, `r ≈ p ⨾ t`), which the
  shared-store `TermNarrowing` port keeps (via `_⨟ⁿ_` and `≈`).  The
  dropped conditions are what made the separated conclusion indices free
  relabelings; the coercion-tracking and mode-pinch analyses in this
  checklist were partly artifacts of that.  Restored (2026-07-05) as
  the mixfix judgment `ΔL ∣ ΔR ∣ ρ ⊢ s ⨟ t ≈ r ∶ A ⊒ B`: a record with
  cross-store typings of both factors and of `r` at one shared mode
  environment (`νᶜᵒᵐᵖ`, an implicit field, like the middle type).  The
  literal composite equality is recovered by `composite-determinedˡ/ʳ`
  via `narrowing-determinedᵐ` rather than stored, because the stored
  form would not transport across the postulated store-change surfaces.
- Supporting `sim-beta` changes for the composition witnesses:
  `sim-beta` now takes mode-generic function-coercion evidence
  (`μsim ∣ … ⊢ p ↦ q ∶ …`) plus the `∶ᶜ` typing of its
  `fun-narrow-domain-dual`, with the argument relation indexed by that
  dual.  `fun-narrow-domain-dual-determined` (proved: duals are
  witness- and mode-independent, by `dualʷ-raw-determined`) does the
  index re-alignments.  One postulate was added with explicit approval:
  `left-change-fun-coercion-narrowing`, the arrow/domain-dual sibling
  of `left-change-source-coercion-narrowing-dual`, consumed by the two
  `sim-beta` recursion sites.  The composition witnesses themselves are
  assembled from the matched constructor's incoming record by taking
  `separated-fun-domain-dual` of its three fields (all at `νᶜᵒᵐᵖ`) and
  bridging the raw indices with `fun-narrow-domain-dual-determined`.
- All four `sim-beta` composition sites are discharged (2026-07-06):
  the two domain-side sites use `cast-fun-comp-domain-dual` /
  `cast-fun-comp-domain-dual₂`, and the two codomain-side sites
  (`sim-beta-cast+-result` and `sim-beta-cast-tail`) thread a
  codomain composition premise obtained by `cast-fun-comp-codomain`
  from the matched constructor's record, transported through the
  catchup store changes with `left-change-composed-index` (both
  proved in `LeftChangeNarrowingSeparated`; no new postulates).
- `separated-dgg-beta{,-left-first,-right-first}` were re-based on the
  new `sim-beta` arity: the free-floating `pᵈ` premise is replaced by
  `fun-narrow-domain-dualᶜ p↦qᶜ` (exactly what `·⊒·ᵗ` inversion
  supplies), and the `∶ᶜ` arrow typing is transported through the
  catchup χs-chains with `left-change-fun-coercion-narrowing`, whose
  returned dual equality re-indexes the caught-up argument relation.
- `DGGBetaCastSeparated` cast patterns were arity-bumped for the new
  composition premise; its six cast *construction* sites now carry
  named `{! …-composition !}` holes (`beta-cast-tail-composition`,
  `target-argument-cast-composition`, `target-result-cast-composition`,
  `source-argument-cast-composition`,
  `source-argument-domain-composition`,
  `source-cast-tail-composition`).  They mirror the discharged
  `sim-beta` sites and should be filled the same way once that file's
  local helpers thread the incoming `compᵏ` records.
- The cambridge25 N.B. types p, q under `Γ | ∅` but r, s, t under
  `Γ | Φ`; the Agda encoding of that split is `tag-or-idᵈ`-versus-`μ`
  mode environments over a shared store (documented at `Mode` in
  `Coercions.agda`).

## Track B. Term Narrowing Surface Needed By `sim-beta`

- [x] Add separated cast-left and cast-right constructors.
- [x] Add separated `ν` and polymorphic constructors (`⊒Λᵗ`, `⊒⟨ν⟩ᵗ`,
  `α⊒αᵗ`, `⊒αᵗ`, `ν⊒νᵗ`, `⊒νᵗ`, 2026-07-05).  Target-only binders
  extend both type contexts with a `right-only` seal entry; the shared
  `α ꞉ q` coercion entry becomes a `matched` entry carrying `q`'s
  endpoint types with the correlating `q ∶ᶜ` as an explicit premise;
  endpoint typing is an explicit `TermTypingEndpointsᶜ` premise so the
  extractors stay total.  Downstream coverage clauses for the six new
  constructors are still being swept through the proof modules.
  (extend)/(split) deferred: let proof attempts guide their design.
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

## Right store changes and shared coercion raws (2026-07-06)

The ξ-⟨⟩ target-cast cases of the main theorem are wired through
`proof/InnerStepCastSeparated.agda`: the ⊒cast±ᵗ node is rebuilt over
the IH's store-changed contexts, with the sibling evidence moved by
three transport lemmas (`change-relation-coercion-narrowing`,
`change-target-coercion-narrowing`, `change-composed-index`).  These
are stated as hole-bodied lemmas, **not** postulates, because the
counterexample check surfaced a real design tension:

- The separated coercion judgment is a 7-tuple sharing **one raw**
  between the two store typings
  (`μ ∣ ΔL ∣ leftStore ρ ⊢ r ∶ A ⊒ B` and
  `μ ∣ ΔR ∣ rightStore ρ ⊢ r ∶ A ⊒ B`).
- Store changes are one-sided and shift de Bruijn indices at the front
  (`applyStore (bind A) Σ = (zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ`), and `cast-seal`
  resolves seal references positionally (`(α , A) ∈ Σ`).
- Hence a right-only `bind` demands the raw be shifted for the right
  typing (the ξ-⟨⟩ reduction indeed rewrites the stepped-under cast to
  `applyCoercion χ c`) while the unchanged left store types the
  *unshifted* raw.  One shared raw cannot satisfy both whenever it
  mentions a seal: `seal A α` needs `(α , A)` in both stores before the
  bind, and `(suc α , ⇑ᵗ A)` in the right store but still `(α , A)` in
  the left store after it.
- The **existing left-change postulate family has the mirrored
  problem**: `left-change-term-narrowing` keeps the target term (with
  its embedded `narrowing-dual t⊒` raws) fixed while `applyLeftChanges`
  shifts the left store those raws are 7-tuple-typed against.

Conclusion recorded for discussion: before the transport holes (and,
retroactively, the left-change postulates) can be discharged, the
separated coercion judgment likely needs either (a) per-side raws
related by a correspondence, or (b) seal references resolved through
`ρ` (names, not positions), or (c) an invariant that the mediating
coercions of ⊒cast±ᵗ nodes are seal-free on the opposite side.  Note
the mode system already distinguishes the sides (`tag-or-idᵈ` vs `μ`),
so (c) may be closest to cambridge25's `Γ | ∅ ⊢ p, q` discipline: the
`∶ᶜ`-side coercions cannot be seals, and the `Γ | Φ`-side raws are
exactly the ones the store changes rewrite.

Design decision (2026-07-06): pursue the ρ-mediated variant — the
coercion index is typed against ONE home store (right/target), and the
matched entries of ρ mediate the source-side endpoint through a
renaming.  Rationale: strict seal-freeness for `∶ᶜ` is too strong
(relating `x ⊒ x` at a matched-seal-typed variable needs `id (＇ α)`),
while mediation keeps such indices and translates their names.
Prototyped in `proof/MediatedNarrowingPrototype.agda`:

- `MedTy`/`MedCo` — mediation relations over an abstract variable
  correspondence, with `ExtVar` binder extension; `MatchedVar ρ` is the
  instance induced by ρ's matched entries.
- Proved: functionality, one/two-sided renaming lemmas, the
  allocation-shaped inclusions for `applyLeftChanges`-,
  `applyRightChange`-, and lockstep-(`⇑ᶜorr`)-shaped extensions —
  `mv-lockstep` shows the six lockstep constructors induce exactly
  `ExtVar` of the old correspondence, reconciling them with the
  one-sided theorem formulas.
- Proved: the crux lemma `med-cast-typing` (mediation preserves cast
  typing across stores) in all ten constructor cases, given
  `ModeCorr`/`StoreMed`/scoping side conditions.
- Proved hole-free: `left-alloc-transport` — the reshaped judgment
  crosses a left store change with the home raw, its typing, and its
  endpoints untouched.  This is the statement whose shared-raw
  analogue is false today.
- Remaining holes are plumbing only: `⟰ᵗ` membership shifts for
  `StoreMed`, the `occurs zero` boolean traversal, the structural
  `Narrowing` witness transport, and ordinary one-store weakening for
  the home-side allocation demo.

Migration sketch (next steps if adopted): extend `StoreCorr` (or a
sibling record) with the `StoreMed` payload invariant and a
`ModeCorr`-style mode discipline; replace the 7-tuple with the
`⊢ᵐ`-shaped judgment; sweep TermNarrowingSeparated constructors and
extractors; restate the left-change family (now provable via
`medTy-mapˡ`-style transports) and the InnerStepCastSeparated holes
(via the right-side lemmas).

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
