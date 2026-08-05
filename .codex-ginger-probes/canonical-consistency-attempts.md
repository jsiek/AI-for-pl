# Canonical Consistency Attempt Log

Context: `GTSFImp/proof/CanonicalConsistency.agda`, proving uniqueness for
canonical consistency. Current hard case is the `instᵏ`/`genᵏ` overlap:

```agda
inst-gen-overlap⊥ : ∀ {Δ} {μ : Env∼ Δ} {A B}
  → zero ∈ᵗ A
  → zero ∈ᵗ B
  → instᵐ μ ⊢ A ∼ᵏ[ gen-blocked ] ⇑ᵗ (`∀ B)
  → genᵐ μ ⊢ ⇑ᵗ (`∀ A) ∼ᵏ[ gen-ok ] B
  → ⊥
```

## Failed / Rejected Paths

1. Too-general `insert-overlap⊥`.

   Rejected statement: arbitrary modes and arbitrary inserted endpoints are
   disjoint.

   Counterexample found by a small model:

   ```text
   A = ★ ⇒ ＇ zero
   B = ＇ zero ⇒ ★
   μ zero = X∼★
   ν zero = ★∼X
   ```

   With both sides in `gen-ok`, the left proof can use top-level `genᵏ` and the
   right proof can use top-level `instᵏ`; both then close componentwise through
   `？ᵏ`/`!ᵏ`. This does not refute the actual theorem because the actual left
   mode is `gen-blocked`.

2. One-sided absence helpers over the paired `InsertOverlapState`.

   Rejected statements:

   ```agda
   state-source-absent-target⊥ :
     InsertOverlapState μ ν X m n A B C D →
     X ∈ᵗ A → X ∉ᵗ B → μ ⊢ A ∼ᵏ[ m ] C → ⊥

   state-target-absent-source⊥ :
     InsertOverlapState μ ν X m n A B C D →
     X ∈ᵗ B → X ∉ᵗ A → ν ⊢ D ∼ᵏ[ n ] B → ⊥
   ```

   These are too broad. A source-side proof can erase the focused occurrence to
   `★` by `_!ᵏ`, while the endpoint tracked by the insert state is fresh. The
   contradiction in the crossed-arrow case has to use both the left and right
   proofs together, not either proof alone.

3. Brute-force search over all small type shapes.

   Result: no counterexample through full type depth 2. Depth 3 explodes
   combinatorially and was stopped.

4. Targeted brute-force search for top-level forall/function crossed-arrow
   shapes.

   Result: no counterexample through component depth 1. Component depth 2
   explodes combinatorially and was stopped.

5. Endpoint-gap-only invariant.

   Rejected after subagent analysis. `EndpointGap` records the inserted-binder
   endpoint relationship, but not whether a state is reachable from the actual
   proof constructors. The state

   ```agda
   ios-geninst ios-base
   ```

   is admissible in the old `InsertOverlapState` even though it would require a
   left `genᵏ` step under `gen-blocked` in the real theorem. That state admits
   the same skew-arrow counterexample family as the earlier over-generalized
   theorem.

6. Broad paired miss helpers over all guarded states.

   Rejected after a small model found a target-miss counterexample. Shape:

   ```text
   state = ios-right-inst ios-base
   X = suc zero
   A = ★
   B = ＇ (suc zero)
   C = `∀ (＇ zero)
   D = ★
   ```

   Both `μ ⊢ A ∼ᵏ C` and `ν ⊢ D ∼ᵏ B` can be inhabited under the generated
   environments, while `X ∉ᵗ A` and `X ∈ᵗ B`. Therefore the helper must be
   specialized to the strict skew-arrow situation left by
   `insert-overlap-state⊥`, not all missing-source/target states.

7. One-sided common-lower shortcut.

   Rejected route: apply `consistent-common-lowerᵐ` to only the left
   component proof `μ ⊢ A ∼ᵏ C` (where `μ X = X∼★`) and use occurrence
   transport to contradict `Fresh X C`.

   Why it fails: the common lower for `X∼★` gives the target-side imprecision
   environment `X⊑★`. Occurrence transport from the lower type to `C` would
   require the focused variable to be mapped by `X⊑X`, so the occurrence is
   allowed to disappear into `★`. The symmetric one-sided common-lower route
   for `ν ⊢ D ∼ᵏ B` with `ν X = ★∼X` has the same problem on the source side.
   The contradiction still has to use both crossed components together.

8. Naive bounded search for the top-level `inst/gen` theorem.

   A quick Python model of `_⊢_∼ᵏ[_]_` for the actual
   `inst-gen-overlap⊥` statement did not return useful bounded results within
   a minute and was interrupted. The search space grows too quickly if
   consistency evidence is recomputed directly with recursive `!`, `？`,
   `inst`, and `gen` cases. Do not retry that naive enumeration; a future
   search needs size-indexed dynamic programming or a narrower target shape.

9. Optimized bounded search for the actual `inst-gen-overlap⊥` statement.

   A narrower memoized model for closed root environments found no
   counterexample through type depth 6. At depth 6 it checked 232,324 pairs
   where both `A` and `B` contain `zero`.

   This is not a proof, but it supports the current diagnosis: the generalized
   Agda proof needs a synchronized-routing invariant for the strict crossed
   arrow cases, rather than a change to the canonical ordering.

10. Naive bounded search for independent `EndpointGap` crossed-star
    contradiction.

    A direct generator for pairs of `EndpointGap`s matching
    `gap-cross-star-left⊥` was interrupted after a minute without producing a
    result. Do not reuse that generator as written; the closure over context
    changes and forall peeling is too broad. If the pure gap lemma is pursued,
    either prove it directly in Agda or use a much narrower symbolic search.

11. General `EndpointGap` function-left projection.

    Scratch probe:

    ```agda
    gap-fun-left-probe :
      EndpointGap X (A ⇒ A′) (B ⇒ B′) → EndpointGap X A B
    ```

    After making the constructor patterns precise enough, Agda rejected the
    definition for termination. The problematic recursive call is the
    `end-strip-both` case:

    ```agda
    gap-fun-left-probe (end-strip-both gap) =
      gap-fun-left-probe (gap-strip-both gap)
    ```

    `gap-strip-both` is a derived lemma, so the recursive call is not visibly
    on a structurally smaller subterm. Do not use a broad `EndpointGap`
    projection as the main route unless it is replaced by a specialized
    terminating eliminator.

    Follow-up: adding `{-# TERMINATING #-}` to the scratch projection makes it
    typecheck. So the blocker is only Agda's termination checker, not a typing
    counterexample. This may be acceptable for a small proof-local projection,
    but it still does not by itself solve the strict skew contradiction.

12. Direct recursion on `inst-gen-overlap⊥`.

    Rejected as the main proof route for now. At the top level it looks
    attractive because the left premise has target `⇑ᵗ (`∀ B)` and the right
    premise has source `⇑ᵗ (`∀ A)`, which rules out many constructors. But the
    first recursive `∀`/`inst` interleavings immediately expose non-definitional
    environment reorderings such as `extᵐ (instᵐ μ)` versus
    `instᵐ (extᵐ μ)`. The current `InsertOverlapState` relation exists to
    track exactly these reorderings, so direct recursion would recreate that
    machinery with less structure.

13. Pure strict-skew state contradiction.

    Rejected statement:

    ```agda
    state-skew-left-right⊥ :
      InsertOverlapState μ ν X m n
        (A ⇒ A′) (B ⇒ B′) (C ⇒ C′) (D ⇒ D′) →
      X ∈ᵗ A → X ∉ᵗ A′ → X ∉ᵗ B → X ∈ᵗ B′ → ⊥
    ```

    The symmetric right-left version is also false. A small reachable
    counterexample uses the constructor path

    ```text
    ios-base -> ios-∀inst -> ios-right-inst
    ```

    with initial endpoint shapes roughly:

    ```agda
    A₀ = `∀ (＇ (suc zero) ⇒ ★)
    B₀ = ★ ⇒ ＇ zero
    ```

    After the path, the focused variable is `suc (suc zero)` and the state has
    endpoint shapes:

    ```text
    A = ＇ X ⇒ ★
    B = ★ ⇒ ＇ X
    C = ★ ⇒ ＇ (suc zero)
    D = ＇ (suc zero) ⇒ ★
    ```

    So the strict skew occurrence premises hold from the state alone. `CanGen`
    does not exclude this path because neither `ios-∀inst` nor
    `ios-right-inst` uses a `CanGen` premise. The strict contradiction must
    use the four component consistency proofs, not only the endpoint state.

14. Too-quick freshness transport in the strict skew holes.

    Rejected proof idea for the first strict skew branch:

    ```agda
    state-freshC st
      (∈-fun-right X∉B (...))
    ```

    This is ill-typed. `state-freshC st` needs an occurrence in `C ⇒ C′`, so
    the `∈-fun-right` constructor requires `X ∉ᵗ C`, not `X ∉ᵗ B`.
    The same mismatch appears symmetrically for `D ⇒ D′`. Absence cannot be
    moved through the endpoint spine for free.

15. Narrow four-proof strict crossed-arrow helper, wired but not proved.

    Tested helper shape:

    ```agda
    strict-cross-left⊥ : ∀ {Δ} {μ ν : Env∼ Δ}
        {m n X A A′ B B′ C C′ D D′}
      → InsertOverlapState μ ν X m n
          (A ⇒ A′) (B ⇒ B′) (C ⇒ C′) (D ⇒ D′)
      → X ∈ᵗ A → X ∉ᵗ A′ → X ∉ᵗ B → X ∈ᵗ B′
      → μ ⊢ A ∼ᵏ[ gen-ok ] C
      → μ ⊢ A′ ∼ᵏ[ gen-ok ] C′
      → ν ⊢ D ∼ᵏ[ gen-ok ] B
      → ν ⊢ D′ ∼ᵏ[ gen-ok ] B′
      → ⊥
    ```

    and the symmetric `strict-cross-right⊥` with
    `X ∉ᵗ A → X ∈ᵗ A′ → X ∈ᵗ B → X ∉ᵗ B′`. Both helper calls typechecked at
    the two holes, but the body did not follow from the current lemmas. The new
    occurrence transports only derive freshness of `C′` from `A′`-absence and
    freshness of `D` from `B`-absence:

    ```agda
    source-absent-target-to-starᵏ (state-to st) c₂ X∉A′
    target-absent-source-from-starᵏ (state-from st) d₁ X∉B
    ```

    The missing bridge is still an occurrence into one of those fresh endpoints
    (`X ∈ᵗ C′` or `X ∈ᵗ D`) from the active strict proofs
    `μ ⊢ A ∼ᵏ C` and `ν ⊢ D′ ∼ᵏ B′`. Producing that occurrence appears to need a
    synchronized strict-route invariant for the paired erasure/introduction
    proofs, not just the existing `InsertOverlapState` spines/freshness and
    asymmetric occurrence transport.

16. Broad nonempty-environment model search.

    Rejected as an exploration route. A Python model search for actual
    `instᵏ`/`genᵏ` overlaps with arbitrary environments of size up to 2 and
    type size up to 7 ran for a minute without producing output and was
    interrupted. This repeats the earlier broad-search problem at a larger
    environment size. Do not rerun this shape. If model search is used again,
    target the predecessor-chain case directly.

17. Targeted small model for actual `instᵏ`/`genᵏ` overlap.

    A memoized search over actual proof shapes, not just endpoint states, found
    no counterexample for contexts of size 0, 1, and 2 with type size up to 5.
    The largest run checked 505,521 candidate pairs at context size 2 and type
    size 5.

    This should not be used as proof evidence inside Agda. Its value is only to
    avoid repeating the same search and to distinguish two facts:

    ```text
    pure strict-skew InsertOverlapState contradiction: false
    actual four-proof strict-skew contradiction: no small counterexample found
    ```

    The next proof attempt should therefore strengthen the proof-local route
    invariant that connects endpoint gaps to the active consistency derivations,
    rather than trying another broad enumerator or another state-only lemma.

18. State-only routed-gap lemma with blocker labels.

    Rejected statement shape:

    ```agda
    strict-cross-left-route :
      InsertOverlapState μ ν X m n
        (A ⇒ A′) (B ⇒ B′) (C ⇒ C′) (D ⇒ D′) →
      X ∈ᵗ A → X ∉ᵗ A′ → X ∉ᵗ B → X ∈ᵗ B′ →
      (∃[ Y ] (Y ∈ᵗ C′ × Y ∉ᵗ A′ × μ Y ≢ ★∼X))
      ⊎
      (∃[ Y ] (Y ∈ᵗ D × Y ∉ᵗ B × ν Y ≢ X∼★))
    ```

    and the symmetric right-route statement.

    A targeted symbolic model found a counterexample to the symmetric
    right-route statement:

    ```text
    path = ios-base -> ios-∀inst -> ios-right-inst
    A = X1 -> X2
    B = X2 -> ★
    C = X1 -> ★
    D = X0 -> X1
    X = X2
    μ = [X∼X, X∼X, X∼★]
    ν = [X∼★, X∼★, ★∼X]
    ```

    The strict-right premises hold:

    ```text
    X ∉ A-left
    X ∈ A-right
    X ∈ B-left
    X ∉ B-right
    ```

    But neither side can produce the requested route witness:

    ```text
    C-left contains only X1, but A-left also contains X1.
    D-right \\ B-right contains X1, but ν X1 = X∼★.
    ```

    In other words, the endpoint state plus blocker labels is still too weak.
    The route lemma must use the active component consistency proofs; otherwise
    it includes states whose side components could only be discharged by
    permissive variable-to-star/star-to-variable proofs.

    A read-only explorer also produced a concrete Agda-shaped counterexample
    to the left-route version:

    ```agda
    A₀ = `∀ (＇ (suc zero) ⇒ ＇ zero)
    B₀ = ★ ⇒ ＇ zero

    st₀ = ios-base {A = A₀} {B = B₀}
    st₁ = ios-∀inst st₀
    st₂ = ios-right-inst st₁
    ```

    At `st₂`, the focus is `X = suc (suc zero)` and the endpoints are:

    ```agda
    A  = ＇ (suc (suc zero))
    A′ = ＇ (suc zero)
    B  = ★
    B′ = ＇ (suc (suc zero))
    C  = ★
    C′ = ＇ (suc zero)
    D  = ＇ (suc zero)
    D′ = ＇ zero
    ```

    Here `C′ \\ A′` is empty and the only candidate in `D \\ B` is
    `suc zero`, but `ν (suc zero) = X∼★`. The active-proof obstruction would be
    an impossible canonical proof like:

    ```agda
    ν ⊢ ＇ zero ∼ᵏ[ gen-ok ] ＇ (suc (suc zero))
    ```

19. Star-endpoint state-route model search.

    After rejecting the broad state-only route, I checked the narrower
    residual shape where the active component proofs have already forced the
    erased/introduced endpoints to be `★`:

    ```text
    strict-left:  C-left = ★ and D-right = ★
    strict-right: C-right = ★ and D-left = ★
    ```

    A targeted symbolic state search did not produce output within one minute
    and was interrupted. Treat this as inconclusive, not supporting evidence.
    Do not rerun this exact search. If this residual route is pursued, prove it
    directly in Agda or search with a narrower constructor-path bound.

20. Whole-type occurrence-survival-or-star shortcut.

    Rejected lemma idea:

    ```agda
    μ X ≡ X∼★ →
    μ ⊢ A ∼ᵏ[ m ] B →
    X ∈ᵗ A →
    (X ∈ᵗ B) ⊎ (B ≡ ★)
    ```

    and the symmetric `★∼X` version.

    Counterexample:

    ```text
    A = X ⇒ ★
    B = ★ ⇒ ★
    μ X = X∼★
    ```

    The left component can use `_!ᵏ` to erase `X` to `★`, but the whole target
    is still an arrow, not `★`. Any useful occurrence-survival statement must
    be component/path-aware.

## Current Direction

Keep the contradiction paired and component/path-aware. The current Agda file
has reduced the original `insert-overlap-state⊥` holes to two active-route
lemmas:

```agda
strict-cross-left-route
strict-cross-right-route
```

These route lemmas include the active component consistency proofs, because the
state-only version is false. The already-proved generalized occurrence
transport lemmas are enough to turn a route witness into a contradiction through
the passive component proof.

The current proof has refined the crossed-arrow cases by splitting on the
opposite function component:

```agda
occurs? X A′
occurs? X B′
```

If the opposite component also contains the focused variable, the existing
paired induction applies to that component. The remaining two holes are the
strict skew cases:

```text
A-left present,  A-right absent, B-left absent, B-right present
A-left absent,   A-right present, B-left present, B-right absent
```

Avoid whole-type occurrence-survival shortcuts; they are false for arrows.
The next proof attempt should either define a component/path-aware survival
classification for the active consistency proofs or prove the active-route
lemmas directly by induction on the active proofs and the state.
