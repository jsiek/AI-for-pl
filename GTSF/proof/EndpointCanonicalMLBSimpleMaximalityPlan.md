# Simple Endpoint MLB Maximality Plan

File Charter:

- Purpose: plan for proving maximality of the simple exhaustive endpoint MLB
  algorithm.
- Scope: the public maximality theorem, durable pruning lemmas, and the new
  occurrence-based plan for the raw upper-cone coverage theorem.
- Main dependencies: `EndpointCanonicalMLBSimple.agda`,
  `EndpointCanonicalMLBSimpleSoundness.agda`, `ImprecisionWf.agda`,
  `TypeProperties.agda`, `ImprecisionProperties.agda`, and
  `MaximalLowerBoundsWf.agda`.

## Goal

The maximality theorem uses the non-GLB shape from
`EndpointCanonicalMLBDesign.md`.  It does not claim that the selected result is
above every common lower bound.  It only rules out strictly larger common lower
bounds above a selected result.

The membership-based theorem remains the central public target:

```agda
allEndpointMlbsAt-maximal :
  ∀ {Δ A B C D} →
  WfTy Δ A →
  WfTy Δ B →
  C ∈ allEndpointMlbsAt Δ A B →
  CommonLowerBoundᵢ Δ A B D →
  idᵢ Δ ∣ Δ ⊢ C ⊑ D ⊣ Δ →
  idᵢ Δ ∣ Δ ⊢ D ⊑ C ⊣ Δ
```

The selector corollaries are small wrappers:

```agda
simpleEndpointMlbAt-maximal :
  ∀ {Δ A B C D} →
  WfTy Δ A →
  WfTy Δ B →
  simpleEndpointMlbAt Δ A B ≡ just C →
  CommonLowerBoundᵢ Δ A B D →
  idᵢ Δ ∣ Δ ⊢ C ⊑ D ⊣ Δ →
  idᵢ Δ ∣ Δ ⊢ D ⊑ C ⊣ Δ

simpleEndpointMlb-maximal :
  ∀ {A B C D} →
  WfTy (endpointCtx A B) A →
  WfTy (endpointCtx A B) B →
  simpleEndpointMlb A B ≡ just C →
  CommonLowerBoundᵢ (endpointCtx A B) A B D →
  idᵢ (endpointCtx A B) ∣ endpointCtx A B ⊢ C ⊑ D
    ⊣ endpointCtx A B →
  idᵢ (endpointCtx A B) ∣ endpointCtx A B ⊢ D ⊑ C
    ⊣ endpointCtx A B
```

## Current Boundary

`EndpointCanonicalMLBSimpleMaximality.agda` now keeps only the durable proof
assembly:

- whole-list pruning shows a kept candidate has no strict above candidate in
  the whole raw list,
- raw upper-cone coverage supplies a raw candidate above the challenged common
  lower bound,
- deduplication completeness moves that candidate into the pruned list's input,
- strict-above completeness contradicts the pruning result.

The direct `ν`/`ν` branch skeleton and its eight holes were removed.  The file
now proves the raw coverage theorem by stitching two semantic frontiers:

```agda
enumMLB⁺-covers-upper-cone
enumMLB⁺-upper-cone-elim
```

Their composition gives:

```agda
rawEndpointMlbsAt-covers-upper-cone :
  ∀ {Δ A B C D} →
  WfTy Δ A →
  WfTy Δ B →
  C ∈ rawEndpointMlbsAt Δ A B →
  CommonLowerBoundᵢ Δ A B D →
  idᵢ Δ ∣ Δ ⊢ C ⊑ D ⊣ Δ →
  ∃[ E ]
    (E ∈ rawEndpointMlbsAt Δ A B ×
     idᵢ Δ ∣ Δ ⊢ D ⊑ E ⊣ Δ)
```

That theorem is deliberately upper-cone scoped.  It is not a GLB property.
It now type-checks as a definition, not as a postulate.

## Why Pivot

The previous proof shape tried to prove the omitted `ν`/`ν` case by splitting
the already-enumerated candidate route and then doing local disjunctive
inversion.  The all-`ν` branch recreated the same endpoint shape under stacked
`ν` contexts, so the proof had no clear decreasing semantic measure.

Occurrence is the better invariant.  A `ν` derivation is only possible when the
newly bound source variable is actually used:

```agda
ν :
  occurs zero A ≡ true →
  νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ `∀ A ⊑ B ⊣ Δᴿ
```

The executable algorithm uses the same test when wrapping candidates:

```agda
wrapAllIfOccurs :
  List Ty → List Ty
```

So `occurs` is not incidental bookkeeping.  It is the gate that says whether a
`ν` route is a real binder dependency or a vacuous binder that should be opened
away.

## Key Occurrence Facts

The new plan should mine or adapt these existing facts from
`MaximalLowerBoundsWf.agda` and `TypeProperties.agda` instead of reproving the
same reasoning from scratch:

- `occurs-zero-rename-ext`
- `occurs-raise-fresh`
- `raise-removeAt-freshᵢ`
- `occurs-backᵢ`
- `no-occurs-νν-supportᵢ`
- `νν-false-support-from-bodyᵢ`
- `sel-νν-no-occursᵢ`
- `sel-νν-from-∀∀-support-true-lowerᵢ`
- `sel-νν-from-∀∀-support-false-lowerᵢ`

The first local target should be an indexed occurrence-back lemma specialized
to identity imprecision:

```agda
occurs-back-idᵢ :
  idᵢ Δ ∣ Δ ⊢ A ⊑ B ⊣ Δ →
  occurs X B ≡ true →
  occurs X A ≡ true
```

This direction is useful because upper-cone coverage often gives a proof
`D ⊑ E`.  If the chosen upper candidate `E` still mentions the fresh variable,
then `D` must mention it too.  Contrapositively, if `D` is fresh for that
variable, then no valid upper candidate can depend on it.

## New Semantic Strategy

Prove raw upper-cone coverage in two conceptual stages.

### Stage 1. A Proof-Only All-Routes Search

Define a proof-only all-routes route relation that includes the fourth
`ν`/`ν` route for `` `∀ A `` and `` `∀ B ``.  The current Agda skeleton uses a
relation, not another executable list:

```agda
data CloseNeither : Ty → Ty → Set where
  close-neither-true :
    occurs zero C ≡ true →
    CloseNeither C (`∀ C)

  close-neither-false :
    occurs zero C ≡ false →
    E ≡ C [ zero ]ᴿ →
    CloseNeither C E

data EnumMLB⁺ :
    ℕ → ImpCtx → ImpCtx → ℕ → ℕ → ℕ → Ty → Ty → Ty → Set where
  supported⁺ :
    C ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B →
    EnumMLB⁺ fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C

  fourth-νν⁺ :
    CloseNeither C E →
    EnumMLB⁺ fuel (νᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
      (suc Δᶜ) Δᴸ Δᴿ (`∀ A) (`∀ B) C →
    EnumMLB⁺ (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B) E
```

The executable algorithm keeps three routes:

```agda
∀ⁱ/∀ⁱ
∀ⁱ/ν
ν/∀ⁱ
```

The proof-only search also includes:

```agda
ν/ν
```

This search may recurse on the same endpoint shape, but it still decreases
fuel.  The point is not efficiency; the point is that coverage for all four
routes should be structurally straightforward.

When building this skeleton, every recursive branch should expose the
smaller-fuel call immediately.  The branch should split route membership,
unwrap `wrapAll`, `wrapAllIfOccurs`, or `arrowProducts`, call
`enumMLB⁺-covers-upper-cone` recursively, and only then leave holes for the
inversion, transport, and final assembly obligations.  Do not leave a whole
recursive branch as a bare hole when a recursive call can already be stated.

The current Agda skeleton exposed an important refinement for the `` `∀ A `` /
`` `∀ B `` case.  The naive recursive call only lines up when the route that
produced `C` matches the outer lower-bound constructors for `D`.  A bounded
Python search of the upper-cone statement found only these inhabited
combinations:

- `C` from `∀ⁱ/∀ⁱ`, with `D` proved by `∀ⁱ/∀ⁱ`.
- `C` from `∀ⁱ/ν`, with `D` proved by `∀ⁱ/ν`.
- `C` from `ν/∀ⁱ`, with `D` proved by `ν/∀ⁱ`.

It found no examples of the suspicious cross-route branches, including
`ν/∀ⁱ` above a `∀ⁱ/ν` lower bound, `∀ⁱ/ν` above a `ν/∀ⁱ` lower bound, or
`∀ⁱ/∀ⁱ` above a `ν/ν` lower bound.

So the next proof step should be a route-preservation inversion for the upper
cone of `` `∀ A `` / `` `∀ B ``.  Given route membership for `C`, lower-bound
evidence for `D`, and `C ⊑ D`, it should either recover matching lower-bound
evidence for `D` or close the branch as impossible.  After that lemma, the
recursive calls should only be made in matching-route branches.

The Agda proof now exposes that boundary with an indexed route result:

```agda
data ∀∀UpperConeRoute :
    ℕ → ImpCtx → ImpCtx → ℕ → ℕ → ℕ → Ty → Ty → Ty → Ty → Set
```

It has exactly three constructors:

- `∀∀-both-preserved`, returning the inner `∀ⁱ/∀ⁱ` obligations.
- `∀∀-left-preserved`, returning the inner `∀ⁱ/ν` obligations.
- `∀∀-right-preserved`, returning the inner `ν/∀ⁱ` obligations.

The inversion lemma is:

```agda
enumMLB-∀∀-upper-cone-route :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D} →
  WfImpCtx² Δᶜ Δᴸ Φᴸ →
  WfImpCtx² Δᶜ Δᴿ Φᴿ →
  C ∈ enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B) →
  Φᴸ ∣ Δᶜ ⊢ D ⊑ `∀ A ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ D ⊑ `∀ B ⊣ Δᴿ →
  idᵢ Δᶜ ∣ Δᶜ ⊢ C ⊑ D ⊣ Δᶜ →
  ∀∀UpperConeRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D
```

This statement forces the outer upper type to be `` `∀ D₀ `` through the
result index and rules out all cross-route branches by construction.

Target theorem:

```agda
enumMLB⁺-covers-upper-cone :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D} →
  WfImpCtx² Δᶜ Δᴸ Φᴸ →
  WfImpCtx² Δᶜ Δᴿ Φᴿ →
  C ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B →
  Φᴸ ∣ Δᶜ ⊢ D ⊑ A ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ D ⊑ B ⊣ Δᴿ →
  idᵢ Δᶜ ∣ Δᶜ ⊢ C ⊑ D ⊣ Δᶜ →
  ∃[ E ]
    (EnumMLB⁺ fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B E ×
     idᵢ Δᶜ ∣ Δᶜ ⊢ D ⊑ E ⊣ Δᶜ)
```

This theorem should be much simpler than the old direct proof because the
`ν`/`ν` common-lower-bound case can choose the fourth route.

### Stage 2. Occurrence-Based Fourth-Route Elimination

Prove that any fourth-route witness needed by an upper-cone argument can be
realized by the real three-route `enumMLB`.

The final statement should stay upper-cone scoped.  Avoid claiming that every
fourth-route candidate is globally dominated by a real candidate until property
testing confirms that stronger claim.

The current top-down target is deliberately broader than only the fourth route:
it eliminates any `EnumMLB⁺` upper witness back to a real `enumMLB` witness.
The `supported⁺` case should be immediate; the `fourth-νν⁺` case is the
occurrence-based work.

```agda
enumMLB⁺-upper-cone-elim :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D E⁺} →
  WfImpCtx² Δᶜ Δᴸ Φᴸ →
  WfImpCtx² Δᶜ Δᴿ Φᴿ →
  C ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B →
  Φᴸ ∣ Δᶜ ⊢ D ⊑ A ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ D ⊑ B ⊣ Δᴿ →
  idᵢ Δᶜ ∣ Δᶜ ⊢ C ⊑ D ⊣ Δᶜ →
  EnumMLB⁺ fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B E⁺ →
  idᵢ Δᶜ ∣ Δᶜ ⊢ D ⊑ E⁺ ⊣ Δᶜ →
  ∃[ E ]
    (E ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B ×
     idᵢ Δᶜ ∣ Δᶜ ⊢ D ⊑ E ⊣ Δᶜ)
```

The `fourth-νν⁺` case should split on occurrence of the fourth-route body.
The current Agda file already exposes exactly those two holes:

```agda
fourth-νν⁺ (close-neither-true occE) E⁺∈
fourth-νν⁺ (close-neither-false noOccE eqE) E⁺∈
```

If the body does not mention zero:

```agda
occurs zero Cνν ≡ false
```

then the binder is vacuous.  Use the existing open-unused style facts, such as
`νν-false-support-from-bodyᵢ`, to replace the fourth-route candidate by its
opened body.  This is the case where `ν` did not create a meaningful outer
candidate.

If the body mentions zero:

```agda
occurs zero Cνν ≡ true
```

then `wrapAllIfOccurs-complete` can place the wrapped candidate into a supported
one-sided route once the corresponding recursive candidate is available.  The
occurrence-back lemmas are used to move occurrence facts across imprecision
proofs and avoid inventing occurrence assumptions.

## Supporting List Lemmas

These remain useful and should be proved independently:

```agda
wrapAll-complete :
  E ∈ xs →
  `∀ E ∈ wrapAll xs

wrapAllIfOccurs-complete :
  occurs zero E ≡ true →
  E ∈ xs →
  `∀ E ∈ wrapAllIfOccurs xs

arrowProducts-complete :
  E₁ ∈ xs →
  E₂ ∈ ys →
  E₁ ⇒ E₂ ∈ arrowProducts xs ys
```

Deduplication completeness is still needed:

```agda
dedupe-complete :
  C ∈ xs →
  C ∈ dedupe xs
```

Whole-list pruning and strict-above completeness are already isolated in the
Agda file.

## Proof Order

1. Keep `EndpointCanonicalMLBSimpleMaximality.agda` at the current boundary:
   public maximality assembled from `rawEndpointMlbsAt-covers-upper-cone`,
   which is itself assembled from `enumMLB⁺-covers-upper-cone` and
   `enumMLB⁺-upper-cone-elim`.
2. Prove or port the simple occurrence lemmas needed locally:
   `occurs-back-idᵢ`, open-unused/freshness facts, and occurrence transport
   through the relevant renamings.
3. Prove the list completeness lemmas for `wrapAll`, `wrapAllIfOccurs`,
   `arrowProducts`, and `dedupe`.
4. Define the proof-only all-routes route relation.  This is already
   represented by `EnumMLB⁺` in the current Agda skeleton.
5. Prove all-routes upper-cone coverage.
6. Prove the occurrence-based fourth-route elimination theorem, starting with
   the `occurs zero Cνν ≡ false` branch because existing support lemmas already
   have that shape.
7. Remove the `enumMLB⁺-covers-upper-cone` postulate.
8. Remove the `enumMLB⁺-upper-cone-elim` postulate.

## Risk

The risky theorem is the fourth-route elimination theorem, not the pruning
assembly.  Keep its statement upper-cone scoped until we have evidence that a
stronger global domination theorem is true.

Before committing to the exact Agda statement, mirror the proposed all-routes
search and fourth-route elimination property in the Python property tests.  If
the global domination version fails, keep the upper-cone-scoped theorem and use
that as the Agda target.

## Relationship To Coherence

Maximality remains a prerequisite for the coherence work, but it will not prove
coherence by itself.  After maximality, coherence still needs a canonical
first-route stability argument.  The occurrence-based maximality proof is
valuable because it should isolate exactly why the omitted `ν`/`ν` route does
not add a new maximal endpoint candidate.
