# Q Hunt Report

Branch: `agent/gtsf-extra-cast-right`

Scope: root scratch only.  No `GTSFImp/`, `Inversion/`, or `Catchup/`
files were edited.

## Verdict

Verdict: **unreachable from the checked gradual-source catalog instances**.

The exact abstract `(c′, q)` package is derivable in the cast-term relation
and still refutes unrestricted `ExtraCastRight²`.  It is not reached by the
source-generated programs checked here.  The source-generated near misses fit a
stricter generated-call shape: catch-up projections at runtime names are only
introduced with matching target injection ancestry; otherwise variable-target
catch-up uses conversion/reveal/seal structure, not a bare projection at a
different tag.

## Abstract Bad Package

`ProjectionMismatchStarRepScratch.agda` checks the target package:

- source seal representation is literally `★`;
- source value is `(($ 0) ⟨ ℕ!ˢ ⟩) ↓ seal X ★`;
- target value is `($ 0) ⟨ ℕ! ⟩`;
- extra cast is `Y? = ？ (idᵍ (＇ Y))`;
- obligation is `probe-q = X⊑X : ＇ X ⊑ᵂ⟨ probe-world ⟩ ＇ Y`.

The target reduct is:

`(($ 0) ⟨ ℕ! ⟩) ⟨ Y? ⟩ —→ blame`

because the top injection ground is `ℕ` and the projection ground is `＇ Y`.
The checked theorem
`extra-cast-right²-contradiction : ExtraCastRight² → ⊥` shows that the
unrestricted theorem surface is too broad for arbitrary `⊢²`.

This is the exact alarm shape.  The hunt question was whether gradual source
programs can generate it.

## Source-Catalog Hunt

`QHuntScratch.agda` adds a root-only scanner:

- `badTopTagFor` detects a top target injection followed by a projection at a
  different variable ground.
- `traceHasBadNameProjection` scans an `Eval` trace.
- `rightTraceHasBadNameProjection` runs the compiled right side of an
  `RS.Entry`.

The following source-derived stress entries all checked by `refl` as having no
bad projected-name signature on the compiled right trace:

| Entry | Stress axis |
|---|---|
| `skew-star-inst` | `★` instantiation under binder |
| `tag-boundary-star-inst` | same compiled `★` boundary as `skew-star-inst` |
| `adversarial-source-star` | adversarial source analogue with `★` suffix |
| `left-only-inst-path` | source-side instantiation vs dynamic right |
| `left-only-gen-path` | gen/inst interleaving against dynamic right |
| `higher-order-shared-arg` | callee-side allocation stress |
| `adversarial-source-chain` | source analogue of the chain stressor |
| `blame-dyn-bool` | real blame path, but base `Bool`/`Nat`, not name projection |

The same scratch also rechecks the clean catalog screen gates for the main
near misses.  `ReachabilityCatalog.agda` itself still checks.

## Nearest Misses

### `skew-star-inst` / `tag-boundary-star-inst`

`Phase3DeepDives.agda` checks the first `★` allocation:

- `star-inst-change₀ : bind ★`;
- `star-inst-world₁ = bothBindWorld X⊑X initialWorld ★ ★`;
- `star-inst-rebase₁ = sameWorldRebaseAt refl star-inst-X-rep₁`;
- `star-inst-function₁` is rebuilt through
  `reveal⊑reveal²` with conversion
  `〖 Fin.zero , ★ ↑ RC.X₀⇒★ 〗`;
- `star-inst-argument₁` uses the ordinary dynamic Nat cast, not a variable
  projection.

So the candidate `★` representation does appear, and a ground-tagged payload
does appear, but the checked post-step obligation is still conversion-shaped.
It does not demand `c′ = ？ (idᵍ (＇ Y))`.

### `adversarial-source-chain`

The trace locators find the expected chain allocations:

- step 0: `bind ℕ`;
- steps 1-3: `keep`;
- step 4: `bind (＇ zero)`;
- step 5: `bind (＇ (suc zero))`;
- step 6: `bind (＇ (suc (suc zero)))`.

The resulting stores are definitionally the stores of a sequence of parked
`bothBindWorld` extensions.  The fresh and original pivots remain parked by
identity embeddings.  The first checked relation boundary uses
`sameWorldRebaseAt`, not an old-target re-park.

### `higher-order-shared-arg`

The located allocations are also parked:

- first allocation: `bind RC.∀X⇒X₀`;
- second allocation: `bind (RC.ℕᵗ {Δ = 1})`.

The checked gates show the callee pivot and shared pivot remain identity
embedded on both sides.  This stresses allocation under a callee but still
does not produce a projected runtime name over a different top injection.

### `blame-dyn-bool`

This entry really does blame through a mismatched dynamic projection, but it is
the ordinary base mismatch `Bool!` followed by `Nat?`.  It is not the target
runtime-name shape `？ (idᵍ (＇ Y))`, and the obligation is not
`＇ X ⊑ᵂ ＇ Y`.

## M4/M5 Call Shapes

The checked M4 worker surfaces in
`GTSFImp/proof/DGG/Catchup/ExtraCastRightProof.agda` are consistent with the
same exclusion:

- `ground-same` and `ground-other` introduce or preserve target injections,
  not variable projections over mismatched tags.
- `project-same` has the exact safe form
  `N ⟨ (idᵍ G) ! ⟩ ⟨ ？ (idᵍ G) ⟩`; if `G = ＇ Y`, the injection ancestry and
  projection name match.
- `project-expand` first expands
  `N ⟨ G! ⟩ ⟨ ？ c ⟩` to
  `N ⟨ G! ⟩ ⟨ G? ⟩ ⟨ c ⟩`, cancels the matching `G!`/`G?`, and only then
  recurses on `c`.  The recursive cast is not applied to the stale `G!`.
- `inst` delegates to M5; M5's checked prefix allocates with `bind ★` and
  emits reveal/conversion structure
  `〖 Fin.zero , ★ ↑ A 〗`, not a mismatched projected name.

`M6DriverDesignScratch.agda` rechecks the imported M4 worker references and
the strict-decrease smoke surface.

## Candidate Invariant Interface

Formalize the generated-call restriction as a side condition on the
`ExtraCastRight²` consumer, not as the unrestricted theorem over all `⊢²`.

Candidate interface:

If an `ExtraCastRight²` call is generated from a gradual source imprecision
derivation by compilation and simulated reduction, then its `(c′, q)` package
satisfies `GeneratedExtraCastRightObligation M′ c′ q`, where:

1. If `c′ = ？ (idᵍ G)` and `q : A ⊑ᵂ⟨ W ⟩ G`, then either the visible target
   value has matching injection ancestry `N ⟨ (idᵍ G) ! ⟩`, or the call is the
   residual recursive call after `project-expand` has already canceled the
   matching `G!`/`G?` pair.
2. In the name case `G = ＇ Y`, a direct state
   `N ⟨ (idᵍ H) ! ⟩ ⟨ ？ (idᵍ (＇ Y)) ⟩` is generated only when
   `H ≡ ＇ Y`.  The `H ≢ ＇ Y` case has no generated-call constructor.
3. If the target obligation mentions a runtime variable but no matching
   injection ancestry is present, the generated catch-up cast is a conversion
   or seal/reveal artifact from instantiation, not a bare target projection.
4. World evolution is parked: generated allocation uses `bothBindWorld`,
   `rightOnlyWorld`, or the source-left analogue, with old target centers
   frozen.  Source-side wrapper descent may use `sameWorldRebaseAt` or a
   frozen-target rebase, but not a moved old target pivot.

In short:

`generated (c′ = ？ (idᵍ (＇ Y))) q` implies either matching `＇Y!` ancestry or
post-cancellation recursion.  It excludes the abstract bad state
`ℕ! ; ？Y` with `q : ＇X ⊑ᵂ ＇Y`.

## Verification

All commands used the requested toolchain:

```sh
AGDA_HOME="/tmp/claude-26597/-home-runner-AI-for-pl/"\
"abaf167a-fb69-4f9e-bdf7-5f069c5047b5/"\
"scratchpad/agda-home"

AGDA_DIR="$AGDA_HOME" agda -i GTSFImp -v0 QHuntScratch.agda
AGDA_DIR="$AGDA_HOME" agda -i GTSFImp -v0 \
  ProjectionMismatchStarRepScratch.agda
AGDA_DIR="$AGDA_HOME" agda -i GTSFImp -v0 \
  GTSFImp/proof/DGG/ReachabilityCatalog.agda
AGDA_DIR="$AGDA_HOME" agda -i GTSFImp -v0 \
  GTSFImp/proof/DGG/Phase3DeepDives.agda
AGDA_DIR="$AGDA_HOME" agda -i GTSFImp -v0 M6DriverDesignScratch.agda
```

Each exited `0`.
