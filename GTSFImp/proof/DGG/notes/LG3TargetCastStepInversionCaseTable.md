LG-3 target-cast-step inversion case table

Target statement:

if `M′ ⟨ c′ ⟩ —→[ χ ] N′`, `Value M`, `Value M′`, and
`W ∣ γ ⊢² M ⊑ M′ ⟨ c′ ⟩ ∶ q`, produce `W′`, `ext`, and
`W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶ transport⊑ᵂ ext q`.

## `⊑cast² c′ premise q`

The derivation head exposes the exact target cast.  Classify `c′`.

| target step shape | machinery |
| --- | --- |
| inert/no step selected | impossible for a reducing target cast; handled by extra-cast value case, not the one-step inversion |
| `β-id` | **core cell checked**: direct retarget by uniqueness of `q` |
| `ground` | **core cell checked**: recover the intermediate ground witness with `ground-cast-target⊑`; full extra-cast worker still needs recursive replay/mapped inert tag |
| `expand` | **core cell checked**: recover the intermediate ground witness with `expand-cast-source⊑`; recursive residual catch-up still pending |
| `tag-untag` | **core replacement checked** through `GeneratedProjectionReplacementProof`; full theorem still needs wrapper dispatch |
| `tag-untag-bad` | impossible under CTI inversion when the source is a value related to the tagged target |
| `β-inst` | delegate to current-fuel `InstCatchupRightAt`; allocation world from the M5/LG-2 surfaces |
| `β-gen` | inert value case when `gen` is `GenSafe`; otherwise type-app/all-spine machinery is needed only when the generated cast sits under a type application |
| `bot-elim` | impossible by target typing and `no-bot-value` |
| `bot-intro` | impossible/refuted by source value typing plus type-imprecision inversion |

## `cast⊑cast² c c′ premise q`

The target cast is still exposed.  Use the same core cast classification as
`⊑cast²`; the recursive premise is the inner `premise`.

2026-08-16 update: the `β-id` paired cell is checked by replaying the source
cast as `cast⊑²`.  The non-identity paired rows expose an additional
post-source endpoint gap: generic reconstruction needs witnesses such as
`A ⊑ G` or `A ⊑ ★` after the source cast, while the paired constructor gives
the pre-source premise `C ⊑ ...` and the final endpoint.  See
`lg3-paired-target-cast-inversion-post-source-gap.red`.

## source-wrapper heads

These do not reduce on the target side.  Strip the source wrapper to its
premise, run the target-cast-step inversion there, and replay the source
wrapper over the transported premise.

| derivation head | machinery |
| --- | --- |
| `cast⊑²` | source-wrapper strip and replay over a right world extension |
| `reveal⊑²` | `StructuralSourceRebaseReplayProof` reveal replay |
| `conceal⊑²` | `StructuralSourceRebaseReplayProof` conceal replay plus hereditary partner/supply where transport alone is insufficient |
| `Λ⊑²` / `Λ⊑²-smart-comma` | source lambda replay surfaces; target side unchanged |
| `Λ⊑Λ²` | equal-mass source/target wrapper case; replay after transporting both lifted premises |
| `reveal⊑reveal²` / `conceal⊑conceal²` | paired wrapper replay; if the target wrapper is the reducing context, use target-strip surfaces below |

## target-wrapper heads

These place the selected cast under a target wrapper.  Use the target strip
surfaces to expose the child cast premise, solve that child, then absorb the
wrapper back into the conclusion.

| derivation head | machinery |
| --- | --- |
| nested `⊑cast²` | target cast absorption through `⊑cast²`, using the mapped outer cast |
| `⊑reveal²` | target reveal peel/replay and absorption |
| `⊑conceal²` | target conceal peel/replay and absorption |
| target side under generated all/reveal/conceal spines | LG-1 target peel packages plus `StructuralTargetFrameAbsorptionDef` |

## Generated-projection replacement

The old proof used `GeneratedProjection`/`CatchupCast` to justify target
projections.  LG-3 recovers the same information from the exposed CTI premise
and right-injection inversion.

Checked core replacement:
`proof.DGG.Catchup.GeneratedProjectionReplacementProof`.

For the matched projection step:

`N ⟨ G ! idᵍ ⟩ ⟨ G ? idᵍ ⟩ —→ N`

use `RightInjInversion²` on
`W ∣ γ ⊢² M ⊑ N ⟨ G ! idᵍ ⟩ ∶ p★`, together with the source value spine, to
produce `W ∣ γ ⊢² M ⊑ N ∶ qG`.

For projection expansion:

`N ⟨ G ! idᵍ ⟩ ⟨ G ? c ⟩ —→ N ⟨ G ! idᵍ ⟩ ⟨ G ? idᵍ ⟩ ⟨ c ⟩`

first use `RightInjInversion²` to recover `W ∣ γ ⊢² M ⊑ N ∶ qG`.  Rebuild the
expanded reduct by applying the target projection/tag CTI layers and the
residual target cast `c`.  The fuel restart for the residual catch-up is
justified by `project-expand-decreaseᵀ : castSize c < castSize (？ c)`.

For generated target wrappers, the same replacement is used under the
wrapper-specific peel/absorption surfaces.  Occupancy-gated partner inversion
is still required only for conceal/seal wrapper replay where transport alone
does not reconstitute the source-side partner obligation.

Remaining Agda obligation: implement the wrapper-aware theorem that performs
this recovery for every CTI head in the tables above.  The generated-projection
provenance object itself is not reintroduced.

2026-08-16 update: the generated-projection replacement and exposed target-only
cells are checked; the remaining Agda obligation is the wrapper-aware theorem
plus the paired non-identity endpoint transport described above.
