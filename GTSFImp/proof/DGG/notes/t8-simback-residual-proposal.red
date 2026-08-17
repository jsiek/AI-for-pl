T8 SimBack residual proposal

Current checked proof surface:

  proof/DGG/SimBackProof.agda

exports a parameterized `sim-back`:

  sim-back-residual : SimBackᵀ
  tr : TransportTermImprecisionᴾᵀ
  --------------------------------
  sim-back : SimBackᵀ

The residual parameter is deliberately not a new Def-level file.  It marks the
case families below while the checked proof closes the structural rows that
only need recursion through an immediate `⊢²` premise:

- `·⊑·²` / target `ξ-·₁`
- `cast⊑cast²` / target `ξ-⟨⟩`
- `⊑cast²` / target `ξ-⟨⟩`
- `cast⊑²` / any target step in the right premise
- `⊕⊑⊕²` / target `ξ-⊕₁`

Blocked case table

| Family | Target step | Why residual is needed |
| --- | --- | --- |
| target root application | `β`, `β-⇒`, `β-reveal-⇒`, `β-conceal-⇒`, `blame-·₁`, `blame-·₂` | source must catch up to value or blame before replaying a whole application square |
| target right application operand | `ξ-·₂` | target operator is already a value; source operator needs less-precise catchup, with a source-blame branch |
| target root type application | `β-∀`, `β-Λ`, `β-gen`, `β-reveal-∀`, `β-conceal-∀`, `blame-•` | source must catch up to a polymorphic value or blame; bind/store evolution affects both type opening and worlds |
| target type-application premise | `ξ-•` | structurally similar to the checked rows, but needs a reusable open/apply transport package for `applyTys-open`/`apply-open` |
| target root cast | `β-id`, `ground`, `expand`, `tag-untag`, `tag-untag-bad`, `blame-bot-intro`, `blame-⟨⟩`, `β-inst` | value/value backward cast closing is not the same as the forward `SimPairedCastValuesᵀ` surface |
| target reveal/conceal roots | `id-reveal`, `conceal-reveal`, `id-conceal`, `blame-reveal`, `blame-conceal`, `β-reveal-∀`, `β-conceal-∀` | needs backward source catchup under seal/rebase boundaries |
| target reveal/conceal frames | `ξ-reveal`, `ξ-conceal` under `⊑reveal²`, `⊑conceal²`, `reveal⊑reveal²`, `conceal⊑conceal²`, `packaged-seal-star²`, and source-only boundary heads | premise relation lives at a boundary world; recursion requires a frame-specific parked-world bridge |
| target primitive root/right operand | `δ-⊕`, `blame-⊕₁`, `blame-⊕₂`, `ξ-⊕₂` | source operand catchup and source-blame branch mirror application-right, then primitive value closing runs backward |
| source-blame relation | `blame⊑²` with any target step | needs a target-step preservation-to-typing bridge plus parked right allocation for bind steps |
| mixed `Λ⊑²` and `Λ⊑²-smart-comma` | any target step in the non-Λ target | needs an induction over the special ∀⊑/smart-comma premise world, not a local syntactic rebuild |

Proposed major surfaces

1. `SimBackOperatorValueCatchupᵀ`

Before context:

  `W ∣ [] ⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB`
  and the target application step is selected in the right operand:

  `L′ · M′ —→[ χᴿ ] N′`

with target operator evidence `Value L′`.

Statement shape:

  if `ParkedWorld W`,
  `W ∣ [] ⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB`,
  `W ∣ [] ⊢² M ⊑ M′ ∶ pA`,
  `Value L′`, and `M′ —→[ χᴿ ] N′`,
  then either the source operator/argument path reaches a related application
  endpoint satisfying the fixed `SimBackᵀ` conclusion for
  `L · M ⊑ L′ · M′`, or the source reaches `blame` with the same fixed
  conclusion via `blame⊑²`.

After context:

  `Σ Δᴸ′ χsᴸ N Δ′ W′ q.
     (L · M —↠[ χsᴸ ] N) ×
     ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
     W′ ∣ [] ⊢² N ⊑ N′ ∶ q`

where `q : applyTys χsᴸ B ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B′`.

2. `SimBackTargetRootClosingᵀ`

Before context:

  the target step is a whole-term root step for an application, type
  application, ordinary cast, reveal, conceal, or primitive operation.

Statement shape:

  for each root-step constructor, if the enclosing `⊢²` derivation has the
  matching head constructor and the required target values are present, then
  the source side can catch up and replay a store-changing trace satisfying the
  unchanged `SimBackᵀ` conclusion.

This should be split by language form before implementation:

- `SimBackPairedFunClosingᵀ`
- `SimBackPairedAllClosingᵀ`
- `SimBackPairedCastValuesᵀ`
- `SimBackTargetCastValuesᵀ`
- `SimBackPrimitiveValuesᵀ`
- reveal/conceal value surfaces indexed by the existing boundary evidence

3. `SimBackTypeApplicationFrameᵀ`

Before context:

  `W ∣ [] ⊢² M ⦂∀ C [ A ] ⊑ M′ ⦂∀ C′ [ A′ ] ∶ r`
  and target premise step
  `M′ —→[ χᴿ ] N′`.

Statement shape:

  if `sim-back` closes the premise square for `M ⊑ M′`, then the lifted type
  application square closes with:

  `M ⦂∀ C [ A ] —↠[ χsᴸ ]
     N ⦂∀ applyBodies χsᴸ C [ applyTys χsᴸ A ]`

and

  `W′ ∣ [] ⊢²
     N ⦂∀ applyBodies χsᴸ C [ applyTys χsᴸ A ]
     ⊑ N′ ⦂∀ applyBody χᴿ C′ [ applyTy χᴿ A′ ] ∶ q`.

The new reusable sublemma should be the transport package:

  `applyTys-open`/`apply-open` commute with `transport⊑ᴾ` and `⊢²`
  constructors for both paired `•⊑•²` and source-only `•⊑²`.

4. `SimBackConversionFramesᵀ`

Before context:

  a target step happens under `↑` or `↓`, or the source relation is already
  under a source/target reveal/conceal boundary whose premise world differs
  from the enclosing world.

Statement shape:

  a record matching `SimConversionFramesᵀ`, but with target-step dispatch:

  - `source-reveal-target-frame`
  - `target-reveal-target-frame`
  - `source-conceal-target-frame`
  - `target-conceal-target-frame`

Each field takes `ParkedWorld W`, the whole boundary-headed `⊢²` relation, and
the target step, and returns the fixed `SimBackᵀ` conclusion for that whole
relation.

5. `SimBackBlameTargetStepᵀ`

Before context:

  `W ∣ [] ⊢² blame ⊑ M′ ∶ p`
  and `M′ —→[ χᴿ ] N′`.

Statement shape:

  if `ParkedWorld W` and target preservation proves `N′` has type
  `applyTy χᴿ B`, then the source takes zero steps to `blame`, the parked
  world evolves along the right step (`evolve-keepᴿ` or
  `evolve-right-bind`), and the endpoint is:

  `W′ ∣ [] ⊢² blame ⊑ N′ ∶ q`

for `q : A ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B`.

This is a preservation/parked-right-allocation bridge, not a change to the
term-imprecision relation.
