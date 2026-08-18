T8 SimBack residual proposal

Current checked proof surface:

  proof/DGG/SimBackProof.agda

exports a parameterized `sim-back`:

  sim-back-application-root : SimBackApplicationRootᵀ
  sim-back-application-right : SimBackApplicationRightᵀ
  sim-back-paired-type-application-root :
    SimBackPairedTypeApplicationRootᵀ
  sim-back-paired-type-application-frame :
    SimBackPairedTypeApplicationFrameᵀ
  sim-back-source-type-application : SimBackSourceTypeApplicationᵀ
  sim-back-paired-cast-root : SimBackPairedCastRootᵀ
  sim-back-target-cast-root : SimBackTargetCastRootᵀ
  sim-back-target-reveal-root : SimBackTargetRevealRootᵀ
  sim-back-target-reveal-frame : SimBackTargetRevealFrameᵀ
  sim-back-target-conceal-root : SimBackTargetConcealRootᵀ
  sim-back-target-conceal-frame : SimBackTargetConcealFrameᵀ
  sim-back-source-reveal-boundary : SimBackSourceRevealBoundaryᵀ
  sim-back-source-conceal-boundary : SimBackSourceConcealBoundaryᵀ
  sim-back-primitive-root : SimBackPrimitiveRootᵀ
  sim-back-primitive-right : SimBackPrimitiveRightᵀ
  sim-back-blame-target-step : SimBackBlameTargetStepᵀ
  sim-back-plain-source-lambda : SimBackPlainSourceLambdaᵀ
  sim-back-smart-source-lambda : SimBackSmartSourceLambdaᵀ
  tr : TransportTermImprecisionᴾᵀ
  --------------------------------
  sim-back : SimBackᵀ

There is no residual parameter of type `SimBackᵀ`.  Each residual surface keeps
the same conclusion shape as `SimBackᵀ`, but adds recognizer premises that pin
the relation family and, when needed, the target step family.  The recognizers
are local Set-valued classifiers such as `ApplicationRel`,
`ApplicationRootStep`, `CastRootStep`, `TargetRevealRel`, and
`PrimitiveRightStep`; they reduce to `⊤` only on the named residual family and
to `⊥` otherwise.

Checked structural rows still proved directly:

- `·⊑·²` / target `ξ-·₁`
- `cast⊑cast²` / target `ξ-⟨⟩`
- `⊑cast²` / target `ξ-⟨⟩`
- `cast⊑²` / any target step in the right premise
- `⊕⊑⊕²` / target `ξ-⊕₁`

Narrow residual surfaces

| Surface | Relation premise | Target step premise |
| --- | --- | --- |
| `SimBackApplicationRootᵀ` | `ApplicationRel rel`, so `rel` is `·⊑·²` | `ApplicationRootStep step`: `β`, `β-⇒`, `β-reveal-⇒`, `β-conceal-⇒`, `blame-·₁`, or `blame-·₂` |
| `SimBackApplicationRightᵀ` | `ApplicationRel rel`, so `rel` is `·⊑·²` | `ApplicationRightStep step`, so the target step is `ξ-·₂` |
| `SimBackPairedTypeApplicationRootᵀ` | `PairedTypeApplicationRel rel`, so `rel` is `•⊑•²` | `TypeApplicationRootStep step`: `β-∀`, `β-Λ`, `β-gen`, `β-reveal-∀`, `β-conceal-∀`, or `blame-•` |
| `SimBackPairedTypeApplicationFrameᵀ` | `PairedTypeApplicationRel rel`, so `rel` is `•⊑•²` | `TypeApplicationFrameStep step`, so the target step is `ξ-•` |
| `SimBackSourceTypeApplicationᵀ` | `SourceTypeApplicationRel rel`, so `rel` is `•⊑²` | the target step is the step of the non-`•` target premise |
| `SimBackPairedCastRootᵀ` | `PairedCastRel rel`, so `rel` is `cast⊑cast²` | `CastRootStep step`: `β-id`, `ground`, `expand`, `tag-untag`, `tag-untag-bad`, `blame-bot-intro`, `blame-⟨⟩`, or `β-inst` |
| `SimBackTargetCastRootᵀ` | `TargetCastRel rel`, so `rel` is `⊑cast²` | `CastRootStep step`: `β-id`, `ground`, `expand`, `tag-untag`, `tag-untag-bad`, `blame-bot-intro`, `blame-⟨⟩`, or `β-inst` |
| `SimBackTargetRevealRootᵀ` | `TargetRevealRel rel`, so `rel` is `⊑reveal²` or `reveal⊑reveal²` | `RevealRootStep step`: `id-reveal`, `conceal-reveal`, or `blame-reveal` |
| `SimBackTargetRevealFrameᵀ` | `TargetRevealRel rel`, so `rel` is `⊑reveal²` or `reveal⊑reveal²` | `RevealFrameStep step`, so the target step is `ξ-reveal` |
| `SimBackTargetConcealRootᵀ` | `TargetConcealRel rel`, so `rel` is `⊑conceal²`, `conceal⊑conceal²`, or `packaged-seal-star²` | `ConcealRootStep step`: `id-conceal` or `blame-conceal` |
| `SimBackTargetConcealFrameᵀ` | `TargetConcealRel rel`, so `rel` is `⊑conceal²`, `conceal⊑conceal²`, or `packaged-seal-star²` | `ConcealFrameStep step`, so the target step is `ξ-conceal` |
| `SimBackSourceRevealBoundaryᵀ` | `SourceRevealRel rel`, so `rel` is `reveal⊑²` | any target step of the non-boundary target premise |
| `SimBackSourceConcealBoundaryᵀ` | `SourceConcealRel rel`, so `rel` is `conceal⊑²` | any target step of the non-boundary target premise |
| `SimBackPrimitiveRootᵀ` | `PrimitiveRel rel`, so `rel` is `⊕⊑⊕²` | `PrimitiveRootStep step`: `δ-⊕`, `blame-⊕₁`, or `blame-⊕₂` |
| `SimBackPrimitiveRightᵀ` | `PrimitiveRel rel`, so `rel` is `⊕⊑⊕²` | `PrimitiveRightStep step`, so the target step is `ξ-⊕₂` |
| `SimBackBlameTargetStepᵀ` | `BlameRel rel`, so `rel` is `blame⊑²` | any target step |
| `SimBackPlainSourceLambdaᵀ` | `PlainSourceLambdaRel rel`, so `rel` is `Λ⊑²` | any target step of the non-`Λ` target |
| `SimBackSmartSourceLambdaᵀ` | `SmartSourceLambdaRel rel`, so `rel` is `Λ⊑²-smart-comma` | any target step of the non-`Λ` target |

Blocked family mapping

| Family | Checked surface |
| --- | --- |
| target root application | `SimBackApplicationRootᵀ` |
| target right application operand | `SimBackApplicationRightᵀ` |
| target root type application | `SimBackPairedTypeApplicationRootᵀ` and `SimBackSourceTypeApplicationᵀ` |
| target type-application premise | `SimBackPairedTypeApplicationFrameᵀ` |
| target root cast | `SimBackPairedCastRootᵀ` and `SimBackTargetCastRootᵀ` |
| target reveal/conceal roots | `SimBackTargetRevealRootᵀ` and `SimBackTargetConcealRootᵀ` |
| target reveal/conceal frames | `SimBackTargetRevealFrameᵀ`, `SimBackTargetConcealFrameᵀ`, `SimBackSourceRevealBoundaryᵀ`, and `SimBackSourceConcealBoundaryᵀ` |
| target primitive root/right operand | `SimBackPrimitiveRootᵀ` and `SimBackPrimitiveRightᵀ` |
| source-blame relation | `SimBackBlameTargetStepᵀ` |
| mixed `Λ⊑²` and `Λ⊑²-smart-comma` | `SimBackPlainSourceLambdaᵀ` and `SimBackSmartSourceLambdaᵀ` |
