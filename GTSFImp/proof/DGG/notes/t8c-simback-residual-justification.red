T8c SimBack residual audit

Result

The eighteen case-shaped residual parameters have become four proof-shaped
residual parameters.  `tr` remains as the pre-existing transport dependency,
so the module has five parameters in total.  The checked telescope is:

    module _
        (sim-back-target-root : SimBackTargetRootᵀ)
        (sim-back-strict-right : SimBackStrictRightᵀ)
        (sim-back-conversion-boundary : SimBackConversionBoundaryᵀ)
        (sim-back-source-lambda : SimBackSourceLambdaᵀ)
        (tr : TransportTermImprecisionᴾᵀ)
      where

The four residual classifiers are exhaustive on their named relation rows and
target-step families.  Their catch-all clauses return `⊥`, so relation/step
combinations outside those rows are refuted by dependent case analysis rather
than hidden behind a general `SimBackᵀ` premise.  No one of the original
eighteen parameters was wholly contradictory, so none has the outcome
`REFUTED`; the impossible subcases disappear in those classifier equations.

Original-parameter outcomes

| Original parameter | Outcome | Proof work or retained case |
| --- | --- | --- |
| `SimBackApplicationRootᵀ` | `COLLAPSED-into-SimBackTargetRootᵀ` | The target `blame-·₁` row is discharged by target-blame catch-up, `appL-↠`, and a final source `blame-·₁`; the other application roots remain. |
| `SimBackApplicationRightᵀ` | `COLLAPSED-into-SimBackStrictRightᵀ` | It is the same left-operator catch-up obligation as primitive right evaluation. |
| `SimBackPairedTypeApplicationRootᵀ` | `COLLAPSED-into-SimBackTargetRootᵀ` | The target `blame-•` row is discharged by catch-up, `typeApp-↠`, and a final source `blame-•`; the value-closing rows remain. |
| `SimBackPairedTypeApplicationFrameᵀ` | `DISCHARGED` | Recursive `sim-back` is lifted through both type applications, with explicit `applyTys-∀`, `applyTy-∀`, `applyTys-open`, `apply-open`, and endpoint transport. |
| `SimBackSourceTypeApplicationᵀ` | `DISCHARGED` | Recursive `sim-back` is lifted through the source-only type application; `applyTy-★` supplies the missing definitional transport. |
| `SimBackPairedCastRootᵀ` | `COLLAPSED-into-SimBackTargetRootᵀ` | The target-body `blame-⟨⟩` row is discharged by catch-up, `cast-↠`, and a final source cast-blame step; the value-closing rows remain. |
| `SimBackTargetCastRootᵀ` | `COLLAPSED-into-SimBackTargetRootᵀ` | The target-only cast blame row is discharged directly from target-blame catch-up; the non-blame roots remain. |
| `SimBackTargetRevealRootᵀ` | `COLLAPSED-into-SimBackTargetRootᵀ` | All target `blame-reveal` rows are discharged through `target-blame-catchup-under-boundary`; paired rows additionally use `reveal-↠` and fire source `blame-reveal`. |
| `SimBackTargetRevealFrameᵀ` | `COLLAPSED-into-SimBackConversionBoundaryᵀ` | It needs the same boundary-world recursion and replay as the source-only and conceal rows. |
| `SimBackTargetConcealRootᵀ` | `COLLAPSED-into-SimBackTargetRootᵀ` | All target `blame-conceal` rows, including `packaged-seal-star²`, are discharged through boundary catch-up; paired rows use `conceal-↠` and fire source `blame-conceal`. |
| `SimBackTargetConcealFrameᵀ` | `COLLAPSED-into-SimBackConversionBoundaryᵀ` | It needs the shared boundary-world recursion and replay lemma. |
| `SimBackSourceRevealBoundaryᵀ` | `COLLAPSED-into-SimBackConversionBoundaryᵀ` | The source-only reveal has the same premise-world/evolution mismatch as paired conversion frames. |
| `SimBackSourceConcealBoundaryᵀ` | `COLLAPSED-into-SimBackConversionBoundaryᵀ` | The source-only conceal has the same premise-world/evolution mismatch as paired conversion frames. |
| `SimBackPrimitiveRootᵀ` | `COLLAPSED-into-SimBackTargetRootᵀ` | Target `blame-⊕₁` is discharged by catch-up, `primL-↠`, and a final source `blame-⊕₁`; `δ-⊕` and right-blame remain. |
| `SimBackPrimitiveRightᵀ` | `COLLAPSED-into-SimBackStrictRightᵀ` | It is the same left-operand catch-up obligation as application right evaluation. |
| `SimBackBlameTargetStepᵀ` | `DISCHARGED` | Source blame stays put by irreducibility; preservation updates target typing, with separate `keep` and right-`bind` parked evolutions. |
| `SimBackPlainSourceLambdaᵀ` | `COLLAPSED-into-SimBackSourceLambdaᵀ` | Plain and smart source lambdas share the recursive source-value proof shape. |
| `SimBackSmartSourceLambdaᵀ` | `COLLAPSED-into-SimBackSourceLambdaᵀ` | The smart-comma world lift is a variant of the same source-lambda obligation. |

Why each parameter remains

`sim-back-target-root : SimBackTargetRootᵀ` is a real closing lemma.  Every
remaining root rule is pinned by an actual target value: application beta and
right-blame, polymorphic beta/generation, cast/reveal/conceal value roots, or
primitive delta/right-blame.  Its source premise need not yet be a value.  The
closed `ValueCatchupRight²` composition starts with a source value and runs the
target, which is the opposite orientation.  These rows first need the left
catch-up stack proposed in unmerged PR #164, then their case-specific closing
proofs, including the D8a.2 substitution work for beta.  Target-blame catch-up
does not apply because the surviving target heads are values, not blame.

`sim-back-strict-right : SimBackStrictRightᵀ` is a real strict-evaluation
lemma.  A target `ξ-·₂` or `ξ-⊕₂` step supplies a target operator/left-operand
value, while the related source operand may still reduce or blame.  The proof
must run the source to a related value or source blame, compose that trace with
the recursively simulated right step, and transport the untouched operand.
That is precisely the missing left catch-up result from the PR #164 stack;
value irreducibility only applies after the source value has been obtained.

`sim-back-conversion-boundary : SimBackConversionBoundaryᵀ` is a real boundary
transport lemma.  The child imprecision derivation lives at the pre-boundary
world `Wᵖ`, but `sim-back` receives `ParkedWorld W`; after recursion it must
evolve or pull the rebase witness and replay a source reveal/conceal through the
whole-term trace.  `reveal-↠` and `conceal-↠` lift a trace once it is known, and
`target-blame-catchup-under-boundary` solves only the terminal target-blame
case; neither supplies the missing parked child world and general endpoint
rebase.  This is conversion-frame proof content, not a renamed case premise.

`sim-back-source-lambda : SimBackSourceLambdaᵀ` is a real source-value lemma.
The plain and smart-comma rows must relate a source `Λ` value to the immediate
target reduct, recursively analyze the body relation under `liftWorldLeft` or
the smart-comma lift, use value irreducibility to force the source trace to be
reflexive, and then perform the D14 Λ-source keep/pullback reasoning.  The
closed right-value catch-up theorem reaches a later target value or blame; it
does not recover imprecision against the particular one-step reduct required
by `SimBackᵀ`.

`tr : TransportTermImprecisionᴾᵀ` is not one of the original eighteen
residuals, but it remains in the total telescope.  The proof on main is a
driver parameterized by `SourceBindTransport²ᵀ` and `BothBindTransport²ᵀ`.
Replacing `tr` inline would therefore add two larger bind lemmas and lengthen
the telescope; closing those is a separate transport arc under the standing
rule.

Machinery audit

The closed target-blame catch-up theorem discharged every target-blame root it
can reach, both directly and under reveal/conceal boundaries.  Value/blame
irreducibility was sufficient for the source-blame row and was checked against
the source-lambda rows, where it cannot establish the missing relation to the
immediate target reduct.  The closed right-value catch-up composition was
checked against every remaining root/right row and has the wrong direction for
their target-value premise.  `★⊑-inv` is not present on merged main; it exists
on `agent/gtsf-sim-left-values`, but its type-only conclusion does not supply
any of the missing reduction, parked-evolution, substitution, or boundary
replay evidence, so this arc does not copy it into main.
