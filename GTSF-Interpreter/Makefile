# Focused checker for the direct GTSF interpreter route.

AGDA = agda +RTS -A128M -M18G -RTS -v0

check-layout:
	sh scripts/check-module-layout.sh

check:
	$(AGDA) -i . -i ../GTSF InterpreterAll.agda

check-outcome:
	$(AGDA) -i . -i ../GTSF Core/InterpreterOutcome.agda

check-fuel:
	$(AGDA) -i . -i ../GTSF Core/InterpreterFuel.agda

check-traces:
	$(AGDA) -i . -i ../GTSF Core/InterpreterTraceExtraction.agda

check-milestone-1: check-milestone-1-firewall

check-milestone-1-firewall:
	sh scripts/check-no-small-step-imports.sh \
	  Milestones/InterpreterMilestoneOne.agda $(AGDA) -i . -i ../GTSF

check-world-narrowing:
	$(AGDA) -i . -i ../GTSF Narrowing/InterpreterWorldNarrowingProperties.agda

check-value-narrowing:
	$(AGDA) -i . -i ../GTSF Narrowing/InterpreterValueNarrowing.agda

check-milestone-2: check-milestone-2-firewall

check-milestone-2-firewall:
	sh scripts/check-no-small-step-imports.sh \
	  Milestones/InterpreterMilestoneTwo.agda $(AGDA) -i . -i ../GTSF

check-term-narrowing:
	$(AGDA) -i . -i ../GTSF Narrowing/InterpreterTermNarrowing.agda

check-compile-narrowing:
	$(AGDA) -i . -i ../GTSF Narrowing/CompileInterpreterNarrowing.agda

check-milestone-3: check-milestone-3-firewall

check-milestone-3-firewall:
	sh scripts/check-no-small-step-imports.sh \
	  Milestones/InterpreterMilestoneThree.agda $(AGDA) -i . -i ../GTSF

check-semantic-typing:
	$(AGDA) -i . -i ../GTSF Typing/InterpreterSemanticTyping.agda

check-error-freedom:
	$(AGDA) -i . -i ../GTSF Typing/InterpreterErrorFreedom.agda

check-type-soundness:
	$(AGDA) -i . -i ../GTSF Typing/InterpreterTypeSoundness.agda

check-adequacy:
	$(AGDA) -i . -i ../GTSF \
	  InterpreterAdequacy/RunReturnSoundness.agda
	$(AGDA) -i . -i ../GTSF \
	  InterpreterAdequacy/RunBlameSoundness.agda
	$(AGDA) -i . -i ../GTSF \
	  InterpreterAdequacy/SmallStepReturnCompleteness.agda
	$(AGDA) -i . -i ../GTSF \
	  InterpreterAdequacy/SmallStepBlameCompleteness.agda
	$(AGDA) -i . -i ../GTSF \
	  InterpreterAdequacy/InterpreterValueCompleteness.agda
	$(AGDA) -i . -i ../GTSF \
	  InterpreterAdequacy/BulletCatchUpContext.agda

check-milestone-4: check-milestone-4-firewall

check-milestone-4-firewall:
	sh scripts/check-no-small-step-imports.sh \
	  Milestones/InterpreterMilestoneFour.agda $(AGDA) -i . -i ../GTSF

check-milestone-5-foundation: check-milestone-5-foundation-firewall \
	check-simulation-layer-firewall

check-static-inversion:
	$(AGDA) -i . -i ../GTSF Examples/InterpreterStaticInversionExamples.agda

check-term-alignment:
	$(AGDA) -i . -i ../GTSF Examples/InterpreterTermAlignmentExamples.agda

check-operational-coercion:
	$(AGDA) -i . -i ../GTSF \
	  Examples/InterpreterOperationalCoercionNarrowingExamples.agda

check-seal-narrowing:
	$(AGDA) -i . -i ../GTSF Examples/InterpreterSealNarrowingExamples.agda

check-function-proxy:
	$(AGDA) -i . -i ../GTSF Simulation/Application/InterpreterFunctionProxySimulation.agda
	$(AGDA) -i . -i ../GTSF Typing/InterpreterFunctionProxyTyping.agda
	$(AGDA) -i . -i ../GTSF \
	  Examples/InterpreterFunctionProxySimulationExamples.agda

check-forall-proxy:
	$(AGDA) -i . -i ../GTSF Simulation/Polymorphism/InterpreterForallProxySimulation.agda
	$(AGDA) -i . -i ../GTSF \
	  Simulation/Polymorphism/InterpreterLeftForallProxySimulation.agda
	$(AGDA) -i . -i ../GTSF \
	  Simulation/Polymorphism/InterpreterRightForallProxySimulation.agda
	$(AGDA) -i . -i ../GTSF Typing/InterpreterForallProxyTyping.agda
	$(AGDA) -i . -i ../GTSF \
	  Examples/InterpreterForallProxySimulationExamples.agda

check-generalized-value:
	$(AGDA) -i . -i ../GTSF \
	  Simulation/Polymorphism/InterpreterGeneralizedValueSimulation.agda
	$(AGDA) -i . -i ../GTSF \
	  Simulation/Polymorphism/InterpreterLeftGeneralizedValueSimulation.agda
	$(AGDA) -i . -i ../GTSF \
	  Simulation/Polymorphism/InterpreterRightGeneralizedValueSimulation.agda
	$(AGDA) -i . -i ../GTSF Typing/InterpreterGeneralizedValueTyping.agda
	$(AGDA) -i . -i ../GTSF \
	  Examples/InterpreterGeneralizedValueSimulationExamples.agda

check-close-value-narrowing:
	$(AGDA) -i . -i ../GTSF Narrowing/InterpreterCloseValueNarrowing.agda
	$(AGDA) -i . -i ../GTSF \
	  Examples/InterpreterCloseValueNarrowingExamples.agda

check-coercion-simulation-foundation:
	$(AGDA) -i . -i ../GTSF Simulation/Coercion/InterpreterCoercionComputation.agda
	$(AGDA) -i . -i ../GTSF \
	  Simulation/Coercion/InterpreterCoercionConstructorSimulation.agda
	$(AGDA) -i . -i ../GTSF \
	  Simulation/Coercion/InterpreterCoercionDynamicSealSimulation.agda
	$(AGDA) -i . -i ../GTSF \
	  Simulation/Coercion/InterpreterCoercionOneSidedSequenceSimulation.agda
	$(AGDA) -i . -i ../GTSF \
	  Simulation/Coercion/InterpreterCoercionQuotientUntagSimulation.agda
	$(AGDA) -i . -i ../GTSF Simulation/Coercion/InterpreterCoercionSealSimulation.agda
	$(AGDA) -i . -i ../GTSF Simulation/Coercion/InterpreterCoercionSequenceSimulation.agda
	$(AGDA) -i . -i ../GTSF Simulation/Coercion/InterpreterCoercionSimulationMotive.agda
	$(AGDA) -i . -i ../GTSF \
	  Simulation/Coercion/InterpreterDynamicSealValueElimination.agda
	$(AGDA) -i . -i ../GTSF Simulation/Coercion/InterpreterQuotientValueElimination.agda
	$(AGDA) -i . -i ../GTSF \
	  Runtime/InterpreterTypeEnvironmentRealizationProperties.agda

check-same-index-compatibility:
	$(AGDA) -i . -i ../GTSF \
	  Simulation/Core/InterpreterSameIndexCompatibility.agda
	$(AGDA) -i . -i ../GTSF \
	  Examples/InterpreterSameIndexCompatibilityExamples.agda

check-application-simulation:
	$(AGDA) -i . -i ../GTSF \
	  Simulation/Application/InterpreterApplicationSimulation.agda

check-instantiation-simulation:
	$(AGDA) -i . -i ../GTSF \
	  Simulation/Polymorphism/InterpreterInstantiationSimulation.agda

check-instantiation-runtime:
	$(AGDA) -i . -i ../GTSF \
	  Runtime/InterpreterInstantiationRuntime.agda

check-instantiation-value-foundation:
	$(AGDA) -i . -i ../GTSF \
	  Typing/InterpreterInstantiationSemanticTyping.agda
	$(AGDA) -i . -i ../GTSF \
	  Simulation/Polymorphism/InterpreterInstantiationSimulationMotive.agda
	$(AGDA) -i . -i ../GTSF \
	  Simulation/Polymorphism/InterpreterTypeAbstractionInstantiationSimulation.agda
	$(AGDA) -i . -i ../GTSF \
	  Narrowing/InterpreterLeftTypeAbstractionNarrowing.agda
	$(AGDA) -i . -i ../GTSF \
	  Examples/InterpreterLeftTypeAbstractionNarrowingExamples.agda
	$(AGDA) -i . -i ../GTSF \
	  Simulation/Polymorphism/InterpreterLeftTypeAbstractionInstantiationSimulation.agda

check-milestone-5-foundation-firewall:
	sh scripts/check-no-small-step-imports.sh \
	  Milestones/InterpreterMilestoneFiveFoundation.agda $(AGDA) -i . -i ../GTSF

check-simulation-layer-firewall:
	sh scripts/check-simulation-layer-imports.sh \
	  Milestones/InterpreterMilestoneFiveFoundation.agda $(AGDA) -i . -i ../GTSF

.PHONY: check-layout check check-outcome check-fuel check-traces \
	check-milestone-1 \
	check-milestone-1-firewall check-world-narrowing \
	check-value-narrowing check-milestone-2 check-milestone-2-firewall \
	check-term-narrowing check-compile-narrowing check-milestone-3 \
	check-milestone-3-firewall check-semantic-typing check-error-freedom \
	check-type-soundness check-adequacy \
	check-milestone-4 check-milestone-4-firewall \
	check-milestone-5-foundation \
	check-static-inversion \
	check-term-alignment \
	check-operational-coercion \
	check-seal-narrowing \
	check-function-proxy \
	check-forall-proxy \
	check-generalized-value \
	check-close-value-narrowing \
	check-coercion-simulation-foundation \
	check-same-index-compatibility \
	check-application-simulation \
	check-instantiation-simulation \
	check-instantiation-runtime \
	check-instantiation-value-foundation \
	check-milestone-5-foundation-firewall \
	check-simulation-layer-firewall
