# Focused checker for the direct GTSF interpreter route.

AGDA = agda +RTS -A128M -M18G -RTS -v0

check:
	$(AGDA) -i . -i ../GTSF InterpreterAll.agda

check-outcome:
	$(AGDA) -i . -i ../GTSF InterpreterOutcome.agda

check-fuel:
	$(AGDA) -i . -i ../GTSF InterpreterFuel.agda

check-traces:
	$(AGDA) -i . -i ../GTSF InterpreterTraceExtraction.agda

check-milestone-1: check-milestone-1-firewall

check-milestone-1-firewall:
	sh scripts/check-no-small-step-imports.sh \
	  InterpreterMilestoneOne.agda $(AGDA) -i . -i ../GTSF

.PHONY: check check-outcome check-fuel check-traces check-milestone-1 \
	check-milestone-1-firewall
