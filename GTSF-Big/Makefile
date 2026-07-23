# Focused checker for the GTSF big-step design draft.

AGDA = agda +RTS -A128M -M18G -RTS -v0

check:
	$(AGDA) -i . -i ../GTSF BigStepAll.agda

.PHONY: check
