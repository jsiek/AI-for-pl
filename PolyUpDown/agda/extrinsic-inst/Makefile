.PHONY: check agda postulate-check

AGDA ?= agda

check: agda postulate-check

agda:
	$(AGDA) --safe -v0 All.agda

postulate-check:
	@echo "Checking for \"postulate\" in PolyUpDown/agda/extrinsic-inst..."
	@! rg -n "postulate" *.agda
