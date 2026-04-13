.PHONY: check agda postulate-check

AGDA ?= agda

check: agda postulate-check

agda:
	$(AGDA) -v0 All.agda

postulate-check:
	@echo "Checking for \"postulate\" in STLC/agda and STLC/agda/proof..."
	@! rg -n "postulate" *.agda proof/*.agda
