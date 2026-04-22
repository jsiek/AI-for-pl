.PHONY: check agda postulate-check

AGDA ?= agda

check: agda postulate-check

agda:
	$(AGDA) --safe -v0 All.agda

postulate-check:
	@echo "Checking for \"postulate\" in STLCRef/agda and STLCRef/agda/proof..."
	@! rg -n "postulate" *.agda proof/*.agda
