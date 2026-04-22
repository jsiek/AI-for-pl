.PHONY: check agda postulate-check

AGDA ?= agda

check: agda postulate-check

# use --safe --disallow-unsound-meta
agda:
	$(AGDA) --safe -v0 All.agda

postulate-check:
	@echo "Checking for \"postulate\" in STLC/agda and STLC/agda/proof..."
	@! rg -n "postulate" *.agda proof/*.agda
