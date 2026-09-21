.PHONY: check agda postulate-check

AGDA ?= agda
AGDA_FLAGS = --safe -v0 -i . -i ../../STLCRef/agda

check: agda postulate-check

agda:
	$(AGDA) $(AGDA_FLAGS) CheckEpistemicLambda.agda

postulate-check:
	@echo "Checking for postulates in EpistemicLambda/agda..."
	@! rg -n "postulate" *.agda proof/*.agda
