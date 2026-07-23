# GTSF build. The RTS flags matter: these files are GC-bound, and a
# larger allocation area with a generous heap cap cuts checking time
# substantially.
AGDA = agda +RTS -A128M -M18G -RTS -v0

# Check a single file with: make agda FILE=NuMetaTheory.agda
FILE ?= All.agda

check: agda

agda:
	$(AGDA) $(FILE)

# Per-definition time report; pick the target with FILE=...
profile:
	$(AGDA) --profile=definitions $(FILE)

profile-modules:
	$(AGDA) --profile=modules $(FILE)

clean:
	find . -name '*~' -delete

.PHONY: check agda profile profile-modules clean
