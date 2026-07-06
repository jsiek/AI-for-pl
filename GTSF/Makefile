# GTSF build. The RTS flags matter: these files are GC-bound, and a
# larger allocation area with a generous heap cap cuts checking time
# substantially. No --safe: this development deliberately uses
# --allow-unsolved-metas and a documented postulate surface
# (proof/LeftChangeNarrowingSeparated.agda) while the separated-store
# DGG is under construction.

# -M18G: proof/SimBetaSeparated.agda's sim-beta definition alone needs
# >14G transiently (see profile: ~275s, 90% of the file); the cap keeps
# runaway checks from getting OS-killed while allowing that one through.
AGDA = agda +RTS -A128M -M18G -RTS -v0

# Check a single file with: make agda FILE=proof/SimBetaSeparated.agda
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
	rm -f *~ proof/*~

.PHONY: check agda profile profile-modules clean
