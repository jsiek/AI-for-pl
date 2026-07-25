# GTSF build. The RTS flags matter: these files are GC-bound, and a
# larger allocation area with a generous heap cap cuts checking time
# substantially.
AGDA = agda +RTS -A128M -M18G -RTS -v0
PYTHON ?= python3
DGG_STRICT_AGGREGATE = \
	proof/DGG/Core/NuDGGUnassembledProofsStrictSpine.agda

# Check a single file with: make agda FILE=NuMetaTheory.agda
FILE ?= All.agda

check: audit agda

agda:
	$(AGDA) $(FILE)

# Source-level repository invariants: local imports resolve, strict DGG cones
# avoid permissive options, and every strict-looking Proof is inventoried.
audit:
	$(PYTHON) scripts/check_agda_imports.py

# Focused checked surface for completed higher-order DGG proof roots that do
# not yet have canonical Lemma consumers.
dgg-check: audit
	$(AGDA) $(DGG_STRICT_AGGREGATE)

# Per-definition time report; pick the target with FILE=...
profile:
	$(AGDA) --profile=definitions $(FILE)

profile-modules:
	$(AGDA) --profile=modules $(FILE)

clean:
	find . -name '*~' -delete

.PHONY: check agda audit dgg-check profile profile-modules clean
