# GTSF build. The RTS flags matter: these files are GC-bound, and a
# larger allocation area with a generous heap cap cuts checking time
# substantially.
AGDA = agda +RTS -A128M -M18G -RTS -v0
STRICT_AGDA = agda --no-allow-unsolved-metas -v0
PYTHON ?= python3
DGG_STRICT_AGGREGATE = \
	proof/DGG/Core/NuDGGUnassembledProofsStrictSpine.agda
COMPOSITIONAL_QUOTIENT_EXAMPLES = \
	proof/Quotient/NuImprecisionCompositionalQuotientExamples.agda
REDUCTION_CLOSED_QUOTIENT_EXAMPLES = \
	proof/Quotient/NuImprecisionReductionClosedQuotientExamples.agda
SINGLE_NARROWING_BOUNDARY_EXAMPLES = \
	proof/Quotient/NuImprecisionSingleNarrowingBoundaryExamples.agda
TARGET_INSTANTIATION_CREATION_EXAMPLES = \
	proof/Quotient/NuImprecisionTargetInstantiationCreationExamples.agda
TARGET_INSTANTIATION_TRANSPORT_EXPERIMENT = \
	proof/Quotient/NuImprecisionTargetInstantiationTransportExperiment.agda
TARGET_INSTANTIATION_TRANSPORT_SPINE_EXPERIMENT = \
	proof/Quotient/NuImprecisionTargetInstantiationTransportSpineExperiment.agda

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

# Check both quotient-design alternatives and their reduction-shape examples
# before changing the live DGG relation.
quotient-design-check: audit
	$(STRICT_AGDA) $(COMPOSITIONAL_QUOTIENT_EXAMPLES)
	$(STRICT_AGDA) $(REDUCTION_CLOSED_QUOTIENT_EXAMPLES)
	$(STRICT_AGDA) $(SINGLE_NARROWING_BOUNDARY_EXAMPLES)
	$(STRICT_AGDA) $(TARGET_INSTANTIATION_CREATION_EXAMPLES)
	$(STRICT_AGDA) $(TARGET_INSTANTIATION_TRANSPORT_EXPERIMENT)
	$(STRICT_AGDA) $(TARGET_INSTANTIATION_TRANSPORT_SPINE_EXPERIMENT)

# Per-definition time report; pick the target with FILE=...
profile:
	$(AGDA) --profile=definitions $(FILE)

profile-modules:
	$(AGDA) --profile=modules $(FILE)

clean:
	find . -name '*~' -delete

.PHONY: check agda audit dgg-check quotient-design-check profile \
	profile-modules clean
