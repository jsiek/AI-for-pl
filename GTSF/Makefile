# GTSF build. The RTS flags matter: these files are GC-bound, and a
# larger allocation area with a generous heap cap cuts checking time
# substantially.
AGDA = agda +RTS -A128M -M18G -RTS -v0
STRICT_AGDA = agda --no-allow-unsolved-metas -v0
PYTHON ?= python3
DGG_STRICT_AGGREGATE = \
	proof/DGG/Core/NuDGGUnassembledProofsStrictSpine.agda
REDUCTION_CLOSED_QUOTIENT_EXAMPLES = \
	proof/Quotient/NuImprecisionReductionClosedQuotientExamples.agda
CAMBRIDGE26_EXAMPLE14_EXPERIMENT = \
	proof/Quotient/NuImprecisionCambridge26Example14Experiment.agda
COMPILE_CANONICAL_PENDING_CLOSE_EXPERIMENT = \
	proof/Compilation/CompileCanonicalPendingCloseExperiment.agda
COMPILE_CANONICAL_DOWN_COMPATIBILITY_EXPERIMENT = \
	proof/Compilation/CompileCanonicalDownCompatibilityExperiment.agda
QUOTIENT_PROOF_DIR = proof/Quotient/
REDUCTION_CLOSED_QUOTIENT_METATHEORY_MODULES = \
	NuImprecisionReductionClosedQuotientTypingExperiment.agda \
	NuImprecisionReductionClosedQuotientValueExperiment.agda \
	NuImprecisionReductionClosedQuotientTermContextShiftExperiment.agda \
	NuImprecisionReductionClosedQuotientSubstitutionExperiment.agda \
	NuImprecisionReductionClosedQuotientSingleSubstitutionExperiment.agda
REDUCTION_CLOSED_QUOTIENT_METATHEORY = \
	$(addprefix $(QUOTIENT_PROOF_DIR), \
	  $(REDUCTION_CLOSED_QUOTIENT_METATHEORY_MODULES))
REDUCTION_CLOSED_QUOTIENT_WORLD_MODULES = \
	NuImprecisionQuotientCompatibilityRename.agda \
	NuImprecisionReductionClosedWorldEmbeddingExperiment.agda \
	NuImprecisionReductionClosedWorldRenameExperiment.agda \
	NuImprecisionEmbeddedTargetInstantiationCreationProperties.agda
REDUCTION_CLOSED_QUOTIENT_WORLD = \
	$(addprefix $(QUOTIENT_PROOF_DIR), \
	  $(REDUCTION_CLOSED_QUOTIENT_WORLD_MODULES))
REDUCTION_CLOSED_QUOTIENT_AUDIT_MODULES = \
	NuImprecisionReductionClosedQuotientIdOnlyCastAudit.agda \
	NuImprecisionReductionClosedQuotientTransientAudit.agda
REDUCTION_CLOSED_QUOTIENT_AUDITS = \
	$(addprefix $(QUOTIENT_PROOF_DIR), \
	  $(REDUCTION_CLOSED_QUOTIENT_AUDIT_MODULES))
TARGET_INSTANTIATION_MIGRATION_MODULES = \
	NuImprecisionTargetInstantiationConsumerMigrationExperiment.agda \
	NuImprecisionTargetInstantiationFramedConsumerMigrationExperiment.agda \
	NuImprecisionTargetInstantiationSimulationExperiment.agda
TARGET_INSTANTIATION_MIGRATIONS = \
	$(addprefix $(QUOTIENT_PROOF_DIR), \
	  $(TARGET_INSTANTIATION_MIGRATION_MODULES))
TARGET_INSTANTIATION_CREATION_EXAMPLES = \
	proof/Quotient/NuImprecisionTargetInstantiationCreationExamples.agda
TARGET_INSTANTIATION_TRANSPORT_EXPERIMENT = \
	proof/Quotient/NuImprecisionTargetInstantiationTransportExperiment.agda
TARGET_INSTANTIATION_TRANSPORT_TERMINAL_EXPERIMENT = \
	proof/Quotient/NuImprecisionTargetInstantiationTransportTerminalExperiment.agda
TARGET_INSTANTIATION_TRANSPORT_SPINE_EXPERIMENT = \
	proof/Quotient/NuImprecisionTargetInstantiationTransportSpineExperiment.agda

define strict-check-each
	@for module in $(1); do \
		$(STRICT_AGDA) $$module || exit $$?; \
	done
endef

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

# Check the selected smaller relation and its migration evidence at a phase
# gate. Use focused module checks while a phase is active.
qti-migration-check: audit
	$(STRICT_AGDA) $(REDUCTION_CLOSED_QUOTIENT_EXAMPLES)
	$(STRICT_AGDA) $(CAMBRIDGE26_EXAMPLE14_EXPERIMENT)
	$(STRICT_AGDA) $(COMPILE_CANONICAL_PENDING_CLOSE_EXPERIMENT)
	$(STRICT_AGDA) $(COMPILE_CANONICAL_DOWN_COMPATIBILITY_EXPERIMENT)
	$(call strict-check-each,$(REDUCTION_CLOSED_QUOTIENT_METATHEORY))
	$(call strict-check-each,$(REDUCTION_CLOSED_QUOTIENT_WORLD))
	$(call strict-check-each,$(REDUCTION_CLOSED_QUOTIENT_AUDITS))
	$(call strict-check-each,$(TARGET_INSTANTIATION_MIGRATIONS))
	$(STRICT_AGDA) $(TARGET_INSTANTIATION_CREATION_EXAMPLES)
	$(STRICT_AGDA) $(TARGET_INSTANTIATION_TRANSPORT_EXPERIMENT)
	$(STRICT_AGDA) $(TARGET_INSTANTIATION_TRANSPORT_TERMINAL_EXPERIMENT)
	$(STRICT_AGDA) $(TARGET_INSTANTIATION_TRANSPORT_SPINE_EXPERIMENT)

# Per-definition time report; pick the target with FILE=...
profile:
	$(AGDA) --profile=definitions $(FILE)

profile-modules:
	$(AGDA) --profile=modules $(FILE)

clean:
	find . -name '*~' -delete

.PHONY: check agda audit dgg-check qti-migration-check profile \
	profile-modules clean
