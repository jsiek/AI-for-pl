.PHONY: check agda in-progress-proof-check postulate-check clean

AGDA ?= agda

# These modules are direct, intentionally partial proofs.  A meta means that a
# local case is still on the to-do list.  Separate parameters remain reserved
# for semantically named lemmas needing their own induction or compilation
# boundary; they must not stand in for unfinished cases.  Manifested files are
# excluded from All.agda and checked through Agda's interaction mode.
# Remove a file from this list and add it to All.agda as soon as its metas close.
IN_PROGRESS_PROOFS := proof/DGG/SimPairedAllValuesProof.agda \
	proof/DGG/SimTargetRevealRebaseClosingProof.agda \
	proof/DGG/ContextualSimProof.agda \
	proof/DGG/Catchup/MorePreciseTargetCastInstantiationCatchupProof.agda

check: agda in-progress-proof-check postulate-check

agda:
	$(AGDA) --safe --no-caching -v0 All.agda

# Interaction mode accepts explicit goals without infecting safe imports with
# --allow-unsolved-metas.  It still rejects type errors and incomplete pattern
# matching, and reports every outstanding goal.  An empty goal list means that
# the file is ready to leave IN_PROGRESS_PROOFS, so the gate fails until the
# manifest and All.agda are updated together.
in-progress-proof-check:
	@set -e; \
	for file in $(IN_PROGRESS_PROOFS); do \
		echo "in-progress-proof-check: $$file"; \
		path="$(CURDIR)/$$file"; \
		command="IOTCM \"$$path\" None Direct (Cmd_load \"$$path\" [])"; \
		if ! output="$$(printf '%s\n' "$$command" \
			| $(AGDA) --safe --interaction \
				--interaction-exit-on-error 2>&1)"; then \
			printf '%s\n' "$$output"; \
			echo "in-progress-proof-check: FAILED: $$file"; \
			exit 1; \
		fi; \
		goal_line="$$(printf '%s\n' "$$output" \
			| grep -F "agda2-goals-action '" | tail -n 1 || true)"; \
		if test -z "$$goal_line"; then \
			printf '%s\n' "$$output"; \
			echo "in-progress-proof-check: FAILED: no goal report for $$file"; \
			exit 1; \
		fi; \
		if printf '%s\n' "$$goal_line" \
			| grep -Fq "agda2-goals-action '()"; then \
			echo "in-progress-proof-check: READY: $$file"; \
			echo "remove it from IN_PROGRESS_PROOFS and add it to All.agda"; \
			exit 1; \
		fi; \
		goal_ids="$$(printf '%s\n' "$$goal_line" \
			| sed -n "s/.*agda2-goals-action '(\([^)]*\)).*/\1/p")"; \
		goal_count="$$(printf '%s\n' "$$goal_ids" | awk '{ print NF }')"; \
		echo "in-progress-proof-check: PENDING: $$file ($$goal_count goals)"; \
	done
	@echo "in-progress-proof-check: OK (listed files remain explicitly partial)"

# Hygiene: only files in IN_PROGRESS_PROOFS may contain interaction holes.
# Postulates and proof-bypassing pragmas remain forbidden in all live code;
# notes/ and experimental/ hold scratch work and negative records.
postulate-check:
	@! grep -rnE 'postulate|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK' \
		--include='*.agda' . \
		| grep -v '/notes/' \
		| grep -v '/experimental/' \
		| grep -v '^[^:]*:[0-9]*: *--' \
		| grep . \
	|| { echo "postulate-check: FAILED (unsafe proof escape above)"; exit 1; }
	@matches="$$(grep -rnE '\{!' --include='*.agda' . \
		| grep -v '/notes/' \
		| grep -v '/experimental/' \
		| grep -v '^[^:]*:[0-9]*: *--' || true)"; \
	for file in $(IN_PROGRESS_PROOFS); do \
		matches="$$(printf '%s\n' "$$matches" \
			| grep -v -F "./$$file:" || true)"; \
	done; \
	if test -n "$$matches"; then \
		printf '%s\n' "$$matches"; \
		echo "postulate-check: FAILED (hole outside IN_PROGRESS_PROOFS)"; \
		exit 1; \
	fi
	@! grep -rn 'NON_COVERING' --include='*.agda' . \
		| grep -v '/notes/' \
		| grep -v '/experimental/' \
		| grep . \
	|| { echo "postulate-check: FAILED (NON_COVERING in live code)"; exit 1; }
	@echo "postulate-check: OK (only manifested proof holes are allowed)"

clean:
	rm -f *~ *.agdai proof/*.agdai proof/**/*.agdai
