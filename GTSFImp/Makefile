.PHONY: check agda agda-legacy postulate-check clean

AGDA ?= agda

check: agda agda-legacy postulate-check

agda:
	$(AGDA) --safe -v0 All.agda

agda-legacy:
	$(AGDA) -v0 LegacyAll.agda

# Hygiene: postulates, holes, and termination pragmas are never allowed in
# live code; notes/ and experimental/ hold scratch work and negative records.
postulate-check:
	@! grep -rnE 'postulate|\{!|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK' \
		--include='*.agda' . \
		| grep -v '/notes/' \
		| grep -v '/experimental/' \
		| grep -v '^[^:]*:[0-9]*: *--' \
		| grep . \
	|| { echo "postulate-check: FAILED (see matches above)"; exit 1; }
	@! grep -rn 'NON_COVERING' --include='*.agda' . \
		| grep -v '/notes/' \
		| grep -v '/experimental/' \
		| grep -v 'proof/DGG/Inversion/SourceStripWorkerProof.agda' \
		| grep -v 'proof/DGG/Inversion/SourceStripColumnView.agda' \
		| grep . \
	|| { echo "postulate-check: FAILED (NON_COVERING outside legacy files)"; exit 1; }
	@test "$$(grep -c '{-# NON_COVERING #-}' proof/DGG/Inversion/SourceStripWorkerProof.agda)" -eq 13 \
	|| { echo "postulate-check: FAILED (NON_COVERING pragma count in SourceStripWorkerProof differs from the legacy baseline of 13)"; exit 1; }
	@test "$$(grep -c '{-# NON_COVERING #-}' proof/DGG/Inversion/SourceStripColumnView.agda)" -eq 1 \
	|| { echo "postulate-check: FAILED (NON_COVERING pragma count in SourceStripColumnView differs from the legacy baseline of 1)"; exit 1; }
	@echo "postulate-check: OK (no postulates; NON_COVERING at legacy baseline)"

clean:
	rm -f *~ *.agdai proof/*.agdai proof/**/*.agdai
