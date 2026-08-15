.PHONY: check agda postulate-check clean

AGDA ?= agda

check: agda postulate-check

# TODO: switch to `$(AGDA) --safe -v0 All.agda` once the legacy
# NON_COVERING pragmas are removed (--safe rejects NON_COVERING;
# verified empirically 2026-08-15). Until then the postulate-check
# below enforces the same pragma bans plus per-file legacy baselines.
agda:
	$(AGDA) -v0 All.agda

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
	@test "$$(grep -c NON_COVERING proof/DGG/Inversion/SourceStripWorkerProof.agda)" -le 22 \
	|| { echo "postulate-check: FAILED (NON_COVERING count in SourceStripWorkerProof exceeds the legacy baseline of 22)"; exit 1; }
	@test "$$(grep -c NON_COVERING proof/DGG/Inversion/SourceStripColumnView.agda)" -le 1 \
	|| { echo "postulate-check: FAILED (NON_COVERING count in SourceStripColumnView exceeds the legacy baseline of 1)"; exit 1; }
	@echo "postulate-check: OK (no postulates; NON_COVERING at legacy baseline)"

clean:
	rm -f *~ *.agdai proof/*.agdai proof/**/*.agdai
