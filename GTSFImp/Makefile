.PHONY: check agda postulate-check clean

AGDA ?= agda

check: agda postulate-check

# No --safe: FunExt.agda carries the one sanctioned postulate.
agda:
	$(AGDA) -v0 All.agda

# Hygiene: FunExt.agda is the only sanctioned postulate. Holes and
# termination pragmas are never allowed in live code; notes/ and
# experimental/ hold scratch work and negative records.
postulate-check:
	@! grep -rnE 'postulate|\{!|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK' \
		--include='*.agda' . \
		| grep -v '/notes/' \
		| grep -v '/experimental/' \
		| grep -v '^\./FunExt.agda' \
		| grep -v '^[^:]*:[0-9]*: *--' \
		| grep . \
	|| { echo "postulate-check: FAILED (see matches above)"; exit 1; }
	@echo "postulate-check: OK (FunExt-only)"

clean:
	rm -f *~ *.agdai proof/*.agdai proof/**/*.agdai
