.PHONY: check agda postulate-check clean

AGDA ?= agda

check: agda postulate-check

agda:
	$(AGDA) -v0 All.agda

# Hygiene: postulates, holes, and termination pragmas are never allowed in
# live code; notes/ and experimental/ hold scratch work and negative records.
postulate-check:
	@! grep -rnE 'postulate|\{!|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK' \
		--include='*.agda' . \
		| grep -v '/notes/' \
		| grep -v '/experimental/' \
		| grep -v '^[^:]*:[0-9]*: *--' \
		| grep . \
	|| { echo "postulate-check: FAILED (see matches above)"; exit 1; }
	@echo "postulate-check: OK"

clean:
	rm -f *~ *.agdai proof/*.agdai proof/**/*.agdai
