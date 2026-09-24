AGDA ?= agda

.PHONY: check agda postulate-check clean

check: agda postulate-check

# Type-check the whole development via the aggregate driver.
agda:
	$(AGDA) --safe -v0 All.agda

# Hygiene: no postulates, holes, or unsafe pragmas in live code.
postulate-check:
	@! grep -rnE 'postulate|\{!|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK' \
		--include='*.agda' . \
		| grep -v '^[^:]*:[0-9]*: *--' \
		| grep . \
	|| { echo "postulate-check: FAILED (see matches above)"; exit 1; }
	@echo "postulate-check: OK (no postulates or holes)"

clean:
	rm -f *~ *.agdai
