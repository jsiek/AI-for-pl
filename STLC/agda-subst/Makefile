.PHONY: check agda postulate-check clean

AGDA ?= agda
# The kit library lives in the top-level `Subst/` directory.
INCLUDES = -i . -i ../..

check: agda postulate-check

# todo: --disallow-unsound-meta
agda:
	$(AGDA) --safe -v0 $(INCLUDES) All.agda

postulate-check:
	! grep -n "postulate" *.agda proof/*.agda ../../Subst/*.agda ../../Subst/proof/*.agda

clean:
	rm -f *~ *.agdai proof/*.agdai
