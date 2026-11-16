.PHONY: check agda postulate-check clean

AGDA ?= agda

check: agda postulate-check

# Module names are `Subst.*`, so the include root is the repository root.
agda:
	$(AGDA) --safe -v0 -i .. All.agda

postulate-check:
	! grep -n -e "postulate" -e "{!" *.agda proof/*.agda examples/*.agda

clean:
	rm -f *~ *.agdai proof/*.agdai
