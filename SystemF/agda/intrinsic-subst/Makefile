.PHONY: check agda postulate-check clean

AGDA ?= agda

check: agda postulate-check

# Module names are relative to SystemF/agda (systemf-agda.agda-lib); the kit
# library lives in the top-level `Subst/` directory.
agda:
	cd .. && $(AGDA) --safe -v0 -i . -i ../.. intrinsic-subst/All.agda

postulate-check:
	! grep -n -e "postulate" -e "{!" *.agda proof/*.agda \
	  ../../../Subst/*.agda ../../../Subst/proof/*.agda

clean:
	rm -f *~ *.agdai proof/*.agdai
