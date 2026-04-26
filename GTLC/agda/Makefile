.PHONY: check agda postulate-check clean

AGDA ?= agda

check: agda postulate-check

agda:
	$(AGDA) -v0 All.agda

postulate-check:
	@! rg -n "postulate|\{!!\}" *.agda proof/*.agda

clean:
	find . -type f \( -name '*~' -o -name '*.agdai' \) -delete
