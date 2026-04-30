AGDA ?= agda

.PHONY: check agda postulate-check clean

check: agda postulate-check

agda:
	$(AGDA) -v0 All.agda

postulate-check:
	@! grep -R "postulate" *.agda proof/*.agda

clean:
	find . -name '*.agdai' -delete
