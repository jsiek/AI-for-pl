AGDA ?= agda

.PHONY: check agda postulate-check wip dashboard clean

check: agda postulate-check

# Type-check the whole development via the aggregate driver.
agda:
	$(AGDA) --safe -v0 All.agda

# Hygiene: no postulates, holes, or unsafe pragmas in any module that
# All.agda imports.  Skeleton proofs with holes may sit in proof/ as long
# as All.agda does not import them (see `make wip`).
postulate-check:
	@mkdir -p _build
	@$(AGDA) --safe -v0 --dependency-graph=_build/deps.dot All.agda
	@python3 tools/reachable_hygiene.py

# Type-check the DGG skeletons, holes allowed (proof/DGG/*Proof.agda).
wip:
	@python3 proof/DGG/dashboard.py --wip

# Regenerate proof/DGG/DASHBOARD.md from proof/DGG/tree.txt and the files.
dashboard:
	@python3 proof/DGG/dashboard.py

clean:
	rm -f *~ *.agdai
