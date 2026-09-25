# Build the PLDI submission.  Needs a TeX installation with latexmk
# (none is installed in the Codex/Claude containers).
main.pdf: main.tex references.bib acmart.cls ACM-Reference-Format.bst
	latexmk -pdf main.tex

clean:
	latexmk -C main.tex

.PHONY: clean
