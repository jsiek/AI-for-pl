# paper/ — the strong-rep-nu paper, for PLDI 2027

* `draft.md` — the content plan: the design decisions in narrative
  order, with examples and related work.
* `main.tex` — the LaTeX paper, set up for PLDI (below).  Build with
  `make` (needs `latexmk`).
* `references.bib` — its bibliography (empty so far).
* `acmart.cls`, `ACM-Reference-Format.bst` — the ACM class and
  bibliography style `main.tex` uses, kept next to it so no TeX
  installation of `acmart` is needed.
* `acmart-v2.20/` — the unmodified ACM sources and the sample:
  `acmart.dtx`, `acmart.ins`, `samples.dtx`, `samples.ins`,
  `README-acmart` (ACM's README), `acmguide.pdf` (the user guide),
  `acmsmall-conf.tex` with its `sample-base.bib`, `sampleteaser.pdf`,
  `sample-franklin.png`, and ACM's rendering `acmsmall-conf.pdf`.

## PLDI requirements

The PLDI 2027 call for papers was not posted yet (2026-09-25); its page
gives only the deadline, **Thursday, November 12, 2026 (AoE)**, and the
double-blind rules.  The format is expected to be PLDI 2026's, quoted
from <https://pldi26.sigplan.org/track/pldi-2026-papers>:

* "Each paper should have no more than 20 pages of text, excluding
  bibliography, using the ACM Proceedings format … a single-column page
  layout with a 10 pt font, 12 pt line spacing".
* "Authors using LaTeX should use the sample-acmsmall-conf.tex file
  (found in the samples folder of the acmart package) with the acmsmall
  option.  We also strongly encourage use of the review and screen
  options as well, e.g.:
  `\documentclass[acmsmall,screen,review,anonymous,nonacm]{acmart}`".
  (acmart v2.20 names that sample `acmsmall-conf.tex`.)
* "Author names and affiliations must be omitted from submissions.  If a
  submission refers to prior work done by the authors, that reference
  should be made in third person."

Re-check against the PLDI 2027 call once it is published.

## Where the files came from

acmart **v2.20 (2026/08/16)**, from CTAN
(<https://mirrors.ctan.org/macros/latex/contrib/acmart.zip>).  CTAN ships
only the sources, and no TeX was available in the container, so
`acmart.cls` and `acmsmall-conf.tex` were generated from them with
`scripts/docstrip.py`, a small reimplementation of LaTeX's docstrip:

    python3 scripts/docstrip.py acmart.dtx class acmart.cls
    python3 scripts/docstrip.py samples.dtx all,proceedings,acmsmall,conf acmsmall-conf.tex

(the options are the ones in `acmart.ins` and `samples.ins`).  The
script was validated byte for byte against docstrip's own output:
`acmart.cls` at v1.60 and v2.16, and `sample-acmsmall-conf.tex` at
v2.16, each generated from the matching tag of
<https://github.com/borisveytsman/acmart> and compared with committed
copies in public repositories.  If a TeX installation is at hand,
`latex acmart.ins` in `acmart-v2.20/` regenerates the class the usual
way.

**Confirmed against ACM's own build (2026-09-25).**  ACM's template zip
(`acmart-primary.zip`, from
<https://portalparts.acm.org/hippo/latex_templates/acmart-primary.zip>,
behind a Cloudflare check, so downloaded by hand) is the same release,
v2.20 (2026/08/16), with the class and samples pre-generated.  Every file
used here is byte-identical to its copy there: `acmart.cls`,
`ACM-Reference-Format.bst`, `acmart.dtx`, `acmart.ins`, `samples.dtx`,
`samples.ins`, `acmsmall-conf.tex`, `sample-base.bib`, `sampleteaser.pdf`,
`sample-franklin.png`.  Only the two prebuilt PDFs (separate builds) and
one maintainer line of ACM's README differ.  The generated class may be distributed only together with its
sources (see its header), which is why `acmart-v2.20/` is kept here.
