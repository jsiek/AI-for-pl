# papers/ — PDFs of related work

One flat directory for every paper PDF the repo uses.  File names are
`firstauthorYEAR-short-title.pdf`, so `ls papers/` sorts by author and
`papers/*gradual*` finds by topic.  Add new papers here, named the same
way, and give each a row below.

**License** says what the PDF itself states.  "ACM ©" means a publisher
PDF with ACM's personal/classroom-use notice; the repo is public, so
those are the ones to prune if hosting them is a concern.

| file | citation | license | used by |
|---|---|---|---|
| `ahmed2011-blame-for-all.pdf` | Amal Ahmed, Robert Bruce Findler, Jeremy G. Siek, Philip Wadler. *Blame for All.* POPL 2011. | ACM © | `SystemF/agda/strong-rep-nu/paper/draft.md`; formerly `GTSFImp/alt/` |
| `ahmed2017-theorems-for-free-for-free.pdf` | Amal Ahmed, Dustin Jamner, Jeremy G. Siek, Philip Wadler. *Theorems for Free for Free: Parametricity, With and Without Types.* ICFP 2017 (PACMPL 1). | CC-BY | `strong-rep-nu/paper/draft.md` (λB) |
| `grossman2000-syntactic-type-abstraction.pdf` | Dan Grossman, Greg Morrisett, Steve Zdancewic. *Syntactic Type Abstraction.* TOPLAS 22(6), 2000, pp. 1037–1080.  Printed page = PDF page + 1036. | ACM © | `SystemF/agda/strong*/notes/TypeAbstractionComparison.md`, `SyntacticTypeAbstraction.md`; `paper/draft.md` (STA) |
| `igarashi2017-on-polymorphic-gradual-typing.pdf` | Yuu Igarashi, Taro Sekiyama, Atsushi Igarashi. *On Polymorphic Gradual Typing.* ICFP 2017 (PACMPL 1). | CC-BY | `paper/draft.md` (F_C) |
| `igarashi2024-space-efficient-polymorphic-gradual-typing.pdf` | Atsushi Igarashi, Shota Ozaki, Taro Sekiyama, Yudai Tanabe. *Space-Efficient Polymorphic Gradual Typing, Mostly Parametric.* PLDI 2024 (PACMPL 8). | CC-BY 4.0 | `paper/draft.md` (λC∀mp / λS∀mp) |
| `labrada2022-gradual-system-f.pdf` | Elizabeth Labrada, Matías Toro, Éric Tanter. *Gradual System F.* JACM 69(5), 2022; arXiv:1807.04596 (the file is the arXiv version). | arXiv | `paper/draft.md` (GSF) |
| `labrada2022-plausible-sealing-gradual-parametricity.pdf` | Elizabeth Labrada, Matías Toro, Éric Tanter, Dominique Devriese. *Plausible Sealing for Gradual Parametricity.* OOPSLA 2022 (PACMPL 6). | CC-BY 4.0 | `strong-rep-nu/paper/draft.md` (related work) |
| `matthews2008-parametric-polymorphism-runtime-sealing.pdf` | Jacob Matthews, Amal Ahmed. *Parametric Polymorphism through Run-Time Sealing, or, Theorems for Low, Low Prices!* ESOP 2008, LNCS 4960. | author's copy | `strong-rep-nu/paper/draft.md` (multi-language boundaries with seals) |
| `neis2011-non-parametric-parametricity.pdf` | Georg Neis, Derek Dreyer, Andreas Rossberg. *Non-Parametric Parametricity.* JFP 21(4–5), 2011 (journal version of ICFP 2009); the file is the authors' preprint. | author's copy | `strong-rep-nu/paper/draft.md` (`new`, global σ) |
| `new2020-graduality-and-parametricity.pdf` | Max S. New, Dustin Jamner, Amal Ahmed. *Graduality and Parametricity: Together Again for the First Time.* POPL 2020 (PACMPL 4). | ACM © | `paper/draft.md` (PolyGν); formerly `PolyG/PolyG.pdf` (`PolyG/PolyG.txt` is its text) |
| `new2020-thesis-semantic-foundation-sound-gradual-typing.pdf` | Max S. New. *A Semantic Foundation for Sound Gradual Typing.* PhD thesis, Northeastern University, 2020.  Ch. 10 = PolyGν / PolyCν. | author's copy | `paper/draft.md` (Decision 9, the ν form) |
| `ozaki2021-is-space-efficient-polymorphic-gradual-typing-possible.pdf` | Shota Ozaki, Taro Sekiyama, Atsushi Igarashi. *Is Space-Efficient Polymorphic Gradual Typing Possible?* Scheme and Functional Programming Workshop 2021. | author's copy | `strong-rep-nu/paper/draft.md` (Decision 11, seal chains) |
| `rossberg2003-generativity-dynamic-opacity.pdf` | Andreas Rossberg. *Generativity and Dynamic Opacity for Abstract Types.* PPDP 2003. | ACM © | `paper/draft.md` (λN); formerly `GTSFImp/alt/` |
| `siek2015-refined-criteria-gradual-typing.pdf` | Jeremy G. Siek, Michael M. Vitousek, Matteo Cimini, John Tang Boyland. *Refined Criteria for Gradual Typing.* SNAPL 2015. | CC-BY | formerly `GTLC/` |
| `siek2021-parameterized-cast-calculi.pdf` | Jeremy G. Siek, Tianyu Chen. *Parameterized Cast Calculi and Reusable Meta-theory for Gradually Typed Lambda Calculi.* JFP 31, e30, 2021. | CC-BY 4.0 | `SystemF/agda/strong*/notes/ParameterizedCastCalculi.md` |
| `toro2019-gradual-parametricity-revisited.pdf` | Matías Toro, Elizabeth Labrada, Éric Tanter. *Gradual Parametricity, Revisited.* POPL 2019 (PACMPL 3). | author-held © (ACM notice) | `strong-rep-nu/paper/draft.md` (related work) |
| `zdancewic1999-principals-in-programming-languages.pdf` | Steve Zdancewic, Dan Grossman, Greg Morrisett. *Principals in Programming Languages: A Syntactic Proof Technique.* ICFP 1999, pp. 197–207. | ACM © | `SystemF/agda/strong*/notes/Zdancewic-embeddings.md`, `TypeAbstractionComparison.md` |

## Text extractions: `papers/text/`

`papers/text/<same-name>.txt` is the text layer of each PDF, extracted
with `pypdf` (no poppler in the container), with `=== PAGE n ===`
markers at PDF page boundaries.  Grep these first; open the PDF only to
confirm a formula.  Known defects:

- Displayed math loses subscripts, superscripts and layout everywhere;
  treat rule transcriptions as a pointer into the PDF, not a source.
- `rossberg2003-…` runs words together ("Thestandardformalism…").
- `matthews2008-…` is garbled by a font-encoding problem (e.g.
  "run6time sealing or5 Theorems for low5 low pricest"); use the PDF.
- `grossman2000-…` has no ToUnicode maps, so some math glyphs are
  missing (see `SystemF/agda/strong*/notes/TypeAbstractionComparison.md`
  §12).
- PDF page ≠ printed page for journal papers (STA: printed = PDF + 1036).

To regenerate after adding a PDF: fetch the `pypdf` wheel from PyPI into
a scratch directory, unzip it, and run
`PYTHONPATH=<dir> python3 -c "from pypdf import PdfReader; …"` over the
file, writing one `=== PAGE n ===` block per page.

## Wanted, not yet here

Nothing at the moment.  Add a line here for a paper a note cites but the
directory does not have.
