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
| `new2020-graduality-and-parametricity.pdf` | Max S. New, Dustin Jamner, Amal Ahmed. *Graduality and Parametricity: Together Again for the First Time.* POPL 2020 (PACMPL 4). | ACM © | `paper/draft.md` (PolyGν); formerly `PolyG/PolyG.pdf` (`PolyG/PolyG.txt` is its text) |
| `new2020-thesis-semantic-foundation-sound-gradual-typing.pdf` | Max S. New. *A Semantic Foundation for Sound Gradual Typing.* PhD thesis, Northeastern University, 2020.  Ch. 10 = PolyGν / PolyCν. | author's copy | `paper/draft.md` (Decision 9, the ν form) |
| `rossberg2003-generativity-dynamic-opacity.pdf` | Andreas Rossberg. *Generativity and Dynamic Opacity for Abstract Types.* PPDP 2003. | ACM © | `paper/draft.md` (λN); formerly `GTSFImp/alt/` |
| `siek2015-refined-criteria-gradual-typing.pdf` | Jeremy G. Siek, Michael M. Vitousek, Matteo Cimini, John Tang Boyland. *Refined Criteria for Gradual Typing.* SNAPL 2015. | CC-BY | formerly `GTLC/` |
| `siek2021-parameterized-cast-calculi.pdf` | Jeremy G. Siek, Tianyu Chen. *Parameterized Cast Calculi and Reusable Meta-theory for Gradually Typed Lambda Calculi.* JFP 31, e30, 2021. | CC-BY 4.0 | `SystemF/agda/strong*/notes/ParameterizedCastCalculi.md` |
| `zdancewic1999-principals-in-programming-languages.pdf` | Steve Zdancewic, Dan Grossman, Greg Morrisett. *Principals in Programming Languages: A Syntactic Proof Technique.* ICFP 1999, pp. 197–207. | ACM © | `SystemF/agda/strong*/notes/Zdancewic-embeddings.md`, `TypeAbstractionComparison.md` |

## Wanted, not yet here

Cited or flagged by `SystemF/agda/strong-rep-nu/paper/draft.md`,
"Related work beyond the named papers":

- Matthews & Ahmed, *Parametric Polymorphism through Run-Time Sealing,
  or, Theorems for Low, Low Prices!*, ESOP 2008
  (`ccs.neu.edu/home/amal/papers/parpolyseal.pdf`).
- Neis, Dreyer & Rossberg, *Non-Parametric Parametricity*, ICFP 2009 /
  JFP 2011.
- Ozaki, Sekiyama & Igarashi, *Is Space-Efficient Polymorphic Gradual
  Typing Possible?*, Scheme Workshop 2021 (on Sekiyama's publications
  page).
- Toro, Labrada & Tanter, *Gradual Parametricity, Revisited*, POPL 2019.
- Labrada, Toro, Tanter & Devriese, *Plausible Sealing for Gradual
  Parametricity*, OOPSLA 2022.
