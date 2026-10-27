# AI-for-pl

Experiments in using AI (GPT-5.3-Codex) to do PL metatheory in Agda and Lean.

STLC - Simply Typed Lambda Calculus

STLCRef - Simply Typed Lambda Calculus with mutable references

STLCRec - Simply Typed Lambda Calculus with recursive functions.
  This includes a proof of type safety via logical relations,
  adapted to de Bruijn variable representation
  from a proof by Peter Thiemann about this calculus but with names.

STLCSub - Simply Typed Lambda Calculus with records and subtyping.

lambda - Untyped lambda calculus

GTLC - Gradually Typed Lambda Calculus

System F - Polymorphic Lambda Calculus with proofs of type safety and parametricity.

GTSF - Gradually Typed System F

PolyCast - A polymorphic cast calculus that uses coercions to express
casts between types. Coercions can cast to and from universal types,
that is, generalization and instantiation.

PolyUpDown - A polymorphic cast calculus that splits imprecision into two
relations, widening and narrowing, and uses them to express casts between types.
The Agda development proves PolyUpDown type safe.

PolyImp - A polymorphic cast calculus that uses imprecision to express
casts between types. Imprecision allows casts to and from universal
types, that is, generalization and instantiation. The Agda development
proves PolyImp type safe.

PolyConvert - Similar to PolyImp, but splits out the "conversion" aspect
into a separate relation.

PolyG - PolyGν, the gradually typed language with polymorphism and dynamic
sealing from Max New's PhD thesis (Ch. 10), and its cast calculus PolyCν,
restricted to the ∀ν fragment (no pairs or existentials). Instantiation
`let x = M {X ≅ B}; N` creates a fresh seal. The Agda development
(`PolyG/agda`) proves:
* type safety and determinism of PolyCν;
* that elaboration from PolyGν to PolyCν preserves typing and term
  precision;
* the dynamic gradual guarantee (graduality) for PolyGν, by a
  denotational method.

The proof uses a graph model with a seal counter and consistency.
Its relations use Kripke worlds, as in New, Jamner, and Ahmed's
logical relation, and relate finite lists of elements jointly.
The design is in `PolyG/notes/denotational-graduality.md`.
An earlier port of the POPL 2020 paper's version is in `PolyG/popl2020`.

PolyBlameI - A failed attempt at a polymorphic cast calculus that uses
imprecision. This design is not type safe because type substitution does not
preserve imprecision typing.

Local bibliography note: `/Users/jsiek/bib/all.bib` is a large catalogue of PL
papers that we use as a reference source when porting examples and designs into
the Agda developments.

Development workflow: GTSF proof workers on `ginger.luddy.indiana.edu` should
use the repository-local wrapper and library configuration documented in
[`scripts/GINGER_AGDA.md`](scripts/GINGER_AGDA.md).

