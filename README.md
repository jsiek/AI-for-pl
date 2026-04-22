# AI-for-pl

Experiments in using AI (GPT-5.3-Codex) to do PL metatheory in Agda and Lean.

STLC - Simply Typed Lambda Calculus

STLCRef - Simply Typed Lambda Calculus with mutable references

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

PolyBlameI - A failed attempt at a polymorphic cast calculus that uses
imprecision. This design is not type safe because type substitution does not
preserve imprecision typing.

Local bibliography note: `/Users/jsiek/bib/all.bib` is a large catalogue of PL
papers that we use as a reference source when porting examples and designs into
the Agda developments.


