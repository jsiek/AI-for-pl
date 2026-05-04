PolyConvert is an extrinsic Agda development for a polymorphic gradual
calculus with the same type grammar as PolyUpDown.

The current `extrinsic-inst` slice defines:

- copied, independent type/context/store infrastructure;
- type imprecision for `⇑` and `⇓` term constructors;
- store-indexed conversions for `↑` and `↓` term constructors;
- the term grammar, values, typing judgment, and reduction relation;
- canonical forms and progress, with proof details in `proof/`.

The development intentionally does not import or share `UpDown.agda`.
