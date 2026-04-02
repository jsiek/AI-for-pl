# AI-for-pl

Experiments in using AI (GPT-5.3-Codex) to do PL metatheory

STLC - Simply Typed Lambda Calculus

lambda - Untyped lambda calculus

GTLC - Gradually Typed Lambda Calculus

System F - Polymorphic Lambda Calculus

GTSF - Gradually Typed System F

PolyCast - A polymorphic cast calculus that is intrinsically typed and
uses coercions to express casts between types. Coercions can cast to
and from universal types, that is, generalization and instantiation.

PolyUpDown - A polymorphic cast calculus that splits imprecision into
two relations, widening and narrowing, and uses them to express casts
between types. The Agda development proves PolyUpDown type safe.

PolyImp - A polymorphic cast calculus that is intrinsically typed and
uses imprecision to express casts between types.  Imprecision allows
casts to and from universal types, that is, generalization and
instantiation. The Agda development proves PolyImp type safe.

PolyBlameI - A failed attempt at a polymorphic cast calculus that uses
imprecision. This design is not type safe because type substitution
does not preserve imprecision typing.

Local bibliography note: `/Users/jsiek/bib/all.bib` is a large catalogue
of PL papers that we use as a reference source when porting examples
and designs into the Agda developments.

# Work in Progress



# Design Notes and Informal Proof Notes

## Design notes

When writing design notes for a calculus or translation:

- Match the style of nearby design notes when there is an established local style.
- Prefer named variables and named substitution in expository notes, even when the Agda mechanization uses de Bruijn indices.
- State important relations as explicit definitions, not just by implication from later rules.
  For example, if typing uses consistency, include the full definition of consistency.
- Include important derived rules as theorem statements when they are used pervasively in the exposition.
- When presenting formal relations in prose, prefer the actual formal clauses and side conditions over informal labels such as "atomic case" or "identity-like case".
- Put formal terms, judgments, and propositions in backticks in the prose and headings so they stand out from the surrounding explanation.
- When giving reduction relations in notes, prefer a clean mathematical presentation with the notation used consistently throughout the document.

## Informal proofs

When writing informal proof documents:

- Emphasize reduction sequences and proof shape over long prose explanations.
- Name the lemmas that justify the important reasoning steps.
- Do not call out constructor names or minor helper lemmas in the prose.
- State lemmas and theorem goals in concise formal mathematical prose using `if ... then ...`.
  Avoid inference-bar formatting in informal proof notes.
- If a proof is by cases, use Markdown headings such as `### Case 1. ...` rather than separator lines.
- Make case headings direct and formula-shaped when possible.
  For example, write `Case 1. λx. N ⊑ λx. N'` instead of a descriptive sentence.
- Phrase case headings according to the relation or judgment that the proof is analyzing.
  If the induction is on a derivation of `c ⊑ A' ?ℓ`, the case headings should be instances of that relation.
- When a case naturally breaks into stages, prefer one compact proof sketch or one annotated
  diagram over many tiny fragments, unless the extra splitting is genuinely clarifying.
- Keep the explanatory text short when a diagram already shows the proof structure.
- Prefer "show, don't tell": when a prose sentence informally describes the shape of a witness term or a reduction step, 
  replace it with the explicit term equation and a diagram whenever practical.
- When inversion gives a more specific term shape, state that shape explicitly.
  For example, write facts such as `V = cast W [ G ! ]` and continue the proof with `W`.

## Diagrams

When using ASCII diagrams in informal proofs:

- Use `Diagram:` as the label, not `Picture:`.
- Use diagrams only when reduction is part of the theorem or proof step.
  If a statement does not involve reduction, prefer a textual proof sketch without a diagram.
- Reduction should be vertical.
- Precision should be horizontal.
- Put the less precise term on the left and the more precise term on the right.
- Do not use code fences around diagrams unless there is a strong reason; plain ASCII diagrams are preferred.
  If Markdown rendering requires preservation of alignment, use simple indented code blocks.
- Align vertical arrows carefully with the source and target terms in the chosen monospaced font.
  In particular, make sure the arrow column agrees with both the top and bottom term on that side.
- Diagrams should depict reductions of whole terms, not just reductions of subterms pulled out of context.
  If a lemma is applied to a subterm, keep the surrounding context in the displayed term and say the lemma is used "lifted through" that context.
- Only place a horizontal precision relation on a row when the proof is actually establishing that relation
  at that point.
- If a diagram annotates steps, use the annotations for lemma applications or uses of the induction
  hypothesis, not for obvious reduction-rule names.
- In diagram annotations, cite lemmas directly by name and say what facts they are applied on.
  Treat induction-hypothesis annotations the same way.
- If a term persists unchanged down one side of a diagram, keep the vertical arrow continuous and label the
  corresponding segment with `0` steps.
- If an annotation would collide with the right-hand column, shift the whole right-hand side further right or split the annotation across multiple lines.


# Agda Development Notes

## Use "constructor form indices" for data type constructors (from 2-26-03-30)

In Agda, constructor form indices are indices of an indexed data type
that are expressed using only data constructors (like zero, suc, [],
or _∷_) and variables, rather than defined functions (like addition
_+_ or maximum max). Adhering to this form is crucial because Agda's
built-in unification algorithm has difficulty solving equality
problems involving user-defined functions that do not immediately
reduce to a constructor-based form.

To resolve "cannot unify" or "I'm not sure if there should be a case"
errors caused by complex indices, you should refactor your data types
and proofs.  Avoid Functions in Indices: If a type has a function call
in its index, for example, max n m ≤ u, the unifier will struggle to
match max n m with other terms (e.g., n + k).  Use Equality Proofs
Internally: Instead of an index f(x), use an explicit equality proof
within the data type's definition to relate the function's result to
the expected value. The type could become something like D : A → Set
where a constructor takes an argument of type f x ≡ y.

## Agda `with` style (from 2026-03-24)

For `with` clauses, if there are two or more cases, use explicit
function-name case clauses rather than `...` shorthand. 
This will avoid problems that arise with nested `with` clauses.

## Agda recursive function termination / `with` style (from 2026-03-24)

Agda termination checking can be tripped by helper functions that took
the recursive function as a higher-order argument.

Working fix:

- Inline those helpers instead of passing recursive function as an argument.
- For nested `with` clauses, use explicit function-name case clauses rather than `...` shorthand.
  (Problems with nested `with` clauses may have been the reason for introducing the helper
   in the first place.)

This avoids confusing Agda's termination checker and keeps recursive
functions accepted without `{-# TERMINATING #-}`.
