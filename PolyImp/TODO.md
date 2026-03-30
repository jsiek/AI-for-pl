This is a list of relatively low priority tasks that need to be
implemented, ordered by importance. Mark the task with an "x" inside
the brackets when the task is complete and checked (see below), 
then move it to the bottom of the file.

## TODO items

[ ] Change the name of the imprecision constructor ν_ to νᵖ_.

## Agda check

Run:
- `for f in PolyImp/*.agda; do agda -i PolyImp "$f"; done`

Result:
- All files in `PolyImp/*.agda` typecheck.


## Postponed TODO items

[ ] Check whether some of the up/down Value constructors are easy to unify
  by parameterizing over the direction, similar to the reduction rules.
  If you find some that are easy to unify, go ahead and refactor them.
  Note: A direct merge of constructors like `V-at-up/down-↦` into a single
  direction-indexed constructor caused dependent pattern-matching failures in
  `canonical-⇒`/`canonical-∀` (`Progress.agda`), because Agda could not solve
  the index unification for `Value V` when the direction remained abstract.
  Revisit only if we also restructure eliminators/views (or add helper
  lemmas) so those indices become explicit at match time.

## Completed TODO items

[x] Remove extra parantheses around brackets, for example, changing
   (〔 (p ↦ q) 〕)
   to
   〔 p ↦ q 〕

[x] The reduction rules (e.g. β-at-∀, β-at-↦) are getting verbose
  because of multiple uses of transport lemmas like cast⊢ and
  id-step-term.  Can you find a way to make these rules more concise
  perhaps by refactoring to make fewer applications of transport
  lemmas?

[x] Change the constructor 
    M ·α α [ eq ] 
    to 
    M • α [ eq ] 

