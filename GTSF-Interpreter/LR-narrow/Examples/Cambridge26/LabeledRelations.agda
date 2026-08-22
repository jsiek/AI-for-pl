module LR-narrow.Examples.Cambridge26.LabeledRelations where

-- File Charter:
--   * Checks the endpoint types of Cambridge26 examples (e)--(g).
--   * Corrects (g): its displayed left term has dynamic function type, not
--     the universal type printed in the note.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.CanonicalNarrowings
open import LR-narrow.Examples.Cambridge26.Specification
open import TypeCheck using (is-just)

example-e : ClosedExample
example-e =
  checked-example PolyId DynId
    poly-id-to-dynamic
    poly-id-to-dynamic-c
    poly-id-to-dynamic-narrowing
  id id★ is-just is-just

example-f : ClosedExample
example-f =
  checked-example PolyId PolyId
    poly-id-reflexive
    poly-id-reflexive-c
    poly-id-reflexive-narrowing
  id (generalize-id id★) is-just is-just

example-g-corrected : ClosedExample
example-g-corrected =
  checked-example PolyId DynId
    poly-id-to-dynamic
    poly-id-to-dynamic-c
    poly-id-to-dynamic-narrowing
  id (instantiate-id-dynamically (generalize-id id★)) is-just is-just
