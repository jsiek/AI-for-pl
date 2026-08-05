module SmallStepInterface.InterpreterTermShapeProperties where

-- File Charter:
--   * Extracts each endpoint's compiler-image certificate from a synchronized
--     interpreter term shape.
--   * Provides the dependency-neutral endpoint facts needed by compiler
--     monotonicity.
--   * Contains no evaluation, interpreter world, or reduction result.

open import SmallStepInterface.InterpreterTermShape

shape-source-interpreter-term :
  ∀ {N N′} →
  InterpreterTermShape N N′ →
  InterpreterTerm N
shape-source-interpreter-term (variable-shape x) =
  variable-term x
shape-source-interpreter-term (closure-shape N~N′) =
  closure-term (shape-source-interpreter-term N~N′)
shape-source-interpreter-term (application-shape L~L′ M~M′) =
  application-term
    (shape-source-interpreter-term L~L′)
    (shape-source-interpreter-term M~M′)
shape-source-interpreter-term
    (paired-type-abstraction-shape vV vV′ V-ok V′-ok) =
  type-abstraction-term vV V-ok
shape-source-interpreter-term
    (left-type-abstraction-shape vV V-ok N′-ok) =
  type-abstraction-term vV V-ok
shape-source-interpreter-term
    (paired-instantiation-shape L~L′) =
  instantiation-term (shape-source-interpreter-term L~L′)
shape-source-interpreter-term
    (left-instantiation-shape L~L′) =
  instantiation-term (shape-source-interpreter-term L~L′)
shape-source-interpreter-term (constant-shape κ) =
  constant-term κ
shape-source-interpreter-term
    (primitive-shape op L~L′ M~M′) =
  primitive-term op
    (shape-source-interpreter-term L~L′)
    (shape-source-interpreter-term M~M′)
shape-source-interpreter-term
    (paired-coercion-application-shape M~M′) =
  coercion-application-term
    (shape-source-interpreter-term M~M′)
shape-source-interpreter-term
    (left-coercion-application-shape M~M′) =
  coercion-application-term
    (shape-source-interpreter-term M~M′)
shape-source-interpreter-term
    (right-coercion-application-shape M~M′) =
  shape-source-interpreter-term M~M′

shape-target-interpreter-term :
  ∀ {N N′} →
  InterpreterTermShape N N′ →
  InterpreterTerm N′
shape-target-interpreter-term (variable-shape x) =
  variable-term x
shape-target-interpreter-term (closure-shape N~N′) =
  closure-term (shape-target-interpreter-term N~N′)
shape-target-interpreter-term (application-shape L~L′ M~M′) =
  application-term
    (shape-target-interpreter-term L~L′)
    (shape-target-interpreter-term M~M′)
shape-target-interpreter-term
    (paired-type-abstraction-shape vV vV′ V-ok V′-ok) =
  type-abstraction-term vV′ V′-ok
shape-target-interpreter-term
    (left-type-abstraction-shape vV V-ok N′-ok) =
  N′-ok
shape-target-interpreter-term
    (paired-instantiation-shape L~L′) =
  instantiation-term (shape-target-interpreter-term L~L′)
shape-target-interpreter-term
    (left-instantiation-shape L~L′) =
  shape-target-interpreter-term L~L′
shape-target-interpreter-term (constant-shape κ) =
  constant-term κ
shape-target-interpreter-term
    (primitive-shape op L~L′ M~M′) =
  primitive-term op
    (shape-target-interpreter-term L~L′)
    (shape-target-interpreter-term M~M′)
shape-target-interpreter-term
    (paired-coercion-application-shape M~M′) =
  coercion-application-term
    (shape-target-interpreter-term M~M′)
shape-target-interpreter-term
    (left-coercion-application-shape M~M′) =
  shape-target-interpreter-term M~M′
shape-target-interpreter-term
    (right-coercion-application-shape M~M′) =
  coercion-application-term
    (shape-target-interpreter-term M~M′)
