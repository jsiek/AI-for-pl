module InterpreterAdequacy.proof.InterpreterTermNoBullet where

-- File Charter:
--   * Proves that every direct-interpreter source term excludes the
--     small-step-only runtime bullet.
--   * Depends only on the interpreter source grammar and Nu term syntax.
--   * Contains no evaluation, reduction, typing, or adequacy argument.

open import SmallStepInterface.InterpreterTermShape using
  ( InterpreterTerm
  ; variable-term
  ; closure-term
  ; application-term
  ; type-abstraction-term
  ; instantiation-term
  ; constant-term
  ; primitive-term
  ; coercion-application-term
  )
import NuTerms as N

interpreter-term-no-bullet :
  ∀ {M} →
  InterpreterTerm M →
  N.No• M
interpreter-term-no-bullet (variable-term x) =
  N.no•-`
interpreter-term-no-bullet (closure-term M-ok) =
  N.no•-ƛ (interpreter-term-no-bullet M-ok)
interpreter-term-no-bullet (application-term L-ok M-ok) =
  N.no•-·
    (interpreter-term-no-bullet L-ok)
    (interpreter-term-no-bullet M-ok)
interpreter-term-no-bullet (type-abstraction-term vV V-ok) =
  N.no•-Λ (interpreter-term-no-bullet V-ok)
interpreter-term-no-bullet (instantiation-term L-ok) =
  N.no•-ν (interpreter-term-no-bullet L-ok)
interpreter-term-no-bullet (constant-term κ) =
  N.no•-$
interpreter-term-no-bullet (primitive-term op L-ok M-ok) =
  N.no•-⊕
    (interpreter-term-no-bullet L-ok)
    (interpreter-term-no-bullet M-ok)
interpreter-term-no-bullet (coercion-application-term M-ok) =
  N.no•-⟨⟩ (interpreter-term-no-bullet M-ok)
