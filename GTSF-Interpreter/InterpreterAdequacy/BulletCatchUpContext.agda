module InterpreterAdequacy.BulletCatchUpContext where

-- File Charter:
--   * Lifts runtime-bullet catch-up through every call-by-value evaluation
--     context of the Nu semantics.
--   * Retains an explicit source-fragment certificate for the context, so the
--     catch-up endpoint can be fed back to the direct interpreter.
--   * Constructs only `keep` steps and performs no interpreter recursion.

open import Data.List using ([]; _∷_)

open import Coercions using (Coercion)
open import InterpreterAdequacy.BulletCatchUp
open import SmallStepInterface.InterpreterTermShape
open import NuReduction using
  ( keep
  ; shift-keep
  ; ξ-·₁
  ; ξ-·₂
  ; ξ-⟨⟩
  ; ξ-ν
  ; ξ-⊕₁
  ; ξ-⊕₂
  ; ↠-refl
  ; ↠-step
  ; _—→[_]_
  ; _—↠[_]_
  )
import NuTerms as N
open import Primitives using (Prim)
open import Types using (Ty)

data EvaluationContext : Set where
  hole : EvaluationContext

  app-left :
    EvaluationContext →
    N.Term →
    EvaluationContext

  app-right :
    ∀ {V} →
    N.Value V →
    EvaluationContext →
    EvaluationContext

  instantiation :
    Ty →
    EvaluationContext →
    Coercion →
    EvaluationContext

  primitive-left :
    EvaluationContext →
    Prim →
    N.Term →
    EvaluationContext

  primitive-right :
    ∀ {V} →
    N.Value V →
    Prim →
    EvaluationContext →
    EvaluationContext

  coercion-frame :
    EvaluationContext →
    Coercion →
    EvaluationContext

plug : EvaluationContext → N.Term → N.Term
plug hole M = M
plug (app-left E N) M = plug E M N.· N
plug (app-right {V = V} vV E) M = V N.· plug E M
plug (instantiation A E c) M = N.ν A (plug E M) c
plug (primitive-left E op N) M = plug E M N.⊕[ op ] N
plug (primitive-right {V = V} vV op E) M =
  V N.⊕[ op ] plug E M
plug (coercion-frame E c) M = plug E M N.⟨ c ⟩

data InterpreterContext : EvaluationContext → Set where
  interpreter-hole :
    InterpreterContext hole

  interpreter-app-left :
    ∀ {E M} →
    InterpreterContext E →
    InterpreterTerm M →
    InterpreterContext (app-left E M)

  interpreter-app-right :
    ∀ {E V} {vV : N.Value V} →
    InterpreterTerm V →
    InterpreterContext E →
    InterpreterContext (app-right vV E)

  interpreter-instantiation :
    ∀ {A E c} →
    InterpreterContext E →
    InterpreterContext (instantiation A E c)

  interpreter-primitive-left :
    ∀ {E op M} →
    InterpreterContext E →
    InterpreterTerm M →
    InterpreterContext (primitive-left E op M)

  interpreter-primitive-right :
    ∀ {E op V} {vV : N.Value V} →
    InterpreterTerm V →
    InterpreterContext E →
    InterpreterContext (primitive-right vV op E)

  interpreter-coercion-frame :
    ∀ {E c} →
    InterpreterContext E →
    InterpreterContext (coercion-frame E c)

plug-interpreter-term :
  ∀ {E M} →
  InterpreterContext E →
  InterpreterTerm M →
  InterpreterTerm (plug E M)
plug-interpreter-term interpreter-hole M-ok = M-ok
plug-interpreter-term
    (interpreter-app-left E-ok N-ok) M-ok =
  application-term (plug-interpreter-term E-ok M-ok) N-ok
plug-interpreter-term
    (interpreter-app-right V-ok E-ok) M-ok =
  application-term V-ok (plug-interpreter-term E-ok M-ok)
plug-interpreter-term
    (interpreter-instantiation E-ok) M-ok =
  instantiation-term (plug-interpreter-term E-ok M-ok)
plug-interpreter-term
    (interpreter-primitive-left E-ok N-ok) M-ok =
  primitive-term _ (plug-interpreter-term E-ok M-ok) N-ok
plug-interpreter-term
    (interpreter-primitive-right V-ok E-ok) M-ok =
  primitive-term _ V-ok (plug-interpreter-term E-ok M-ok)
plug-interpreter-term
    (interpreter-coercion-frame E-ok) M-ok =
  coercion-application-term (plug-interpreter-term E-ok M-ok)

lift-keep-step :
  ∀ E {M N} →
  M —→[ keep ] N →
  plug E M —→[ keep ] plug E N
lift-keep-step hole M→N = M→N
lift-keep-step (app-left E P) M→N =
  ξ-·₁ (lift-keep-step E M→N) shift-keep
lift-keep-step (app-right vV E) M→N =
  ξ-·₂ vV shift-keep (lift-keep-step E M→N)
lift-keep-step (instantiation A E c) M→N =
  ξ-ν (lift-keep-step E M→N)
lift-keep-step (primitive-left E op P) M→N =
  ξ-⊕₁ (lift-keep-step E M→N) shift-keep
lift-keep-step (primitive-right vV op E) M→N =
  ξ-⊕₂ vV shift-keep (lift-keep-step E M→N)
lift-keep-step (coercion-frame E c) M→N =
  ξ-⟨⟩ (lift-keep-step E M→N)

lift-all-keep-trace :
  ∀ E {M N χs} →
  AllKeep χs →
  M —↠[ χs ] N →
  plug E M —↠[ χs ] plug E N
lift-all-keep-trace E all-keep-empty ↠-refl = ↠-refl
lift-all-keep-trace E (all-keep-cons keeps)
    (↠-step M→L L↠N) =
  ↠-step (lift-keep-step E M→L)
    (lift-all-keep-trace E keeps L↠N)

context-bullet-catch-up-trace :
  ∀ E {M R} →
  (catch-up : BulletCatchUp M R) →
  plug E M —↠[ bulletChanges catch-up ] plug E R
context-bullet-catch-up-trace E catch-up =
  lift-all-keep-trace E
    (bulletChanges-all-keep catch-up)
    (bullet-catch-up-trace catch-up)

context-bullet-catch-up-interpreter-term :
  ∀ {E M R} →
  InterpreterContext E →
  BulletCatchUp M R →
  InterpreterTerm (plug E R)
context-bullet-catch-up-interpreter-term E-ok catch-up =
  plug-interpreter-term E-ok
    (bullet-catch-up-interpreter-term catch-up)
