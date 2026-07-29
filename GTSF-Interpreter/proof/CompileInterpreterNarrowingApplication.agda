module proof.CompileInterpreterNarrowingApplication where

-- File Charter:
--   * Supplies syntax-only compiler-image constructors for casts and
--     applications.
--   * Accepts recursive compiler-image facts as arguments.
--   * Contains no evaluation or reduction result.

open import Data.List using ([])

open import Compile using (CastPlan; cast)
open import InterpreterTermNarrowingCore
import NuTerms as N
open import Types

compiled-cast-interpreter-term :
  ∀ {Δ A B M} →
  (plan : CastPlan Δ [] A B) →
  InterpreterTerm M →
  InterpreterTerm (cast plan M)
compiled-cast-interpreter-term plan M-ok =
  coercion-application-term
    (coercion-application-term M-ok)

compiled-application-interpreter-term :
  ∀ {Δ A B L M} →
  (plan : CastPlan Δ [] A B) →
  InterpreterTerm L →
  InterpreterTerm M →
  InterpreterTerm (L N.· cast plan M)
compiled-application-interpreter-term plan L-ok M-ok =
  application-term L-ok
    (compiled-cast-interpreter-term plan M-ok)

compiled-dynamic-application-interpreter-term :
  ∀ {Δ A B C D L M} →
  (function-plan : CastPlan Δ [] A B) →
  (argument-plan : CastPlan Δ [] C D) →
  InterpreterTerm L →
  InterpreterTerm M →
  InterpreterTerm
    (cast function-plan L N.· cast argument-plan M)
compiled-dynamic-application-interpreter-term
    function-plan argument-plan L-ok M-ok =
  application-term
    (compiled-cast-interpreter-term function-plan L-ok)
    (compiled-cast-interpreter-term argument-plan M-ok)

paired-cast-shape :
  ∀ {M M′ c c′} →
  InterpreterTermShape M M′ →
  InterpreterTermShape (M N.⟨ c ⟩) (M′ N.⟨ c′ ⟩)
paired-cast-shape =
  paired-coercion-application-shape

right-cast-shape :
  ∀ {M M′ c′} →
  InterpreterTermShape M M′ →
  InterpreterTermShape M (M′ N.⟨ c′ ⟩)
right-cast-shape =
  right-coercion-application-shape

compiled-application-shape :
  ∀ {L L′ M M′ c d c′ d′} →
  InterpreterTermShape L L′ →
  InterpreterTermShape M M′ →
  InterpreterTermShape
    (L N.· ((M N.⟨ c ⟩) N.⟨ d ⟩))
    (L′ N.· ((M′ N.⟨ c′ ⟩) N.⟨ d′ ⟩))
compiled-application-shape
    {L = L} {L′ = L′} {M = M} {M′ = M′}
    {c = c} {d = d} {c′ = c′} {d′ = d′}
    L~L′ M~M′ =
  application-shape
    {L = L} {L′ = L′}
    {M = (M N.⟨ c ⟩) N.⟨ d ⟩}
    {M′ = (M′ N.⟨ c′ ⟩) N.⟨ d′ ⟩}
    L~L′
    (paired-cast-shape {c = d} {c′ = d′}
      (paired-cast-shape {c = c} {c′ = c′} M~M′))

compiled-right-dynamic-application-shape :
  ∀ {L L′ M M′ f′ g′ c d c′ d′} →
  InterpreterTermShape L L′ →
  InterpreterTermShape M M′ →
  InterpreterTermShape
    (L N.· ((M N.⟨ c ⟩) N.⟨ d ⟩))
    (((L′ N.⟨ f′ ⟩) N.⟨ g′ ⟩)
      N.· ((M′ N.⟨ c′ ⟩) N.⟨ d′ ⟩))
compiled-right-dynamic-application-shape
    {L = L} {L′ = L′} {M = M} {M′ = M′}
    {f′ = f′} {g′ = g′}
    {c = c} {d = d} {c′ = c′} {d′ = d′}
    L~L′ M~M′ =
  application-shape
    {L = L}
    {L′ = (L′ N.⟨ f′ ⟩) N.⟨ g′ ⟩}
    {M = (M N.⟨ c ⟩) N.⟨ d ⟩}
    {M′ = (M′ N.⟨ c′ ⟩) N.⟨ d′ ⟩}
    (right-cast-shape {c′ = g′}
      (right-cast-shape {c′ = f′} L~L′))
    (paired-cast-shape {c = d} {c′ = d′}
      (paired-cast-shape {c = c} {c′ = c′} M~M′))

compiled-dynamic-application-shape :
  ∀ {L L′ M M′ f g f′ g′ c d c′ d′} →
  InterpreterTermShape L L′ →
  InterpreterTermShape M M′ →
  InterpreterTermShape
    (((L N.⟨ f ⟩) N.⟨ g ⟩)
      N.· ((M N.⟨ c ⟩) N.⟨ d ⟩))
    (((L′ N.⟨ f′ ⟩) N.⟨ g′ ⟩)
      N.· ((M′ N.⟨ c′ ⟩) N.⟨ d′ ⟩))
compiled-dynamic-application-shape
    {L = L} {L′ = L′} {M = M} {M′ = M′}
    {f = f} {g = g} {f′ = f′} {g′ = g′}
    {c = c} {d = d} {c′ = c′} {d′ = d′}
    L~L′ M~M′ =
  application-shape
    {L = (L N.⟨ f ⟩) N.⟨ g ⟩}
    {L′ = (L′ N.⟨ f′ ⟩) N.⟨ g′ ⟩}
    {M = (M N.⟨ c ⟩) N.⟨ d ⟩}
    {M′ = (M′ N.⟨ c′ ⟩) N.⟨ d′ ⟩}
    (paired-cast-shape {c = g} {c′ = g′}
      (paired-cast-shape {c = f} {c′ = f′} L~L′))
    (paired-cast-shape {c = d} {c′ = d′}
      (paired-cast-shape {c = c} {c′ = c′} M~M′))
