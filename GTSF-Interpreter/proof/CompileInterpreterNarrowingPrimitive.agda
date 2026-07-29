module proof.CompileInterpreterNarrowingPrimitive where

-- File Charter:
--   * Supplies compiler-image constructors for primitive applications whose
--     operands have compiler-inserted casts.
--   * Accepts recursive image facts explicitly.
--   * Contains no operational semantics.

open import Data.List using ([])

open import Compile using (CastPlan; cast)
open import InterpreterTermNarrowingCore
import NuTerms as N
open import Primitives using (Prim)
open import Types
open import proof.CompileInterpreterNarrowingApplication using
  (compiled-cast-interpreter-term; paired-cast-shape)

compiled-primitive-interpreter-term :
  ∀ {Δ A B C D L M} →
  (left-plan : CastPlan Δ [] A B) →
  (right-plan : CastPlan Δ [] C D) →
  (op : Prim) →
  InterpreterTerm L →
  InterpreterTerm M →
  InterpreterTerm
    (cast left-plan L N.⊕[ op ] cast right-plan M)
compiled-primitive-interpreter-term
    left-plan right-plan op L-ok M-ok =
  primitive-term op
    (compiled-cast-interpreter-term left-plan L-ok)
    (compiled-cast-interpreter-term right-plan M-ok)

compiled-primitive-shape :
  ∀ {L L′ M M′ c d c′ d′ e f e′ f′} →
  (op : Prim) →
  InterpreterTermShape L L′ →
  InterpreterTermShape M M′ →
  InterpreterTermShape
    (((L N.⟨ c ⟩) N.⟨ d ⟩)
      N.⊕[ op ] ((M N.⟨ e ⟩) N.⟨ f ⟩))
    (((L′ N.⟨ c′ ⟩) N.⟨ d′ ⟩)
      N.⊕[ op ] ((M′ N.⟨ e′ ⟩) N.⟨ f′ ⟩))
compiled-primitive-shape
    {L = L} {L′ = L′} {M = M} {M′ = M′}
    {c = c} {d = d} {c′ = c′} {d′ = d′}
    {e = e} {f = f} {e′ = e′} {f′ = f′}
    op L~L′ M~M′ =
  primitive-shape
    {L = (L N.⟨ c ⟩) N.⟨ d ⟩}
    {L′ = (L′ N.⟨ c′ ⟩) N.⟨ d′ ⟩}
    {M = (M N.⟨ e ⟩) N.⟨ f ⟩}
    {M′ = (M′ N.⟨ e′ ⟩) N.⟨ f′ ⟩}
    op
    (paired-cast-shape {c = d} {c′ = d′}
      (paired-cast-shape {c = c} {c′ = c′} L~L′))
    (paired-cast-shape {c = f} {c′ = f′}
      (paired-cast-shape {c = e} {c′ = e′} M~M′))
