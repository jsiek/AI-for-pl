module InterpreterAdequacy.proof.BulletCatchUpCompleteness where

-- File Charter:
--   * Constructs the finite administrative catch-up trace for every typed
--     polymorphic value in the direct-interpreter source fragment.
--   * Recurses through forall proxies and stops at a type abstraction or a
--     generalized value, exactly matching runtime-bullet reduction.
--   * Supplies the constructive alignment fact needed after a small-step
--     `ν` allocation; it does not run the interpreter.

open import Data.List using ([])
open import Data.Nat using (zero)
open import Data.Product using (Σ-syntax; _,_)

import Coercions as C
open import InterpreterAdequacy.BulletCatchUp using
  ( BulletCatchUp
  ; bullet-forall-proxy
  ; bullet-generalized
  ; bullet-type-abstraction
  )
open import SmallStepInterface.InterpreterTermShape using
  ( InterpreterTerm
  ; closure-term
  ; coercion-application-term
  ; constant-term
  ; type-abstraction-term
  )
import NuTerms as N
open import Primitives using (κℕ)
open import Types using (Ty; TyCtx; `∀)

bullet-catch-up-complete :
  ∀ {Δ Σ V A} →
  (vV : N.Value V) →
  (V-ok : InterpreterTerm V) →
  N._∣_∣_⊢_⦂_ Δ Σ [] V (`∀ A) →
  Σ[ R ∈ N.Term ] BulletCatchUp (V N.•) R
bullet-catch-up-complete (N.ƛ M) (closure-term M-ok) ()
bullet-catch-up-complete (N.Λ vV)
    (type-abstraction-term vV′ V-ok) (N.⊢Λ vV″ V⊢) =
  _ , bullet-type-abstraction vV V-ok
bullet-catch-up-complete (N.$ (κℕ n)) (constant-term (κℕ .n)) ()
bullet-catch-up-complete
    (vV N.⟨ G C.! ⟩) (coercion-application-term V-ok)
    (N.⊢⟨⟩ () V⊢)
bullet-catch-up-complete
    (vV N.⟨ C.seal B X ⟩) (coercion-application-term V-ok)
    (N.⊢⟨⟩ () V⊢)
bullet-catch-up-complete
    (vV N.⟨ p C.↦ q ⟩) (coercion-application-term V-ok)
    (N.⊢⟨⟩ () V⊢)
bullet-catch-up-complete
    (vV N.⟨ C.`∀ c ⟩) (coercion-application-term V-ok)
    (N.⊢⟨⟩ (C.cast-all c⊢) V⊢)
    with bullet-catch-up-complete vV V-ok V⊢
bullet-catch-up-complete
    (vV N.⟨ C.`∀ c ⟩) (coercion-application-term V-ok)
    (N.⊢⟨⟩ (C.cast-all c⊢) V⊢) | R , catch-up =
  R N.⟨ c C.[ zero ]ᶜ ⟩ ,
    bullet-forall-proxy vV catch-up
bullet-catch-up-complete
    {V = V N.⟨ C.gen B c ⟩}
    (vV N.⟨ C.gen B c ⟩) (coercion-application-term V-ok)
    (N.⊢⟨⟩ (C.cast-gen B-wf occurs c⊢) V⊢) =
  V N.⟨ c C.[ zero ]ᶜ ⟩ ,
    bullet-generalized vV V-ok
