module Runtime.InterpreterClosedValueFrame where

-- File Charter:
--   * Gives the coherent one-inert-cast fragment of the `ClosedValue` graph.
--   * Shares the payload value definitionally with the enclosing runtime
--     wrapper, avoiding an invalid uniqueness assumption for abstract names.
--   * Extracts the fragment from a closed inert syntactic cast.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; Σ-syntax)

open import Coercions using (Inert)
import Coercions as C
open import Interpreter
open import Runtime.InterpreterClosedValue
import NuTerms as N
open import Types using (Ground)

data ClosedValueFrame
    (θ : TypeEnvironment) (V : Value) :
    ∀ {c} → Inert c → Value → Set where
  closed-tag-frame :
    ∀ {G} {gG : Ground G} →
    ClosedValueFrame θ V (C._! G)
      (tagged gG θ V)

  closed-seal-frame :
    ∀ {A X α} →
    lookup θ X ≡ just (seal-name α) →
    ClosedValueFrame θ V (C.seal A X)
      (sealed α V)

  closed-function-frame :
    ∀ {p q} →
    ClosedValueFrame θ V (p C.↦ q)
      (function-proxy p q θ V)

  closed-forall-frame :
    ∀ {c} →
    ClosedValueFrame θ V (C.`∀ c)
      (forall-proxy c θ V)

  closed-generalized-frame :
    ∀ {A c} →
    ClosedValueFrame θ V (C.gen A c)
      (generalized A c θ V)

closed-value-inert-frame :
  ∀ {γ θ M U c}
    {vM : N.Value M} {ic : Inert c} →
  ClosedValue γ θ (vM N.⟨ ic ⟩) U →
  Σ[ V ∈ Value ]
    (ClosedValue γ θ vM V ×
     ClosedValueFrame θ V ic U)
closed-value-inert-frame
    (closed-tagged body) =
  _ , body , closed-tag-frame
closed-value-inert-frame
    (closed-sealed lookup body) =
  _ , body , closed-seal-frame lookup
closed-value-inert-frame
    (closed-function-proxy body) =
  _ , body , closed-function-frame
closed-value-inert-frame
    (closed-forall-proxy body) =
  _ , body , closed-forall-frame
closed-value-inert-frame
    (closed-generalized body) =
  _ , body , closed-generalized-frame
