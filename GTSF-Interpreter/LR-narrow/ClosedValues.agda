module LR-narrow.ClosedValues where

-- File Charter:
--   * Defines closure of semantic values and captured term environments.
--   * Treats term variables through closure environments; type names and
--     seals remain governed by the LR interpretation and Kripke world.
--   * Contains no term-imprecision or operational-semantics dependency.

open import Data.List using ([]; _∷_)

open import Interpreter
open import Narrowing.InterpreterWorldNarrowing using
  (Allocated; TypeEnvironmentScoped)
open import Types using (Ground)

mutual

  data ClosedValue : World → Value → Set where
    closure-closed : ∀ {W N γ θ}
      → ClosedEnvironment W γ
      → TypeEnvironmentScoped W θ
      → ClosedValue W (closure N γ θ)

    constant-closed : ∀ {W κ}
      → ClosedValue W (constant κ)

    tagged-closed : ∀ {W G} {gG : Ground G} {θ V}
      → TypeEnvironmentScoped W θ
      → ClosedValue W V
      → ClosedValue W (tagged gG θ V)

    sealed-closed : ∀ {W α V}
      → Allocated W α
      → ClosedValue W V
      → ClosedValue W (sealed α V)

    function-proxy-closed : ∀ {W p q θ V}
      → TypeEnvironmentScoped W θ
      → ClosedValue W V
      → ClosedValue W (function-proxy p q θ V)

    type-abstraction-closed : ∀ {W X V}
      → ClosedValue W V
      → ClosedValue W (type-abstraction X V)

    forall-proxy-closed : ∀ {W c θ V}
      → TypeEnvironmentScoped W θ
      → ClosedValue W V
      → ClosedValue W (forall-proxy c θ V)

    generalized-closed : ∀ {W A c θ V}
      → TypeEnvironmentScoped W θ
      → ClosedValue W V
      → ClosedValue W (generalized A c θ V)

  data ClosedEnvironment : World → Environment → Set where
    []-closed : ∀ {W}
      → ClosedEnvironment W []

    _∷-closed_ : ∀ {W V γ}
      → ClosedValue W V
      → ClosedEnvironment W γ
      → ClosedEnvironment W (V ∷ γ)

infixr 5 _∷-closed_
