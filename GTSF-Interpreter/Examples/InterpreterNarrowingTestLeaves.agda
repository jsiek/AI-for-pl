module Examples.InterpreterNarrowingTestLeaves where

-- File Charter:
--   * Provides proof-irrelevant leaves for structural narrowing examples.
--   * Keeps regression modules focused on worlds, values, and binders.
--   * Is test infrastructure, not part of the DGG theorem surface.

open import Narrowing.InterpreterValueNarrowing
data Trivial : Set₁ where
  trivial : Trivial

data Impossible : Set₁ where

trivialLeaves : NarrowingLeaves
trivialLeaves =
  record
    { BodyNarrowing = λ R γ γ′ θ θ′ N N′ → Trivial
    ; BodyNarrowingWeaken = λ R≤S proof → proof
    ; TypeNarrowing = λ A A′ → Trivial
    ; GroundNarrowing = λ gG gH → Trivial
    ; CoercionNarrowing = λ R θ θ′ c c′ → Trivial
    ; CoercionNarrowingWeaken = λ R≤S proof → proof
    ; QuotientValueFrame = λ R V V′ U U′ → Impossible
    ; QuotientValueFrameWeaken = λ R≤S ()
    ; QuotientValueFrameSealLink = λ ()
    ; LeftTaggedBoundary = λ gG → Trivial
    ; RightTaggedBoundary = λ gH → Trivial
    ; LeftFunctionProxyBoundary = λ R θ p q → Trivial
    ; LeftFunctionProxyBoundaryWeaken = λ R≤S proof → proof
    ; RightFunctionProxyBoundary = λ R θ′ p′ q′ → Trivial
    ; RightFunctionProxyBoundaryWeaken = λ R≤S proof → proof
    ; LeftForallProxyBoundary = λ R θ c → Trivial
    ; LeftForallProxyBoundaryWeaken = λ R≤S proof → proof
    ; RightForallProxyBoundary = λ R θ′ c′ → Trivial
    ; RightForallProxyBoundaryWeaken = λ R≤S proof → proof
    ; LeftTypeAbstractionBoundary = λ X → Trivial
    ; LeftGeneralizationBoundary = λ R θ A c → Trivial
    ; LeftGeneralizationBoundaryWeaken = λ R≤S proof → proof
    ; RightGeneralizationBoundary = λ R θ′ A′ c′ → Trivial
    ; RightGeneralizationBoundaryWeaken = λ R≤S proof → proof
    }
