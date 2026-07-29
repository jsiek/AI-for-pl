module DoubleInterpreter where

-- File Charter:
--   * Runs the two compiled endpoints of a closed gradual-term imprecision
--     derivation together.
--   * Defines structural narrowing for semantic values, including closure
--     bodies, environments, type environments, and allocation worlds.
--   * Makes temporary skew explicit: after one side returns, bounded catch-up
--     reruns only the lagging side at successively larger step indices.
--   * Exposes the one remaining proof boundary as a decision procedure for
--     whether two returned worlds and values form a synchronized join.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (zero; suc)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Coercions using (Coercion)
open import CompileTermImprecision using
  (compile-preserves-term-imprecision)
open import Ctx using (ctxWf-[])
open import GradualTermImprecision using
  (_∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter
open import NuTerms using (Term)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types

------------------------------------------------------------------------
-- Synchronized semantic narrowing
------------------------------------------------------------------------

-- The parameters below are deliberately the syntax-specific leaves of the
-- relation.  The enclosing module supplies all semantic structure:
--
-- * `BodyNarrowing` should be instantiated by compiled term narrowing for
--   open closure bodies;
-- * the type, ground, and coercion relations should be obtained from the
--   corresponding compile-monotonicity judgments; and
-- * the wrapper relations cover genuinely asymmetric value cases introduced
--   by casts.  They are not a license to compare arbitrary values.
module Synchronized
  (BodyNarrowing : Term → Term → Set₁)
  (TypeNarrowing : Ty → Ty → Set₁)
  (GroundNarrowing :
    ∀ {G H} → Ground G → Ground H → Set₁)
  (CoercionNarrowing : Coercion → Coercion → Set₁)
  (NameNarrowing : Name → Name → Set₁)
  (SealNameNarrowing : SealName → SealName → Set₁)
  (LeftValueWrapperNarrowing : Value → Value → Set₁)
  (RightValueWrapperNarrowing : Value → Value → Set₁)
  where

  data TypeNameNarrowing : TypeName → TypeName → Set₁ where
    abstract-name⊑ :
      ∀ {X X′} →
      NameNarrowing X X′ →
      TypeNameNarrowing (abstract-name X) (abstract-name X′)

    seal-name⊑ :
      ∀ {α α′} →
      SealNameNarrowing α α′ →
      TypeNameNarrowing (seal-name α) (seal-name α′)

  data TypeEnvironmentNarrowing :
      TypeEnvironment → TypeEnvironment → Set₁ where
    []⊑[]ᵗᵉ :
      TypeEnvironmentNarrowing [] []

    _∷⊑∷ᵗᵉ_ :
      ∀ {X X′ θ θ′} →
      TypeNameNarrowing X X′ →
      TypeEnvironmentNarrowing θ θ′ →
      TypeEnvironmentNarrowing (X ∷ θ) (X′ ∷ θ′)

  mutual

    data ValueNarrowing : Value → Value → Set₁ where
      closure⊑ :
        ∀ {N N′ γ γ′ θ θ′} →
        BodyNarrowing N N′ →
        EnvironmentNarrowing γ γ′ →
        TypeEnvironmentNarrowing θ θ′ →
        ValueNarrowing (closure N γ θ) (closure N′ γ′ θ′)

      constant⊑ :
        ∀ κ →
        ValueNarrowing (constant κ) (constant κ)

      tagged⊑ :
        ∀ {G H} {gG : Ground G} {gH : Ground H}
          {θ θ′ V V′} →
        GroundNarrowing gG gH →
        TypeEnvironmentNarrowing θ θ′ →
        ValueNarrowing V V′ →
        ValueNarrowing (tagged gG θ V) (tagged gH θ′ V′)

      sealed⊑ :
        ∀ {α α′ V V′} →
        SealNameNarrowing α α′ →
        ValueNarrowing V V′ →
        ValueNarrowing (sealed α V) (sealed α′ V′)

      function-proxy⊑ :
        ∀ {p p′ q q′ θ θ′ V V′} →
        CoercionNarrowing p p′ →
        CoercionNarrowing q q′ →
        TypeEnvironmentNarrowing θ θ′ →
        ValueNarrowing V V′ →
        ValueNarrowing
          (function-proxy p q θ V)
          (function-proxy p′ q′ θ′ V′)

      type-abstraction⊑ :
        ∀ {X X′ V V′} →
        NameNarrowing X X′ →
        ValueNarrowing V V′ →
        ValueNarrowing
          (type-abstraction X V)
          (type-abstraction X′ V′)

      forall-proxy⊑ :
        ∀ {c c′ θ θ′ V V′} →
        CoercionNarrowing c c′ →
        TypeEnvironmentNarrowing θ θ′ →
        ValueNarrowing V V′ →
        ValueNarrowing
          (forall-proxy c θ V)
          (forall-proxy c′ θ′ V′)

      generalized⊑ :
        ∀ {A A′ c c′ θ θ′ V V′} →
        TypeNarrowing A A′ →
        CoercionNarrowing c c′ →
        TypeEnvironmentNarrowing θ θ′ →
        ValueNarrowing V V′ →
        ValueNarrowing
          (generalized A c θ V)
          (generalized A′ c′ θ′ V′)

      left-wrapper⊑ :
        ∀ {L V R} →
        LeftValueWrapperNarrowing L V →
        ValueNarrowing V R →
        ValueNarrowing L R

      right-wrapper⊑ :
        ∀ {L V R} →
        ValueNarrowing L V →
        RightValueWrapperNarrowing V R →
        ValueNarrowing L R

    data EnvironmentNarrowing :
        Environment → Environment → Set₁ where
      []⊑[]ᵉ :
        EnvironmentNarrowing [] []

      _∷⊑∷ᵉ_ :
        ∀ {V V′ γ γ′} →
        ValueNarrowing V V′ →
        EnvironmentNarrowing γ γ′ →
        EnvironmentNarrowing (V ∷ γ) (V′ ∷ γ′)

  data AllocationNarrowing : Allocation → Allocation → Set₁ where
    allocation⊑ :
      ∀ {α α′ A A′ θ θ′} →
      SealNameNarrowing α α′ →
      TypeNarrowing A A′ →
      TypeEnvironmentNarrowing θ θ′ →
      AllocationNarrowing
        (allocation α A θ)
        (allocation α′ A′ θ′)

  -- Allocations may temporarily be unmatched.  A later synchronized result
  -- can retain those one-sided cells while still recording every matched
  -- allocation explicitly.
  data AllocationAlignment :
      List Allocation → List Allocation → Set₁ where
    []⊑[]ᵃ :
      AllocationAlignment [] []

    bothᵃ :
      ∀ {a a′ cells cells′} →
      AllocationNarrowing a a′ →
      AllocationAlignment cells cells′ →
      AllocationAlignment (a ∷ cells) (a′ ∷ cells′)

    left-onlyᵃ :
      ∀ {a cells cells′} →
      AllocationAlignment cells cells′ →
      AllocationAlignment (a ∷ cells) cells′

    right-onlyᵃ :
      ∀ {a′ cells cells′} →
      AllocationAlignment cells cells′ →
      AllocationAlignment cells (a′ ∷ cells′)

  data WorldNarrowing : World → World → Set₁ where
    world⊑ :
      ∀ {next next′ cells cells′} →
      AllocationAlignment cells cells′ →
      WorldNarrowing
        (world next cells)
        (world next′ cells′)

  record Joined
      (W : World) (V : Value) (W′ : World) (V′ : Value) : Set₁ where
    constructor joined-by
    field
      worlds-narrow : WorldNarrowing W W′
      values-narrow : ValueNarrowing V V′

  ----------------------------------------------------------------------
  -- Observable states of the double-headed interpreter
  ----------------------------------------------------------------------

  data DoubleResult : Set₁ where
    synchronized :
      (left-index right-index : StepIndex) →
      (W : World) (V : Value) (W′ : World) (V′ : Value) →
      Joined W V W′ V′ →
      DoubleResult

    both-timeout :
      (index : StepIndex) →
      World →
      World →
      DoubleResult

    left-ahead :
      (left-index right-index : StepIndex) →
      (W : World) (V : Value) →
      (W′ : World) →
      DoubleResult

    right-ahead :
      (left-index right-index : StepIndex) →
      (W : World) →
      (W′ : World) (V′ : Value) →
      DoubleResult

    stopped :
      (left-index right-index : StepIndex) →
      Outcome →
      Outcome →
      DoubleResult

    unrelated-returns :
      (left-index right-index : StepIndex) →
      (W : World) (V : Value) (W′ : World) (V′ : Value) →
      ¬ Joined W V W′ V′ →
      DoubleResult

  joinReturned :
    (joined? :
      ∀ W V W′ V′ → Dec (Joined W V W′ V′)) →
    (left-index right-index : StepIndex) →
    (W : World) (V : Value) (W′ : World) (V′ : Value) →
    DoubleResult
  joinReturned joined? left-index right-index W V W′ V′
      with joined? W V W′ V′
  joinReturned joined? left-index right-index W V W′ V′
      | yes V⊑V′ =
    synchronized left-index right-index W V W′ V′ V⊑V′
  joinReturned joined? left-index right-index W V W′ V′
      | no V⋢V′ =
    unrelated-returns left-index right-index W V W′ V′ V⋢V′

  ----------------------------------------------------------------------
  -- Single-sided catch-up
  ----------------------------------------------------------------------

  catchRight :
    (joined? :
      ∀ W V W′ V′ → Dec (Joined W V W′ V′)) →
    (right-term : Term) →
    (left-index right-index : StepIndex) →
    (W : World) (V : Value) →
    (W′ : World) →
    (catch-up : StepIndex) →
    DoubleResult
  catchRight joined? right-term left-index right-index W V W′ zero =
    left-ahead left-index right-index W V W′
  catchRight joined? right-term left-index right-index W V W′
      (suc catch-up)
      with run right-term (suc right-index)
  catchRight joined? right-term left-index right-index W V W′
      (suc catch-up) | timed W₂ =
    catchRight joined? right-term left-index (suc right-index)
      W V W₂ catch-up
  catchRight joined? right-term left-index right-index W V W′
      (suc catch-up) | blamed W₂ =
    stopped left-index (suc right-index)
      (returned W V) (blamed W₂)
  catchRight joined? right-term left-index right-index W V W′
      (suc catch-up) | failed W₂ e =
    stopped left-index (suc right-index)
      (returned W V) (failed W₂ e)
  catchRight joined? right-term left-index right-index W V W′
      (suc catch-up) | returned W₂ V₂ =
    joinReturned joined? left-index (suc right-index) W V W₂ V₂

  catchLeft :
    (joined? :
      ∀ W V W′ V′ → Dec (Joined W V W′ V′)) →
    (left-term : Term) →
    (left-index right-index : StepIndex) →
    (W : World) →
    (W′ : World) (V′ : Value) →
    (catch-up : StepIndex) →
    DoubleResult
  catchLeft joined? left-term left-index right-index W W′ V′ zero =
    right-ahead left-index right-index W W′ V′
  catchLeft joined? left-term left-index right-index W W′ V′
      (suc catch-up)
      with run left-term (suc left-index)
  catchLeft joined? left-term left-index right-index W W′ V′
      (suc catch-up) | timed W₂ =
    catchLeft joined? left-term (suc left-index) right-index
      W₂ W′ V′ catch-up
  catchLeft joined? left-term left-index right-index W W′ V′
      (suc catch-up) | blamed W₂ =
    stopped (suc left-index) right-index
      (blamed W₂) (returned W′ V′)
  catchLeft joined? left-term left-index right-index W W′ V′
      (suc catch-up) | failed W₂ e =
    stopped (suc left-index) right-index
      (failed W₂ e) (returned W′ V′)
  catchLeft joined? left-term left-index right-index W W′ V′
      (suc catch-up) | returned W₂ V₂ =
    joinReturned joined? (suc left-index) right-index W₂ V₂ W′ V′

  ----------------------------------------------------------------------
  -- Core entry point: evaluate a compiled narrowing derivation at both heads
  ----------------------------------------------------------------------

  doubleInterpretCompiled :
    (joined? :
      ∀ W V W′ V′ → Dec (Joined W V W′ V′)) →
    ∀ {N N′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
    (N⊑N′ :
      [] ∣ 0 ∣ 0 ∣ [] ∣ []
        ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p) →
    (index catch-up : StepIndex) →
    DoubleResult
  doubleInterpretCompiled joined? {N = N} {N′ = N′}
      N⊑N′ index catch-up
      with run N index | run N′ index
  doubleInterpretCompiled joined? N⊑N′ index catch-up
      | timed W | timed W′ =
    both-timeout index W W′
  doubleInterpretCompiled joined? N⊑N′ index catch-up
      | timed W | blamed W′ =
    stopped index index (timed W) (blamed W′)
  doubleInterpretCompiled joined? N⊑N′ index catch-up
      | timed W | failed W′ e′ =
    stopped index index (timed W) (failed W′ e′)
  doubleInterpretCompiled joined? {N = N} N⊑N′ index catch-up
      | timed W | returned W′ V′ =
    catchLeft joined? N index index W W′ V′ catch-up
  doubleInterpretCompiled joined? N⊑N′ index catch-up
      | blamed W | timed W′ =
    stopped index index (blamed W) (timed W′)
  doubleInterpretCompiled joined? N⊑N′ index catch-up
      | blamed W | blamed W′ =
    stopped index index (blamed W) (blamed W′)
  doubleInterpretCompiled joined? N⊑N′ index catch-up
      | blamed W | failed W′ e′ =
    stopped index index (blamed W) (failed W′ e′)
  doubleInterpretCompiled joined? N⊑N′ index catch-up
      | blamed W | returned W′ V′ =
    stopped index index (blamed W) (returned W′ V′)
  doubleInterpretCompiled joined? N⊑N′ index catch-up
      | failed W e | timed W′ =
    stopped index index (failed W e) (timed W′)
  doubleInterpretCompiled joined? N⊑N′ index catch-up
      | failed W e | blamed W′ =
    stopped index index (failed W e) (blamed W′)
  doubleInterpretCompiled joined? N⊑N′ index catch-up
      | failed W e | failed W′ e′ =
    stopped index index (failed W e) (failed W′ e′)
  doubleInterpretCompiled joined? N⊑N′ index catch-up
      | failed W e | returned W′ V′ =
    stopped index index (failed W e) (returned W′ V′)
  doubleInterpretCompiled joined? {N′ = N′}
      N⊑N′ index catch-up
      | returned W V | timed W′ =
    catchRight joined? N′ index index W V W′ catch-up
  doubleInterpretCompiled joined? N⊑N′ index catch-up
      | returned W V | blamed W′ =
    stopped index index (returned W V) (blamed W′)
  doubleInterpretCompiled joined? N⊑N′ index catch-up
      | returned W V | failed W′ e′ =
    stopped index index (returned W V) (failed W′ e′)
  doubleInterpretCompiled joined? N⊑N′ index catch-up
      | returned W V | returned W′ V′ =
    joinReturned joined? index index W V W′ V′

  ----------------------------------------------------------------------
  -- Source entry point
  ----------------------------------------------------------------------

  doubleInterpret :
    (joined? :
      ∀ W V W′ V′ → Dec (Joined W V W′ V′)) →
    ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
    (M⊑M′ :
      [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
    (index catch-up : StepIndex) →
    DoubleResult
  doubleInterpret joined? M⊑M′ =
    doubleInterpretCompiled joined?
      (compile-preserves-term-imprecision
        ctxWf-[] ctxWf-[] M⊑M′)
