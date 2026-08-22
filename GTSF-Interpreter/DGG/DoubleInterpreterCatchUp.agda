module DGG.DoubleInterpreterCatchUp where

-- File Charter:
--   * EXPERIMENTAL DEAD END: proves conditional facts about the abandoned
--     double-interpreter route, not an unconditional DGG catch-up theorem.
--   * Proves that the single-sided loops in `DGG.DoubleInterpreter` find every
--     synchronized return (or permitted left blame) described by a finite
--     sequence of larger-index interpreter observations.
--   * Lifts those loop lemmas to `doubleInterpretCompiled`.
--   * Separates this executable completeness fact from the DGG obligation
--     that related programs actually possess the required finite traces.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Nat using (zero; suc)
open import Relation.Nullary using (Dec; yes; no)

open import Coercions using (Coercion)
import DGG.DoubleInterpreter as Double
open import GradualTermImprecision using
  (_∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter
open import DGG.InterpreterDynamicGradualGuaranteeDirect using
  (compiled-leftᴰ; compiled-rightᴰ)
open import NuTerms using (Term)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types

module CatchUp
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

  open Double.Synchronized
    BodyNarrowing
    TypeNarrowing
    GroundNarrowing
    CoercionNarrowing
    NameNarrowing
    SealNameNarrowing
    LeftValueWrapperNarrowing
    RightValueWrapperNarrowing

  ----------------------------------------------------------------------
  -- Successful result shapes
  ----------------------------------------------------------------------

  data IsSynchronizedAt
      (left-index right-index : StepIndex)
      (W : World) (V : Value) (W′ : World) (V′ : Value) :
      DoubleResult → Set₁ where
    synchronized-at :
      (V⊑V′ : Joined W V W′ V′) →
      IsSynchronizedAt left-index right-index W V W′ V′
        (synchronized left-index right-index W V W′ V′ V⊑V′)

  data IsLeftBlameAt
      (left-index right-index : StepIndex)
      (W : World) (W′ : World) (V′ : Value) :
      DoubleResult → Set where
    left-blame-at :
      IsLeftBlameAt left-index right-index W W′ V′
        (stopped left-index right-index
          (blamed W) (returned W′ V′))

  joinReturned-complete :
    (joined? :
      ∀ W V W′ V′ → Dec (Joined W V W′ V′)) →
    ∀ {left-index right-index W V W′ V′} →
    Joined W V W′ V′ →
    IsSynchronizedAt left-index right-index W V W′ V′
      (joinReturned joined? left-index right-index W V W′ V′)
  joinReturned-complete joined? {W = W} {V = V}
      {W′ = W′} {V′ = V′} V⊑V′
      with joined? W V W′ V′
  joinReturned-complete joined? V⊑V′ | yes V⊑V″ =
    synchronized-at V⊑V″
  joinReturned-complete joined? V⊑V′ | no V⋢V′ =
    ⊥-elim (V⋢V′ V⊑V′)

  ----------------------------------------------------------------------
  -- Finite evidence that a lagging right side reaches a related value
  ----------------------------------------------------------------------

  data RightCatchUpTrace
      (right-term : Term) (W : World) (V : Value) :
      (right-index catch-up terminal-index : StepIndex) →
      World → Value → Set₁ where

    right-return :
      ∀ {right-index catch-up W′ V′} →
      run right-term (suc right-index) ≡ returned W′ V′ →
      Joined W V W′ V′ →
      RightCatchUpTrace right-term W V
        right-index (suc catch-up) (suc right-index) W′ V′

    right-timeout :
      ∀ {right-index catch-up terminal-index W₁ W′ V′} →
      run right-term (suc right-index) ≡ timed W₁ →
      RightCatchUpTrace right-term W V
        (suc right-index) catch-up terminal-index W′ V′ →
      RightCatchUpTrace right-term W V
        right-index (suc catch-up) terminal-index W′ V′

  catchRight-complete :
    (joined? :
      ∀ W V W′ V′ → Dec (Joined W V W′ V′)) →
    ∀ {right-term left-index right-index catch-up terminal-index
       W V W₀′ W′ V′} →
    RightCatchUpTrace right-term W V
      right-index catch-up terminal-index W′ V′ →
    IsSynchronizedAt left-index terminal-index W V W′ V′
      (catchRight joined? right-term left-index right-index
        W V W₀′ catch-up)
  catchRight-complete joined?
      (right-return {right-index = right-index} run-eq V⊑V′)
      rewrite run-eq =
    joinReturned-complete joined? V⊑V′
  catchRight-complete joined?
      (right-timeout {right-index = right-index} run-eq trace)
      rewrite run-eq =
    catchRight-complete joined? trace

  ----------------------------------------------------------------------
  -- Finite evidence that a lagging left side reaches a related value
  ----------------------------------------------------------------------

  data LeftCatchUpTrace
      (left-term : Term) (W′ : World) (V′ : Value) :
      (left-index catch-up terminal-index : StepIndex) →
      World → Value → Set₁ where

    left-return :
      ∀ {left-index catch-up W V} →
      run left-term (suc left-index) ≡ returned W V →
      Joined W V W′ V′ →
      LeftCatchUpTrace left-term W′ V′
        left-index (suc catch-up) (suc left-index) W V

    left-timeout :
      ∀ {left-index catch-up terminal-index W₁ W V} →
      run left-term (suc left-index) ≡ timed W₁ →
      LeftCatchUpTrace left-term W′ V′
        (suc left-index) catch-up terminal-index W V →
      LeftCatchUpTrace left-term W′ V′
        left-index (suc catch-up) terminal-index W V

  catchLeft-complete :
    (joined? :
      ∀ W V W′ V′ → Dec (Joined W V W′ V′)) →
    ∀ {left-term left-index right-index catch-up terminal-index
       W₀ W W′ V V′} →
    LeftCatchUpTrace left-term W′ V′
      left-index catch-up terminal-index W V →
    IsSynchronizedAt terminal-index right-index W V W′ V′
      (catchLeft joined? left-term left-index right-index
        W₀ W′ V′ catch-up)
  catchLeft-complete joined?
      (left-return {left-index = left-index} run-eq V⊑V′)
      rewrite run-eq =
    joinReturned-complete joined? V⊑V′
  catchLeft-complete joined?
      (left-timeout {left-index = left-index} run-eq trace)
      rewrite run-eq =
    catchLeft-complete joined? trace

  ----------------------------------------------------------------------
  -- Finite evidence for the permitted backward-DGG blame alternative
  ----------------------------------------------------------------------

  data LeftBlameCatchUpTrace
      (left-term : Term) :
      (left-index catch-up terminal-index : StepIndex) →
      World → Set where

    left-blame :
      ∀ {left-index catch-up W} →
      run left-term (suc left-index) ≡ blamed W →
      LeftBlameCatchUpTrace left-term
        left-index (suc catch-up) (suc left-index) W

    left-blame-timeout :
      ∀ {left-index catch-up terminal-index W₁ W} →
      run left-term (suc left-index) ≡ timed W₁ →
      LeftBlameCatchUpTrace left-term
        (suc left-index) catch-up terminal-index W →
      LeftBlameCatchUpTrace left-term
        left-index (suc catch-up) terminal-index W

  catchLeft-blame-complete :
    (joined? :
      ∀ W V W′ V′ → Dec (Joined W V W′ V′)) →
    ∀ {left-term left-index right-index catch-up terminal-index
       W₀ W W′ V′} →
    LeftBlameCatchUpTrace left-term
      left-index catch-up terminal-index W →
    IsLeftBlameAt terminal-index right-index W W′ V′
      (catchLeft joined? left-term left-index right-index
        W₀ W′ V′ catch-up)
  catchLeft-blame-complete joined?
      (left-blame {left-index = left-index} run-eq)
      rewrite run-eq =
    left-blame-at
  catchLeft-blame-complete joined?
      (left-blame-timeout
        {left-index = left-index} run-eq trace)
      rewrite run-eq =
    catchLeft-blame-complete joined? trace

  ----------------------------------------------------------------------
  -- Completeness lifted to the compiled double interpreter
  ----------------------------------------------------------------------

  doubleInterpretCompiled-catches-right :
    (joined? :
      ∀ W V W′ V′ → Dec (Joined W V W′ V′)) →
    ∀ {N N′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0}
      {index catch-up terminal-index W V W₀′ W′ V′} →
    (N⊑N′ :
      [] ∣ 0 ∣ 0 ∣ [] ∣ []
        ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p) →
    run N index ≡ returned W V →
    run N′ index ≡ timed W₀′ →
    RightCatchUpTrace N′ W V
      index catch-up terminal-index W′ V′ →
    IsSynchronizedAt index terminal-index W V W′ V′
      (doubleInterpretCompiled joined? N⊑N′ index catch-up)
  doubleInterpretCompiled-catches-right
      joined? N⊑N′ left-eq right-eq trace
      rewrite left-eq | right-eq =
    catchRight-complete joined? trace

  doubleInterpretCompiled-catches-left :
    (joined? :
      ∀ W V W′ V′ → Dec (Joined W V W′ V′)) →
    ∀ {N N′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0}
      {index catch-up terminal-index W₀ W W′ V V′} →
    (N⊑N′ :
      [] ∣ 0 ∣ 0 ∣ [] ∣ []
        ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p) →
    run N index ≡ timed W₀ →
    run N′ index ≡ returned W′ V′ →
    LeftCatchUpTrace N W′ V′
      index catch-up terminal-index W V →
    IsSynchronizedAt terminal-index index W V W′ V′
      (doubleInterpretCompiled joined? N⊑N′ index catch-up)
  doubleInterpretCompiled-catches-left
      joined? N⊑N′ left-eq right-eq trace
      rewrite left-eq | right-eq =
    catchLeft-complete joined? trace

  doubleInterpretCompiled-catches-left-blame :
    (joined? :
      ∀ W V W′ V′ → Dec (Joined W V W′ V′)) →
    ∀ {N N′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0}
      {index catch-up terminal-index W₀ W W′ V′} →
    (N⊑N′ :
      [] ∣ 0 ∣ 0 ∣ [] ∣ []
        ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p) →
    run N index ≡ timed W₀ →
    run N′ index ≡ returned W′ V′ →
    LeftBlameCatchUpTrace N
      index catch-up terminal-index W →
    IsLeftBlameAt terminal-index index W W′ V′
      (doubleInterpretCompiled joined? N⊑N′ index catch-up)
  doubleInterpretCompiled-catches-left-blame
      joined? N⊑N′ left-eq right-eq trace
      rewrite left-eq | right-eq =
    catchLeft-blame-complete joined? trace

  ----------------------------------------------------------------------
  -- Completeness lifted to the source-level double interpreter
  ----------------------------------------------------------------------

  doubleInterpret-catches-right :
    (joined? :
      ∀ W V W′ V′ → Dec (Joined W V W′ V′)) →
    ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0}
      {index catch-up terminal-index W V W₀′ W′ V′} →
    (M⊑M′ :
      [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
    run (compiled-leftᴰ M⊑M′) index ≡ returned W V →
    run (compiled-rightᴰ M⊑M′) index ≡ timed W₀′ →
    RightCatchUpTrace (compiled-rightᴰ M⊑M′) W V
      index catch-up terminal-index W′ V′ →
    IsSynchronizedAt index terminal-index W V W′ V′
      (doubleInterpret joined? M⊑M′ index catch-up)
  doubleInterpret-catches-right
      joined? M⊑M′ left-eq right-eq trace
      rewrite left-eq | right-eq =
    catchRight-complete joined? trace

  doubleInterpret-catches-left :
    (joined? :
      ∀ W V W′ V′ → Dec (Joined W V W′ V′)) →
    ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0}
      {index catch-up terminal-index W₀ W W′ V V′} →
    (M⊑M′ :
      [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
    run (compiled-leftᴰ M⊑M′) index ≡ timed W₀ →
    run (compiled-rightᴰ M⊑M′) index ≡ returned W′ V′ →
    LeftCatchUpTrace (compiled-leftᴰ M⊑M′) W′ V′
      index catch-up terminal-index W V →
    IsSynchronizedAt terminal-index index W V W′ V′
      (doubleInterpret joined? M⊑M′ index catch-up)
  doubleInterpret-catches-left
      joined? M⊑M′ left-eq right-eq trace
      rewrite left-eq | right-eq =
    catchLeft-complete joined? trace

  doubleInterpret-catches-left-blame :
    (joined? :
      ∀ W V W′ V′ → Dec (Joined W V W′ V′)) →
    ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0}
      {index catch-up terminal-index W₀ W W′ V′} →
    (M⊑M′ :
      [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
    run (compiled-leftᴰ M⊑M′) index ≡ timed W₀ →
    run (compiled-rightᴰ M⊑M′) index ≡ returned W′ V′ →
    LeftBlameCatchUpTrace (compiled-leftᴰ M⊑M′)
      index catch-up terminal-index W →
    IsLeftBlameAt terminal-index index W W′ V′
      (doubleInterpret joined? M⊑M′ index catch-up)
  doubleInterpret-catches-left-blame
      joined? M⊑M′ left-eq right-eq trace
      rewrite left-eq | right-eq =
    catchLeft-blame-complete joined? trace

  ----------------------------------------------------------------------
  -- A fixed zero catch-up budget cannot establish synchronization
  ----------------------------------------------------------------------

  catchRight-zero :
    (joined? :
      ∀ W V W′ V′ → Dec (Joined W V W′ V′)) →
    ∀ right-term left-index right-index W V W′ →
    catchRight joined? right-term left-index right-index
      W V W′ zero
      ≡ left-ahead left-index right-index W V W′
  catchRight-zero joined? right-term left-index right-index W V W′ =
    refl

  catchLeft-zero :
    (joined? :
      ∀ W V W′ V′ → Dec (Joined W V W′ V′)) →
    ∀ left-term left-index right-index W W′ V′ →
    catchLeft joined? left-term left-index right-index
      W W′ V′ zero
      ≡ right-ahead left-index right-index W W′ V′
  catchLeft-zero joined? left-term left-index right-index W W′ V′ =
    refl
