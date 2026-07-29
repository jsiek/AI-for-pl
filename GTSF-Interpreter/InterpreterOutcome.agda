module InterpreterOutcome where

-- File Charter:
--   * Classifies direct-interpreter outcomes as timeout or terminal.
--   * Provides decidable terminality and discrimination between the four
--     observable outcome forms.
--   * Depends only on the direct interpreter, never on reduction semantics.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (Dec; yes; no)

open import Interpreter

data Terminal : Outcome → Set where
  terminal-blame :
    ∀ {W} →
    Terminal (blamed W)

  terminal-error :
    ∀ {W e} →
    Terminal (failed W e)

  terminal-return :
    ∀ {W V} →
    Terminal (returned W V)

data IsTimed : Outcome → Set where
  is-timed :
    ∀ {W} →
    IsTimed (timed W)

terminal? : (o : Outcome) → Dec (Terminal o)
terminal? (timed W) = no (λ ())
terminal? (blamed W) = yes terminal-blame
terminal? (failed W e) = yes terminal-error
terminal? (returned W V) = yes terminal-return

classifyOutcome : (o : Outcome) → IsTimed o ⊎ Terminal o
classifyOutcome (timed W) = inj₁ is-timed
classifyOutcome (blamed W) = inj₂ terminal-blame
classifyOutcome (failed W e) = inj₂ terminal-error
classifyOutcome (returned W V) = inj₂ terminal-return

terminal-not-timed :
  ∀ {o W} →
  Terminal o →
  o ≢ timed W
terminal-not-timed terminal-blame ()
terminal-not-timed terminal-error ()
terminal-not-timed terminal-return ()

timed-not-terminal :
  ∀ {o W} →
  Terminal o →
  timed W ≢ o
timed-not-terminal terminal-blame ()
timed-not-terminal terminal-error ()
timed-not-terminal terminal-return ()

timed≢blamed :
  ∀ {W W′ : World} →
  _≡_ {A = Outcome} (timed W) (blamed W′) →
  ⊥
timed≢blamed ()

timed≢failed :
  ∀ {W W′ : World} {e : ErrorKind} →
  _≡_ {A = Outcome} (timed W) (failed W′ e) →
  ⊥
timed≢failed ()

timed≢returned :
  ∀ {W W′ : World} {V : Value} →
  _≡_ {A = Outcome} (timed W) (returned W′ V) →
  ⊥
timed≢returned ()

blamed≢failed :
  ∀ {W W′ : World} {e : ErrorKind} →
  _≡_ {A = Outcome} (blamed W) (failed W′ e) →
  ⊥
blamed≢failed ()

blamed≢returned :
  ∀ {W W′ : World} {V : Value} →
  _≡_ {A = Outcome} (blamed W) (returned W′ V) →
  ⊥
blamed≢returned ()

failed≢returned :
  ∀ {W W′ : World} {e : ErrorKind} {V : Value} →
  _≡_ {A = Outcome} (failed W e) (returned W′ V) →
  ⊥
failed≢returned ()

timed-terminal-absurd :
  ∀ {o W} →
  timed W ≡ o →
  Terminal o →
  ⊥
timed-terminal-absurd eq terminal =
  timed-not-terminal terminal eq
