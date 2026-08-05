module Narrowing.InterpreterTagNarrowing where

-- File Charter:
--   * Relates runtime ground tags through static type narrowing and concrete
--     type-environment realization.
--   * Proves successful paired tag construction for all ground-type forms.
--   * Uses no coercion execution or reduction semantics.

open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Empty
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; Σ-syntax)

open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterTagNarrowingCore public
open import Runtime.InterpreterTypeEnvironmentRealization
import proof.InterpreterTagNarrowingProof as Proof
open import Types

open TagRelatedWorlds

tagOf-narrowing :
  ∀ {W W′ Φ Δᴸ Δᴿ θ θ′ G H}
    {R : WorldRelation W W′}
    (gG : Ground G) (gH : Ground H) →
  TypeEnvironmentRealization R Φ θ θ′ →
  Φ ∣ Δᴸ ⊢ G ⊑ H ⊣ Δᴿ →
  Σ[ tag ∈ Tag ]
  Σ[ tag′ ∈ Tag ]
    tagOf θ gG ≡ just tag ×
    tagOf θ′ gH ≡ just tag′ ×
    TagNarrowing R tag tag′
tagOf-narrowing =
  Proof.tagOf-narrowing

tag-match-forward :
  ∀ {W W′ expected expected′ actual actual′}
    {R : WorldRelation W W′} →
  TagNarrowing R expected expected′ →
  TagNarrowing R actual actual′ →
  expected ≡ actual →
  expected′ ≡ actual′
tag-match-forward =
  Proof.tag-match-forward

tag-match-backward :
  ∀ {W W′ expected expected′ actual actual′}
    {R : WorldRelation W W′} →
  TagNarrowing R expected expected′ →
  TagNarrowing R actual actual′ →
  expected′ ≡ actual′ →
  expected ≡ actual
tag-match-backward =
  Proof.tag-match-backward

target-tag-mismatch-reflects :
  ∀ {W W′ expected expected′ actual actual′}
    {R : WorldRelation W W′} →
  TagNarrowing R expected expected′ →
  TagNarrowing R actual actual′ →
  (expected′ ≡ actual′ → Data.Empty.⊥) →
  expected ≡ actual →
  Data.Empty.⊥
target-tag-mismatch-reflects =
  Proof.target-tag-mismatch-reflects
