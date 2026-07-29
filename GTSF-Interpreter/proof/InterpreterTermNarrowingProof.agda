module proof.InterpreterTermNarrowingProof where

-- File Charter:
--   * Proves structural closure and source-shape exclusions for interpreter
--     terms.
--   * Proves world weakening and endpoint typing for open interpreter
--     narrowing.
--   * Uses only syntax, typing projections, and world metatheory.

open import Data.Nat using (zero; suc)
open import Data.Empty using (⊥)

open import InterpreterCoercionNarrowing
open import InterpreterTermNarrowingCore
open import InterpreterWorldNarrowing
import NuTermImprecision as NTI
import NuTerms as N
import QuotientedTermImprecision as QTI
import TermTyping as TT
open import Types
open import proof.NuTermProperties using
  ( renameᵗᵐ-preserves-Value
  ; renameˣᵐ-preserves-Value
  ; substˣᵐ-preserves-Value
  )

interpreter-term-no-bullet :
  ∀ {M} →
  InterpreterTerm M →
  N.No• M
interpreter-term-no-bullet (variable-term x) =
  N.no•-`
interpreter-term-no-bullet (closure-term M-ok) =
  N.no•-ƛ (interpreter-term-no-bullet M-ok)
interpreter-term-no-bullet (application-term L-ok M-ok) =
  N.no•-·
    (interpreter-term-no-bullet L-ok)
    (interpreter-term-no-bullet M-ok)
interpreter-term-no-bullet
    (type-abstraction-term vV V-ok) =
  N.no•-Λ (interpreter-term-no-bullet V-ok)
interpreter-term-no-bullet (instantiation-term L-ok) =
  N.no•-ν (interpreter-term-no-bullet L-ok)
interpreter-term-no-bullet (constant-term κ) =
  N.no•-$
interpreter-term-no-bullet
    (primitive-term op L-ok M-ok) =
  N.no•-⊕
    (interpreter-term-no-bullet L-ok)
    (interpreter-term-no-bullet M-ok)
interpreter-term-no-bullet
    (coercion-application-term M-ok) =
  N.no•-⟨⟩ (interpreter-term-no-bullet M-ok)

interpreter-type-abstraction-value :
  ∀ {V} →
  InterpreterTerm (N.Λ V) →
  N.Value V
interpreter-type-abstraction-value
    (type-abstraction-term vV V-ok) =
  vV

interpreter-term-not-blame :
  InterpreterTerm N.blame →
  ⊥
interpreter-term-not-blame ()

interpreter-term-type-rename :
  ∀ ρ {M} →
  InterpreterTerm M →
  InterpreterTerm (N.renameᵗᵐ ρ M)
interpreter-term-type-rename ρ (variable-term x) =
  variable-term x
interpreter-term-type-rename ρ (closure-term M-ok) =
  closure-term (interpreter-term-type-rename ρ M-ok)
interpreter-term-type-rename ρ
    (application-term L-ok M-ok) =
  application-term
    (interpreter-term-type-rename ρ L-ok)
    (interpreter-term-type-rename ρ M-ok)
interpreter-term-type-rename ρ
    (type-abstraction-term vV V-ok) =
  type-abstraction-term
    (renameᵗᵐ-preserves-Value (extᵗ ρ) vV)
    (interpreter-term-type-rename (extᵗ ρ) V-ok)
interpreter-term-type-rename ρ
    (instantiation-term L-ok) =
  instantiation-term (interpreter-term-type-rename ρ L-ok)
interpreter-term-type-rename ρ (constant-term κ) =
  constant-term κ
interpreter-term-type-rename ρ
    (primitive-term op L-ok M-ok) =
  primitive-term op
    (interpreter-term-type-rename ρ L-ok)
    (interpreter-term-type-rename ρ M-ok)
interpreter-term-type-rename ρ
    (coercion-application-term M-ok) =
  coercion-application-term
    (interpreter-term-type-rename ρ M-ok)

interpreter-term-rename :
  ∀ ρ {M} →
  InterpreterTerm M →
  InterpreterTerm (N.renameˣᵐ ρ M)
interpreter-term-rename ρ (variable-term x) =
  variable-term (ρ x)
interpreter-term-rename ρ (closure-term M-ok) =
  closure-term (interpreter-term-rename (N.extʳ ρ) M-ok)
interpreter-term-rename ρ (application-term L-ok M-ok) =
  application-term
    (interpreter-term-rename ρ L-ok)
    (interpreter-term-rename ρ M-ok)
interpreter-term-rename ρ
    (type-abstraction-term vV V-ok) =
  type-abstraction-term
    (renameˣᵐ-preserves-Value ρ vV)
    (interpreter-term-rename ρ V-ok)
interpreter-term-rename ρ (instantiation-term L-ok) =
  instantiation-term (interpreter-term-rename ρ L-ok)
interpreter-term-rename ρ (constant-term κ) =
  constant-term κ
interpreter-term-rename ρ
    (primitive-term op L-ok M-ok) =
  primitive-term op
    (interpreter-term-rename ρ L-ok)
    (interpreter-term-rename ρ M-ok)
interpreter-term-rename ρ
    (coercion-application-term M-ok) =
  coercion-application-term
    (interpreter-term-rename ρ M-ok)

interpreter-term-substitute :
  ∀ {σ M} →
  (∀ x → InterpreterTerm (σ x)) →
  InterpreterTerm M →
  InterpreterTerm (N.substˣᵐ σ M)
interpreter-term-substitute σ-ok (variable-term x) =
  σ-ok x
interpreter-term-substitute σ-ok (closure-term M-ok) =
  closure-term
    (interpreter-term-substitute extended-ok M-ok)
  where
    extended-ok :
      ∀ x →
      InterpreterTerm (N.extˢˣ _ x)
    extended-ok zero =
      variable-term zero
    extended-ok (suc x) =
      interpreter-term-rename suc (σ-ok x)
interpreter-term-substitute σ-ok
    (application-term L-ok M-ok) =
  application-term
    (interpreter-term-substitute σ-ok L-ok)
    (interpreter-term-substitute σ-ok M-ok)
interpreter-term-substitute {σ = σ} σ-ok
    (type-abstraction-term vV V-ok) =
  type-abstraction-term
    (substˣᵐ-preserves-Value (N.↑ᵗᵐ σ) vV)
    (interpreter-term-substitute lifted-ok V-ok)
  where
    lifted-ok :
      ∀ x →
      InterpreterTerm (N.↑ᵗᵐ σ x)
    lifted-ok x =
      interpreter-term-type-rename suc (σ-ok x)
interpreter-term-substitute σ-ok
    (instantiation-term L-ok) =
  instantiation-term
    (interpreter-term-substitute σ-ok L-ok)
interpreter-term-substitute σ-ok (constant-term κ) =
  constant-term κ
interpreter-term-substitute σ-ok
    (primitive-term op L-ok M-ok) =
  primitive-term op
    (interpreter-term-substitute σ-ok L-ok)
    (interpreter-term-substitute σ-ok M-ok)
interpreter-term-substitute σ-ok
    (coercion-application-term M-ok) =
  coercion-application-term
    (interpreter-term-substitute σ-ok M-ok)

open RelatedWorlds

open-interpreter-narrowing-world-weaken :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ ρ γ N N′ A B p}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  WorldExtension R S →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γ N N′ A B p →
  OpenInterpreterTermNarrowing
    S Φ Δᴸ Δᴿ ρ γ N N′ A B p
open-interpreter-narrowing-world-weaken R≤S
    (open-interpreter-narrowing N-ok N′-ok N~N′) =
  open-interpreter-narrowing N-ok N′-ok N~N′

open-interpreter-narrowing-source-typing :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γ N N′ A B p}
    {R : WorldRelation W W′} →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γ N N′ A B p →
  TT._∣_∣_⊢_⦂_
    Δᴸ (NTI.leftStoreⁱ ρ) (NTI.leftCtxⁱ γ) N A
open-interpreter-narrowing-source-typing relation =
  QTI.nu-term-imprecision-source-typing
    (static-narrowing relation)

open-interpreter-narrowing-target-typing :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γ N N′ A B p}
    {R : WorldRelation W W′} →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γ N N′ A B p →
  TT._∣_∣_⊢_⦂_
    Δᴿ (NTI.rightStoreⁱ ρ) (NTI.rightCtxⁱ γ) N′ B
open-interpreter-narrowing-target-typing relation =
  QTI.nu-term-imprecision-target-typing
    (static-narrowing relation)
