module proof.InterpreterTermShapeProof where

-- File Charter:
--   * Proves endpoint image, renaming, and substitution properties of the
--     synchronized interpreter term-shape relation.
--   * Handles compiler-produced left-only polymorphic forms explicitly.
--   * Does not inspect the broader runtime-oriented static certificate.

open import Data.Nat using (zero; suc)

open import Narrowing.InterpreterTermNarrowingCore
import NuTerms as N
open import Types
open import proof.InterpreterTermNarrowingProof using
  ( interpreter-term-rename
  ; interpreter-term-substitute
  ; interpreter-term-type-rename
  )
open import SmallStepInterface.InterpreterTermShapeProperties public using
  (shape-source-interpreter-term; shape-target-interpreter-term)
open import proof.NuTermProperties using
  ( renameᵗᵐ-preserves-Value
  ; renameˣᵐ-preserves-Value
  ; substˣᵐ-preserves-Value
  )

shape-type-rename :
  ∀ ρ {N N′} →
  InterpreterTermShape N N′ →
  InterpreterTermShape
    (N.renameᵗᵐ ρ N)
    (N.renameᵗᵐ ρ N′)
shape-type-rename ρ (variable-shape x) =
  variable-shape x
shape-type-rename ρ (closure-shape N~N′) =
  closure-shape (shape-type-rename ρ N~N′)
shape-type-rename ρ (application-shape L~L′ M~M′) =
  application-shape
    (shape-type-rename ρ L~L′)
    (shape-type-rename ρ M~M′)
shape-type-rename ρ
    (paired-type-abstraction-shape vV vV′ V-ok V′-ok) =
  paired-type-abstraction-shape
    (renameᵗᵐ-preserves-Value (extᵗ ρ) vV)
    (renameᵗᵐ-preserves-Value (extᵗ ρ) vV′)
    (interpreter-term-type-rename (extᵗ ρ) V-ok)
    (interpreter-term-type-rename (extᵗ ρ) V′-ok)
shape-type-rename ρ
    (left-type-abstraction-shape vV V-ok N′-ok) =
  left-type-abstraction-shape
    (renameᵗᵐ-preserves-Value (extᵗ ρ) vV)
    (interpreter-term-type-rename (extᵗ ρ) V-ok)
    (interpreter-term-type-rename ρ N′-ok)
shape-type-rename ρ (paired-instantiation-shape L~L′) =
  paired-instantiation-shape (shape-type-rename ρ L~L′)
shape-type-rename ρ (left-instantiation-shape L~L′) =
  left-instantiation-shape (shape-type-rename ρ L~L′)
shape-type-rename ρ (constant-shape κ) =
  constant-shape κ
shape-type-rename ρ (primitive-shape op L~L′ M~M′) =
  primitive-shape op
    (shape-type-rename ρ L~L′)
    (shape-type-rename ρ M~M′)
shape-type-rename ρ
    (paired-coercion-application-shape M~M′) =
  paired-coercion-application-shape
    (shape-type-rename ρ M~M′)
shape-type-rename ρ
    (left-coercion-application-shape M~M′) =
  left-coercion-application-shape
    (shape-type-rename ρ M~M′)
shape-type-rename ρ
    (right-coercion-application-shape M~M′) =
  right-coercion-application-shape
    (shape-type-rename ρ M~M′)

shape-rename :
  ∀ ρ {N N′} →
  InterpreterTermShape N N′ →
  InterpreterTermShape
    (N.renameˣᵐ ρ N)
    (N.renameˣᵐ ρ N′)
shape-rename ρ (variable-shape x) =
  variable-shape (ρ x)
shape-rename ρ (closure-shape N~N′) =
  closure-shape (shape-rename (N.extʳ ρ) N~N′)
shape-rename ρ (application-shape L~L′ M~M′) =
  application-shape
    (shape-rename ρ L~L′)
    (shape-rename ρ M~M′)
shape-rename ρ
    (paired-type-abstraction-shape vV vV′ V-ok V′-ok) =
  paired-type-abstraction-shape
    (renameˣᵐ-preserves-Value ρ vV)
    (renameˣᵐ-preserves-Value ρ vV′)
    (interpreter-term-rename ρ V-ok)
    (interpreter-term-rename ρ V′-ok)
shape-rename ρ
    (left-type-abstraction-shape vV V-ok N′-ok) =
  left-type-abstraction-shape
    (renameˣᵐ-preserves-Value ρ vV)
    (interpreter-term-rename ρ V-ok)
    (interpreter-term-rename ρ N′-ok)
shape-rename ρ (paired-instantiation-shape L~L′) =
  paired-instantiation-shape (shape-rename ρ L~L′)
shape-rename ρ (left-instantiation-shape L~L′) =
  left-instantiation-shape (shape-rename ρ L~L′)
shape-rename ρ (constant-shape κ) =
  constant-shape κ
shape-rename ρ (primitive-shape op L~L′ M~M′) =
  primitive-shape op
    (shape-rename ρ L~L′)
    (shape-rename ρ M~M′)
shape-rename ρ (paired-coercion-application-shape M~M′) =
  paired-coercion-application-shape (shape-rename ρ M~M′)
shape-rename ρ (left-coercion-application-shape M~M′) =
  left-coercion-application-shape (shape-rename ρ M~M′)
shape-rename ρ (right-coercion-application-shape M~M′) =
  right-coercion-application-shape (shape-rename ρ M~M′)

shape-substitute :
  ∀ {σ σ′ N N′} →
  (∀ x → InterpreterTermShape (σ x) (σ′ x)) →
  InterpreterTermShape N N′ →
  InterpreterTermShape
    (N.substˣᵐ σ N)
    (N.substˣᵐ σ′ N′)
shape-substitute σ~σ′ (variable-shape x) =
  σ~σ′ x
shape-substitute σ~σ′ (closure-shape N~N′) =
  closure-shape (shape-substitute extended N~N′)
  where
    extended :
      ∀ x →
      InterpreterTermShape (N.extˢˣ _ x) (N.extˢˣ _ x)
    extended zero =
      variable-shape zero
    extended (suc x) =
      shape-rename suc (σ~σ′ x)
shape-substitute {σ = σ} {σ′ = σ′} σ~σ′
    (application-shape L~L′ M~M′) =
  application-shape
    (shape-substitute σ~σ′ L~L′)
    (shape-substitute σ~σ′ M~M′)
shape-substitute {σ = σ} {σ′ = σ′} σ~σ′
    (paired-type-abstraction-shape vV vV′ V-ok V′-ok) =
  paired-type-abstraction-shape
    (substˣᵐ-preserves-Value (N.↑ᵗᵐ σ) vV)
    (substˣᵐ-preserves-Value (N.↑ᵗᵐ σ′) vV′)
    (interpreter-term-substitute left-lifted V-ok)
    (interpreter-term-substitute right-lifted V′-ok)
  where
    left-lifted :
      ∀ x →
      InterpreterTerm (N.↑ᵗᵐ σ x)
    left-lifted x =
      interpreter-term-type-rename suc
        (shape-source-interpreter-term (σ~σ′ x))

    right-lifted :
      ∀ x →
      InterpreterTerm (N.↑ᵗᵐ σ′ x)
    right-lifted x =
      interpreter-term-type-rename suc
        (shape-target-interpreter-term (σ~σ′ x))
shape-substitute {σ = σ} {σ′ = σ′} σ~σ′
    (left-type-abstraction-shape vV V-ok N′-ok) =
  left-type-abstraction-shape
    (substˣᵐ-preserves-Value (N.↑ᵗᵐ σ) vV)
    (interpreter-term-substitute left-lifted V-ok)
    (interpreter-term-substitute right-ok N′-ok)
  where
    left-lifted :
      ∀ x →
      InterpreterTerm (N.↑ᵗᵐ σ x)
    left-lifted x =
      interpreter-term-type-rename suc
        (shape-source-interpreter-term (σ~σ′ x))

    right-ok :
      ∀ x →
      InterpreterTerm (σ′ x)
    right-ok x =
      shape-target-interpreter-term (σ~σ′ x)
shape-substitute σ~σ′ (paired-instantiation-shape L~L′) =
  paired-instantiation-shape (shape-substitute σ~σ′ L~L′)
shape-substitute σ~σ′ (left-instantiation-shape L~L′) =
  left-instantiation-shape (shape-substitute σ~σ′ L~L′)
shape-substitute σ~σ′ (constant-shape κ) =
  constant-shape κ
shape-substitute σ~σ′ (primitive-shape op L~L′ M~M′) =
  primitive-shape op
    (shape-substitute σ~σ′ L~L′)
    (shape-substitute σ~σ′ M~M′)
shape-substitute σ~σ′
    (paired-coercion-application-shape M~M′) =
  paired-coercion-application-shape
    (shape-substitute σ~σ′ M~M′)
shape-substitute σ~σ′
    (left-coercion-application-shape M~M′) =
  left-coercion-application-shape
    (shape-substitute σ~σ′ M~M′)
shape-substitute σ~σ′
    (right-coercion-application-shape M~M′) =
  right-coercion-application-shape
    (shape-substitute σ~σ′ M~M′)
