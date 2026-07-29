module InterpreterTermNarrowing where

-- File Charter:
--   * Public surface for reduction-free interpreter source-term narrowing.
--   * Exposes structural closure, compiler-image exclusions, world weakening,
--     and endpoint typing with their claims stated at the use site.
--   * Delegates proof scripts to `proof.InterpreterTermNarrowingProof`.

open import Data.Nat using (suc)
open import Data.Empty using (⊥)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Interpreter using (Value; closeValue; closure)
import InterpreterCoercionNarrowing as ICN
open import InterpreterTermNarrowingCore public
open import InterpreterValueNarrowing
import NuTermImprecision as NTI
import NuTerms as N
import TermTyping as TT
open import Types
import proof.InterpreterTermNarrowingProof as Proof
import proof.InterpreterTermShapeProof as ShapeProof

interpreterNarrowingLeaves : NarrowingLeaves
interpreterNarrowingLeaves =
  record
    { BodyNarrowing = InterpreterBodyNarrowing
    ; TypeNarrowing = ICN.InterpreterTypeNarrowing
    ; GroundNarrowing = ICN.InterpreterGroundNarrowing
    ; CoercionNarrowing = ICN.InterpreterCoercionNarrowing
    ; LeftTaggedBoundary = ICN.LeftTaggedBoundary
    ; RightTaggedBoundary = ICN.RightTaggedBoundary
    ; LeftFunctionProxyBoundary = ICN.LeftFunctionProxyBoundary
    ; RightFunctionProxyBoundary = ICN.RightFunctionProxyBoundary
    ; LeftForallProxyBoundary = ICN.LeftForallProxyBoundary
    ; RightForallProxyBoundary = ICN.RightForallProxyBoundary
    ; LeftGeneralizationBoundary = ICN.LeftGeneralizationBoundary
    ; RightGeneralizationBoundary = ICN.RightGeneralizationBoundary
    }

interpreter-term-no-bullet :
  ∀ {M} →
  InterpreterTerm M →
  N.No• M
interpreter-term-no-bullet =
  Proof.interpreter-term-no-bullet

interpreter-type-abstraction-value :
  ∀ {V} →
  InterpreterTerm (N.Λ V) →
  N.Value V
interpreter-type-abstraction-value =
  Proof.interpreter-type-abstraction-value

interpreter-term-not-blame :
  InterpreterTerm N.blame →
  ⊥
interpreter-term-not-blame =
  Proof.interpreter-term-not-blame

interpreter-term-type-rename :
  ∀ ρ {M} →
  InterpreterTerm M →
  InterpreterTerm (N.renameᵗᵐ ρ M)
interpreter-term-type-rename =
  Proof.interpreter-term-type-rename

interpreter-term-type-name-substitute :
  ∀ α {M} →
  InterpreterTerm M →
  InterpreterTerm (N.renameᵗᵐ (singleRenameᵗ α) M)
interpreter-term-type-name-substitute α =
  Proof.interpreter-term-type-rename (singleRenameᵗ α)

interpreter-term-rename :
  ∀ ρ {M} →
  InterpreterTerm M →
  InterpreterTerm (N.renameˣᵐ ρ M)
interpreter-term-rename =
  Proof.interpreter-term-rename

interpreter-term-weaken :
  ∀ {M} →
  InterpreterTerm M →
  InterpreterTerm (N.renameˣᵐ suc M)
interpreter-term-weaken =
  Proof.interpreter-term-rename suc

interpreter-term-substitute :
  ∀ {σ M} →
  (∀ x → InterpreterTerm (σ x)) →
  InterpreterTerm M →
  InterpreterTerm (N.substˣᵐ σ M)
interpreter-term-substitute =
  Proof.interpreter-term-substitute

interpreter-narrowing-source-term :
  ∀ {N N′} →
  InterpreterTermShape N N′ →
  InterpreterTerm N
interpreter-narrowing-source-term =
  ShapeProof.shape-source-interpreter-term

interpreter-narrowing-target-term :
  ∀ {N N′} →
  InterpreterTermShape N N′ →
  InterpreterTerm N′
interpreter-narrowing-target-term =
  ShapeProof.shape-target-interpreter-term

interpreter-narrowing-type-rename :
  ∀ ρ {N N′} →
  InterpreterTermShape N N′ →
  InterpreterTermShape
    (N.renameᵗᵐ ρ N)
    (N.renameᵗᵐ ρ N′)
interpreter-narrowing-type-rename =
  ShapeProof.shape-type-rename

interpreter-narrowing-type-name-substitute :
  ∀ α {N N′} →
  InterpreterTermShape N N′ →
  InterpreterTermShape
    (N.renameᵗᵐ (singleRenameᵗ α) N)
    (N.renameᵗᵐ (singleRenameᵗ α) N′)
interpreter-narrowing-type-name-substitute α =
  ShapeProof.shape-type-rename (singleRenameᵗ α)

interpreter-narrowing-rename :
  ∀ ρ {N N′} →
  InterpreterTermShape N N′ →
  InterpreterTermShape
    (N.renameˣᵐ ρ N)
    (N.renameˣᵐ ρ N′)
interpreter-narrowing-rename =
  ShapeProof.shape-rename

interpreter-narrowing-weaken :
  ∀ {N N′} →
  InterpreterTermShape N N′ →
  InterpreterTermShape
    (N.renameˣᵐ suc N)
    (N.renameˣᵐ suc N′)
interpreter-narrowing-weaken =
  ShapeProof.shape-rename suc

interpreter-narrowing-substitute :
  ∀ {σ σ′ N N′} →
  (∀ x → InterpreterTermShape (σ x) (σ′ x)) →
  InterpreterTermShape N N′ →
  InterpreterTermShape
    (N.substˣᵐ σ N)
    (N.substˣᵐ σ′ N′)
interpreter-narrowing-substitute =
  ShapeProof.shape-substitute

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
open-interpreter-narrowing-world-weaken =
  Proof.open-interpreter-narrowing-world-weaken

open-interpreter-narrowing-source-typing :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γ N N′ A B p}
    {R : WorldRelation W W′} →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γ N N′ A B p →
  TT._∣_∣_⊢_⦂_
    Δᴸ (NTI.leftStoreⁱ ρ) (NTI.leftCtxⁱ γ) N A
open-interpreter-narrowing-source-typing =
  Proof.open-interpreter-narrowing-source-typing

open-interpreter-narrowing-target-typing :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γ N N′ A B p}
    {R : WorldRelation W W′} →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γ N N′ A B p →
  TT._∣_∣_⊢_⦂_
    Δᴿ (NTI.rightStoreⁱ ρ) (NTI.rightCtxⁱ γ) N′ B
open-interpreter-narrowing-target-typing =
  Proof.open-interpreter-narrowing-target-typing

module InterpreterValues =
  ValueNarrowing interpreterNarrowingLeaves

open InterpreterValues

close-lambda-bodies-preserve-narrowing :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p}
    {R : WorldRelation W W′}
    {γ γ′ θ θ′} →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p →
  EnvironmentNarrowing R γ γ′ →
  TypeEnvironmentNarrowing R θ θ′ →
  ValueNarrowing R
    (closure N γ θ)
    (closure N′ γ′ θ′)
close-lambda-bodies-preserve-narrowing
    N~N′ γ~γ′ θ~θ′ =
  closure⊑ (body-narrowing N~N′) γ~γ′ θ~θ′

close-related-lambdas-preserve-body-narrowing :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p}
    {R : WorldRelation W W′}
    {γ γ′ θ θ′} →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p →
  EnvironmentNarrowing R γ γ′ →
  TypeEnvironmentNarrowing R θ θ′ →
  Σ[ V ∈ Value ] Σ[ V′ ∈ Value ]
    (closeValue (N.ƛ N) γ θ ≡ just V) ×
    (closeValue (N.ƛ N′) γ′ θ′ ≡ just V′) ×
    ValueNarrowing R V V′
close-related-lambdas-preserve-body-narrowing
    N~N′ γ~γ′ θ~θ′ =
  closure _ _ _ , closure _ _ _ ,
  refl , refl ,
  close-lambda-bodies-preserve-narrowing
    N~N′ γ~γ′ θ~θ′
