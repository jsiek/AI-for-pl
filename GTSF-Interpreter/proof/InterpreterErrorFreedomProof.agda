module proof.InterpreterErrorFreedomProof where

-- File Charter:
--   * EXPERIMENTAL: origin retired the compiler relation consumed here; O35
--     will reconnect these compiled-endpoint corollaries to live QTI.
--   * Derives error freedom for both compiler endpoints of a closed gradual
--     narrowing derivation.
--   * Uses the compiler's synchronized shape certificate and its ordinary
--     typing output.
--   * Depends only on compilation and direct interpreter typing, never on
--     reduction.

open import Data.List using ([])
open import Data.Nat using (zero)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Compile using (compileᵀ)
open import Narrowing.CompileInterpreterNarrowing using
  (compile-preserves-interpreter-narrowing)
open import Ctx using (ctxWf-[])
import GradualTermImprecision as GTI
open import GradualTermImprecision using
  (_∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter using (Error; failed; run)
open import Narrowing.InterpreterTermNarrowing using
  (interpreter-narrowing-source-term;
   interpreter-narrowing-target-term; term-shape)
open import proof.InterpreterErrorFreedomCore using
  (closed-run-never-fails)
open import TermTyping using (forget)
open import Types

compiled-source-never-fails :
  ∀ {M M′ A B}
    {p : [] ∣ zero ⊢ A ⊑ B ⊣ zero} →
  (M⊑M′ : [] ∣ zero ∣ zero ∣ []
    ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  ∀ n U e →
  let
    M⊢ = GTI.gradual-term-imprecision-source-typing M⊑M′
    N = proj₁ (compileᵀ ctxWf-[] M⊢)
  in
  run N n ≢ failed U e
compiled-source-never-fails M⊑M′ n U e =
  closed-run-never-fails n
    (interpreter-narrowing-source-term
      (term-shape
        (compile-preserves-interpreter-narrowing
          ctxWf-[] ctxWf-[] M⊑M′)))
    (forget
      (proj₂
        (compileᵀ ctxWf-[]
          (GTI.gradual-term-imprecision-source-typing M⊑M′))))

compiled-target-never-fails :
  ∀ {M M′ A B}
    {p : [] ∣ zero ⊢ A ⊑ B ⊣ zero} →
  (M⊑M′ : [] ∣ zero ∣ zero ∣ []
    ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  ∀ n U e →
  let
    M′⊢ = GTI.gradual-term-imprecision-target-typing M⊑M′
    N′ = proj₁ (compileᵀ ctxWf-[] M′⊢)
  in
  run N′ n ≢ failed U e
compiled-target-never-fails M⊑M′ n U e =
  closed-run-never-fails n
    (interpreter-narrowing-target-term
      (term-shape
        (compile-preserves-interpreter-narrowing
          ctxWf-[] ctxWf-[] M⊑M′)))
    (forget
      (proj₂
        (compileᵀ ctxWf-[]
          (GTI.gradual-term-imprecision-target-typing M⊑M′))))
