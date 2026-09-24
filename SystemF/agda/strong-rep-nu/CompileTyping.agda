module strong-rep-nu.CompileTyping where

-- File Charter:
--   * THE ELABORATION THEOREMS: `compile` (strong-rep-nu.Compile)
--     preserves typing, and a compiled closed source program is type
--     safe in the run-time language.  Thin wrappers around
--     strong-rep-nu.proof.Compile, stated explicitly.

open import Data.Nat using (ℕ)
open import Data.List using ([]; length)
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx using (wf-empty)
open import strong-rep-nu.Terms
open import strong-rep-nu.Reduction
open import strong-rep-nu.Source
open import strong-rep-nu.Compile
open import strong-rep-nu.TypeSafety using (type-safety)
open import strong-rep-nu.proof.Preserve using (CtxWf; CtxWf-[])
import strong-rep-nu.proof.Compile as C

-- compile preserves typing on any run-time context with as many live
-- names as the source has type variables
compile-⊢ : ∀ {n Δ Γ M A}
  → WfCtx Δ
  → CtxWf Δ Γ
  → length (names Δ) ≡ n
  → (d : n ∣ Γ ⊢ˢ M ⦂ A)
    ----------------------------
  → Δ ∣ Γ ⊢ compile d ⦂ A
compile-⊢ = C.compile-⊢

compile-closed : ∀ {M A}
  → (d : 0 ∣ [] ⊢ˢ M ⦂ A)
    ----------------------------
  → empty ∣ [] ⊢ compile d ⦂ A
compile-closed d = C.compile-⊢ wf-empty CtxWf-[] refl d

-- a compiled closed program never gets stuck
compile-safe : ∀ {M A N}
  → (d : 0 ∣ [] ⊢ˢ M ⦂ A)
  → (r : empty ⊢ compile d -→* N)
    ---------------------------------------------
  → Value N
    ⊎ (Σ[ N′ ∈ Term ] Σ[ δ ∈ Alloc ] (runCtx r ⊢ N -→ N′ ∣ δ))
compile-safe d r = type-safety wf-empty (compile-closed d) r
