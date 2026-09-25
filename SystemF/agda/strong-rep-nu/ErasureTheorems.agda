module strong-rep-nu.ErasureTheorems where

-- File Charter:
--   * THE ERASURE THEOREMS, STATED EXPLICITLY IN ONE PLACE:
--     `ErasureTyping`, `ErasureSimulation`, `ErasureStutter`,
--     `ErasureStep`, `ErasureRun`, `ErasureReflection`,
--     `CompiledRunErases`, `EraseCompileAt`, `EraseCompile`.
--   * NO PROOFS: every right-hand side delegates to proof/Erasure*.
--   * The erasure itself is strong-rep-nu.Erasure; the design and the
--     rulings are notes/ErasureSketch.md.

open import Data.List using ([])
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ-syntax; ∃-syntax)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.Terms using (Term; _∣_⊢_⦂_)
open import strong-rep-nu.Reduction
open import strong-rep-nu.Source using (_∣_⊢ˢ_⦂_)
open import strong-rep-nu.SourceReduction
open import strong-rep-nu.Compile using (compile)
open import strong-rep-nu.Erasure
import strong-rep-nu.proof.ErasureCompile as EC
import strong-rep-nu.proof.ErasureTyping as ET
import strong-rep-nu.proof.ErasureSim as ES
import strong-rep-nu.proof.ErasureReflect as ER

------------------------------------------------------------------------
-- 1. The statements
------------------------------------------------------------------------

-- TYPING.  Erasure preserves typing, at the erased type, over the count
-- of abstract cells.
ErasureTyping : Set
ErasureTyping = ∀ {Δ Γ M A}
  → WfCtx Δ
  → Δ ∣ Γ ⊢ M ⦂ A
    ------------------------------------------------------------
  → srcScope (reps Δ) ∣ eraseCtx Δ Γ ⊢ˢ erase Δ M ⦂ eraseTy Δ A

-- SIMULATION (Blame for All, Prop. 1).  The contractum is erased at the
-- context it lives at, `apply δ Δ`.
ErasureSimulation : Set
ErasureSimulation = ∀ {Δ M M′ A δ}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→ M′ ∣ δ
    --------------------------------------------------------------
  → (erase Δ M ≡ erase (apply δ Δ) M′)
    ⊎ (erase Δ M ⟶ˢ erase (apply δ Δ) M′)

-- A stutter leaves the erasure unchanged …
ErasureStutter : Set
ErasureStutter = ∀ {Δ M M′ A δ}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → (r : Δ ⊢ M -→ M′ ∣ δ)
  → Stutter r
    ---------------------------------------
  → erase Δ M ≡ erase (apply δ Δ) M′

-- … and every other step is exactly one source step.
-- (Together they imply ErasureSimulation.)
ErasureStep : Set
ErasureStep = ∀ {Δ M M′ A δ}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → (r : Δ ⊢ M -→ M′ ∣ δ)
  → ¬ Stutter r
    ---------------------------------------
  → erase Δ M ⟶ˢ erase (apply δ Δ) M′

-- RUNS.  (From ErasureSimulation and preservation.)
ErasureRun : Set
ErasureRun = ∀ {Δ M N A}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → (r : Δ ⊢ M -→* N)
    ----------------------------------
  → erase Δ M ⟶ˢ* erase (runCtx r) N

-- REFLECTION (the converse; not in BfA).  Every source step of the
-- erasure is matched by a finite run, stutters then one β-rule.  It
-- needs the stutter rules (Wrap, Merge, Id) to terminate.
ErasureReflection : Set
ErasureReflection = ∀ {Δ M A N}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → erase Δ M ⟶ˢ N
    -------------------------------------------------------------
  → ∃[ M′ ] Σ[ r ∈ Δ ⊢ M -→* M′ ] (erase (runCtx r) M′ ≡ N)

-- A compiled program's run is its own source run, with stutters.
-- (From EraseCompile and ErasureRun.)
CompiledRunErases : Set
CompiledRunErases = ∀ {M A N}
  → (d : 0 ∣ [] ⊢ˢ M ⦂ A)
  → (r : empty ⊢ compile d -→* N)
    ------------------------------
  → M ⟶ˢ* erase (runCtx r) N


-- AT ANY CONTEXT: erasing the compiled term replaces each type variable
-- by what the context says it denotes.
-- AT ANY CONTEXT: erasing the compiled term replaces each type variable
-- by what the context says it denotes.
EraseCompileAt : Set
EraseCompileAt = ∀ (Δ : Ctxᵗ) {n Γ M A} (d : n ∣ Γ ⊢ˢ M ⦂ A)
  → erase Δ (compile d) ≡ substˢᵗ (nameσ Δ) M

EraseCompile : Set
EraseCompile = ∀ {n Γ M A} (d : n ∣ Γ ⊢ˢ M ⦂ A)
  → erase (idCtx n) (compile d) ≡ M
------------------------------------------------------------------------
-- 2. The theorems
------------------------------------------------------------------------

erasure-typing : ErasureTyping
erasure-typing = ET.erasure-typing

erasure-stutter : ErasureStutter
erasure-stutter = ES.erasure-stutter

erasure-step : ErasureStep
erasure-step = ES.erasure-step

erasure-simulation : ErasureSimulation
erasure-simulation = ES.erasure-sim

erasure-run : ErasureRun
erasure-run = ES.erasure-run

erasure-reflection : ErasureReflection
erasure-reflection = ER.erasure-reflection

compiled-run-erases : CompiledRunErases
compiled-run-erases = ES.compiled-run-erases

erase-compile-at : EraseCompileAt
erase-compile-at = EC.erase-compile-at

erase-compile : EraseCompile
erase-compile = EC.erase-compile
