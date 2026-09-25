module strong-rep-nu.proof.ErasureCompile where

-- File Charter:
--   * COMPILE THEN ERASE: `erase-compile-at` (at any context, the
--     erasure of `compile d` is the source term with each type
--     variable replaced by what the context denotes) and its
--     `idCtx` instance `erase-compile`.  Stated in
--     strong-rep-nu.ErasureTheorems.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.Source
open import strong-rep-nu.SourceReduction
open import strong-rep-nu.Compile using (compile)
open import strong-rep-nu.Erasure
open import strong-rep-nu.proof.ErasureTypes
  using (nameσ-underΛ; substˢᵗ-cong; substˢᵗ-id)

erase-compile-at : ∀ (Δ : Ctxᵗ) {n Γ M A} (d : n ∣ Γ ⊢ˢ M ⦂ A)
  → erase Δ (compile d) ≡ substˢᵗ (nameσ Δ) M
erase-compile-at Δ ⊢ˢ$ = refl
erase-compile-at Δ ⊢ˢtrue = refl
erase-compile-at Δ ⊢ˢfalse = refl
erase-compile-at Δ (⊢ˢ` x) = refl
erase-compile-at Δ (⊢ˢƛ wA d) =
  cong (ƛ_∙_ _) (erase-compile-at Δ d)
erase-compile-at Δ (⊢ˢ· d e) =
  cong₂ _·_ (erase-compile-at Δ d) (erase-compile-at Δ e)
erase-compile-at Δ (⊢ˢΛ {N = N} v d) =
  cong Λ_ (trans (erase-compile-at (underΛ Δ) d)
                 (substˢᵗ-cong (nameσ-underΛ Δ) N))
erase-compile-at Δ (⊢ˢ[] d wA) =
  cong (_[ _ ]) (erase-compile-at Δ d)

nameσ-idCtx : ∀ n X → nameσ (idCtx n) X ≡ ` X
nameσ-idCtx zero    X       = refl
nameσ-idCtx (suc n) zero    = refl
nameσ-idCtx (suc n) (suc X) =
  trans (nameσ-underΛ (idCtx n) (suc X)) (cong ⇑ᵗ (nameσ-idCtx n X))

erase-compile : ∀ {n Γ M A} (d : n ∣ Γ ⊢ˢ M ⦂ A)
  → erase (idCtx n) (compile d) ≡ M
erase-compile {n} {M = M} d =
  trans (erase-compile-at (idCtx n) d) (substˢᵗ-id (nameσ-idCtx n) M)
