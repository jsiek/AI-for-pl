module strong.Progress where

-- Strong System F v8 — PROGRESS, unconditionally.
--
-- `proof.Progress` discharges every case against one parameter, the
-- canonicity of a value boundary's conversion; `proof.ConvCanonicity`
-- proves that parameter.  This module ties them together and states
-- the theorem.

open import Data.List using ([])
open import Data.Product using (Σ-syntax; _,_)
open import Data.Sum using (_⊎_)

open import strong.Types using (Ty)
open import strong.Ctx using (Store; Ctxᵗ)
open import strong.Terms using (Term; Value; _∣_∣_⊢_⦂_)
open import strong.Reduction using (_∣_⊢_—→_⊣_)
open import strong.proof.ConvCanonicity using (canonicity)
import strong.proof.Progress as P

open P.Proof canonicity using () renaming (progress to progress′)

-- A closed, well-typed term is a value or takes a step, possibly
-- extending the store.
progress : ∀ {Σ Δ M A}
  → Σ ∣ Δ ∣ [] ⊢ M ⦂ A
  → Value M ⊎ (Σ[ N ∈ Term ] Σ[ Σ′ ∈ Store ] (Σ ∣ Δ ⊢ M —→ N ⊣ Σ′))
progress = progress′
