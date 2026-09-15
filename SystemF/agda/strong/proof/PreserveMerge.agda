module strong.proof.PreserveMerge where

-- Strong System F v8 — preservation for `Merge`.
--
--   (M ⟨ c ⟩) ⟨ d ⟩  -→  M ⟨ c ⨟ d ⟩
--
-- The rule does NOTHING but compose, and the typing follows the rule:
-- the inner boundary's conversion runs from the body's type out to the
-- outer boundary's interior, which is exactly where the outer
-- conversion starts.  `⨟-typing` chains them and `⨟-NF` supplies the
-- normal form.  In v7 this case additionally had to concatenate stores
-- and scopes and re-admit the composite scope change.

open import Data.List using (List; [])
open import strong.Types
open import strong.Ctx
open import strong.Conversion
open import strong.ConversionReduction using (_⨟_; ⨟-NF)
open import strong.Terms
open import strong.proof.CompositionTyping using (⨟-typing)

preserve-Merge : ∀ {Sg Δ Γ M c d C}
  → NameFn Δ
  → Sg ∣ Δ ∣ Γ ⊢ (M ⟨ c ⟩) ⟨ d ⟩ ⦂ C
  → Sg ∣ Δ ∣ Γ ⊢ M ⟨ c ⨟ d ⟩ ⦂ C
preserve-Merge {c = c} {d = d} nf
  (⊢⟨⟩ nf-d (⊢⟨⟩ nf-c ⊢M conv-c) conv-d) =
  ⊢⟨⟩ (⨟-NF c d) ⊢M (⨟-typing nf conv-c conv-d)
