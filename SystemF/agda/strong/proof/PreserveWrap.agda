module strong.proof.PreserveWrap where

-- Strong System F v8 — preservation for `Wrap`.
--
--   ((λx:A₀. N) ⟨ c ⟩) · W  -→  ((λx:A₀. N) · (W ⟨ c₁ ⟩)) ⟨ c₂ ⟩
--                                       if arr A₀ c = (c₁ , c₂)
--
-- `arr` splits the conversion; `arr-typing` types both halves, and the
-- CONTRAVARIANT one ends at the λ's own annotation, which is exactly
-- the type the argument's new boundary must deliver.  In v7 this case
-- additionally needed the dual scope `-χ` and the argument weakened
-- under the store.

open import Data.List using (List; [])
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.Ctx
open import strong.Conversion
open import strong.ConversionReduction using (arr)
open import strong.Terms
open import strong.proof.ArrTyping using (arr-typing)

preserve-Wrap : ∀ {Sg Δ A₀ N c W c₁ c₂ B}
  → NameFn Δ
  → arr A₀ c ≡ just (c₁ , c₂)
  → Sg ∣ Δ ∣ [] ⊢ ((ƛ A₀ ∙ N) ⟨ c ⟩) · W ⦂ B
  → Sg ∣ Δ ∣ [] ⊢ ((ƛ A₀ ∙ N) · (W ⟨ c₁ ⟩)) ⟨ c₂ ⟩ ⦂ B
preserve-Wrap nf arr-eq (⊢· (⊢⟨⟩ nf-c (⊢ƛ wfA ⊢N) conv) ⊢W)
  with arr-typing nf conv arr-eq
preserve-Wrap nf arr-eq (⊢· (⊢⟨⟩ nf-c (⊢ƛ wfA ⊢N) conv) ⊢W)
  | ty₁ , ty₂ , nf₁ , nf₂ =
  ⊢⟨⟩ nf₂ (⊢· (⊢ƛ wfA ⊢N) (⊢⟨⟩ nf₁ ⊢W ty₁)) ty₂
