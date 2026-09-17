module strong.notes.RunToTrue where

-- The source program of `notes/SourceToTyWrapGap`, applied to an
-- argument so the whole thing can run to a literal:
--
--   (( ΛX. λf:(∀S. S→𝔹). f [X] ) [𝔹] · ( ΛS. λz:S. true )) · true  :  𝔹

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion
open import strong.ConversionReduction
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction
open import strong.notes.SourceToTyWrapGap
  using (M₀; M₁; M₂; M₃; M₄; M₅; Sg; R; c₂; W; T; int₂;
         step₁; step₂; step₃; step₄; step₅)

N₀ N₁ N₂ N₃ N₄ N₅ : Term
N₀ = M₀ · (# true)
N₁ = M₁ · (# true)
N₂ = M₂ · (# true)
N₃ = M₃ · (# true)
N₄ = M₄ · (# true)
N₅ = M₅ · (# true)

-- the first five steps, under the application
s₁ : [] ∣ ([] ∥ []) ⊢ N₀ —→ N₁ ⊣ []
s₁ = ξ-·-l step₁
s₂ : [] ∣ ([] ∥ []) ⊢ N₁ —→ N₂ ⊣ Sg
s₂ = ξ-·-l step₂
s₃ : Sg ∣ ([] ∥ []) ⊢ N₂ —→ N₃ ⊣ Sg
s₃ = ξ-·-l step₃
s₄ : Sg ∣ ([] ∥ []) ⊢ N₃ —→ N₄ ⊣ Sg
s₄ = ξ-·-l step₄
s₅ : Sg ∣ ([] ∥ []) ⊢ N₄ —→ N₅ ⊣ Sg
s₅ = ξ-·-l step₅

-- 6.  the ν discharges: β becomes the next store level
Sg′ : Store
Sg′ = Sg ∷ʳ R

N₆ : Term
N₆ = (((ƛ (` zero) ∙ (# true)) ⟨ W ⟩) [ lvl (length Sg) ]ᵃᴹ)
       ⟨ c₂ ⟩ · (# true)

s₆ : Sg ∣ ([] ∥ []) ⊢ N₅ —→ N₆ ⊣ Sg′
s₆ = ξ-·-l (ξ-⟨⟩ int₂ Alloc)

-- 7.  two boundaries meet, so `Merge` composes the conversions
W′ : Conv                      -- `W` with the ν's address discharged
W′ = ((seal zero (lvl (suc zero)) ∷ᶜ id (` zero))
       ↦ (show zero (lvl (suc zero)) ∷ᶜ id `𝔹))
     ∷ᶜ hide zero (lvl zero) ∷ᶜ id T

discharged : ((ƛ (` zero) ∙ (# true)) ⟨ W ⟩) [ lvl (length Sg) ]ᵃᴹ
           ≡ (ƛ (` zero) ∙ (# true)) ⟨ W′ ⟩
discharged = refl

nf-W′ : NF W′
nf-W′ = nf-cons (nf-fun (nf-cons nf-seal nf-id irr-id)
                        (nf-cons nf-show nf-id irr-id))
          (nf-cons nf-hide nf-id irr-id) (irr-cons refl)

v₇ : Value ((ƛ (` zero) ∙ (# true)) ⟨ W′ ⟩)
v₇ = V⟨⟩ Sƛ nf-W′ (inert-arr (` zero) refl)

N₇ : Term
N₇ = ((ƛ (` zero) ∙ (# true)) ⟨ W′ ⨟ c₂ ⟩) · (# true)

s₇ : Sg′ ∣ ([] ∥ []) ⊢ N₆ —→ N₇ ⊣ Sg′
s₇ = ξ-·-l (Merge v₇)

-- 8.  `Wrap`.  `arr` dualizes every crossing: the `id{-X:=α}` goes to
-- the ARGUMENT side as `id{+X:=α}`, and on the result side it meets the
-- `id{+X:=α}` the reveal builder left there and CANCELS.
d₁ d₂ : Conv
d₁ = seal zero (lvl zero) ∷ᶜ show zero (lvl zero)
     ∷ᶜ seal zero (lvl (suc zero)) ∷ᶜ id (` zero)
d₂ = show zero (lvl (suc zero)) ∷ᶜ id `𝔹

split : arr (` zero) (W′ ⨟ c₂) ≡ just (d₁ , d₂)
split = refl

nf-merged : NF (W′ ⨟ c₂)
nf-merged = ⨟-NF W′ c₂

v₈ : Value ((ƛ (` zero) ∙ (# true)) ⟨ W′ ⨟ c₂ ⟩)
v₈ = V⟨⟩ Sƛ nf-merged (inert-arr (` zero) split)

N₈ : Term
N₈ = ((ƛ (` zero) ∙ (# true)) · ((# true) ⟨ d₁ ⟩)) ⟨ d₂ ⟩

s₈ : Sg′ ∣ ([] ∥ []) ⊢ N₇ —→ N₈ ⊣ Sg′
s₈ = Wrap v₈ (Vs S#) split

-- 9.  the argument is a value (its conversion is inert at a variable),
-- so `Beta` fires inside the boundary
v₉ : Value ((# true) ⟨ d₁ ⟩)
v₉ = V⟨⟩ S# (nf-cons nf-seal (nf-cons nf-show
                (nf-cons nf-seal nf-id irr-id) (irr-cons refl))
              (irr-cons refl))
       (inert-var refl)

N₉ : Term
N₉ = (# true) ⟨ d₂ ⟩

s₉ : Sg′ ∣ ([] ∥ []) ⊢ N₈ —→ N₉ ⊣ Sg′
s₉ = ξ-⟨⟩ refl (Beta v₉)

-- 10.  a literal behind a ground terminator: `Const`
s₁₀ : Sg′ ∣ ([] ∥ []) ⊢ N₉ —→ (# true) ⊣ Sg′
s₁₀ = Const literal-# refl

------------------------------------------------------------------------
-- the whole run
------------------------------------------------------------------------

run : [] ∣ ([] ∥ []) ⊢ N₀ —↠ (# true) ⊣ Sg′
run = s₁ then s₂ then s₃ then s₄ then s₅ then s₆ then s₇ then s₈
        then s₉ then s₁₀ then done
