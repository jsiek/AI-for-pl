module proof.TypeSafety.notes.InstXDeterminismCounterexample where

-- File Charter:
--   * A checked counterexample to determinism for the current `InstX`.
--   * Applying `inst-⟪⟫` twice admits a non-value with a `Merge` step as
--     a `TyBeta` redex, so the enclosing `ν` has two different changes.

open import Data.List using ([])
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Types
open import Ctx
open import proof.Ctx using (wf-empty)
open import Conversion
open import Boundary
open import Terms
open import Reduction

idℕ : Conv
idℕ = ⌞ id `ℕ ⌟

all-idℕ : Conv
all-idℕ = ⌞ `∀ idℕ ⌟

poly-seven : Term
poly-seven = Λ ($ 7)

once : Term
once = poly-seven ⟪ [] , all-idℕ ⟫

twice : Term
twice = once ⟪ [] , all-idℕ ⟫

bad-redex : Term
bad-redex = ν `ℕ · twice ⟨ idℕ ⟩

empty-bw : BoundaryWf empty [] empty empty
empty-bw = bw wf-empty (interior changes[]) (conversion conv[])

idℕ-⊢ : ∀ {Δ} → Δ ⊢ idℕ ∶ `ℕ ⇝ `ℕ
idℕ-⊢ = conv-tail (conv-mid (conv-id base-ℕ))

all-idℕ-⊢ : ∀ {Δ} → Δ ⊢ all-idℕ ∶ `∀ `ℕ ⇝ `∀ `ℕ
all-idℕ-⊢ = conv-tail (conv-mid (conv-all idℕ-⊢))

same-∀ℕ : empty ⊢ `∀ `ℕ ≈ `∀ `ℕ ⊣ empty
same-∀ℕ = `∀ `ℕ , same-∀ same-ℕ , same-∀ same-ℕ

poly-seven-⊢ : empty ∣ [] ⊢ poly-seven ⦂ `∀ `ℕ
poly-seven-⊢ = ⊢Λ (V-simple S-$) ⊢$

once-⊢ : empty ∣ [] ⊢ once ⦂ `∀ `ℕ
once-⊢ = boundary empty-bw poly-seven-⊢ all-idℕ-⊢
                   same-∀ℕ same-∀ℕ (wf-∀ wf-ℕ)

twice-⊢ : empty ∣ [] ⊢ twice ⦂ `∀ `ℕ
twice-⊢ = boundary empty-bw once-⊢ all-idℕ-⊢
                    same-∀ℕ same-∀ℕ (wf-∀ wf-ℕ)

bad-redex-⊢ : empty ∣ [] ⊢ bad-redex ⦂ `ℕ
bad-redex-⊢ =
  ⊢ν wf-ℕ same-ℕ twice-⊢ TyBeta-bw idℕ-⊢
     (`ℕ , same-ℕ , same-ℕ) wf-ℕ

inst-twice : InstX twice (($ 7 ⟪ [] , idℕ ⟫) ⟪ [] , idℕ ⟫)
inst-twice = inst-⟪⟫ (inst-⟪⟫ (inst-Λ (V-simple S-$)))

tybeta-step :
  empty ⊢ bad-redex
    -→ (($ 7 ⟪ [] , idℕ ⟫) ⟪ [] , idℕ ⟫)
         ⟪ TyBetaBoundary , idℕ ⟫ ∣ new `ℕ
tybeta-step = TyBeta inst-twice same-ℕ

all-idℕ-reading : names empty ⊩ all-idℕ ~ all-idℕ
all-idℕ-reading =
  sameᶜ-tail (sameᶜ-mid (sameᶜ-all
    (sameᶜ-tail (sameᶜ-mid (sameᶜ-id same-ℕ)))))

all-idℕ-same : SameConv empty all-idℕ empty all-idℕ
all-idℕ-same = all-idℕ , all-idℕ-reading , all-idℕ-reading

once-value : Value once
once-value = V-⟪⟫ (S-Λ (V-simple S-$)) I-all

merge-step :
  empty ⊢ twice
    -→ poly-seven ⟪ [] , empty ⊢ all-idℕ ⨟ all-idℕ ⟫ ∣ none
merge-step =
  Merge once-value (interior changes[])
        (conversion conv[]) (conversion conv[])
        (conversion conv[]) all-idℕ-same all-idℕ-same

frame-step :
  empty ⊢ bad-redex
    -→ ν `ℕ · (poly-seven ⟪ [] , empty ⊢ all-idℕ ⨟ all-idℕ ⟫)
         ⟨ idℕ ⟩ ∣ none
frame-step = ξ-ν merge-step

changes-differ : new `ℕ ≢ none
changes-differ ()
