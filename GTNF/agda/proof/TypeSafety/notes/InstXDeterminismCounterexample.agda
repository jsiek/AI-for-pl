module proof.TypeSafety.notes.InstXDeterminismCounterexample where

-- File Charter:
--   * REGRESSION TEST for a determinism bug found in M1 (2026-10-02).
--     Before the fix, applying `inst-⟪⟫` twice admitted the non-value
--     `twice` (a boundary over a boundary, a `Merge` redex) as a `TyBeta`
--     redex, so `bad-redex` had two steps with different changes
--     (`new ℕ` by TyBeta, `none` by ξ-ν Merge).
--   * THE FIX (Jeremy, 2026-10-02; design.md §6.2): `TyBeta` requires
--     `Value V`, `inst-∀` requires `Value W`, and `inst-⟪⟫` requires
--     `Simple U` (a `Value U` premise would still admit `twice`, because
--     `once` is a value).  Below: `twice` is not a value and has no
--     `InstX`, while the `Merge` step remains.

open import Data.List using ([])
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (¬_)

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

-- the fix: `twice` is not a value, and `InstX` cannot reach through it
twice-not-value : ¬ Value twice
twice-not-value (V-simple ())
twice-not-value (V-⟪⟫ () _)

no-inst-twice : ∀ {N} → ¬ InstX twice N
no-inst-twice (inst-⟪⟫ () _)

all-idℕ-reading : names empty ⊩ all-idℕ ~ all-idℕ
all-idℕ-reading =
  sameᶜ-tail (sameᶜ-mid (sameᶜ-all
    (sameᶜ-tail (sameᶜ-mid (sameᶜ-id same-ℕ)))))

all-idℕ-same : SameConv empty all-idℕ empty all-idℕ
all-idℕ-same = all-idℕ , all-idℕ-reading , all-idℕ-reading

once-value : Value once
once-value = V-⟪⟫ (S-Λ (V-simple S-$)) I-all

-- the Merge step is still there, and is now the only step
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
