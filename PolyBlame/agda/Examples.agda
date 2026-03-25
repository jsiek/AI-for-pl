module Examples where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Base using (z<s)
open import Data.Unit using (tt)

open import PolyBlame

------------------------------------------------------------------------
-- Small helper for context closure
------------------------------------------------------------------------

ξ : {Σ Π : Store} {F : Frame} {M N : Term} →
    (Σ ⊲ M) —→ (Π ⊲ N) →
    (Σ ⊲ plug F M) —→ (Π ⊲ plug F N)
ξ s = ξξ refl refl s

plugC : Frame → Config → Config
plugC F (Σ ⊲ M) = Σ ⊲ plug F M

ξc : {F : Frame} {c₁ c₂ : Config} →
     c₁ —→ c₂ →
     plugC F c₁ —→ plugC F c₂
ξc {F = F} {c₁ = Σ ⊲ M} {c₂ = Π ⊲ N} s = ξ {F = F} s

ξ* : {F : Frame} {c₁ c₂ : Config} →
     c₁ —↠ c₂ →
     plugC F c₁ —↠ plugC F c₂
ξ* (_ ∎) = _ ∎
ξ* (c₁ —→⟨ s ⟩ ms) =
  _ —→⟨ ξc s ⟩ ξ* ms

------------------------------------------------------------------------
-- Closed evaluation-to relation (final store abstracted)
------------------------------------------------------------------------

infix 2 _⇓_

data _⇓_ (M V : Term) : Set where
  evals-to : ∀ {Σ} → ([] ⊲ M) —↠ (Σ ⊲ V) → M ⇓ V

------------------------------------------------------------------------
-- Shared terms and casts used in notes.md examples
------------------------------------------------------------------------

polyId : Term
polyId = Λ (ƛ (＇ zero) ⇒ ` zero)

idDyn : Term
idDyn = ƛ `★ ⇒ ` zero

nat : ℕ → Term
nat n = $ (κℕ n)

c : Term
c = nat 7

n42 : Term
n42 = nat 42

n69 : Term
n69 = nat 69

tag-ι : Imp
tag-ι = injTag (idι `ℕ) (G-ι `ℕ)

tag-ι-typing : ∀ {Δ Σ} → Δ ∣ Σ ⊢ᵖ tag-ι ⦂ ‵ `ℕ ⊑ `★
tag-ι-typing = ⊢tag ⊢idι

c★ : Term
c★ = c at up tag-ι

n42★ : Term
n42★ = n42 at up tag-ι

n69★ : Term
n69★ = n69 at up tag-ι

seal-ι : Seal → Imp
seal-ι α = sealImp α (⌈ idι `ℕ ⌉)

seal-ι-typing :
  ∀ {Δ Σ a} →
  Σ ∋ˢ a ⦂ ‵ `ℕ →
  Δ ∣ Σ ⊢ᵖ seal-ι a ⦂ ｀ a ⊑ ‵ `ℕ
seal-ι-typing hα = ⊢seal hα (⊢⌈⌉ ⊢idι)

seal-★ : Seal → Imp
seal-★ α = sealImp α id★

seal-★-typing :
  ∀ {Δ Σ a} →
  Σ ∋ˢ a ⦂ `★ →
  Δ ∣ Σ ⊢ᵖ seal-★ a ⦂ ｀ a ⊑ `★
seal-★-typing hα = ⊢seal hα ⊢id★

seal-ι→seal-ι : Seal → Imp
seal-ι→seal-ι a = ⌈ (seal-ι a) →ᵖ (seal-ι a) ⌉

seal-ι→seal-ι-typing :
  ∀ {Δ Σ a} →
  Σ ∋ˢ a ⦂ ‵ `ℕ →
  Δ ∣ Σ ⊢ᵖ seal-ι→seal-ι a ⦂ (｀ a ⇒ ｀ a) ⊑ (‵ `ℕ ⇒ ‵ `ℕ)
seal-ι→seal-ι-typing hα =
  ⊢⌈⌉ (⊢→ᵖ (seal-ι-typing hα) (seal-ι-typing hα))

seal-★→seal-★ : Seal → Imp
seal-★→seal-★ a = ⌈ (seal-★ a) →ᵖ (seal-★ a) ⌉

seal-★→seal-★-typing :
  ∀ {Δ Σ a} →
  Σ ∋ˢ a ⦂ `★ →
  Δ ∣ Σ ⊢ᵖ seal-★→seal-★ a ⦂ (｀ a ⇒ ｀ a) ⊑ (`★ ⇒ `★)
seal-★→seal-★-typing hα =
  ⊢⌈⌉ (⊢→ᵖ (seal-★-typing hα) (seal-★-typing hα))

nu-seal-★→seal-★ : Imp
nu-seal-★→seal-★ = nuImp (⌈ (seal-★ 0) →ᵖ (seal-★ 0) ⌉)

nu-seal-★→seal-★-typing :
  ∀ {Δ Σ} →
  Δ ∣ Σ ⊢ᵖ nu-seal-★→seal-★ ⦂ `∀ (＇ zero ⇒ ＇ zero) ⊑ (`★ ⇒ `★)
nu-seal-★→seal-★-typing =
  ⊢ν
    (⊢⌈⌉ (⊢→ᵖ (seal-★-typing Zˢ) (seal-★-typing Zˢ)))
    (wf⇒ (wfX z<s) (wfX z<s))
    (wf⇒ wf★ wf★)

Σι : Store
Σι = ‵ `ℕ ∷ []

Σ★ : Store
Σ★ = `★ ∷ []

v-c★ : Value c★
v-c★ = v+tag vκ

v-n42★ : Value n42★
v-n42★ = v+tag vκ

v-n69★ : Value n69★
v-n69★ = v+tag vκ

------------------------------------------------------------------------
-- Example 1 (notes.md)
------------------------------------------------------------------------

example1-left : Term
example1-left = ν:= ‵ `ℕ ∙ (((polyId ·α 0) at up (seal-ι→seal-ι 0)) · c)

example1-right : Term
example1-right = ν:= `★ ∙ (((polyId ·α 0) at up (seal-★→seal-★ 0)) · c★)

example1-left-evals : example1-left ⇓ c
example1-left-evals =
  evals-to
    (_ —→⟨ ξν ⟩
     _ —→⟨ ξ {F = □· c} (ξ {F = □at-up (seal-ι→seal-ι 0)} β-Λ) ⟩
     _ —→⟨ β-→+ vƛ vκ ⟩
     _ —→⟨ ξ {F = □at-up (seal-ι 0)} (β-ƛ (v-seal vκ)) ⟩
     _ —→⟨ β-seal vκ ⟩
     _ —→⟨ ξ {F = □at-up ⌈ idι `ℕ ⌉} (β-id- vκ tt) ⟩
     _ —→⟨ β-id+ vκ tt ⟩
     _ ∎)

example1-right-evals : example1-right ⇓ c★
example1-right-evals =
  evals-to
    (_ —→⟨ ξν ⟩
     _ —→⟨ ξ {F = □· c★} (ξ {F = □at-up (seal-★→seal-★ 0)} β-Λ) ⟩
     _ —→⟨ β-→+ vƛ v-c★ ⟩
     _ —→⟨ ξ {F = □at-up (seal-★ 0)} (β-ƛ (v-seal v-c★)) ⟩
     _ —→⟨ β-seal v-c★ ⟩
     _ —→⟨ ξ {F = □at-up id★} (β-id- v-c★ tt) ⟩
     _ —→⟨ β-id+ v-c★ tt ⟩
     _ ∎)

------------------------------------------------------------------------
-- Example 2 (notes.md)
------------------------------------------------------------------------

example2-left : Term
example2-left = example1-left

example2-right : Term
example2-right = idDyn · c★

example2-left-evals : example2-left ⇓ c
example2-left-evals = example1-left-evals

example2-right-evals : example2-right ⇓ c★
example2-right-evals =
  evals-to (_ —→⟨ β-ƛ v-c★ ⟩ _ ∎)

------------------------------------------------------------------------
-- Example 3 (notes.md)
------------------------------------------------------------------------

example3-left : Term
example3-left = (polyId at up nu-seal-★→seal-★) · c★

example3-right : Term
example3-right = example2-right

example3-left-evals : example3-left ⇓ c★
example3-left-evals =
  evals-to
    (_ —→⟨ ξ {F = □· c★} (β-ν+ vΛ) ⟩
     _ —→⟨ ξ {F = □· c★} (ξν) ⟩
     _ —→⟨ ξ {F = □· c★} (ξ {F = □at-up (seal-★→seal-★ 0)} β-Λ) ⟩
     _ —→⟨ β-→+ vƛ v-c★ ⟩
     _ —→⟨ ξ {F = □at-up (seal-★ 0)} (β-ƛ (v-seal v-c★)) ⟩
     _ —→⟨ β-seal v-c★ ⟩
     _ —→⟨ ξ {F = □at-up id★} (β-id- v-c★ tt) ⟩
     _ —→⟨ β-id+ v-c★ tt ⟩
     _ ∎)

example3-right-evals : example3-right ⇓ c★
example3-right-evals = example2-right-evals

------------------------------------------------------------------------
-- Example 4 (notes.md)
------------------------------------------------------------------------

example4-left : Term
example4-left = example1-left

example4-right : Term
example4-right = example3-left

example4-left-evals : example4-left ⇓ c
example4-left-evals = example1-left-evals

example4-right-evals : example4-right ⇓ c★
example4-right-evals = example3-left-evals

------------------------------------------------------------------------
-- Examples 5-11 (notes.md)
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Example 5 (up and then down)
------------------------------------------------------------------------

example5-left : Term
example5-left = example1-left

example5-right : Term
example5-right = (example1-left at up id★) at down id★

example5-left-evals : example5-left ⇓ c
example5-left-evals = example1-left-evals

example5-right-evals : example5-right ⇓ c
example5-right-evals with example1-left-evals
... | evals-to {Σ = Σ} ms =
  evals-to
    (multi-trans
      (ξ* {F = □at-down id★} (ξ* {F = □at-up id★} ms))
      (_ —→⟨ ξ {F = □at-down id★} (β-id+ vκ tt) ⟩
       _ —→⟨ β-id- vκ tt ⟩
       _ ∎))

------------------------------------------------------------------------
-- Example 6 (up, down, up)
------------------------------------------------------------------------

example6-left : Term
example6-left = example1-left

example6-right : Term
example6-right = (example1-right at down id★) at up id★

example6-left-evals : example6-left ⇓ c
example6-left-evals = example1-left-evals

example6-right-evals : example6-right ⇓ c★
example6-right-evals with example1-right-evals
... | evals-to {Σ = Σ} ms =
  evals-to
    (multi-trans
      (ξ* {F = □at-up id★} (ξ* {F = □at-down id★} ms))
      (_ —→⟨ ξ {F = □at-up id★} (β-id- v-c★ tt) ⟩
       _ —→⟨ β-id+ v-c★ tt ⟩
       _ ∎))

------------------------------------------------------------------------
-- Example 7 (up, down, up, down)
------------------------------------------------------------------------

example7-left : Term
example7-left = example1-left

example7-right : Term
example7-right = (example5-right at up id★) at down id★

example7-left-evals : example7-left ⇓ c
example7-left-evals = example1-left-evals

example7-right-evals : example7-right ⇓ c
example7-right-evals with example5-right-evals
... | evals-to {Σ = Σ} ms =
  evals-to
    (multi-trans
      (ξ* {F = □at-down id★} (ξ* {F = □at-up id★} ms))
      (_ —→⟨ ξ {F = □at-down id★} (β-id+ vκ tt) ⟩
       _ —→⟨ β-id- vκ tt ⟩
       _ ∎))

------------------------------------------------------------------------
-- Example 8 (down on the right)
------------------------------------------------------------------------

example8-left : Term
example8-left = example1-left

example8-right : Term
example8-right = example1-left at down id★

example8-left-evals : example8-left ⇓ c
example8-left-evals = example1-left-evals

example8-right-evals : example8-right ⇓ c
example8-right-evals with example1-left-evals
... | evals-to {Σ = Σ} ms =
  evals-to
    (multi-trans
      (ξ* {F = □at-down id★} ms)
      (_ —→⟨ β-id- vκ tt ⟩
       _ ∎))

------------------------------------------------------------------------
-- Example 9 (constant function)
------------------------------------------------------------------------

Kpoly : Term
Kpoly = Λ (Λ (ƛ (＇ (suc zero)) ⇒ ƛ (＇ zero) ⇒ ` (suc zero)))

Kdyn : Term
Kdyn = ƛ `★ ⇒ ƛ `★ ⇒ ` (suc zero)

example9-left : Term
example9-left = (((Kpoly ·α 0) ·α 1) · n42) · n69

example9-right : Term
example9-right = (Kdyn · n42★) · n69★

example9-left-evals : example9-left ⇓ n42
example9-left-evals =
  evals-to
    (_ —→⟨ ξ {F = □· n69} (ξ {F = □· n42} (ξ {F = □·α 1} β-Λ)) ⟩
     _ —→⟨ ξ {F = □· n69} (ξ {F = □· n42} β-Λ) ⟩
     _ —→⟨ ξ {F = □· n69} (β-ƛ vκ) ⟩
     _ —→⟨ β-ƛ vκ ⟩
     _ ∎)

example9-right-evals : example9-right ⇓ n42★
example9-right-evals =
  evals-to
    (_ —→⟨ ξ {F = □· n69★} (β-ƛ v-n42★) ⟩
     _ —→⟨ β-ƛ v-n69★ ⟩
     _ ∎)

------------------------------------------------------------------------
-- Example 10 (constant function, up on the right)
------------------------------------------------------------------------

example10-left : Term
example10-left = example9-left

example10-right : Term
example10-right = ((Kdyn at up id★) · n42★) · n69★

example10-left-evals : example10-left ⇓ n42
example10-left-evals = example9-left-evals

example10-right-evals : example10-right ⇓ n42★
example10-right-evals =
  evals-to
    (_ —→⟨ ξ {F = □· n69★} (ξ {F = □· n42★} (β-id+ vƛ tt)) ⟩
     _ —→⟨ ξ {F = □· n69★} (β-ƛ v-n42★) ⟩
     _ —→⟨ β-ƛ v-n69★ ⟩
     _ ∎)

------------------------------------------------------------------------
-- Example 11 (rebinding-style nested ν)
------------------------------------------------------------------------

example11-left : Term
example11-left =
  ν:= ‵ `ℕ ∙
    ((ƛ (｀ 0) ⇒ (ν:= ｀ 0 ∙ ((ƛ (｀ 0) ⇒ ` zero) · ` zero))) · c)

example11-right : Term
example11-right = (ƛ `★ ⇒ ((ƛ `★ ⇒ ` zero) · ` zero)) · c★

example11-left-evals : example11-left ⇓ c
example11-left-evals =
  evals-to
    (_ —→⟨ ξν ⟩
     _ —→⟨ β-ƛ vκ ⟩
     _ —→⟨ ξν ⟩
     _ —→⟨ β-ƛ vκ ⟩
     _ ∎)

example11-right-evals : example11-right ⇓ c★
example11-right-evals =
  evals-to
    (_ —→⟨ β-ƛ v-c★ ⟩
     _ —→⟨ β-ƛ v-c★ ⟩
     _ ∎)

------------------------------------------------------------------------
-- Example 12 (exercise β-ν-)
------------------------------------------------------------------------

tag-α : Seal → Imp
tag-α α = injTag (idα α) (G-α α)

tag-α-typing :
  ∀ {Δ Σ a A} →
  Σ ∋ˢ a ⦂ A →
  Δ ∣ Σ ⊢ᵖ tag-α a ⦂ ｀ a ⊑ `★
tag-α-typing hα = ⊢tag (⊢idα hα)

v-c-tagα0 : Value (c at up tag-α 0)
v-c-tagα0 = v+tag vκ

example12 : Term
example12 =
  ((c at up tag-α 0) at down (nuImp (sealImp 0 id★))) ·α 0

example12-evals : example12 ⇓ c
example12-evals =
  evals-to
    (_ —→⟨ β-ν- v-c-tagα0 ⟩
     _ —→⟨ β-tag-ok vκ ⟩
     _ —→⟨ ξ {F = □at-down ⌈ idα 0 ⌉} (β-id+ vκ tt) ⟩
     _ —→⟨ β-id- vκ tt ⟩
     _ ∎)

------------------------------------------------------------------------
-- Example 13 (nested ν; mixing α0/α1 changes behavior)
------------------------------------------------------------------------

example13-good : Term
example13-good =
  ν:= `★ ∙
    (ν:= `★ ∙
      ((c at up tag-α 1) at down tag-α 1))

example13-mixed : Term
example13-mixed =
  ν:= `★ ∙
    (ν:= `★ ∙
      ((c at up tag-α 1) at down tag-α 0))

α1≢α0 : G-α 1 ≡ G-α 0 → ⊥
α1≢α0 ()

α0≢α1 : G-α 0 ≡ G-α 1 → ⊥
α0≢α1 ()

example13-good-evals : example13-good ⇓ c
example13-good-evals =
  evals-to
    (_ —→⟨ ξν ⟩
     _ —→⟨ ξν ⟩
     _ —→⟨ β-tag-ok vκ ⟩
     _ —→⟨ ξ {F = □at-down ⌈ idα 0 ⌉} (β-id+ vκ tt) ⟩
     _ —→⟨ β-id- vκ tt ⟩
     _ ∎)

example13-mixed-evals : example13-mixed ⇓ blame
example13-mixed-evals =
  evals-to
    (_ —→⟨ ξν ⟩
     _ —→⟨ ξν ⟩
     _ —→⟨ β-tag-bad vκ α0≢α1 ⟩
     _ ∎)
