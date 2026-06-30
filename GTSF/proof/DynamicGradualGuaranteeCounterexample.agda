module proof.DynamicGradualGuaranteeCounterexample where

-- File Charter:
--   * Records the current obstruction to the `ν⊒ν`/`ν-step` case of the
--     dynamic gradual guarantee.
--   * Proves that the existing term-narrowing relation cannot target the
--     runtime bullet form produced by `ν-step`, even under the recursive
--     source-only wrappers that preserve an arbitrary target.
--   * This is evidence that the present `dynamicGradualGuarantee` statement is
--     missing either a runtime-bullet narrowing rule or a different target
--     closure for store-opening steps.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Nat using (zero)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types
open import Coercions
open import Primitives
open import NuTerms
open import NuReduction
open import NarrowWiden
open import TermNarrowing

data RuntimeBulletTarget : Term → Set where
  runtime-bullet : ∀ {V} → RuntimeBulletTarget (V •)

data RuntimeBulletIdCastTarget : Term → Set where
  runtime-bullet-id-cast :
    ∀ {V A} → RuntimeBulletIdCastTarget ((V •) ⟨ id A ⟩)

runtime-bullet-id-cast-inner :
  ∀ {M c} →
  RuntimeBulletIdCastTarget (M ⟨ c ⟩) →
  RuntimeBulletTarget M
runtime-bullet-id-cast-inner runtime-bullet-id-cast = runtime-bullet

runtime-bullet-target-⇑ᵗᵐ :
  ∀ {T} →
  RuntimeBulletTarget T →
  RuntimeBulletTarget (⇑ᵗᵐ T)
runtime-bullet-target-⇑ᵗᵐ runtime-bullet = runtime-bullet

runtime-bullet-id-cast-target-⇑ᵗᵐ :
  ∀ {T} →
  RuntimeBulletIdCastTarget T →
  RuntimeBulletIdCastTarget (⇑ᵗᵐ T)
runtime-bullet-id-cast-target-⇑ᵗᵐ runtime-bullet-id-cast =
  runtime-bullet-id-cast

no-runtime-bullet-target :
  ∀ {Δ σ γ M T p} →
  RuntimeBulletTarget T →
  Δ ∣ σ ∣ γ ⊢ M ⊒ T ∶ p →
  ⊥
no-runtime-bullet-target is• (extend qᶜ pαᶜ M⊒T) =
  no-runtime-bullet-target is• M⊒T
no-runtime-bullet-target is• (split qᶜ pαᶜ M⊒T) =
  no-runtime-bullet-target is• M⊒T
no-runtime-bullet-target () (⊒blame pᶜ)
no-runtime-bullet-target () (x⊒x pᶜ x∋p)
no-runtime-bullet-target () (ƛ⊒ƛ p↦qᶜ M⊒T)
no-runtime-bullet-target () (·⊒· qᶜ L⊒L′ M⊒M′)
no-runtime-bullet-target () (Λ⊒Λ allᶜ vV V⊒V′)
no-runtime-bullet-target () (⊒Λ pᶜ N⊒V′)
no-runtime-bullet-target () (⊒⟨ν⟩ pᶜ sᵢ N⊒V′s)
no-runtime-bullet-target () (α⊒α qᶜ pαᶜ L⊒L′)
no-runtime-bullet-target () (⊒α pαᶜ L⊒L′)
no-runtime-bullet-target () (ν⊒ν pᶜ qᶜ N⊒N′)
no-runtime-bullet-target () (⊒ν pᶜ N⊒N′)
no-runtime-bullet-target is• (ν⊒ pᶜ M⊒T) =
  no-runtime-bullet-target (runtime-bullet-target-⇑ᵗᵐ is•) M⊒T
no-runtime-bullet-target () (κ⊒κ κ)
no-runtime-bullet-target () (⊕⊒⊕ M⊒M′ N⊒N′)
no-runtime-bullet-target () (⊒cast+ qᶜ q⨟s≈r M⊒M′)
no-runtime-bullet-target () (⊒cast- qᶜ q⨟s≈r M⊒M′)
no-runtime-bullet-target is• (cast+⊒ pᶜ r≈t⨟p M⊒T) =
  no-runtime-bullet-target is• M⊒T
no-runtime-bullet-target is• (cast-⊒ pᶜ r≈t⨟p M⊒T) =
  no-runtime-bullet-target is• M⊒T

no-runtime-bullet-id-cast-target :
  ∀ {Δ σ γ M T p} →
  RuntimeBulletIdCastTarget T →
  Δ ∣ σ ∣ γ ⊢ M ⊒ T ∶ p →
  ⊥
no-runtime-bullet-id-cast-target is•id (extend qᶜ pαᶜ M⊒T) =
  no-runtime-bullet-id-cast-target is•id M⊒T
no-runtime-bullet-id-cast-target is•id (split qᶜ pαᶜ M⊒T) =
  no-runtime-bullet-id-cast-target is•id M⊒T
no-runtime-bullet-id-cast-target () (⊒blame pᶜ)
no-runtime-bullet-id-cast-target () (x⊒x pᶜ x∋p)
no-runtime-bullet-id-cast-target () (ƛ⊒ƛ p↦qᶜ M⊒T)
no-runtime-bullet-id-cast-target () (·⊒· qᶜ L⊒L′ M⊒M′)
no-runtime-bullet-id-cast-target () (Λ⊒Λ allᶜ vV V⊒V′)
no-runtime-bullet-id-cast-target () (⊒Λ pᶜ N⊒V′)
no-runtime-bullet-id-cast-target () (⊒⟨ν⟩ pᶜ sᵢ N⊒V′s)
no-runtime-bullet-id-cast-target () (α⊒α qᶜ pαᶜ L⊒L′)
no-runtime-bullet-id-cast-target () (⊒α pαᶜ L⊒L′)
no-runtime-bullet-id-cast-target () (ν⊒ν pᶜ qᶜ N⊒N′)
no-runtime-bullet-id-cast-target () (⊒ν pᶜ N⊒N′)
no-runtime-bullet-id-cast-target is•id (ν⊒ pᶜ M⊒T) =
  no-runtime-bullet-id-cast-target
    (runtime-bullet-id-cast-target-⇑ᵗᵐ is•id) M⊒T
no-runtime-bullet-id-cast-target () (κ⊒κ κ)
no-runtime-bullet-id-cast-target () (⊕⊒⊕ M⊒M′ N⊒N′)
no-runtime-bullet-id-cast-target is•id (⊒cast+ qᶜ q⨟s≈r M⊒M′) =
  no-runtime-bullet-target (runtime-bullet-id-cast-inner is•id) M⊒M′
no-runtime-bullet-id-cast-target is•id (⊒cast- qᶜ q⨟s≈r M⊒M′) =
  no-runtime-bullet-target (runtime-bullet-id-cast-inner is•id) M⊒M′
no-runtime-bullet-id-cast-target is•id (cast+⊒ pᶜ r≈t⨟p M⊒T) =
  no-runtime-bullet-id-cast-target is•id M⊒T
no-runtime-bullet-id-cast-target is•id (cast-⊒ pᶜ r≈t⨟p M⊒T) =
  no-runtime-bullet-id-cast-target is•id M⊒T

idℕᶜ :
  ∀ {Δ Σ} →
  Δ ∣ Σ ⊢ id (‵ `ℕ) ∶ᶜ ‵ `ℕ ⊒ ‵ `ℕ
idℕᶜ = cast-id wfBase refl , cross (id-‵ `ℕ)

id★ᶜ :
  ∀ {Δ Σ} →
  Δ ∣ Σ ⊢ id ★ ∶ᶜ ★ ⊒ ★
id★ᶜ = cast-id wf★ refl , id★

ν⊒ν-step-example :
  zero ∣ [] ∣ [] ⊢
    ν ★ ($ (κℕ 0)) (id (‵ `ℕ))
    ⊒ ν ★ ($ (κℕ 0)) (id (‵ `ℕ)) ∶ id (‵ `ℕ)
ν⊒ν-step-example =
  ν⊒ν idℕᶜ id★ᶜ (κ⊒κ (κℕ 0))

ν-step-example :
  ν ★ ($ (κℕ 0)) (id (‵ `ℕ)) —→[ bind ★ ]
    (($ (κℕ 0) •) ⟨ id (‵ `ℕ) ⟩)
ν-step-example = ν-step ($ (κℕ 0)) no•-$

ν-step-example-target-not-narrowable :
  ∀ {Δ σ M p} →
  Δ ∣ σ ∣ [] ⊢ M ⊒ (($ (κℕ 0) •) ⟨ id (‵ `ℕ) ⟩) ∶ p →
  ⊥
ν-step-example-target-not-narrowable =
  no-runtime-bullet-id-cast-target runtime-bullet-id-cast
