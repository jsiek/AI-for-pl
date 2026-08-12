module LR.DynamicPayload where

-- File Charter:
--   * Constructs DynamicPayloadRelated for every GTSFImp ground form.
--   * Reuses the recursive payload relation without spending another index.
--   * Makes variable-tag consistency evidence explicit at the use site.

open import Data.Nat using (ℕ)

open import Types
open import CastTerms using (Term; _⟨_⟩)
import Consistency as C
open C using (Env∼; _⊢_∼★)
import Imprecision as I
open import LR.World
open import LR.LogicalRelation

dynamic-payload-base : ∀ {Δ} {W : World Δ} {k : ℕ}
    {ι : Base} {μᴾ μᴵ : Env∼ Δ} {Uᴵ Uᴾ : Term Δ}
  → ValueImprecision W (I.ι⊑ι {ι = ι}) k Uᴵ Uᴾ
  → DynamicPayloadRelated W k
      (Uᴵ ⟨ groundInjection (Types.‵ ι) (C.ι∼★ {μ = μᴵ}) ⟩)
      (Uᴾ ⟨ groundInjection (Types.‵ ι) (C.ι∼★ {μ = μᴾ}) ⟩)
dynamic-payload-base {ι = ι} {μᴾ = μᴾ} {μᴵ = μᴵ} payload-related =
  tags-and-payload (Types.‵ ι) (Types.‵ ι)
    (C.ι∼★ {μ = μᴾ}) (C.ι∼★ {μ = μᴵ}) I.ι⊑ι
    payload-related

dynamic-payload-function : ∀ {Δ} {W : World Δ} {k : ℕ}
    {μᴾ μᴵ : Env∼ Δ} {Uᴵ Uᴾ : Term Δ}
  → ValueImprecision W (I.⇒⊑⇒ I.★⊑★ I.★⊑★) k Uᴵ Uᴾ
  → DynamicPayloadRelated W k
      (Uᴵ ⟨ groundInjection ★⇒★ (C.⇒∼★ {μ = μᴵ}) ⟩)
      (Uᴾ ⟨ groundInjection ★⇒★ (C.⇒∼★ {μ = μᴾ}) ⟩)
dynamic-payload-function {μᴾ = μᴾ} {μᴵ = μᴵ} payload-related =
  tags-and-payload ★⇒★ ★⇒★ (C.⇒∼★ {μ = μᴾ})
    (C.⇒∼★ {μ = μᴵ}) (I.⇒⊑⇒ I.★⊑★ I.★⊑★)
    payload-related

dynamic-payload-variable : ∀ {Δ} {W : World Δ} {k : ℕ}
    {X : TyVar Δ} {μᴾ μᴵ : Env∼ Δ} {Uᴵ Uᴾ : Term Δ}
    (precise-to-star : μᴾ ⊢ ＇ X ∼★)
    (imprecise-to-star : μᴵ ⊢ ＇ X ∼★)
  → ValueImprecision W (I.X⊑X {X = X}) k Uᴵ Uᴾ
  → DynamicPayloadRelated W k
      (Uᴵ ⟨ groundInjection (Types.＇ X) imprecise-to-star ⟩)
      (Uᴾ ⟨ groundInjection (Types.＇ X) precise-to-star ⟩)
dynamic-payload-variable {X = X} precise-to-star imprecise-to-star
    payload-related =
  tags-and-payload (Types.＇ X) (Types.＇ X) precise-to-star
    imprecise-to-star I.X⊑X payload-related

dynamic-payload-universal : ∀ {Δ} {W : World Δ} {k : ℕ}
    {μᴾ μᴵ : Env∼ Δ} {Uᴵ Uᴾ : Term Δ}
  → ValueImprecision W (I.∀⊑∀ I.★⊑★) k Uᴵ Uᴾ
  → DynamicPayloadRelated W k
      (Uᴵ ⟨ groundInjection ∀★ (C.∀∼★ {μ = μᴵ}) ⟩)
      (Uᴾ ⟨ groundInjection ∀★ (C.∀∼★ {μ = μᴾ}) ⟩)
dynamic-payload-universal {μᴾ = μᴾ} {μᴵ = μᴵ} payload-related =
  tags-and-payload ∀★ ∀★ (C.∀∼★ {μ = μᴾ})
    (C.∀∼★ {μ = μᴵ})
    (I.∀⊑∀ I.★⊑★) payload-related
