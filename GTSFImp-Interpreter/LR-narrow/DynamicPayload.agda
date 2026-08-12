module LR-narrow.DynamicPayload where

-- File Charter:
--   * Constructs DynamicPayloadRelated for every GTSFImp ground form.
--   * Supports distinct endpoint contexts via the world's center embeddings.
--   * Uses semantic-atom alignment for the variable-tag case.
--   * Constructs one-sided dynamic boundaries for the ground-to-★ clauses.

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types
open import CastTerms using (Term; _⟨_⟩)
import Consistency as C
open C using (Env∼; _⊢_∼★; toRenameᵗ)
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.LogicalRelation

dynamic-payload-base : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {ι : Base} {μᴾ : Env∼ Δᴾ} {μᴵ : Env∼ Δᴵ}
    {Uᴵ : Term Δᴵ} {Uᴾ : Term Δᴾ}
  → ValueImprecision W (I.ι⊑ι {ι = ι}) k Uᴵ Uᴾ
  → DynamicPayloadRelated W k
      (Uᴵ ⟨ groundInjection (Types.‵ ι) (C.ι∼★ {μ = μᴵ}) ⟩)
      (Uᴾ ⟨ groundInjection (Types.‵ ι) (C.ι∼★ {μ = μᴾ}) ⟩)
dynamic-payload-base {ι = ι} {μᴾ = μᴾ} {μᴵ = μᴵ} payload-related =
  tags-and-payload (Types.‵ ι) (Types.‵ ι)
    (C.ι∼★ {μ = μᴾ}) (C.ι∼★ {μ = μᴵ}) I.ι⊑ι
    payload-related

dynamic-payload-function : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {μᴾ : Env∼ Δᴾ} {μᴵ : Env∼ Δᴵ}
    {Uᴵ : Term Δᴵ} {Uᴾ : Term Δᴾ}
  → ValueImprecision W (I.⇒⊑⇒ I.★⊑★ I.★⊑★) k Uᴵ Uᴾ
  → DynamicPayloadRelated W k
      (Uᴵ ⟨ groundInjection ★⇒★ (C.⇒∼★ {μ = μᴵ}) ⟩)
      (Uᴾ ⟨ groundInjection ★⇒★ (C.⇒∼★ {μ = μᴾ}) ⟩)
dynamic-payload-function {μᴾ = μᴾ} {μᴵ = μᴵ} payload-related =
  tags-and-payload ★⇒★ ★⇒★ (C.⇒∼★ {μ = μᴾ})
    (C.⇒∼★ {μ = μᴵ}) (I.⇒⊑⇒ I.★⊑★ I.★⊑★)
    payload-related

semantic-variable-imprecision : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {Z : TyVar Δᶜ}
    (a : SemanticAtom (core W) Z)
  → ＇ preciseVariable a ⊑ᵂ⟨ core W ⟩ ＇ impreciseVariable a
semantic-variable-imprecision a
  rewrite preciseAligned a | impreciseAligned a = I.X⊑X

dynamic-payload-variable : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ} {Z : TyVar Δᶜ}
    {μᴾ : Env∼ Δᴾ} {μᴵ : Env∼ Δᴵ}
    {Uᴵ : Term Δᴵ} {Uᴾ : Term Δᴾ}
    (a : SemanticAtom (core W) Z)
    (precise-to-star : μᴾ ⊢ ＇ preciseVariable a ∼★)
    (imprecise-to-star : μᴵ ⊢ ＇ impreciseVariable a ∼★)
  → ValueImprecision W (semantic-variable-imprecision {W = W} a) k Uᴵ Uᴾ
  → DynamicPayloadRelated W k
      (Uᴵ ⟨ groundInjection (Types.＇ impreciseVariable a)
        imprecise-to-star ⟩)
      (Uᴾ ⟨ groundInjection (Types.＇ preciseVariable a)
        precise-to-star ⟩)
dynamic-payload-variable {W = W} a precise-to-star imprecise-to-star
    payload-related =
  tags-and-payload (Types.＇ preciseVariable a)
    (Types.＇ impreciseVariable a) precise-to-star
    imprecise-to-star (semantic-variable-imprecision {W = W} a)
    payload-related

dynamic-payload-universal : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {μᴾ : Env∼ Δᴾ} {μᴵ : Env∼ Δᴵ}
    {Uᴵ : Term Δᴵ} {Uᴾ : Term Δᴾ}
  → ValueImprecision W (I.∀⊑∀ I.★⊑★) k Uᴵ Uᴾ
  → DynamicPayloadRelated W k
      (Uᴵ ⟨ groundInjection ∀★ (C.∀∼★ {μ = μᴵ}) ⟩)
      (Uᴾ ⟨ groundInjection ∀★ (C.∀∼★ {μ = μᴾ}) ⟩)
dynamic-payload-universal {μᴾ = μᴾ} {μᴵ = μᴵ} payload-related =
  tags-and-payload ∀★ ∀★ (C.∀∼★ {μ = μᴾ})
    (C.∀∼★ {μ = μᴵ})
    (I.∀⊑∀ I.★⊑★) payload-related

right-tags-and-payload : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Gᴵ : Ty Δᴵ} (gᴵ : Ground Gᴵ)
    {μᴵ : Env∼ Δᴵ} (Gᴵ∼★ : μᴵ ⊢ Gᴵ ∼★)
    {Uᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (q : impEnv (core W) I.⊢ Aᴾ ⊑ embedImprecise (core W) Gᴵ)
  → ValueImprecision W q k Uᴵ Vᴾ
  → RightDynamicPayloadRelated W Aᴾ k
      (Uᴵ ⟨ groundInjection gᴵ Gᴵ∼★ ⟩) Vᴾ
right-tags-and-payload gᴵ Gᴵ∼★ q related =
  right-dynamic-payload-shape _ gᴵ _ Gᴵ∼★ _ refl q , related

right-dynamic-payload-base : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ} {ι : Base}
    {μᴵ : Env∼ Δᴵ} {Uᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.ι⊑ι {ι = ι}) k Uᴵ Vᴾ
  → RightDynamicPayloadRelated W (‵ ι) k
      (Uᴵ ⟨ groundInjection (Types.‵ ι)
        (C.ι∼★ {μ = μᴵ}) ⟩) Vᴾ
right-dynamic-payload-base {μᴵ = μᴵ} related =
  right-tags-and-payload _ (C.ι∼★ {μ = μᴵ}) I.ι⊑ι related

right-dynamic-payload-function : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Bᴾ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ ★)
    (q : impEnv (core W) I.⊢ Bᴾ ⊑ ★)
    {μᴵ : Env∼ Δᴵ} {Uᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.⇒⊑⇒ p q) k Uᴵ Vᴾ
  → RightDynamicPayloadRelated W (Aᴾ ⇒ Bᴾ) k
      (Uᴵ ⟨ groundInjection ★⇒★ (C.⇒∼★ {μ = μᴵ}) ⟩) Vᴾ
right-dynamic-payload-function p q {μᴵ = μᴵ} related =
  right-tags-and-payload ★⇒★ (C.⇒∼★ {μ = μᴵ})
    (I.⇒⊑⇒ p q) related

right-dynamic-payload-universal : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    (p : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ ★)
    {μᴵ : Env∼ Δᴵ} {Uᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.∀⊑∀ p) k Uᴵ Vᴾ
  → RightDynamicPayloadRelated W (`∀ Aᴾ) k
      (Uᴵ ⟨ groundInjection ∀★ (C.∀∼★ {μ = μᴵ}) ⟩) Vᴾ
right-dynamic-payload-universal p {μᴵ = μᴵ} related =
  right-tags-and-payload ∀★ (C.∀∼★ {μ = μᴵ})
    (I.∀⊑∀ p) related

right-dynamic-payload-universal-star : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {μᴵ : Env∼ Δᴵ} {Uᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.∀⊑∀ I.★⊑★) k Uᴵ Vᴾ
  → RightDynamicPayloadRelated W (`∀ ★) k
      (Uᴵ ⟨ groundInjection ∀★ (C.∀∼★ {μ = μᴵ}) ⟩) Vᴾ
right-dynamic-payload-universal-star {μᴵ = μᴵ} related =
  right-tags-and-payload ∀★ (C.∀∼★ {μ = μᴵ})
    (I.∀⊑∀ I.★⊑★) related
