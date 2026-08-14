module LR-narrow.Cast where

-- File Charter:
--   * Exposes the checked value-level cast compatibility boundary.
--   * Covers paired and one-sided identity casts.
--   * Exposes the `X`-tag/`id★` square needed by CTI cast constructors.

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import CastTerms
import Consistency as C
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
import proof.LR-narrow.Cast as Proof

related-imprecise-identity : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k : ℕ}
    {μᴵ : C.Env∼ Δᴵ} {aᴵ : Atom Bᴵ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k
      (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩) Vᴾ
related-imprecise-identity = Proof.related-imprecise-identity

related-precise-identity : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴾ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k : ℕ}
    {μᴾ : C.Env∼ Δᴾ} {aᴾ : Atom Bᴾ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k Vᴵ
      (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩)
related-precise-identity = Proof.related-precise-identity

related-identities : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴾ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k : ℕ}
    {μᴾ : C.Env∼ Δᴾ} {aᴾ : Atom Bᴾ}
    {μᴵ : C.Env∼ Δᴵ} {aᴵ : Atom Bᴵ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k
      (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩)
      (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩)
related-identities = Proof.related-identities

related-dynamic-tag-left : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ} {Z : TyVar Δᶜ}
    {mode : impEnv (core W) Z ≡ I.X⊑★}
    {Gᴾ : Ty Δᴾ} (gᴾ : Ground Gᴾ)
    (ground-center : embedPrecise (core W) Gᴾ ≡ ＇ Z)
    {μᴾ : C.Env∼ Δᴾ} (Gᴾ∼★ : μᴾ C.⊢ Gᴾ ∼★)
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.X⊑★ mode) k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation I.★⊑★) k Vᴵ
      (Vᴾ ⟨ groundInjection gᴾ Gᴾ∼★ ⟩)
related-dynamic-tag-left = Proof.related-dynamic-tag-left

related-dynamic-id★-tag : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ} {Z : TyVar Δᶜ}
    {mode : impEnv (core W) Z ≡ I.X⊑★}
    {Gᴾ : Ty Δᴾ} (gᴾ : Ground Gᴾ)
    (ground-center : embedPrecise (core W) Gᴾ ≡ ＇ Z)
    {μᴾ : C.Env∼ Δᴾ} (Gᴾ∼★ : μᴾ C.⊢ Gᴾ ∼★)
    {μᴵ : C.Env∼ Δᴵ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.X⊑★ mode) k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation I.★⊑★) k
      (Vᴵ ⟨ C.id {μ = μᴵ} ★ ⟩)
      (Vᴾ ⟨ groundInjection gᴾ Gᴾ∼★ ⟩)
related-dynamic-id★-tag = Proof.related-dynamic-id★-tag
