open import LR-narrow.CastObligations using (CastValueObligations)

module LR-narrow.Cast (ob : CastValueObligations) where

-- File Charter:
--   * Exposes checked value- and open-term cast compatibility, relative
--     to the explicit value-level obligations of
--     LR-narrow.CastObligations.
--   * Covers paired and one-sided structural casts and their identity cases.
--   * Exposes the `X`-tag/`id★` square needed by CTI cast constructors.

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import CastTerms
import Consistency as C
import Imprecision as I
import proof.DGG.CtxImp as CTI
import proof.DGG.CastTermImprecision as CTIR
open CTIR using (_∣_⊢²_⊑_∶_)
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.TermRelation
import proof.LR-narrow.Cast ob as Proof

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

cast-cast-compatible : ∀
    {Δᴾ Δᴵ Δᶜ : TyCtx} {W : World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Cᴾ Dᴾ : Ty Δᴾ} {Cᴵ Dᴵ : Ty Δᴵ}
    {p : Cᴾ ⊑ᵂ⟨ core W ⟩ Cᴵ}
    {μᴾ : C.Env∼ Δᴾ} (cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ)
    {μᴵ : C.Env∼ Δᴵ} (cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ)
    {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
  → (q : Dᴾ ⊑ᵂ⟨ core W ⟩ Dᴵ)
  → (∀ k → CompiledTermRelation {W = W} p k Γ Mᴾ Mᴵ)
  → ∀ k → CompiledTermRelation {W = W} q k Γ
      (Mᴾ ⟨ cᴾ ⟩) (Mᴵ ⟨ cᴵ ⟩)
cast-cast-compatible = Proof.cast-cast-compatible

right-cast-compatible : ∀
    {Δᴾ Δᴵ Δᶜ : TyCtx} {W : World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Cᴾ : Ty Δᴾ} {Cᴵ Dᴵ : Ty Δᴵ}
    {p : Cᴾ ⊑ᵂ⟨ core W ⟩ Cᴵ}
    {μᴵ : C.Env∼ Δᴵ} (cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ)
    {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
  → (q : Cᴾ ⊑ᵂ⟨ core W ⟩ Dᴵ)
  → (∀ k → CompiledTermRelation {W = W} p k Γ Mᴾ Mᴵ)
  → ∀ k → CompiledTermRelation {W = W} q k Γ
      Mᴾ (Mᴵ ⟨ cᴵ ⟩)
right-cast-compatible = Proof.right-cast-compatible

left-cast-compatible : ∀
    {Δᴾ Δᴵ Δᶜ : TyCtx} {W : World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Cᴾ Dᴾ : Ty Δᴾ} {Cᴵ : Ty Δᴵ}
    {p : Cᴾ ⊑ᵂ⟨ core W ⟩ Cᴵ}
    {μᴾ : C.Env∼ Δᴾ} (cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ)
    {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
  → (q : Dᴾ ⊑ᵂ⟨ core W ⟩ Cᴵ)
  → (∀ k → CompiledTermRelation {W = W} p k Γ Mᴾ Mᴵ)
  → ∀ k → CompiledTermRelation {W = W} q k Γ
      (Mᴾ ⟨ cᴾ ⟩) Mᴵ
left-cast-compatible = Proof.left-cast-compatible
