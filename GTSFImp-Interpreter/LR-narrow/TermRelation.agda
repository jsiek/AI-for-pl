module LR-narrow.TermRelation where

-- File Charter:
--   * Defines the open logical relation for compiled cast terms.
--   * Quantifies over future worlds and closes both endpoint terms with
--     related typed substitutions before applying the computation relation.
--   * Bridges the LR world and context to the cast-term imprecision relation.
--   * Contains no compatibility proof.

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

open import Types
open import CastTerms using (Term)
import proof.DGG.CastTermImprecision2 as CTI
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.ClosingSubstitution
open import LR-narrow.ClosingSubstitutionProperties

------------------------------------------------------------------------
-- The syntactic shadow of an LR world
------------------------------------------------------------------------

forgetWorld : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx}
  → World Δᴾ Δᴵ Δᶜ
  → CTI.World Δᴾ Δᴵ Δᶜ
forgetWorld W =
  CTI.world (preciseEmbedding (core W)) (impreciseEmbedding (core W))
    (impEnv (core W)) (preciseStore (core W))
    (impreciseStore (core W))

compiledContext : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx}
    (W : World Δᴾ Δᴵ Δᶜ)
  → CTI.CtxImp (forgetWorld W)
  → ContextImprecision W
compiledContext W [] = []
compiledContext W (CTI.ctx-imp Aᴾ Aᴵ p ∷ Γ) =
  context-imp Aᴾ Aᴵ p ∷ compiledContext W Γ

compiled-context-lookup : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp (forgetWorld W)} {x Aᴾ Aᴵ p}
  → Γ CTI.∋ʷ x ⦂ CTI.ctx-imp Aᴾ Aᴵ p
  → compiledContext W Γ ∋ᴿ x ⦂ context-imp Aᴾ Aᴵ p
compiled-context-lookup CTI.Zʷ = Zᴿ
compiled-context-lookup (CTI.Sʷ x∈) =
  Sᴿ (compiled-context-lookup x∈)

compiled-precise-context-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (Γ : CTI.CtxImp (forgetWorld W))
  → preciseContext
      (liftContextImprecision W≼W′ (compiledContext W Γ))
      ≡ liftPreciseContext W≼W′ (CTI.srcCtxʷ Γ)
compiled-precise-context-future W≼W′ [] = refl
compiled-precise-context-future W≼W′
    (CTI.ctx-imp Aᴾ Aᴵ p ∷ Γ) =
  cong₂ _∷_ refl (compiled-precise-context-future W≼W′ Γ)

compiled-imprecise-context-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (Γ : CTI.CtxImp (forgetWorld W))
  → impreciseContext
      (liftContextImprecision W≼W′ (compiledContext W Γ))
      ≡ liftImpreciseContext W≼W′ (CTI.tgtCtxʷ Γ)
compiled-imprecise-context-future W≼W′ [] = refl
compiled-imprecise-context-future W≼W′
    (CTI.ctx-imp Aᴾ Aᴵ p ∷ Γ) =
  cong₂ _∷_ refl (compiled-imprecise-context-future W≼W′ Γ)

------------------------------------------------------------------------
-- Open compiled terms
------------------------------------------------------------------------

TermRelation : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
  → (p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ)
  → ℕ
  → (Γ : ContextImprecision W)
  → Term Δᴾ
  → Term Δᴵ
  → Set₁
TermRelation {W = W} p k Γ Mᴾ Mᴵ =
  ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
    (W≼W′ : Future W W′)
    (γ : RelatedClosingSubstitutions W′ k
      (liftContextImprecision W≼W′ Γ))
  → ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ p)) k
      (close (impreciseClosingSubstitution γ)
        (liftImpreciseTerm W≼W′ Mᴵ))
      (close (preciseClosingSubstitution γ)
        (liftPreciseTerm W≼W′ Mᴾ))

CompiledTermRelation : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
  → (p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ)
  → ℕ
  → (Γ : CTI.CtxImp (forgetWorld W))
  → Term Δᴾ
  → Term Δᴵ
  → Set₁
CompiledTermRelation {W = W} p k Γ =
  TermRelation p k (compiledContext W Γ)
