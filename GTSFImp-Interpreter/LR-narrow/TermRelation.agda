module LR-narrow.TermRelation where

-- File Charter:
--   * Defines the open logical relation for compiled cast terms.
--   * Quantifies over future worlds and closes both endpoint terms with
--     related typed substitutions before applying the computation relation.
--   * Bridges the LR world and context to the cast-term imprecision relation.
--   * Defines paired and precise-only semantic universal body premises.
--   * Contains no compatibility proof.

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

open import Types
open import Conversion using (〖_,_↑_〗)
open import CastTerms using (Term; _↑_)
import TermCtx as T
import Imprecision as I
import proof.DGG.CtxImp as CTI
import proof.DGG.CastTermImprecision as CTIR
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.ClosingSubstitution
open import LR-narrow.ClosingSubstitutionProperties
open import LR-narrow.TypeBetaExpansion using (paired-step; precise-step)

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

lifted-source-context : ∀ {Δᴾ Δᴵ Δᶜ v}
    {W : CTI.World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp W} {Γ′ : CTI.CtxImp (CTI.liftWorldBoth v W)}
  → CTI.LiftCtx v Γ Γ′
  → CTI.srcCtxʷ Γ′ ≡ T.⇑ᶜ (CTI.srcCtxʷ Γ)
lifted-source-context CTI.lift-[] = refl
lifted-source-context (CTI.lift-∷ liftΓ) =
  cong₂ _∷_ refl (lifted-source-context liftΓ)

lifted-target-context : ∀ {Δᴾ Δᴵ Δᶜ v}
    {W : CTI.World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp W} {Γ′ : CTI.CtxImp (CTI.liftWorldBoth v W)}
  → CTI.LiftCtx v Γ Γ′
  → CTI.tgtCtxʷ Γ′ ≡ T.⇑ᶜ (CTI.tgtCtxʷ Γ)
lifted-target-context CTI.lift-[] = refl
lifted-target-context (CTI.lift-∷ liftΓ) =
  cong₂ _∷_ refl (lifted-target-context liftΓ)

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

------------------------------------------------------------------------
-- Open terms below a universal type binder
------------------------------------------------------------------------

CompiledUniversalBodyRelation : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
  → (p : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ)
  → (Bᴾ : Ty (suc Δᴾ))
  → (Bᴵ : Ty (suc Δᴵ))
  → ℕ
  → (Γ : CTI.CtxImp (forgetWorld W))
  → Term (suc Δᴾ)
  → Term (suc Δᴵ)
  → Set₁
CompiledUniversalBodyRelation {W = W} p Bᴾ Bᴵ k Γ Nᴾ Nᴵ =
  ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
    (W≼W′ : Future W W′)
    (γ : RelatedClosingSubstitutions W′ k
      (liftContextImprecision W≼W′ (compiledContext W Γ)))
    (Rᴾ : Ty Δᴾ′) (Rᴵ : Ty Δᴵ′)
    (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
    (fresh : SemanticAtom (pairedBindCore (core W′) Rᴾ Rᴵ) Fin.zero)
    (s : liftPreciseBody W≼W′ Bᴾ [ Rᴾ ]ᵗ
      ⊑ᵂ⟨ core W′ ⟩ liftImpreciseBody W≼W′ Bᴵ [ Rᴵ ]ᵗ)
  → let tested = pairedBindWorld W′ Rᴾ Rᴵ fresh
        test-step = paired-step W′ r fresh
    in ComputationsRelated tested
        (FutureValueRelation (liftCenterImprecision test-step s)) k
        (closeTypeBody (impreciseClosingSubstitution γ)
          (liftImpreciseBodyTerm W≼W′ Nᴵ)
          ↑ 〖 Fin.zero , ⇑ᵗ Rᴵ ↑
            liftImpreciseBody W≼W′ Bᴵ 〗)
        (closeTypeBody (preciseClosingSubstitution γ)
          (liftPreciseBodyTerm W≼W′ Nᴾ)
          ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ liftPreciseBody W≼W′ Bᴾ 〗)

CompiledRightUniversalBodyRelation : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
  → (p : I.instᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ)
  → (Bᴾ : Ty (suc Δᴾ))
  → (Bᴵ : Ty Δᴵ)
  → ℕ
  → (Γ : CTI.CtxImp (forgetWorld W))
  → Term (suc Δᴾ)
  → Term Δᴵ
  → Set₁
CompiledRightUniversalBodyRelation {W = W} p Bᴾ Bᴵ k Γ Nᴾ Mᴵ =
  ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
    (W≼W′ : Future W W′)
    (γ : RelatedClosingSubstitutions W′ k
      (liftContextImprecision W≼W′ (compiledContext W Γ)))
    (Rᴾ : Ty Δᴾ′)
    (fresh : DynamicSemanticAtom
      (preciseBindCore (core W′) Rᴾ) Fin.zero)
    (s : liftPreciseBody W≼W′ Bᴾ [ Rᴾ ]ᵗ
      ⊑ᵂ⟨ core W′ ⟩ liftImpreciseTy W≼W′ Bᴵ)
  → let tested = preciseBindWorld W′ Rᴾ fresh
        test-step = precise-step W′ fresh
    in ComputationsRelated tested
        (FutureValueRelation (liftCenterImprecision test-step s)) k
        (close (impreciseClosingSubstitution γ)
          (liftImpreciseTerm W≼W′ Mᴵ))
        (closeTypeBody (preciseClosingSubstitution γ)
          (liftPreciseBodyTerm W≼W′ Nᴾ)
          ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑
            liftPreciseBody W≼W′ Bᴾ 〗)
