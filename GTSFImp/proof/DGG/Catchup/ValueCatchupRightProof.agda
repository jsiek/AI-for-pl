module proof.DGG.Catchup.ValueCatchupRightProof where

-- File Charter:
--   * Provides checked structural row combinators for the fuel-indexed value
--     catch-up recursion.
--   * `ValueCatchupRightAt` now consumes the CTI derivation for the whole
--     target term rather than a separate column witness.
--   * The internal worker surface carries `StructuralWorldExtendᴿ`; the
--     adapter in `StructuralCatchupRightDef` erases it to the public
--     `WorldExtendᴿ` boundary.

open import Data.Nat using (_<_)
open import Relation.Binary.PropositionalEquality using (sym)
  renaming (subst to subst≡)

open import Types using (Ty)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (Conv↓)
open import CastTerms using (Term; Value; Inert; _⟨_⟩; _《_》)
open import Reduction using (applyConsistencies)
open import proof.Reduction using (_++χ_; castSize-applyConsistencies)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.ExtraCastRight2 as ECR
open CTX using
  (World;
   CtxImp;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (castSize; TargetCastBound)
open import proof.DGG.Catchup.StructuralWorldExtendDef using
  (StructuralWorldExtendᴿ)
open import proof.DGG.Catchup.StructuralWorldExtendProof using
  (structural-world-extendᴿ)
open import proof.DGG.Catchup.StructuralWorldTagRebaseDef using
  (mapPivotChanges)
open import proof.DGG.Catchup.StructuralCatchupRightDef public using
  (StructuralCatchupRightResult; StructuralValueCatchupRightAt;
   StructuralExtraCastRightAt; erase-structural-value-catchup-right-at;
   structural-catchup-compose-target-cast;
   structural-catchup-compose-paired-target-cast)


structural-target-cast-row : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
  → (value-worker : StructuralValueCatchupRightAt fuel)
  → (extra-worker : StructuralExtraCastRightAt fuel)
  → (c′ : ν ⊢ B ∼ B′)
  → (vM : Value M)
  → (rel : W ∣ γ ⊢² M ⊑ M′ ∶ p)
  → (c′<fuel : castSize c′ < fuel)
  → (bound : TargetCastBound fuel rel)
  → StructuralCatchupRightResult W γ M (M′ ⟨ c′ ⟩) q
structural-target-cast-row {fuel = fuel} {γ = γ} {q = q}
    value-worker extra-worker c′ vM rel c′<fuel bound =
  structural-catchup-compose-target-cast c′ child residual
  where
  child = value-worker vM rel bound
  plan = StructuralCatchupRightResult.structural-ext child
  ext = structural-world-extendᴿ plan
  χs = StructuralCatchupRightResult.χs child
  cχ = applyConsistencies χs c′
  cχ<fuel =
    subst≡ (λ n → n < fuel)
      (sym (castSize-applyConsistencies χs c′))
      c′<fuel
  residual =
    extra-worker cχ cχ<fuel
      (CTI2.⊑cast² cχ
        (StructuralCatchupRightResult.final-relation child)
        (ECR.transport⊑ᵂ ext q))
      vM
      (StructuralCatchupRightResult.final-value child)


structural-paired-target-cast-row : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {C A : Ty Δᴸ} {C′ A′ : Ty Δᴿ}
    {ν : Env∼ Δᴸ} {ν′ : Env∼ Δᴿ}
    {p : C ⊑ᵂ⟨ W ⟩ C′} {q : A ⊑ᵂ⟨ W ⟩ A′}
  → (value-worker : StructuralValueCatchupRightAt fuel)
  → (extra-worker : StructuralExtraCastRightAt fuel)
  → (c : ν ⊢ C ∼ A)
  → (c′ : ν′ ⊢ C′ ∼ A′)
  → (vM : Value M)
  → (inert : Inert c)
  → (rel : W ∣ γ ⊢² M ⊑ M′ ∶ p)
  → (c′<fuel : castSize c′ < fuel)
  → (bound : TargetCastBound fuel rel)
  → StructuralCatchupRightResult W γ (M ⟨ c ⟩) (M′ ⟨ c′ ⟩) q
structural-paired-target-cast-row {fuel = fuel} {γ = γ} {q = q}
    value-worker extra-worker c c′ vM inert rel c′<fuel bound =
  structural-catchup-compose-paired-target-cast
    c c′ child residual
  where
  child = value-worker vM rel bound
  plan = StructuralCatchupRightResult.structural-ext child
  ext = structural-world-extendᴿ plan
  χs = StructuralCatchupRightResult.χs child
  cχ = applyConsistencies χs c′
  cχ<fuel =
    subst≡ (λ n → n < fuel)
      (sym (castSize-applyConsistencies χs c′))
      c′<fuel
  residual =
    extra-worker cχ cχ<fuel
      (CTI2.cast⊑cast² c cχ
        (StructuralCatchupRightResult.final-relation child)
        (ECR.transport⊑ᵂ ext q))
      (vM 《 inert 》)
      (StructuralCatchupRightResult.final-value child)
