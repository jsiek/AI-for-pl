module proof.DGG.Catchup.StructuralGenDescentProof where

-- File Charter:
--   * Rebuilds relational structural descent across target β-gen.
--   * Consumes the strictly smaller allocated child package.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import Types using
  (Ty; TyVar; NonVar; _∈ᵗ_; ＇_; ★; _[_]ᵗ; ⇑ᵗ)
open import Consistency using (Env∼; _⊢_∼_; genᵐ; gen_)
open import CastTerms using
  (Term; Value; GenSafe; _⟨_⟩; _⦂∀_[_]; _↑_; ⇑ᵗᵐ)
open import Conversion using (〖_,_↑_〗)
open import Reduction using (bind; β-gen)
open import proof.TypeSafety.Preservation using (replace-zero-open)
import proof.DGG.CtxImp as CTI2
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationReductionProof
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralInstantiationDescentDef
open import proof.DGG.Catchup.StructuralInstantiationDescentProof


structural-gen-descent : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {L : Ty Δᴸ} {A : Ty Δᴿ} {B : Ty (suc Δᴿ)}
    {E : Ty Δᴿ} {μ : Env∼ Δᴿ}
    {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
    ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : Fin.zero ∈ᵗ B ⦄
    {X : TyVar Δᴿ} {q : L CTI2.⊑ᵂ⟨ W ⟩ E}
    (vV : Value V) (A≠★ : A ≢ ★) (safe : GenSafe c)
    (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → (fresh : CTI2.RightBindFresh W (＇ X))
  → let ins = TE.rightBindTargetInsert fresh
        ext = target-insert-bind-world-extendᴿ ins refl
     in StructuralInstantiationDescentPackage
          (CTI2.rightOnlyWorld W (＇ X) fresh)
          (ECR.mapCtxᴿ ext γ) M (⇑ᵗᵐ V)
          (cast-frame c ▻ⁱ
            reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
            type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
            mapInstantiationSpine (bind (＇ X)) spine)
          (ECR.transport⊑ᵂ ext q)
  → StructuralInstantiationDescentPackage W γ M
      (V ⟨ (gen c) A≠★ ⟩)
      (name-type-app-frame B X refl refl ▻ⁱ spine) q
structural-gen-descent {W = W} {X = X} vV A≠★ safe spine fresh child =
  structural-descent-bind-step
    (TE.rightBindTargetInsert fresh) refl
    (lift-instantiation-spine-bind (β-gen vV A≠★ safe) spine)
    child
