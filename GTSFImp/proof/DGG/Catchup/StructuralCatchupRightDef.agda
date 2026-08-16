module proof.DGG.Catchup.StructuralCatchupRightDef where

-- File Charter:
--   * Defines the LG-3 internal right-catch-up result package that carries
--     `StructuralWorldExtendᴿ`.
--   * Provides erasure adapters to the public `WorldExtendᴿ` result surfaces
--     used by `ValueCatchupRightAt` and `ExtraCastRightAt`.
--   * Keeps structural traces internal; no public fuel statement is widened.

import Data.Fin as Fin
open import Data.Nat using (ℕ; suc; _<_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≢_; sym)
  renaming (subst to subst≡)

open import Types using (Ty; TyCtx; NonVar; _∈ᵗ_; ★; `∀; ⇑ᵗ)
open import Consistency using (Env∼; _⊢_∼_; inst_; instᵐ)
open import CastTerms using (Term; Value; Inert; _⟨_⟩; _《_》)
open import Reduction using (StoreChanges; []; _∷_; keep; _—→[_]_;
  _—↠[_]_; _—→[_]⟨_⟩_; _∎[]; applyConsistencies)
open import proof.Reduction using (cast-↠; applyConsistencies-Inert)

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Inversion.SpineValueDef using (AllValueView)
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (TargetCastBound; ValueCatchupRight²; ValueCatchupRightAt;
   ExtraCastRightAt; InstCatchupRightAt; castSize)
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


record StructuralCatchupRightResult {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W)
    (M : Term Δᴸ) (M″ : Term Δᴿ)
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    (q : A ⊑ᵂ⟨ W ⟩ B) : Set₁ where
  field
    Δᴿ′ : TyCtx
    χs : StoreChanges Δᴿ Δᴿ′
    Δ′ : TyCtx
    W′ : World Δᴸ Δᴿ′ Δ′
    structural-ext : StructuralWorldExtendᴿ χs W W′
    N′ : Term Δᴿ′
    final-value : Value N′
    post-reduction : M″ —↠[ χs ] N′
    final-relation :
      W′ ∣ ECR.mapCtxᴿ (structural-world-extendᴿ structural-ext) γ
        ⊢² M ⊑ N′ ∶
          ECR.transport⊑ᵂ (structural-world-extendᴿ structural-ext) q


erase-structural-catchup-result : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M″ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → StructuralCatchupRightResult W γ M M″ q
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ ext ∈ ECR.WorldExtendᴿ χs W W′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
        × (M″ —↠[ χs ] N′)
        × (W′ ∣ ECR.mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
            ECR.transport⊑ᵂ ext q))
erase-structural-catchup-result result =
  StructuralCatchupRightResult.Δᴿ′ result ,
  StructuralCatchupRightResult.χs result ,
  StructuralCatchupRightResult.Δ′ result ,
  StructuralCatchupRightResult.W′ result ,
  structural-world-extendᴿ
    (StructuralCatchupRightResult.structural-ext result) ,
  StructuralCatchupRightResult.N′ result ,
  StructuralCatchupRightResult.final-value result ,
  StructuralCatchupRightResult.post-reduction result ,
  StructuralCatchupRightResult.final-relation result


structural-catchup-refl : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {N′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → Value N′
  → W ∣ γ ⊢² M ⊑ N′ ∶ q
  → StructuralCatchupRightResult W γ M N′ q
structural-catchup-refl {Δᴿ = Δᴿ} {Δ = Δ} {W = W} {γ = γ}
    {M = M} {N′ = N′} {q = q} vN′ rel =
  record
    { Δᴿ′ = Δᴿ
    ; χs = []
    ; Δ′ = Δ
    ; W′ = W
    ; structural-ext = structural-[]
    ; N′ = N′
    ; final-value = vN′
    ; post-reduction = N′ ∎[]
    ; final-relation =
        subst≡ (λ γ′ → W ∣ γ′ ⊢² M ⊑ N′ ∶ q)
          (sym (ECR.mapCtxᴿ-same γ)) rel
    }


structural-catchup-keep-step : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M″ N′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → Value N′
  → M″ —→[ keep ] N′
  → W ∣ γ ⊢² M ⊑ N′ ∶ q
  → StructuralCatchupRightResult W γ M M″ q
structural-catchup-keep-step {Δᴿ = Δᴿ} {Δ = Δ} {W = W} {γ = γ}
    {M = M} {M″ = M″} {N′ = N′} {q = q} vN′ step rel =
  record
    { Δᴿ′ = Δᴿ
    ; χs = keep ∷ []
    ; Δ′ = Δ
    ; W′ = W
    ; structural-ext = structural-keep structural-[]
    ; N′ = N′
    ; final-value = vN′
    ; post-reduction =
        M″ —→[ keep ]⟨ step ⟩
        N′ ∎[]
    ; final-relation =
        subst≡ (λ γ′ → W ∣ γ′ ⊢² M ⊑ N′ ∶ q)
          (sym (ECR.mapCtxᴿ-keep γ)) rel
    }


structural-catchup-source-cast : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M″ : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {ν : Env∼ Δᴸ}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
  → (c : ν ⊢ A ∼ A′)
  → StructuralCatchupRightResult W γ M M″ p
  → StructuralCatchupRightResult W γ (M ⟨ c ⟩) M″ q
structural-catchup-source-cast {q = q} c result = record
  { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ result
  ; χs = StructuralCatchupRightResult.χs result
  ; Δ′ = StructuralCatchupRightResult.Δ′ result
  ; W′ = StructuralCatchupRightResult.W′ result
  ; structural-ext = StructuralCatchupRightResult.structural-ext result
  ; N′ = StructuralCatchupRightResult.N′ result
  ; final-value = StructuralCatchupRightResult.final-value result
  ; post-reduction = StructuralCatchupRightResult.post-reduction result
  ; final-relation =
      CTI2.cast⊑² c
        (StructuralCatchupRightResult.final-relation result)
        (ECR.transport⊑ᵂ
          (structural-world-extendᴿ
            (StructuralCatchupRightResult.structural-ext result))
          q)
  }


structural-catchup-target-inert-cast : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M″ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
  → (c′ : ν ⊢ B ∼ B′)
  → Inert c′
  → StructuralCatchupRightResult W γ M M″ p
  → StructuralCatchupRightResult W γ M (M″ ⟨ c′ ⟩) q
structural-catchup-target-inert-cast {q = q} c′ inert result = record
  { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ result
  ; χs = StructuralCatchupRightResult.χs result
  ; Δ′ = StructuralCatchupRightResult.Δ′ result
  ; W′ = StructuralCatchupRightResult.W′ result
  ; structural-ext = StructuralCatchupRightResult.structural-ext result
  ; N′ = StructuralCatchupRightResult.N′ result
      ⟨ applyConsistencies (StructuralCatchupRightResult.χs result) c′ ⟩
  ; final-value =
      StructuralCatchupRightResult.final-value result 《
        applyConsistencies-Inert
          (StructuralCatchupRightResult.χs result) inert 》
  ; post-reduction =
      cast-↠ c′ (StructuralCatchupRightResult.post-reduction result)
  ; final-relation =
      CTI2.⊑cast²
        (applyConsistencies (StructuralCatchupRightResult.χs result) c′)
        (StructuralCatchupRightResult.final-relation result)
        (ECR.transport⊑ᵂ
          (structural-world-extendᴿ
            (StructuralCatchupRightResult.structural-ext result))
          q)
  }


StructuralValueCatchupRight² : Set₁
StructuralValueCatchupRight² = ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M″ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → Value M
  → W ∣ γ ⊢² M ⊑ M″ ∶ q
  → StructuralCatchupRightResult W γ M M″ q


erase-structural-value-catchup-right² :
  StructuralValueCatchupRight² → ValueCatchupRight²
erase-structural-value-catchup-right² worker vM rel =
  erase-structural-catchup-result (worker vM rel)


StructuralExtraCastRightAt : ℕ → Set₁
StructuralExtraCastRightAt fuel = ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′}
  → (c′ : ν ⊢ B ∼ B′)
  → castSize c′ < fuel
  → W ∣ γ ⊢² M ⊑ (M′ ⟨ c′ ⟩) ∶ q
  → Value M
  → Value M′
  → StructuralCatchupRightResult W γ M (M′ ⟨ c′ ⟩) q


erase-structural-extra-cast-right-at : ∀ {fuel}
  → StructuralExtraCastRightAt fuel
  → ExtraCastRightAt fuel
erase-structural-extra-cast-right-at worker c′ c′<fuel rel vM vM′ =
  erase-structural-catchup-result (worker c′ c′<fuel rel vM vM′)


StructuralValueCatchupRightAt : ℕ → Set₁
StructuralValueCatchupRightAt fuel = ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M″ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → Value M
  → (rel : W ∣ γ ⊢² M ⊑ M″ ∶ q)
  → TargetCastBound fuel rel
  → StructuralCatchupRightResult W γ M M″ q


erase-structural-value-catchup-right-at : ∀ {fuel}
  → StructuralValueCatchupRightAt fuel
  → ValueCatchupRightAt fuel
erase-structural-value-catchup-right-at worker vM rel bound =
  erase-structural-catchup-result (worker vM rel bound)


StructuralInstCatchupRightAt : ℕ → Set₁
StructuralInstCatchupRightAt fuel = ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → AllValueView M′
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → castSize ((inst c′) B′≢★) < fuel
  → (q : A ⊑ᵂ⟨ W ⟩ B′)
  → StructuralCatchupRightResult W γ M
      (M′ ⟨ (inst c′) B′≢★ ⟩) q


erase-structural-inst-catchup-right-at : ∀ {fuel}
  → StructuralInstCatchupRightAt fuel
  → InstCatchupRightAt fuel
erase-structural-inst-catchup-right-at worker rel vM vM′ spine c′
    B′≢★ c′<fuel q =
  erase-structural-catchup-result
    (worker rel vM vM′ spine c′ B′≢★ c′<fuel q)
