module proof.DGG.Catchup.StructuralCatchupRightDef where

-- File Charter:
--   * Defines the LG-3 internal right-catch-up result package that carries
--     `StructuralWorldExtendᴿ`.
--   * Provides erasure adapters to the public `WorldExtendᴿ` result surfaces
--     used by `ValueCatchupRightAt` and `ExtraCastRightAt`.
--   * Keeps structural traces internal; no public fuel statement is widened.

import Data.Fin as Fin
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; suc; _<_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
  renaming (subst to subst≡)

open import Types using
  (Ty; TyCtx; TyVar; NonVar; _∈ᵗ_; ★; `∀; ⇑ᵗ)
open import Consistency using (Env∼; _⊢_∼_; inst_; instᵐ)
open import Conversion using (Conv↑; Conv↓)
open import CastTerms using
  (Term; Value; Inert; _⟨_⟩; _《_》; _↑_; _↓_)
open import Reduction using (StoreChanges; []; _∷_; keep; _—→[_]_;
  _—↠[_]_; _—→[_]⟨_⟩_; _∎[]; applyConsistencies)
open import proof.Reduction using
  (cast-↠; applyConsistencies-Inert; _++χ_; applyTys-++;
   composeReduction)

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.TargetBindLift as TBL
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Inversion.SpineValueDef using (AllValueView)
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralWorldRebaseProof using
  (structural-rebase-atᴸ-pullback)
open import proof.DGG.Catchup.StructuralWorldTagRebaseDef
open import proof.DGG.Catchup.StructuralWorldTagRebaseProof using
  (structural-tag-rebase-atᴸ-pullback)
open import proof.DGG.Catchup.StructuralWorldEvidenceProof using
  (mapCtxᴿ-sameCtx; structural-source-reveal; structural-source-conceal)
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
    source-conceal-endpoint-partner : ∀ {A₀ A₁ : Ty Δᴸ}
        {c : Conv↓ Δᴸ A₀ A₁} {Xᴿ?}
      → CTI2.SourceConcealPartnerOK W M c Xᴿ? M″
      → CTI2.SourceConcealPartnerOK W′ M c
          (mapPivotChanges χs Xᴿ?) N′


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


rel-target-transportᴿ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
  → (eq : B ≡ B′)
  → (p : A ⊑ᵂ⟨ W ⟩ B)
  → W ∣ γ ⊢² M ⊑ N ∶ p
  → W ∣ γ ⊢² M ⊑ N ∶
      subst≡ (λ C → A ⊑ᵂ⟨ W ⟩ C) eq p
rel-target-transportᴿ refl p rel = rel


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
    ; source-conceal-endpoint-partner = λ ok → ok
    }


structural-catchup-keep-step : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M″ N′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → Value N′
  → M″ —→[ keep ] N′
  → W ∣ γ ⊢² M ⊑ N′ ∶ q
  → (∀ {A₀ A₁ : Ty Δᴸ} {c : Conv↓ Δᴸ A₀ A₁} {Xᴿ?}
      → CTI2.SourceConcealPartnerOK W M c Xᴿ? M″
      → CTI2.SourceConcealPartnerOK W M c Xᴿ? N′)
  → StructuralCatchupRightResult W γ M M″ q
structural-catchup-keep-step {Δᴿ = Δᴿ} {Δ = Δ} {W = W} {γ = γ}
    {M = M} {M″ = M″} {N′ = N′} {q = q}
    vN′ step rel partner-step =
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
    ; source-conceal-endpoint-partner = partner-step
    }


structural-catchup-source-cast : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M″ : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {ν : Env∼ Δᴸ}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
  → (c : ν ⊢ A ∼ A′)
  → (result : StructuralCatchupRightResult W γ M M″ p)
  → (∀ {A₀ A₁ : Ty Δᴸ} {c₀ : Conv↓ Δᴸ A₀ A₁} {Xᴿ?}
      → CTI2.SourceConcealPartnerOK W (M ⟨ c ⟩) c₀ Xᴿ? M″
      → CTI2.SourceConcealPartnerOK
          (StructuralCatchupRightResult.W′ result)
          (M ⟨ c ⟩) c₀
          (mapPivotChanges (StructuralCatchupRightResult.χs result) Xᴿ?)
          (StructuralCatchupRightResult.N′ result))
  → StructuralCatchupRightResult W γ (M ⟨ c ⟩) M″ q
structural-catchup-source-cast {q = q} c result partner-endpoint = record
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
  ; source-conceal-endpoint-partner = partner-endpoint
  }


structural-catchup-target-inert-cast : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M″ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
  → (c′ : ν ⊢ B ∼ B′)
  → Inert c′
  → (result : StructuralCatchupRightResult W γ M M″ p)
  → (∀ {A₀ A₁ : Ty Δᴸ} {c₀ : Conv↓ Δᴸ A₀ A₁} {Xᴿ?}
      → CTI2.SourceConcealPartnerOK W M c₀ Xᴿ? (M″ ⟨ c′ ⟩)
      → CTI2.SourceConcealPartnerOK
          (StructuralCatchupRightResult.W′ result)
          M c₀
          (mapPivotChanges (StructuralCatchupRightResult.χs result) Xᴿ?)
          (StructuralCatchupRightResult.N′ result
            ⟨ applyConsistencies
              (StructuralCatchupRightResult.χs result) c′ ⟩))
  → StructuralCatchupRightResult W γ M (M″ ⟨ c′ ⟩) q
structural-catchup-target-inert-cast {q = q}
    c′ inert result partner-endpoint = record
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
  ; source-conceal-endpoint-partner = partner-endpoint
  }


structural-catchup-source-reveal : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {c : Conv↑ Δᴸ A A′}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
  → CTI2.ImpEnvMono W Wᵖ
  → (rb : CTI2.RebaseAtᴸ W Wᵖ Xᴸ?)
  → CTI2.SameCtx γ γᵖ
  → CTI2.sourceStoreʷ W CTI2.⊢↑[ Xᴸ? ] c
  → (child : StructuralCatchupRightResult Wᵖ γᵖ M M′ p)
  → (∀ {A₀ A₁ : Ty Δᴸ} {c₀ : Conv↓ Δᴸ A₀ A₁} {Xᴿ?}
      → let pull = structural-rebase-atᴸ-pullback
              (StructuralCatchupRightResult.structural-ext child) rb
         in CTI2.SourceConcealPartnerOK W (M ↑ c) c₀ Xᴿ? M′
            → CTI2.SourceConcealPartnerOK
                (StructuralRebaseAtᴸPullbackResult.W′ pull)
                (M ↑ c) c₀
                (mapPivotChanges
                  (StructuralCatchupRightResult.χs child) Xᴿ?)
                (StructuralCatchupRightResult.N′ child))
  → StructuralCatchupRightResult W γ (M ↑ c) M′ q
structural-catchup-source-reveal {γ = γ} {q = q}
    mono rb sc c⊢ child partner-endpoint
    with structural-rebase-atᴸ-pullback
      (StructuralCatchupRightResult.structural-ext child) rb
structural-catchup-source-reveal {γ = γ} {q = q}
    mono rb sc c⊢ child partner-endpoint
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ child
    ; χs = StructuralCatchupRightResult.χs child
    ; Δ′ = StructuralCatchupRightResult.Δ′ child
    ; W′ = W′
    ; structural-ext = plan
    ; N′ = StructuralCatchupRightResult.N′ child
    ; final-value = StructuralCatchupRightResult.final-value child
    ; post-reduction = StructuralCatchupRightResult.post-reduction child
    ; final-relation =
        CTI2.reveal⊑² (mono′ mono) rb′
          (mapCtxᴿ-sameCtx
            (structural-world-extendᴿ plan)
            (structural-world-extendᴿ
              (StructuralCatchupRightResult.structural-ext child))
            sc)
          (structural-source-reveal plan c⊢)
          (StructuralCatchupRightResult.final-relation child)
          (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)
    ; source-conceal-endpoint-partner = partner-endpoint
    }


structural-catchup-source-conceal : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {c : Conv↓ Δᴸ A A′}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
  → CTI2.ImpEnvMono W Wᵖ
  → (rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
  → CTI2.SameCtx γ γᵖ
  → CTI2.sourceStoreʷ W CTI2.⊢↓[ Xᴸ? ] c
  → (child : StructuralCatchupRightResult Wᵖ γᵖ M M′ p)
  → CTI2.SourceConcealPartnerOK
      (StructuralCatchupRightResult.W′ child) M c
      (mapPivotChanges (StructuralCatchupRightResult.χs child) Xᴿ?)
      (StructuralCatchupRightResult.N′ child)
  → (∀ {A₀ A₁ : Ty Δᴸ} {c₀ : Conv↓ Δᴸ A₀ A₁} {Yᴿ?}
      → let pull = structural-tag-rebase-atᴸ-pullback
              (StructuralCatchupRightResult.structural-ext child) rb
         in CTI2.SourceConcealPartnerOK W (M ↓ c) c₀ Yᴿ? M′
            → CTI2.SourceConcealPartnerOK
                (StructuralTagRebaseAtᴸPullbackResult.W′ pull)
                (M ↓ c) c₀
                (mapPivotChanges
                  (StructuralCatchupRightResult.χs child) Yᴿ?)
                (StructuralCatchupRightResult.N′ child))
  → StructuralCatchupRightResult W γ (M ↓ c) M′ q
structural-catchup-source-conceal {γ = γ} {q = q}
    mono rb sc c⊢ child ok partner-endpoint
    with structural-tag-rebase-atᴸ-pullback
      (StructuralCatchupRightResult.structural-ext child) rb
structural-catchup-source-conceal {γ = γ} {q = q}
    mono rb sc c⊢ child ok partner-endpoint
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ child
    ; χs = StructuralCatchupRightResult.χs child
    ; Δ′ = StructuralCatchupRightResult.Δ′ child
    ; W′ = W′
    ; structural-ext = plan
    ; N′ = StructuralCatchupRightResult.N′ child
    ; final-value = StructuralCatchupRightResult.final-value child
    ; post-reduction = StructuralCatchupRightResult.post-reduction child
    ; final-relation =
        CTI2.conceal⊑² ok (mono′ mono) rb′
          (mapCtxᴿ-sameCtx
            (structural-world-extendᴿ plan)
            (structural-world-extendᴿ
              (StructuralCatchupRightResult.structural-ext child))
            sc)
          (structural-source-conceal plan c⊢)
          (StructuralCatchupRightResult.final-relation child)
          (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)
    ; source-conceal-endpoint-partner = partner-endpoint
    }


structural-catchup-compose : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M₀ : Term Δᴿ}
    {A : Ty Δᴸ} {B₀ B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B₀} {q : A ⊑ᵂ⟨ W ⟩ B}
  → (result₁ : StructuralCatchupRightResult W γ M M₀ p)
  → StructuralCatchupRightResult
      (StructuralCatchupRightResult.W′ result₁)
      (ECR.mapCtxᴿ
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext result₁))
        γ)
      M
      (StructuralCatchupRightResult.N′ result₁)
      (ECR.transport⊑ᵂ
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext result₁))
        q)
  → StructuralCatchupRightResult W γ M M₀ q
structural-catchup-compose {γ = γ} {B = B} {q = q} result₁ result₂ =
  record
    { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ result₂
    ; χs = χs₁ ++χ χs₂
    ; Δ′ = StructuralCatchupRightResult.Δ′ result₂
    ; W′ = StructuralCatchupRightResult.W′ result₂
    ; structural-ext = composeStructuralWorldExtendᴿ plan₁ plan₂
    ; N′ = StructuralCatchupRightResult.N′ result₂
    ; final-value = StructuralCatchupRightResult.final-value result₂
    ; post-reduction =
        composeReduction
          (StructuralCatchupRightResult.post-reduction result₁)
          (StructuralCatchupRightResult.post-reduction result₂)
    ; final-relation =
        subst≡
          (λ γ′ → StructuralCatchupRightResult.W′ result₂ ∣ γ′ ⊢² _
            ⊑ _ ∶ ECR.transport⊑ᵂ ext q)
          (mapCtxᴿ-structural-compose plan₁ plan₂ γ)
          (TBL.⊢²-retarget
            (rel-target-transportᴿ
              (applyTys-++ χs₁ χs₂ B)
              (ECR.transport⊑ᵂ ext₂
                (ECR.transport⊑ᵂ ext₁ q))
              (StructuralCatchupRightResult.final-relation result₂)))
    ; source-conceal-endpoint-partner =
        λ {A₀ = A₀} {A₁ = A₁} {c = c} {Xᴿ? = Xᴿ?} ok →
        subst≡
          (λ pivot → CTI2.SourceConcealPartnerOK
            (StructuralCatchupRightResult.W′ result₂) _ c pivot
            (StructuralCatchupRightResult.N′ result₂))
          (sym (mapPivotChanges-++ χs₁ χs₂ Xᴿ?))
          (StructuralCatchupRightResult.source-conceal-endpoint-partner
            result₂
            (StructuralCatchupRightResult.source-conceal-endpoint-partner
              result₁ ok))
    }
  where
  χs₁ = StructuralCatchupRightResult.χs result₁
  χs₂ = StructuralCatchupRightResult.χs result₂
  plan₁ = StructuralCatchupRightResult.structural-ext result₁
  plan₂ = StructuralCatchupRightResult.structural-ext result₂
  ext₁ = structural-world-extendᴿ plan₁
  ext₂ = structural-world-extendᴿ plan₂
  ext = structural-world-extendᴿ (composeStructuralWorldExtendᴿ plan₁ plan₂)


structural-catchup-compose-target-cast : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M₀ : Term Δᴿ}
    {A : Ty Δᴸ} {B₀ B : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B₀} {q : A ⊑ᵂ⟨ W ⟩ B}
  → (c′ : ν ⊢ B₀ ∼ B)
  → (child : StructuralCatchupRightResult W γ M M₀ p)
  → (residual : StructuralCatchupRightResult
      (StructuralCatchupRightResult.W′ child)
      (ECR.mapCtxᴿ
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext child))
        γ)
      M
      (StructuralCatchupRightResult.N′ child
        ⟨ applyConsistencies
          (StructuralCatchupRightResult.χs child) c′ ⟩)
      (ECR.transport⊑ᵂ
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext child))
        q))
  → (∀ {A₀ A₁ : Ty Δᴸ} {c₀ : Conv↓ Δᴸ A₀ A₁} {Xᴿ?}
      → CTI2.SourceConcealPartnerOK W M c₀ Xᴿ? (M₀ ⟨ c′ ⟩)
      → CTI2.SourceConcealPartnerOK
          (StructuralCatchupRightResult.W′ residual)
          M c₀
          (mapPivotChanges
            (StructuralCatchupRightResult.χs child ++χ
             StructuralCatchupRightResult.χs residual)
            Xᴿ?)
          (StructuralCatchupRightResult.N′ residual))
  → StructuralCatchupRightResult W γ M (M₀ ⟨ c′ ⟩) q
structural-catchup-compose-target-cast {γ = γ} {B = B} {q = q}
    c′ child residual partner-endpoint =
  record
    { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ residual
    ; χs = χs₁ ++χ χs₂
    ; Δ′ = StructuralCatchupRightResult.Δ′ residual
    ; W′ = StructuralCatchupRightResult.W′ residual
    ; structural-ext = composeStructuralWorldExtendᴿ plan₁ plan₂
    ; N′ = StructuralCatchupRightResult.N′ residual
    ; final-value = StructuralCatchupRightResult.final-value residual
    ; post-reduction =
        composeReduction
          (cast-↠ c′ (StructuralCatchupRightResult.post-reduction child))
          (StructuralCatchupRightResult.post-reduction residual)
    ; final-relation =
        subst≡
          (λ γ′ → StructuralCatchupRightResult.W′ residual ∣ γ′ ⊢² _
            ⊑ _ ∶ ECR.transport⊑ᵂ ext q)
          (mapCtxᴿ-structural-compose plan₁ plan₂ γ)
          (TBL.⊢²-retarget
            (rel-target-transportᴿ
              (applyTys-++ χs₁ χs₂ B)
              (ECR.transport⊑ᵂ ext₂
                (ECR.transport⊑ᵂ ext₁ q))
              (StructuralCatchupRightResult.final-relation residual)))
    ; source-conceal-endpoint-partner = partner-endpoint
    }
  where
  χs₁ = StructuralCatchupRightResult.χs child
  χs₂ = StructuralCatchupRightResult.χs residual
  plan₁ = StructuralCatchupRightResult.structural-ext child
  plan₂ = StructuralCatchupRightResult.structural-ext residual
  ext₁ = structural-world-extendᴿ plan₁
  ext₂ = structural-world-extendᴿ plan₂
  ext = structural-world-extendᴿ (composeStructuralWorldExtendᴿ plan₁ plan₂)


structural-catchup-compose-paired-target-cast : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M₀ : Term Δᴿ}
    {C A : Ty Δᴸ} {C′ A′ : Ty Δᴿ}
    {ν : Env∼ Δᴸ} {ν′ : Env∼ Δᴿ}
    {p : C ⊑ᵂ⟨ W ⟩ C′} {q : A ⊑ᵂ⟨ W ⟩ A′}
  → (c : ν ⊢ C ∼ A)
  → (c′ : ν′ ⊢ C′ ∼ A′)
  → (child : StructuralCatchupRightResult W γ M M₀ p)
  → (residual : StructuralCatchupRightResult
      (StructuralCatchupRightResult.W′ child)
      (ECR.mapCtxᴿ
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext child))
        γ)
      (M ⟨ c ⟩)
      (StructuralCatchupRightResult.N′ child
        ⟨ applyConsistencies
          (StructuralCatchupRightResult.χs child) c′ ⟩)
      (ECR.transport⊑ᵂ
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext child))
        q))
  → (∀ {A₀ A₁ : Ty Δᴸ} {c₀ : Conv↓ Δᴸ A₀ A₁} {Xᴿ?}
      → CTI2.SourceConcealPartnerOK W (M ⟨ c ⟩) c₀ Xᴿ?
          (M₀ ⟨ c′ ⟩)
      → CTI2.SourceConcealPartnerOK
          (StructuralCatchupRightResult.W′ residual)
          (M ⟨ c ⟩) c₀
          (mapPivotChanges
            (StructuralCatchupRightResult.χs child ++χ
             StructuralCatchupRightResult.χs residual)
            Xᴿ?)
          (StructuralCatchupRightResult.N′ residual))
  → StructuralCatchupRightResult W γ (M ⟨ c ⟩) (M₀ ⟨ c′ ⟩) q
structural-catchup-compose-paired-target-cast {γ = γ} {A′ = A′}
    {q = q} c c′ child residual partner-endpoint =
  record
    { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ residual
    ; χs = χs₁ ++χ χs₂
    ; Δ′ = StructuralCatchupRightResult.Δ′ residual
    ; W′ = StructuralCatchupRightResult.W′ residual
    ; structural-ext = composeStructuralWorldExtendᴿ plan₁ plan₂
    ; N′ = StructuralCatchupRightResult.N′ residual
    ; final-value = StructuralCatchupRightResult.final-value residual
    ; post-reduction =
        composeReduction
          (cast-↠ c′ (StructuralCatchupRightResult.post-reduction child))
          (StructuralCatchupRightResult.post-reduction residual)
    ; final-relation =
        subst≡
          (λ γ′ → StructuralCatchupRightResult.W′ residual ∣ γ′ ⊢² _
            ⊑ _ ∶ ECR.transport⊑ᵂ ext q)
          (mapCtxᴿ-structural-compose plan₁ plan₂ γ)
          (TBL.⊢²-retarget
            (rel-target-transportᴿ
              (applyTys-++ χs₁ χs₂ A′)
              (ECR.transport⊑ᵂ ext₂
                (ECR.transport⊑ᵂ ext₁ q))
              (StructuralCatchupRightResult.final-relation residual)))
    ; source-conceal-endpoint-partner = partner-endpoint
    }
  where
  χs₁ = StructuralCatchupRightResult.χs child
  χs₂ = StructuralCatchupRightResult.χs residual
  plan₁ = StructuralCatchupRightResult.structural-ext child
  plan₂ = StructuralCatchupRightResult.structural-ext residual
  ext₁ = structural-world-extendᴿ plan₁
  ext₂ = structural-world-extendᴿ plan₂
  ext = structural-world-extendᴿ (composeStructuralWorldExtendᴿ plan₁ plan₂)


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
