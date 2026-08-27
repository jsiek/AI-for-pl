{-# OPTIONS --safe #-}

module proof.DGG.SimSourceRebaseStackProof where

-- File Charter:
--   * Develops forward simulation under a balanced source-rebase stack.
--   * First exposes the complete CTI constructor split; recursive calls are
--     installed across all contextual source reductions before local cases
--     are discharged.
--   * Is parameterized by genuine CTI transport and value catch-up along
--     first-order stack evolution.

open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (_≢_; cong; refl; subst; sym; trans)
open import CastTerms using
  (_·_; _⦂∀_[_]; _⟨_⟩; _↑_; _↓_; _⊕[_]_)
open import Imprecision using (⇒⊑⇒)
open import Primitives using (primArgTy; primResultTy)
open import Types using (_⇒_; _[_]ᵗ)
open import Reduction
open import proof.Reduction
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.CastTermImprecisionTyping using (target-typing)
open import proof.DGG.ConversionPivotAlignment using
  (generator-absent; generator-here)
open import proof.DGG.CatchupSourceRebaseStackDef using
  (CatchupSourceRebaseStackᵀ)
open import proof.DGG.SimSourceRebaseStackDef using
  (SimSourceRebaseStackᵀ)
open import proof.DGG.SourceRebaseStackDef using
  ( composeSourceRebaseStackEvolution
  ; stack-evolution-keep-left
  ; stack-top-evolution
  )
open import proof.DGG.TransportSourceRebaseStackDef using
  (TransportSourceRebaseStackᵀ)
open import proof.DGG.World using (_⊑ᵀ⟨_⟩_)
open import proof.DGG.WorldEvolutionSequence using
  ( multi-aligned
  ; multi-source-conceal
  ; multi-source-conceal-position
  ; multi-source-disaligned
  ; multi-source-mark
  ; multi-source-reveal
  ; multi-source-reveal-position
  ; multi-⊑ᵀ
  ; multi-target-conceal
  ; multi-target-conceal-position
  ; multi-target-reveal
  ; multi-target-reveal-position
  )
import proof.Imprecision as PI
open import proof.TypeSafety.Preservation using (apply-open)


generator-here≠absent : generator-here ≢ generator-absent
generator-here≠absent ()


module _
    (transport-source-rebase-stack : TransportSourceRebaseStackᵀ)
    (catchup-source-rebase-stack : CatchupSourceRebaseStackᵀ)
  where

  sim-source-rebase-stack : SimSourceRebaseStackᵀ
  sim-source-rebase-stack {stack = stack}
      (CTI.x⊑x² source∋ target∋) (pure-step ())

  sim-source-rebase-stack {stack = stack}
      (CTI.ƛ⊑ƛ² related) (pure-step ())

  sim-source-rebase-stack {stack = stack}
      (CTI.·⊑·² {A = A} {A′ = A′} {B = B} {B′ = B′}
        {pA = pA} function-related argument-related)
      (ξ-·₁ {χ = χ} function-step refl)
      with sim-source-rebase-stack
        {stack = stack} function-related function-step
  sim-source-rebase-stack {stack = stack}
      (CTI.·⊑·² {A = A} {A′ = A′} {B = B} {B′ = B′}
        {pA = pA} function-related argument-related)
      (ξ-·₁ {χ = χ} function-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-function , γ′ , γᵖ′ , stack′ , p ,
      target-steps , stack-evolution , related′
      with subst
        (λ T →
          Σ[ r ∈ (applyTy χ A ⇒ applyTy χ B) ⊑ᵀ⟨ γᵖ′ ⟩ T ]
            (γᵖ′ CTI.⊢² _ ⊑ target-function ∶ r))
        (applyTys-⇒ χsᴿ A′ B′)
        (subst
          (λ S →
            Σ[ r ∈ S ⊑ᵀ⟨ γᵖ′ ⟩ applyTys χsᴿ (A′ ⇒ B′) ]
              (γᵖ′ CTI.⊢² _ ⊑ target-function ∶ r))
          (applyTy-⇒ χ A B) (p , related′))
  sim-source-rebase-stack {stack = stack}
      (CTI.·⊑·² {A = A} {A′ = A′} {B = B} {B′ = B′}
        {pA = pA} function-related argument-related)
      (ξ-·₁ {χ = χ} function-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-function , γ′ , γᵖ′ , stack′ , p ,
      target-steps , stack-evolution , related′
    | (⇒⊑⇒ qA qB) , function-related′ =
      Δᴿ′ , Σᴿ′ , χsᴿ ,
      target-function · applyTerms χsᴿ _ , γ′ , γᵖ′ , stack′ , qB ,
      appL-↠ target-steps , stack-evolution ,
      CTI.·⊑·² function-related′
        (subst (λ r → γᵖ′ CTI.⊢² _ ⊑ _ ∶ r)
          (PI.⊑-unique
            (multi-⊑ᵀ (stack-top-evolution stack-evolution) pA) qA)
          (transport-source-rebase-stack
            stack-evolution argument-related))

  sim-source-rebase-stack {stack = stack}
      (CTI.·⊑·² {L′ = L′} {M′ = M′} {A = A} {A′ = A′}
        {B = B} {B′ = B′} function-related argument-related)
      (ξ-·₂ {χ = χ} function-value argument-step refl)
      with catchup-source-rebase-stack
        {stack = stack} function-related function-value
  sim-source-rebase-stack {stack = stack}
      (CTI.·⊑·² {L′ = L′} {M′ = M′} {A = A} {A′ = A′}
        {B = B} {B′ = B′} function-related argument-related)
      (ξ-·₂ {χ = χ} function-value argument-step refl)
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-function , γ₁ , γᵖ₁ , stack₁ , q₁ ,
      function-steps , target-value , stack-evolution₁ , function-related₁
      with sim-source-rebase-stack
        {stack = stack₁}
        (transport-source-rebase-stack stack-evolution₁ argument-related)
        argument-step
  sim-source-rebase-stack {stack = stack}
      (CTI.·⊑·² {L′ = L′} {M′ = M′} {A = A} {A′ = A′}
        {B = B} {B′ = B′} function-related argument-related)
      (ξ-·₂ {χ = χ} function-value argument-step refl)
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-function , γ₁ , γᵖ₁ , stack₁ , q₁ ,
      function-steps , target-value , stack-evolution₁ , function-related₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , target-argument , γ₂ , γᵖ₂ , stack₂ , q₂ ,
      argument-steps , stack-evolution₂ ,
      argument-related₂
      with subst
        (λ T →
          Σ[ r ∈ (applyTy χ A ⇒ applyTy χ B) ⊑ᵀ⟨ γᵖ₂ ⟩ T ]
            (γᵖ₂ CTI.⊢² applyTerm χ _ ⊑
              applyTerms χsᴿ₂ target-function ∶ r))
        (trans
          (cong (applyTys χsᴿ₂) (applyTys-⇒ χsᴿ₁ A′ B′))
          (applyTys-⇒ χsᴿ₂
            (applyTys χsᴿ₁ A′) (applyTys χsᴿ₁ B′)))
        (subst
          (λ S →
            Σ[ r ∈ S ⊑ᵀ⟨ γᵖ₂ ⟩
                applyTys χsᴿ₂ (applyTys χsᴿ₁ (A′ ⇒ B′)) ]
              (γᵖ₂ CTI.⊢² applyTerm χ _ ⊑
                applyTerms χsᴿ₂ target-function ∶ r))
          (applyTy-⇒ χ A B)
          (multi-⊑ᵀ (stack-top-evolution stack-evolution₂) q₁ ,
            transport-source-rebase-stack
              stack-evolution₂ function-related₁))
  sim-source-rebase-stack {stack = stack}
      (CTI.·⊑·² {L′ = L′} {M′ = M′} {A = A} {A′ = A′}
        {B = B} {B′ = B′} function-related argument-related)
      (ξ-·₂ {χ = χ} function-value argument-step refl)
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-function , γ₁ , γᵖ₁ , stack₁ , q₁ ,
      function-steps , target-value , stack-evolution₁ , function-related₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , target-argument , γ₂ , γᵖ₂ , stack₂ , q₂ ,
      argument-steps , stack-evolution₂ ,
      argument-related₂
    | (⇒⊑⇒ qA qB) , function-related₂
      with subst
        (λ T →
          Σ[ r ∈ applyTy χ B ⊑ᵀ⟨ γᵖ₂ ⟩ T ]
            (γᵖ₂ CTI.⊢² applyTerm χ _ · _ ⊑
              applyTerms χsᴿ₂ target-function · target-argument ∶ r))
        (applyTys-++ χsᴿ₁ χsᴿ₂ B′)
        (qB , CTI.·⊑·² function-related₂
          (subst (λ r → γᵖ₂ CTI.⊢² _ ⊑ target-argument ∶ r)
            (PI.⊑-unique q₂ qA) argument-related₂))
  sim-source-rebase-stack {stack = stack}
      (CTI.·⊑·² {L′ = L′} {M′ = M′} {A = A} {A′ = A′}
        {B = B} {B′ = B′} function-related argument-related)
      (ξ-·₂ {χ = χ} function-value argument-step refl)
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-function , γ₁ , γᵖ₁ , stack₁ , q₁ ,
      function-steps , target-value , stack-evolution₁ , function-related₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , target-argument , γ₂ , γᵖ₂ , stack₂ , q₂ ,
      argument-steps , stack-evolution₂ ,
      argument-related₂
    | (⇒⊑⇒ qA qB) , function-related₂
    | qB′ , application-related =
      Δᴿ₂ , Σᴿ₂ , χsᴿ₁ ++χ χsᴿ₂ ,
      applyTerms χsᴿ₂ target-function · target-argument , γ₂ ,
      γᵖ₂ , stack₂ , qB′ ,
      (L′ · M′
         —↠+[ χsᴿ₁ ]⟨ appL-↠ function-steps ⟩
       target-function · applyTerms χsᴿ₁ M′
         —↠[ χsᴿ₂ ]⟨ appR-↠ target-value argument-steps ⟩
       applyTerms χsᴿ₂ target-function · target-argument ∎[]) ,
      composeSourceRebaseStackEvolution
        stack-evolution₁ stack-evolution₂ ,
      application-related

  sim-source-rebase-stack {stack = stack}
      (CTI.·⊑·² function-related argument-related)
      (pure-step (β argument-value)) = {!!}
  sim-source-rebase-stack {stack = stack}
      (CTI.·⊑·² function-related argument-related)
      (pure-step (β-⇒ function-value argument-value)) = {!!}
  sim-source-rebase-stack {stack = stack}
      (CTI.·⊑·² function-related argument-related)
      (pure-step (β-reveal-⇒ function-value argument-value)) = {!!}
  sim-source-rebase-stack {stack = stack}
      (CTI.·⊑·² function-related argument-related)
      (pure-step (β-conceal-⇒ function-value argument-value)) = {!!}
  sim-source-rebase-stack {stack = stack}
      relation@(CTI.·⊑·² {L′ = L′} {M′ = M′} {pB = pB}
        function-related argument-related)
      (pure-step blame-·₁) =
    _ , _ , [] , L′ · M′ , _ , _ , stack , pB ,
    (L′ · M′ ∎[]) , stack-evolution-keep-left ,
    CTI.blame⊑² (target-typing relation) pB
  sim-source-rebase-stack {stack = stack}
      relation@(CTI.·⊑·² {L′ = L′} {M′ = M′} {pB = pB}
        function-related argument-related)
      (pure-step (blame-·₂ source-value)) =
    _ , _ , [] , L′ · M′ , _ , _ , stack , pB ,
    (L′ · M′ ∎[]) , stack-evolution-keep-left ,
    CTI.blame⊑² (target-typing relation) pB

  sim-source-rebase-stack {stack = stack}
      (CTI.Λ⊑Λ² source-value target-value related q) (pure-step ())

  sim-source-rebase-stack {stack = stack}
      (CTI.Λ⊑² nonvar occurs source-value target⊢ related q)
      (pure-step ())

  sim-source-rebase-stack {stack = stack}
      (CTI.•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ related q r)
      (ξ-• {χ = χ} source-step refl refl)
      with sim-source-rebase-stack {stack = stack} related source-step
  sim-source-rebase-stack {stack = stack}
      (CTI.•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ related q r)
      (ξ-• {χ = χ} source-step refl refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , p ,
      target-steps , stack-evolution , related′
      rewrite applyTy-∀ χ C | applyTys-∀ χsᴿ C′
      with p | related′
  sim-source-rebase-stack {stack = stack}
      (CTI.•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ related q r)
      (ξ-• {χ = χ} source-step refl refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , p ,
      target-steps , stack-evolution , related′
    | p∀′ | related″
      with subst
        (λ S →
          Σ[ s ∈ S ⊑ᵀ⟨ γᵖ′ ⟩ applyTys χsᴿ (C′ [ A′ ]ᵗ) ]
            (γᵖ′ CTI.⊢²
              _ ⦂∀ applyBody χ C [ applyTy χ A ] ⊑
              target-body ⦂∀ applyBodies χsᴿ C′
                [ applyTys χsᴿ A′ ] ∶ s))
        (sym (apply-open χ C A))
        (subst
          (λ T →
            Σ[ s ∈
              ((applyBody χ C) [ applyTy χ A ]ᵗ) ⊑ᵀ⟨ γᵖ′ ⟩ T ]
              (γᵖ′ CTI.⊢²
                _ ⦂∀ applyBody χ C [ applyTy χ A ] ⊑
                target-body ⦂∀ applyBodies χsᴿ C′
                  [ applyTys χsᴿ A′ ] ∶ s))
          (sym (applyTys-open χsᴿ C′ A′))
          (subst
              (λ T → ((applyBody χ C) [ applyTy χ A ]ᵗ)
                ⊑ᵀ⟨ γᵖ′ ⟩ T)
              (applyTys-open χsᴿ C′ A′)
              (subst (λ S → S ⊑ᵀ⟨ γᵖ′ ⟩
                  applyTys χsᴿ (C′ [ A′ ]ᵗ))
                (apply-open χ C A) (multi-⊑ᵀ (stack-top-evolution stack-evolution) r)) ,
            CTI.•⊑•² p∀′ related″ (multi-⊑ᵀ (stack-top-evolution stack-evolution) q)
              (subst
                (λ T → ((applyBody χ C) [ applyTy χ A ]ᵗ)
                  ⊑ᵀ⟨ γᵖ′ ⟩ T)
                (applyTys-open χsᴿ C′ A′)
                (subst (λ S → S ⊑ᵀ⟨ γᵖ′ ⟩
                    applyTys χsᴿ (C′ [ A′ ]ᵗ))
                  (apply-open χ C A) (multi-⊑ᵀ (stack-top-evolution stack-evolution) r)))))
  sim-source-rebase-stack {stack = stack}
      (CTI.•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ related q r)
      (ξ-• {χ = χ} source-step refl refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , p ,
      target-steps , stack-evolution , related′
    | p∀′ | related″
    | r′ , type-application-related =
      Δᴿ′ , Σᴿ′ , χsᴿ ,
      target-body ⦂∀ applyBodies χsᴿ C′ [ applyTys χsᴿ A′ ] ,
      γ′ , γᵖ′ , stack′ , r′ , typeApp-↠ target-steps , stack-evolution , type-application-related

  sim-source-rebase-stack {stack = stack}
      (CTI.•⊑•² p∀ related q r)
      (pure-step (β-∀ source-value instantiated)) = {!!}
  sim-source-rebase-stack {stack = stack}
      relation@(CTI.•⊑•² {M′ = M′} {C′ = C′} {A′ = A′}
        p∀ related q r)
      (pure-step blame-•) =
    _ , _ , [] , M′ ⦂∀ C′ [ A′ ] , _ , _ , stack , r ,
    (M′ ⦂∀ C′ [ A′ ] ∎[]) ,
    stack-evolution-keep-left ,
    CTI.blame⊑² (target-typing relation) r
  sim-source-rebase-stack {stack = stack}
      (CTI.•⊑•² p∀ related q r)
      (β-Λ source-value) = {!!}
  sim-source-rebase-stack {stack = stack}
      (CTI.•⊑•² p∀ related q r)
      (β-gen source-value A≠★ safe) = {!!}
  sim-source-rebase-stack {stack = stack}
      (CTI.•⊑•² p∀ related q r)
      (β-reveal-∀ source-value) = {!!}
  sim-source-rebase-stack {stack = stack}
      (CTI.•⊑•² p∀ related q r)
      (β-conceal-∀ source-value) = {!!}

  sim-source-rebase-stack {stack = stack}
      (CTI.•⊑² {C = C} {A = A} {B = B} p∀ related q r)
      (ξ-• {χ = χ} source-step refl refl)
      with sim-source-rebase-stack {stack = stack} related source-step
  sim-source-rebase-stack {stack = stack}
      (CTI.•⊑² {C = C} {A = A} {B = B} p∀ related q r)
      (ξ-• {χ = χ} source-step refl refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , p ,
      target-steps , stack-evolution , related′
      rewrite applyTy-∀ χ C
      with p | related′
  sim-source-rebase-stack {stack = stack}
      (CTI.•⊑² {C = C} {A = A} {B = B} p∀ related q r)
      (ξ-• {χ = χ} source-step refl refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , p ,
      target-steps , stack-evolution , related′
    | p∀′ | related″
      with subst
        (λ S →
          Σ[ s ∈ S ⊑ᵀ⟨ γᵖ′ ⟩ applyTys χsᴿ B ]
            (γᵖ′ CTI.⊢²
              _ ⦂∀ applyBody χ C [ applyTy χ A ] ⊑
              target-body ∶ s))
        (sym (apply-open χ C A))
        (subst (λ S → S ⊑ᵀ⟨ γᵖ′ ⟩ applyTys χsᴿ B)
          (apply-open χ C A) (multi-⊑ᵀ (stack-top-evolution stack-evolution) r) ,
          CTI.•⊑² p∀′ related″
            (subst (λ T → applyTy χ A ⊑ᵀ⟨ γᵖ′ ⟩ T)
              (applyTys-★ χsᴿ) (multi-⊑ᵀ (stack-top-evolution stack-evolution) q))
            (subst (λ S → S ⊑ᵀ⟨ γᵖ′ ⟩ applyTys χsᴿ B)
              (apply-open χ C A) (multi-⊑ᵀ (stack-top-evolution stack-evolution) r)))
  sim-source-rebase-stack {stack = stack}
      (CTI.•⊑² {C = C} {A = A} {B = B} p∀ related q r)
      (ξ-• {χ = χ} source-step refl refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , p ,
      target-steps , stack-evolution , related′
    | p∀′ | related″
    | r′ , whole-related =
      Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , r′ ,
      target-steps , stack-evolution , whole-related

  sim-source-rebase-stack {stack = stack}
      (CTI.•⊑² p∀ related q r)
      (pure-step (β-∀ source-value instantiated)) = {!!}
  sim-source-rebase-stack {stack = stack}
      relation@(CTI.•⊑² {M′ = M′} p∀ related q r)
      (pure-step blame-•) =
    _ , _ , [] , M′ , _ , _ , stack , r ,
    (M′ ∎[]) , stack-evolution-keep-left ,
    CTI.blame⊑² (target-typing relation) r
  sim-source-rebase-stack {stack = stack}
      (CTI.•⊑² p∀ related q r)
      (β-Λ source-value) = {!!}
  sim-source-rebase-stack {stack = stack}
      (CTI.•⊑² p∀ related q r)
      (β-gen source-value A≠★ safe) = {!!}
  sim-source-rebase-stack {stack = stack}
      (CTI.•⊑² p∀ related q r)
      (β-reveal-∀ source-value) = {!!}
  sim-source-rebase-stack {stack = stack}
      (CTI.•⊑² p∀ related q r)
      (β-conceal-∀ source-value) = {!!}

  sim-source-rebase-stack {stack = stack}
      (CTI.κ⊑κ² constant p) (pure-step ())

  sim-source-rebase-stack {stack = stack}
      (CTI.cast⊑cast² source-cast target-cast related q)
      (ξ-⟨⟩ {χ = χ} source-step refl)
      with sim-source-rebase-stack {stack = stack} related source-step
  sim-source-rebase-stack {stack = stack}
      (CTI.cast⊑cast² source-cast target-cast related q)
      (ξ-⟨⟩ {χ = χ} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , r ,
      target-steps , stack-evolution , related′ =
      Δᴿ′ , Σᴿ′ , χsᴿ ,
      target-body ⟨ applyConsistencies χsᴿ target-cast ⟩ , γ′ , γᵖ′ , stack′ ,
      multi-⊑ᵀ (stack-top-evolution stack-evolution) q ,
      cast-↠ target-cast target-steps , stack-evolution ,
      CTI.cast⊑cast² (applyConsistency χ source-cast)
        (applyConsistencies χsᴿ target-cast) related′
        (multi-⊑ᵀ (stack-top-evolution stack-evolution) q)

  sim-source-rebase-stack {stack = stack}
      (CTI.cast⊑cast² source-cast target-cast related q)
      (pure-step (β-id source-value)) = {!!}
  sim-source-rebase-stack {stack = stack}
      (CTI.cast⊑cast² source-cast target-cast related q)
      (pure-step (ground source-value unequal)) = {!!}
  sim-source-rebase-stack {stack = stack}
      (CTI.cast⊑cast² source-cast target-cast related q)
      (pure-step (expand source-value unequal)) = {!!}
  sim-source-rebase-stack {stack = stack}
      (CTI.cast⊑cast² source-cast target-cast related q)
      (pure-step (tag-untag source-value)) = {!!}
  sim-source-rebase-stack {stack = stack}
      relation@(CTI.cast⊑cast² {M′ = M′}
        source-cast target-cast related q)
      (pure-step (tag-untag-bad source-value unequal)) =
    _ , _ , [] , M′ ⟨ target-cast ⟩ , _ , _ , stack , q ,
    (M′ ⟨ target-cast ⟩ ∎[]) , stack-evolution-keep-left ,
    CTI.blame⊑² (target-typing relation) q
  sim-source-rebase-stack {stack = stack}
      relation@(CTI.cast⊑cast² {M′ = M′}
        source-cast target-cast related q)
      (pure-step (blame-bot-intro source-value)) =
    _ , _ , [] , M′ ⟨ target-cast ⟩ , _ , _ , stack , q ,
    (M′ ⟨ target-cast ⟩ ∎[]) , stack-evolution-keep-left ,
    CTI.blame⊑² (target-typing relation) q
  sim-source-rebase-stack {stack = stack}
      relation@(CTI.cast⊑cast² {M′ = M′}
        source-cast target-cast related q)
      (pure-step blame-⟨⟩) =
    _ , _ , [] , M′ ⟨ target-cast ⟩ , _ , _ , stack , q ,
    (M′ ⟨ target-cast ⟩ ∎[]) , stack-evolution-keep-left ,
    CTI.blame⊑² (target-typing relation) q
  sim-source-rebase-stack {stack = stack}
      (CTI.cast⊑cast² source-cast target-cast related q)
      (β-inst source-value B≠★) = {!!}

  sim-source-rebase-stack {stack = stack}
      (CTI.⊑cast² target-cast related q) source-step
      with sim-source-rebase-stack {stack = stack} related source-step
  sim-source-rebase-stack {stack = stack}
      (CTI.⊑cast² target-cast related q) source-step
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , r ,
      target-steps , stack-evolution , related′ =
      Δᴿ′ , Σᴿ′ , χsᴿ ,
      target-body ⟨ applyConsistencies χsᴿ target-cast ⟩ , γ′ , γᵖ′ , stack′ ,
      multi-⊑ᵀ (stack-top-evolution stack-evolution) q ,
      cast-↠ target-cast target-steps , stack-evolution ,
      CTI.⊑cast² (applyConsistencies χsᴿ target-cast) related′
        (multi-⊑ᵀ (stack-top-evolution stack-evolution) q)

  sim-source-rebase-stack {stack = stack}
      (CTI.⊑reveal-identity target-reveal absent related q)
      source-step
      with sim-source-rebase-stack {stack = stack} related source-step
  sim-source-rebase-stack {stack = stack}
      (CTI.⊑reveal-identity target-reveal absent related q)
      source-step
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , r ,
      target-steps , stack-evolution , related′ =
      Δᴿ′ , Σᴿ′ , χsᴿ , target-body ↑ applyReveals χsᴿ _ , γ′ , γᵖ′ , stack′ ,
      multi-⊑ᵀ (stack-top-evolution stack-evolution) q ,
      reveal-↠ _ target-steps , stack-evolution ,
      CTI.⊑reveal-identity
        (multi-target-reveal (stack-top-evolution stack-evolution) target-reveal)
        (trans
          (multi-target-reveal-position (stack-top-evolution stack-evolution) target-reveal)
          absent)
        related′ (multi-⊑ᵀ (stack-top-evolution stack-evolution) q)

  sim-source-rebase-stack {stack = stack}
      (CTI.⊑conceal-identity target-conceal absent related q)
      source-step
      with sim-source-rebase-stack {stack = stack} related source-step
  sim-source-rebase-stack {stack = stack}
      (CTI.⊑conceal-identity target-conceal absent related q)
      source-step
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , r ,
      target-steps , stack-evolution , related′ =
      Δᴿ′ , Σᴿ′ , χsᴿ , target-body ↓ applyConceals χsᴿ _ , γ′ , γᵖ′ , stack′ ,
      multi-⊑ᵀ (stack-top-evolution stack-evolution) q ,
      conceal-↠ _ target-steps , stack-evolution ,
      CTI.⊑conceal-identity
        (multi-target-conceal (stack-top-evolution stack-evolution) target-conceal)
        (trans
          (multi-target-conceal-position (stack-top-evolution stack-evolution) target-conceal)
          absent)
        related′ (multi-⊑ᵀ (stack-top-evolution stack-evolution) q)

  sim-source-rebase-stack {stack = stack}
      (CTI.cast⊑² source-cast related q)
      (ξ-⟨⟩ {χ = χ} source-step refl)
      with sim-source-rebase-stack {stack = stack} related source-step
  sim-source-rebase-stack {stack = stack}
      (CTI.cast⊑² source-cast related q)
      (ξ-⟨⟩ {χ = χ} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , r ,
      target-steps , stack-evolution , related′ =
      Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ ,
      multi-⊑ᵀ (stack-top-evolution stack-evolution) q , target-steps , stack-evolution ,
      CTI.cast⊑² (applyConsistency χ source-cast) related′
        (multi-⊑ᵀ (stack-top-evolution stack-evolution) q)

  sim-source-rebase-stack {stack = stack}
      (CTI.cast⊑² source-cast related q)
      (pure-step (β-id source-value)) = {!!}
  sim-source-rebase-stack {stack = stack}
      (CTI.cast⊑² source-cast related q)
      (pure-step (ground source-value unequal)) = {!!}
  sim-source-rebase-stack {stack = stack}
      (CTI.cast⊑² source-cast related q)
      (pure-step (expand source-value unequal)) = {!!}
  sim-source-rebase-stack {stack = stack}
      (CTI.cast⊑² source-cast related q)
      (pure-step (tag-untag source-value)) = {!!}
  sim-source-rebase-stack {stack = stack}
      relation@(CTI.cast⊑² {M′ = M′} source-cast related q)
      (pure-step (tag-untag-bad source-value unequal)) =
    _ , _ , [] , M′ , _ , _ , stack , q ,
    (M′ ∎[]) , stack-evolution-keep-left ,
    CTI.blame⊑² (target-typing relation) q
  sim-source-rebase-stack {stack = stack}
      relation@(CTI.cast⊑² {M′ = M′} source-cast related q)
      (pure-step (blame-bot-intro source-value)) =
    _ , _ , [] , M′ , _ , _ , stack , q ,
    (M′ ∎[]) , stack-evolution-keep-left ,
    CTI.blame⊑² (target-typing relation) q
  sim-source-rebase-stack {stack = stack}
      relation@(CTI.cast⊑² {M′ = M′} source-cast related q)
      (pure-step blame-⟨⟩) =
    _ , _ , [] , M′ , _ , _ , stack , q ,
    (M′ ∎[]) , stack-evolution-keep-left ,
    CTI.blame⊑² (target-typing relation) q
  sim-source-rebase-stack {stack = stack}
      (CTI.cast⊑² source-cast related q)
      (β-inst source-value B≠★) = {!!}

  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑-identity {c = c} source-reveal absent related q)
      (ξ-reveal {χ = keep} source-step refl)
      with sim-source-rebase-stack {stack = stack} related source-step
  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑-identity {c = c} source-reveal absent related q)
      (ξ-reveal {χ = keep} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , r ,
      target-steps , stack-evolution , related′ =
      Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ ,
      multi-⊑ᵀ (stack-top-evolution stack-evolution) q , target-steps , stack-evolution ,
      subst
        (λ K → γᵖ′ CTI.⊢² K ⊑ target-body ∶
          multi-⊑ᵀ (stack-top-evolution stack-evolution) q)
        (sym (renamedReveal-term _ c))
        (CTI.reveal⊑-identity
          (multi-source-reveal (stack-top-evolution stack-evolution) source-reveal)
          (trans
            (multi-source-reveal-position (stack-top-evolution stack-evolution) source-reveal)
            absent)
          related′ (multi-⊑ᵀ (stack-top-evolution stack-evolution) q))

  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑-identity {c = c} source-reveal absent related q)
      (ξ-reveal {χ = bind A} source-step refl)
      with sim-source-rebase-stack {stack = stack} related source-step
  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑-identity {c = c} source-reveal absent related q)
      (ξ-reveal {χ = bind A} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , r ,
      target-steps , stack-evolution , related′ =
      Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ ,
      multi-⊑ᵀ (stack-top-evolution stack-evolution) q , target-steps , stack-evolution ,
      CTI.reveal⊑-identity
        (multi-source-reveal (stack-top-evolution stack-evolution) source-reveal)
        (trans
          (multi-source-reveal-position (stack-top-evolution stack-evolution) source-reveal)
          absent)
        related′ (multi-⊑ᵀ (stack-top-evolution stack-evolution) q)

  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑-identity {M′ = M′} {p = p}
        source-reveal absent related q)
      (pure-step (id-reveal source-value)) =
    _ , _ , [] , M′ , _ , _ , stack , q ,
    (M′ ∎[]) , stack-evolution-keep-left ,
    subst (λ r → _ CTI.⊢² _ ⊑ M′ ∶ r) (PI.⊑-unique p q) related
  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑-identity
        (Conv.⊢↑-unseal member) absent related q)
      (pure-step (conceal-reveal source-value)) =
    ⊥-elim (generator-here≠absent absent)
  sim-source-rebase-stack {stack = stack}
      relation@(CTI.reveal⊑-identity {M′ = M′}
        source-reveal absent related q)
      (pure-step blame-reveal) =
    _ , _ , [] , M′ , _ , _ , stack , q ,
    (M′ ∎[]) , stack-evolution-keep-left ,
    CTI.blame⊑² (target-typing relation) q

  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑-only² {c = c} source-reveal present mark free
        represented related q) (ξ-reveal {χ = keep} source-step refl)
      with sim-source-rebase-stack {stack = stack} related source-step
  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑-only² {c = c} source-reveal present mark free
        represented related q) (ξ-reveal {χ = keep} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , r ,
      target-steps , stack-evolution , related′ =
      Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ ,
      multi-⊑ᵀ (stack-top-evolution stack-evolution) q , target-steps , stack-evolution ,
      subst
        (λ K → γᵖ′ CTI.⊢² K ⊑ target-body ∶
          multi-⊑ᵀ (stack-top-evolution stack-evolution) q)
        (sym (renamedReveal-term _ c))
        (CTI.reveal⊑-only²
          (multi-source-reveal (stack-top-evolution stack-evolution) source-reveal)
          (λ absent′ → present
            (trans
              (sym (multi-source-reveal-position
                (stack-top-evolution stack-evolution) source-reveal)) absent′))
          (multi-source-mark (stack-top-evolution stack-evolution) mark)
          (multi-source-disaligned (stack-top-evolution stack-evolution) free)
          (subst (λ T → _ ⊑ᵀ⟨ γᵖ′ ⟩ T)
            (applyTys-★ χsᴿ)
            (multi-⊑ᵀ (stack-top-evolution stack-evolution) represented))
          related′ (multi-⊑ᵀ (stack-top-evolution stack-evolution) q))

  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑-only² {c = c} source-reveal present mark free
        represented related q) (ξ-reveal {χ = bind A} source-step refl)
      with sim-source-rebase-stack {stack = stack} related source-step
  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑-only² {c = c} source-reveal present mark free
        represented related q) (ξ-reveal {χ = bind A} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , r ,
      target-steps , stack-evolution , related′ =
      Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ ,
      multi-⊑ᵀ (stack-top-evolution stack-evolution) q , target-steps , stack-evolution ,
      CTI.reveal⊑-only²
        (multi-source-reveal (stack-top-evolution stack-evolution) source-reveal)
        (λ absent′ → present
          (trans
            (sym (multi-source-reveal-position
              (stack-top-evolution stack-evolution) source-reveal)) absent′))
        (multi-source-mark (stack-top-evolution stack-evolution) mark)
        (multi-source-disaligned (stack-top-evolution stack-evolution) free)
        (subst (λ T → _ ⊑ᵀ⟨ γᵖ′ ⟩ T)
          (applyTys-★ χsᴿ) (multi-⊑ᵀ (stack-top-evolution stack-evolution) represented))
        related′ (multi-⊑ᵀ (stack-top-evolution stack-evolution) q)

  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑-only²
        (Conv.⊢↑-id-var member X≠Y) present mark free represented
        related q)
      (pure-step (id-reveal source-value)) =
    ⊥-elim (present refl)
  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑-only²
        (Conv.⊢↑-id-base member) present mark free represented
        related q)
      (pure-step (id-reveal source-value)) =
    ⊥-elim (present refl)
  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑-only²
        (Conv.⊢↑-id-star member) present mark free represented
        related q)
      (pure-step (id-reveal source-value)) =
    ⊥-elim (present refl)
  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑-only² source-reveal present mark free represented
        related q)
      (pure-step (conceal-reveal source-value)) = {!!}
  sim-source-rebase-stack {stack = stack}
      relation@(CTI.reveal⊑-only² {M′ = M′}
        source-reveal present mark free represented related q)
      (pure-step blame-reveal) =
    _ , _ , [] , M′ , _ , _ , stack , q ,
    (M′ ∎[]) , stack-evolution-keep-left ,
    CTI.blame⊑² (target-typing relation) q

  sim-source-rebase-stack {stack = stack}
      (CTI.conceal⊑-identity {c = c} source-conceal absent related q)
      (ξ-conceal {χ = keep} source-step refl)
      with sim-source-rebase-stack {stack = stack} related source-step
  sim-source-rebase-stack {stack = stack}
      (CTI.conceal⊑-identity {c = c} source-conceal absent related q)
      (ξ-conceal {χ = keep} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , r ,
      target-steps , stack-evolution , related′ =
      Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ ,
      multi-⊑ᵀ (stack-top-evolution stack-evolution) q , target-steps , stack-evolution ,
      subst
        (λ K → γᵖ′ CTI.⊢² K ⊑ target-body ∶
          multi-⊑ᵀ (stack-top-evolution stack-evolution) q)
        (sym (renamedConceal-term _ c))
        (CTI.conceal⊑-identity
          (multi-source-conceal (stack-top-evolution stack-evolution) source-conceal)
          (trans
            (multi-source-conceal-position (stack-top-evolution stack-evolution) source-conceal)
            absent)
          related′ (multi-⊑ᵀ (stack-top-evolution stack-evolution) q))

  sim-source-rebase-stack {stack = stack}
      (CTI.conceal⊑-identity {c = c} source-conceal absent related q)
      (ξ-conceal {χ = bind A} source-step refl)
      with sim-source-rebase-stack {stack = stack} related source-step
  sim-source-rebase-stack {stack = stack}
      (CTI.conceal⊑-identity {c = c} source-conceal absent related q)
      (ξ-conceal {χ = bind A} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , r ,
      target-steps , stack-evolution , related′ =
      Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ ,
      multi-⊑ᵀ (stack-top-evolution stack-evolution) q , target-steps , stack-evolution ,
      CTI.conceal⊑-identity
        (multi-source-conceal (stack-top-evolution stack-evolution) source-conceal)
        (trans
          (multi-source-conceal-position (stack-top-evolution stack-evolution) source-conceal)
          absent)
        related′ (multi-⊑ᵀ (stack-top-evolution stack-evolution) q)

  sim-source-rebase-stack {stack = stack}
      (CTI.conceal⊑-identity {M′ = M′} {p = p}
        source-conceal absent related q)
      (pure-step (id-conceal source-value)) =
    _ , _ , [] , M′ , _ , _ , stack , q ,
    (M′ ∎[]) , stack-evolution-keep-left ,
    subst (λ r → _ CTI.⊢² _ ⊑ M′ ∶ r) (PI.⊑-unique p q) related
  sim-source-rebase-stack {stack = stack}
      relation@(CTI.conceal⊑-identity {M′ = M′}
        source-conceal absent related q)
      (pure-step blame-conceal) =
    _ , _ , [] , M′ , _ , _ , stack , q ,
    (M′ ∎[]) , stack-evolution-keep-left ,
    CTI.blame⊑² (target-typing relation) q

  sim-source-rebase-stack {stack = stack}
      (CTI.conceal⊑-only² {c = c} source-conceal present mark free
        represented related q) (ξ-conceal {χ = keep} source-step refl)
      with sim-source-rebase-stack {stack = stack} related source-step
  sim-source-rebase-stack {stack = stack}
      (CTI.conceal⊑-only² {c = c} source-conceal present mark free
        represented related q) (ξ-conceal {χ = keep} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , r ,
      target-steps , stack-evolution , related′ =
      Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ ,
      multi-⊑ᵀ (stack-top-evolution stack-evolution) q , target-steps , stack-evolution ,
      subst
        (λ K → γᵖ′ CTI.⊢² K ⊑ target-body ∶
          multi-⊑ᵀ (stack-top-evolution stack-evolution) q)
        (sym (renamedConceal-term _ c))
        (CTI.conceal⊑-only²
          (multi-source-conceal (stack-top-evolution stack-evolution) source-conceal)
          (λ absent′ → present
            (trans
              (sym (multi-source-conceal-position
                (stack-top-evolution stack-evolution) source-conceal)) absent′))
          (multi-source-mark (stack-top-evolution stack-evolution) mark)
          (multi-source-disaligned (stack-top-evolution stack-evolution) free)
          (subst (λ T → _ ⊑ᵀ⟨ γᵖ′ ⟩ T)
            (applyTys-★ χsᴿ)
            (multi-⊑ᵀ (stack-top-evolution stack-evolution) represented))
          related′ (multi-⊑ᵀ (stack-top-evolution stack-evolution) q))

  sim-source-rebase-stack {stack = stack}
      (CTI.conceal⊑-only² {c = c} source-conceal present mark free
        represented related q) (ξ-conceal {χ = bind A} source-step refl)
      with sim-source-rebase-stack {stack = stack} related source-step
  sim-source-rebase-stack {stack = stack}
      (CTI.conceal⊑-only² {c = c} source-conceal present mark free
        represented related q) (ξ-conceal {χ = bind A} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , r ,
      target-steps , stack-evolution , related′ =
      Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ ,
      multi-⊑ᵀ (stack-top-evolution stack-evolution) q , target-steps , stack-evolution ,
      CTI.conceal⊑-only²
        (multi-source-conceal (stack-top-evolution stack-evolution) source-conceal)
        (λ absent′ → present
          (trans
            (sym (multi-source-conceal-position
              (stack-top-evolution stack-evolution) source-conceal)) absent′))
        (multi-source-mark (stack-top-evolution stack-evolution) mark)
        (multi-source-disaligned (stack-top-evolution stack-evolution) free)
        (subst (λ T → _ ⊑ᵀ⟨ γᵖ′ ⟩ T)
          (applyTys-★ χsᴿ) (multi-⊑ᵀ (stack-top-evolution stack-evolution) represented))
        related′ (multi-⊑ᵀ (stack-top-evolution stack-evolution) q)

  sim-source-rebase-stack {stack = stack}
      (CTI.conceal⊑-only²
        (Conv.⊢↓-id-var member X≠Y) present mark free represented
        related q)
      (pure-step (id-conceal source-value)) =
    ⊥-elim (present refl)
  sim-source-rebase-stack {stack = stack}
      (CTI.conceal⊑-only²
        (Conv.⊢↓-id-base member) present mark free represented
        related q)
      (pure-step (id-conceal source-value)) =
    ⊥-elim (present refl)
  sim-source-rebase-stack {stack = stack}
      (CTI.conceal⊑-only²
        (Conv.⊢↓-id-star member) present mark free represented
        related q)
      (pure-step (id-conceal source-value)) =
    ⊥-elim (present refl)
  sim-source-rebase-stack {stack = stack}
      relation@(CTI.conceal⊑-only² {M′ = M′}
        source-conceal present mark free represented related q)
      (pure-step blame-conceal) =
    _ , _ , [] , M′ , _ , _ , stack , q ,
    (M′ ∎[]) , stack-evolution-keep-left ,
    CTI.blame⊑² (target-typing relation) q

  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑reveal² {c = c} {c′ = c′}
        source-reveal target-reveal positions aligned represented related q)
      (ξ-reveal {χ = keep} source-step refl)
      with sim-source-rebase-stack {stack = stack} related source-step
  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑reveal² {c = c} {c′ = c′}
        source-reveal target-reveal positions aligned represented related q)
      (ξ-reveal {χ = keep} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , r ,
      target-steps , stack-evolution , related′ =
      Δᴿ′ , Σᴿ′ , χsᴿ , target-body ↑ applyReveals χsᴿ c′ , γ′ , γᵖ′ , stack′ ,
      multi-⊑ᵀ (stack-top-evolution stack-evolution) q , reveal-↠ c′ target-steps , stack-evolution ,
      subst
        (λ K → γᵖ′ CTI.⊢² K ⊑ target-body ↑ applyReveals χsᴿ c′ ∶
          multi-⊑ᵀ (stack-top-evolution stack-evolution) q)
        (sym (renamedReveal-term _ c))
        (CTI.reveal⊑reveal²
          (multi-source-reveal (stack-top-evolution stack-evolution) source-reveal)
          (multi-target-reveal (stack-top-evolution stack-evolution) target-reveal)
          (trans
            (multi-source-reveal-position (stack-top-evolution stack-evolution) source-reveal)
            (trans positions
              (sym (multi-target-reveal-position
                (stack-top-evolution stack-evolution) target-reveal))))
          (multi-aligned (stack-top-evolution stack-evolution) aligned)
          (multi-⊑ᵀ (stack-top-evolution stack-evolution) represented)
          related′ (multi-⊑ᵀ (stack-top-evolution stack-evolution) q))

  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑reveal² {c = c} {c′ = c′}
        source-reveal target-reveal positions aligned represented related q)
      (ξ-reveal {χ = bind A} source-step refl)
      with sim-source-rebase-stack {stack = stack} related source-step
  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑reveal² {c = c} {c′ = c′}
        source-reveal target-reveal positions aligned represented related q)
      (ξ-reveal {χ = bind A} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , r ,
      target-steps , stack-evolution , related′ =
      Δᴿ′ , Σᴿ′ , χsᴿ , target-body ↑ applyReveals χsᴿ c′ , γ′ , γᵖ′ , stack′ ,
      multi-⊑ᵀ (stack-top-evolution stack-evolution) q , reveal-↠ c′ target-steps , stack-evolution ,
      CTI.reveal⊑reveal²
        (multi-source-reveal (stack-top-evolution stack-evolution) source-reveal)
        (multi-target-reveal (stack-top-evolution stack-evolution) target-reveal)
        (trans
          (multi-source-reveal-position (stack-top-evolution stack-evolution) source-reveal)
          (trans positions
            (sym (multi-target-reveal-position
              (stack-top-evolution stack-evolution) target-reveal))))
        (multi-aligned (stack-top-evolution stack-evolution) aligned)
        (multi-⊑ᵀ (stack-top-evolution stack-evolution) represented)
        related′ (multi-⊑ᵀ (stack-top-evolution stack-evolution) q)

  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑reveal² {M′ = M′} {c′ = c′}
        (Conv.⊢↑-id-var member X≠Y) target-reveal positions aligned
        represented related q)
      (pure-step (id-reveal source-value)) =
    _ , _ , [] , M′ ↑ c′ , _ , _ , stack , q ,
    (M′ ↑ c′ ∎[]) , stack-evolution-keep-left ,
    CTI.⊑reveal-identity target-reveal (sym positions) related q
  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑reveal² {M′ = M′} {c′ = c′}
        (Conv.⊢↑-id-base member) target-reveal positions aligned
        represented related q)
      (pure-step (id-reveal source-value)) =
    _ , _ , [] , M′ ↑ c′ , _ , _ , stack , q ,
    (M′ ↑ c′ ∎[]) , stack-evolution-keep-left ,
    CTI.⊑reveal-identity target-reveal (sym positions) related q
  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑reveal² {M′ = M′} {c′ = c′}
        (Conv.⊢↑-id-star member) target-reveal positions aligned
        represented related q)
      (pure-step (id-reveal source-value)) =
    _ , _ , [] , M′ ↑ c′ , _ , _ , stack , q ,
    (M′ ↑ c′ ∎[]) , stack-evolution-keep-left ,
    CTI.⊑reveal-identity target-reveal (sym positions) related q
  sim-source-rebase-stack {stack = stack}
      (CTI.reveal⊑reveal² source-reveal target-reveal positions aligned
        represented related q)
      (pure-step (conceal-reveal source-value)) = {!!}
  sim-source-rebase-stack {stack = stack}
      relation@(CTI.reveal⊑reveal² {M′ = M′} {c′ = c′}
        source-reveal target-reveal positions aligned represented related q)
      (pure-step blame-reveal) =
    _ , _ , [] , M′ ↑ c′ , _ , _ , stack , q ,
    (M′ ↑ c′ ∎[]) , stack-evolution-keep-left ,
    CTI.blame⊑² (target-typing relation) q

  sim-source-rebase-stack {stack = stack}
      (CTI.conceal⊑conceal² {c = c} {c′ = c′}
        source-conceal target-conceal positions aligned represented related q)
      (ξ-conceal {χ = keep} source-step refl)
      with sim-source-rebase-stack {stack = stack} related source-step
  sim-source-rebase-stack {stack = stack}
      (CTI.conceal⊑conceal² {c = c} {c′ = c′}
        source-conceal target-conceal positions aligned represented related q)
      (ξ-conceal {χ = keep} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , r ,
      target-steps , stack-evolution , related′ =
      Δᴿ′ , Σᴿ′ , χsᴿ , target-body ↓ applyConceals χsᴿ c′ , γ′ , γᵖ′ , stack′ ,
      multi-⊑ᵀ (stack-top-evolution stack-evolution) q , conceal-↠ c′ target-steps , stack-evolution ,
      subst
        (λ K → γᵖ′ CTI.⊢² K ⊑ target-body ↓ applyConceals χsᴿ c′ ∶
          multi-⊑ᵀ (stack-top-evolution stack-evolution) q)
        (sym (renamedConceal-term _ c))
        (CTI.conceal⊑conceal²
          (multi-source-conceal (stack-top-evolution stack-evolution) source-conceal)
          (multi-target-conceal (stack-top-evolution stack-evolution) target-conceal)
          (trans
            (multi-source-conceal-position (stack-top-evolution stack-evolution) source-conceal)
            (trans positions
              (sym (multi-target-conceal-position
                (stack-top-evolution stack-evolution) target-conceal))))
          (multi-aligned (stack-top-evolution stack-evolution) aligned)
          (multi-⊑ᵀ (stack-top-evolution stack-evolution) represented)
          related′ (multi-⊑ᵀ (stack-top-evolution stack-evolution) q))

  sim-source-rebase-stack {stack = stack}
      (CTI.conceal⊑conceal² {c = c} {c′ = c′}
        source-conceal target-conceal positions aligned represented related q)
      (ξ-conceal {χ = bind A} source-step refl)
      with sim-source-rebase-stack {stack = stack} related source-step
  sim-source-rebase-stack {stack = stack}
      (CTI.conceal⊑conceal² {c = c} {c′ = c′}
        source-conceal target-conceal positions aligned represented related q)
      (ξ-conceal {χ = bind A} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , r ,
      target-steps , stack-evolution , related′ =
      Δᴿ′ , Σᴿ′ , χsᴿ , target-body ↓ applyConceals χsᴿ c′ , γ′ , γᵖ′ , stack′ ,
      multi-⊑ᵀ (stack-top-evolution stack-evolution) q , conceal-↠ c′ target-steps , stack-evolution ,
      CTI.conceal⊑conceal²
        (multi-source-conceal (stack-top-evolution stack-evolution) source-conceal)
        (multi-target-conceal (stack-top-evolution stack-evolution) target-conceal)
        (trans
          (multi-source-conceal-position (stack-top-evolution stack-evolution) source-conceal)
          (trans positions
            (sym (multi-target-conceal-position
              (stack-top-evolution stack-evolution) target-conceal))))
        (multi-aligned (stack-top-evolution stack-evolution) aligned)
        (multi-⊑ᵀ (stack-top-evolution stack-evolution) represented)
        related′ (multi-⊑ᵀ (stack-top-evolution stack-evolution) q)

  sim-source-rebase-stack {stack = stack}
      (CTI.conceal⊑conceal² {M′ = M′} {c′ = c′}
        (Conv.⊢↓-id-var member X≠Y) target-conceal positions aligned
        represented related q)
      (pure-step (id-conceal source-value)) =
    _ , _ , [] , M′ ↓ c′ , _ , _ , stack , q ,
    (M′ ↓ c′ ∎[]) , stack-evolution-keep-left ,
    CTI.⊑conceal-identity target-conceal (sym positions) related q
  sim-source-rebase-stack {stack = stack}
      (CTI.conceal⊑conceal² {M′ = M′} {c′ = c′}
        (Conv.⊢↓-id-base member) target-conceal positions aligned
        represented related q)
      (pure-step (id-conceal source-value)) =
    _ , _ , [] , M′ ↓ c′ , _ , _ , stack , q ,
    (M′ ↓ c′ ∎[]) , stack-evolution-keep-left ,
    CTI.⊑conceal-identity target-conceal (sym positions) related q
  sim-source-rebase-stack {stack = stack}
      (CTI.conceal⊑conceal² {M′ = M′} {c′ = c′}
        (Conv.⊢↓-id-star member) target-conceal positions aligned
        represented related q)
      (pure-step (id-conceal source-value)) =
    _ , _ , [] , M′ ↓ c′ , _ , _ , stack , q ,
    (M′ ↓ c′ ∎[]) , stack-evolution-keep-left ,
    CTI.⊑conceal-identity target-conceal (sym positions) related q
  sim-source-rebase-stack {stack = stack}
      relation@(CTI.conceal⊑conceal² {M′ = M′} {c′ = c′}
        source-conceal target-conceal positions aligned represented related q)
      (pure-step blame-conceal) =
    _ , _ , [] , M′ ↓ c′ , _ , _ , stack , q ,
    (M′ ↓ c′ ∎[]) , stack-evolution-keep-left ,
    CTI.blame⊑² (target-typing relation) q

  sim-source-rebase-stack {stack = stack}
      (CTI.⊑reveal-rebase² target-reveal nested-rebase related q)
      source-step = {!!}

  sim-source-rebase-stack {stack = stack}
      (CTI.⊑conceal-rebase² target-conceal enclosing-rebase related q)
      source-step = {!!}

  sim-source-rebase-stack {stack = stack}
      (CTI.blame⊑² target⊢ p) (pure-step ())

  sim-source-rebase-stack {stack = stack}
      (CTI.⊕⊑⊕² op {L′ = target-left} {M = M} {M′ = M′}
        left-related right-related r)
      (ξ-⊕₁ {χ = χ} {L′ = N} left-step refl)
      with sim-source-rebase-stack
        {stack = stack} left-related left-step
  sim-source-rebase-stack {stack = stack}
      (CTI.⊕⊑⊕² op {L′ = target-left} {M = M} {M′ = M′}
        left-related right-related r)
      (ξ-⊕₁ {χ = χ} {L′ = N} left-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-left′ , γ′ , γᵖ′ , stack′ , q ,
      target-steps , stack-evolution , related′
      with subst
        (λ S →
          Σ[ s ∈ S ⊑ᵀ⟨ γᵖ′ ⟩ primArgTy op ]
            (γᵖ′ CTI.⊢² N ⊑ target-left′ ∶ s))
        (applyTys-primArgTy (χ ∷ []) op)
        (subst
          (λ T →
            Σ[ s ∈ applyTy χ (primArgTy op) ⊑ᵀ⟨ γᵖ′ ⟩ T ]
              (γᵖ′ CTI.⊢² N ⊑ target-left′ ∶ s))
          (applyTys-primArgTy χsᴿ op) (q , related′))
        | subst
        (λ S →
          Σ[ s ∈ S ⊑ᵀ⟨ γᵖ′ ⟩ primArgTy op ]
            (γᵖ′ CTI.⊢² applyTerm χ M ⊑
              applyTerms χsᴿ M′ ∶ s))
        (applyTys-primArgTy (χ ∷ []) op)
        (subst
          (λ T →
            Σ[ s ∈ applyTy χ (primArgTy op) ⊑ᵀ⟨ γᵖ′ ⟩ T ]
              (γᵖ′ CTI.⊢² applyTerm χ M ⊑
                applyTerms χsᴿ M′ ∶ s))
          (applyTys-primArgTy χsᴿ op)
          (multi-⊑ᵀ (stack-top-evolution stack-evolution) _ ,
            transport-source-rebase-stack
              stack-evolution right-related))
  sim-source-rebase-stack {stack = stack}
      (CTI.⊕⊑⊕² op {L′ = target-left} {M = M} {M′ = M′}
        left-related right-related r)
      (ξ-⊕₁ {χ = χ} {L′ = N} left-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-left′ , γ′ , γᵖ′ , stack′ , q ,
      target-steps , stack-evolution , related′
    | q′ , related″ | q″ , right-related′
      with multi-⊑ᵀ (stack-top-evolution stack-evolution) r
  sim-source-rebase-stack {stack = stack}
      (CTI.⊕⊑⊕² op {L′ = target-left} {M = M} {M′ = M′}
        left-related right-related r)
      (ξ-⊕₁ {χ = χ} {L′ = N} left-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-left′ , γ′ , γᵖ′ , stack′ , q ,
      target-steps , stack-evolution , related′
    | q′ , related″ | q″ , right-related′
    | r′
      with subst
        (λ S → S ⊑ᵀ⟨ γᵖ′ ⟩ primResultTy op)
        (applyTys-primResultTy (χ ∷ []) op)
        (subst
          (λ T → applyTy χ (primResultTy op) ⊑ᵀ⟨ γᵖ′ ⟩ T)
          (applyTys-primResultTy χsᴿ op) r′)
  sim-source-rebase-stack {stack = stack}
      (CTI.⊕⊑⊕² op {L′ = target-left} {M = M} {M′ = M′}
        left-related right-related r)
      (ξ-⊕₁ {χ = χ} {L′ = N} left-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-left′ , γ′ , γᵖ′ , stack′ , q ,
      target-steps , stack-evolution , related′
    | q′ , related″ | q″ , right-related′
    | r′ | r⁺
      with subst
        (λ S →
          Σ[ s ∈ S ⊑ᵀ⟨ γᵖ′ ⟩ applyTys χsᴿ (primResultTy op) ]
            (γᵖ′ CTI.⊢² N ⊕[ op ] applyTerm χ M ⊑
              target-left′ ⊕[ op ] applyTerms χsᴿ M′ ∶ s))
        (sym (applyTys-primResultTy (χ ∷ []) op))
        (subst
          (λ T →
            Σ[ s ∈ primResultTy op ⊑ᵀ⟨ γᵖ′ ⟩ T ]
              (γᵖ′ CTI.⊢² N ⊕[ op ] applyTerm χ M ⊑
                target-left′ ⊕[ op ] applyTerms χsᴿ M′ ∶ s))
          (sym (applyTys-primResultTy χsᴿ op))
          (r⁺ , CTI.⊕⊑⊕² op related″ right-related′ r⁺))
  sim-source-rebase-stack {stack = stack}
      (CTI.⊕⊑⊕² op {L′ = target-left} {M = M} {M′ = M′}
        left-related right-related r)
      (ξ-⊕₁ {χ = χ} {L′ = N} left-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-left′ , γ′ , γᵖ′ , stack′ , q ,
      target-steps , stack-evolution , related′
    | q′ , related″ | q″ , right-related′
    | r′ | r⁺
    | r″ , whole-related =
      Δᴿ′ , Σᴿ′ , χsᴿ ,
      target-left′ ⊕[ op ] applyTerms χsᴿ M′ , γ′ , γᵖ′ , stack′ , r″ ,
      primL-↠ target-steps , stack-evolution ,
      whole-related

  sim-source-rebase-stack {stack = stack}
      (CTI.⊕⊑⊕² op {L = L} {L′ = L′} {M′ = M′}
        left-related right-related r)
      (ξ-⊕₂ {χ = χ} left-value right-step refl)
      with catchup-source-rebase-stack
        {stack = stack} left-related left-value
  sim-source-rebase-stack {stack = stack}
      (CTI.⊕⊑⊕² op {L = L} {L′ = L′} {M′ = M′}
        left-related right-related r)
      (ξ-⊕₂ {χ = χ} left-value right-step refl)
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-left , γ₁ , γᵖ₁ , stack₁ , q₁ ,
      left-steps , target-value , stack-evolution₁ , left-related₁
      with sim-source-rebase-stack
        {stack = stack₁}
        (transport-source-rebase-stack stack-evolution₁ right-related)
        right-step
  sim-source-rebase-stack {stack = stack}
      (CTI.⊕⊑⊕² op {L = L} {L′ = L′} {M′ = M′}
        left-related right-related r)
      (ξ-⊕₂ {χ = χ} left-value right-step refl)
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-left , γ₁ , γᵖ₁ , stack₁ , q₁ ,
      left-steps , target-value , stack-evolution₁ , left-related₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , target-right , γ₂ , γᵖ₂ , stack₂ , q₂ ,
      right-steps , stack-evolution₂ ,
      right-related₂
      with subst
        (λ S →
          Σ[ s ∈ S ⊑ᵀ⟨ γᵖ₂ ⟩ primArgTy op ]
            (γᵖ₂ CTI.⊢² applyTerm χ L ⊑
              applyTerms χsᴿ₂ target-left ∶ s))
        (applyTys-primArgTy (χ ∷ []) op)
        (subst
          (λ T →
            Σ[ s ∈ applyTy χ (primArgTy op) ⊑ᵀ⟨ γᵖ₂ ⟩ T ]
              (γᵖ₂ CTI.⊢² applyTerm χ L ⊑
                applyTerms χsᴿ₂ target-left ∶ s))
          (trans (applyTys-++ χsᴿ₁ χsᴿ₂ (primArgTy op))
            (applyTys-primArgTy (χsᴿ₁ ++χ χsᴿ₂) op))
          (multi-⊑ᵀ (stack-top-evolution stack-evolution₂) q₁ ,
            transport-source-rebase-stack
              stack-evolution₂ left-related₁))
        | subst
        (λ S →
          Σ[ s ∈ S ⊑ᵀ⟨ γᵖ₂ ⟩ primArgTy op ]
            (γᵖ₂ CTI.⊢² _ ⊑ target-right ∶ s))
        (applyTys-primArgTy (χ ∷ []) op)
        (subst
          (λ T →
            Σ[ s ∈ applyTy χ (primArgTy op) ⊑ᵀ⟨ γᵖ₂ ⟩ T ]
              (γᵖ₂ CTI.⊢² _ ⊑ target-right ∶ s))
          (trans (applyTys-++ χsᴿ₁ χsᴿ₂ (primArgTy op))
            (applyTys-primArgTy (χsᴿ₁ ++χ χsᴿ₂) op))
          (q₂ , right-related₂))
  sim-source-rebase-stack {stack = stack}
      (CTI.⊕⊑⊕² op {L = L} {L′ = L′} {M′ = M′}
        left-related right-related r)
      (ξ-⊕₂ {χ = χ} left-value right-step refl)
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-left , γ₁ , γᵖ₁ , stack₁ , q₁ ,
      left-steps , target-value , stack-evolution₁ , left-related₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , target-right , γ₂ , γᵖ₂ , stack₂ , q₂ ,
      right-steps , stack-evolution₂ ,
      right-related₂
    | qL , left-related₂ | qR , right-related₃
      with subst
        (λ S → S ⊑ᵀ⟨ γᵖ₂ ⟩ primResultTy op)
        (applyTys-primResultTy (χ ∷ []) op)
        (subst
          (λ T → applyTy χ (primResultTy op) ⊑ᵀ⟨ γᵖ₂ ⟩ T)
          (trans (applyTys-++ χsᴿ₁ χsᴿ₂ (primResultTy op))
            (applyTys-primResultTy (χsᴿ₁ ++χ χsᴿ₂) op))
          (multi-⊑ᵀ (stack-top-evolution stack-evolution₂)
            (multi-⊑ᵀ (stack-top-evolution stack-evolution₁) r)))
  sim-source-rebase-stack {stack = stack}
      (CTI.⊕⊑⊕² op {L = L} {L′ = L′} {M′ = M′}
        left-related right-related r)
      (ξ-⊕₂ {χ = χ} left-value right-step refl)
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-left , γ₁ , γᵖ₁ , stack₁ , q₁ ,
      left-steps , target-value , stack-evolution₁ , left-related₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , target-right , γ₂ , γᵖ₂ , stack₂ , q₂ ,
      right-steps , stack-evolution₂ ,
      right-related₂
    | qL , left-related₂ | qR , right-related₃
    | r₂
      with subst
        (λ S →
          Σ[ s ∈ S ⊑ᵀ⟨ γᵖ₂ ⟩
              applyTys (χsᴿ₁ ++χ χsᴿ₂) (primResultTy op) ]
            (γᵖ₂ CTI.⊢² applyTerm χ L ⊕[ op ] _ ⊑
              applyTerms χsᴿ₂ target-left ⊕[ op ] target-right ∶ s))
        (sym (applyTys-primResultTy (χ ∷ []) op))
        (subst
          (λ T →
            Σ[ s ∈ primResultTy op ⊑ᵀ⟨ γᵖ₂ ⟩ T ]
              (γᵖ₂ CTI.⊢² applyTerm χ L ⊕[ op ] _ ⊑
                applyTerms χsᴿ₂ target-left ⊕[ op ] target-right ∶ s))
          (sym (applyTys-primResultTy (χsᴿ₁ ++χ χsᴿ₂) op))
          (r₂ , CTI.⊕⊑⊕² op left-related₂ right-related₃ r₂))
  sim-source-rebase-stack {stack = stack}
      (CTI.⊕⊑⊕² op {L = L} {L′ = L′} {M′ = M′}
        left-related right-related r)
      (ξ-⊕₂ {χ = χ} left-value right-step refl)
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-left , γ₁ , γᵖ₁ , stack₁ , q₁ ,
      left-steps , target-value , stack-evolution₁ , left-related₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , target-right , γ₂ , γᵖ₂ , stack₂ , q₂ ,
      right-steps , stack-evolution₂ ,
      right-related₂
    | qL , left-related₂ | qR , right-related₃
    | r₂
    | r′ , whole-related =
      Δᴿ₂ , Σᴿ₂ , χsᴿ₁ ++χ χsᴿ₂ ,
      applyTerms χsᴿ₂ target-left ⊕[ op ] target-right , γ₂ , γᵖ₂ , stack₂ ,
      r′ ,
      (L′ ⊕[ op ] M′
         —↠+[ χsᴿ₁ ]⟨ primL-↠ left-steps ⟩
       target-left ⊕[ op ] applyTerms χsᴿ₁ M′
         —↠[ χsᴿ₂ ]⟨ primR-↠ target-value right-steps ⟩
       applyTerms χsᴿ₂ target-left ⊕[ op ] target-right ∎[]) ,
      composeSourceRebaseStackEvolution
        stack-evolution₁ stack-evolution₂ ,
      whole-related

  sim-source-rebase-stack {stack = stack}
      (CTI.⊕⊑⊕² op left-related right-related r)
      (pure-step (δ-⊕ primitive-step)) = {!!}
  sim-source-rebase-stack {stack = stack}
      relation@(CTI.⊕⊑⊕² op {L′ = L′} {M′ = M′}
        left-related right-related r)
      (pure-step blame-⊕₁) =
    _ , _ , [] , L′ ⊕[ op ] M′ , _ , _ , stack , r ,
    (L′ ⊕[ op ] M′ ∎[]) , stack-evolution-keep-left ,
    CTI.blame⊑² (target-typing relation) r
  sim-source-rebase-stack {stack = stack}
      relation@(CTI.⊕⊑⊕² op {L′ = L′} {M′ = M′}
        left-related right-related r)
      (pure-step (blame-⊕₂ source-value)) =
    _ , _ , [] , L′ ⊕[ op ] M′ , _ , _ , stack , r ,
    (L′ ⊕[ op ] M′ ∎[]) , stack-evolution-keep-left ,
    CTI.blame⊑² (target-typing relation) r
