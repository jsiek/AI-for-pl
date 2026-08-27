{-# OPTIONS --safe #-}

module proof.DGG.SimBackProof where

-- File Charter:
--   * Develops backward one-step simulation by induction on the canonical
--     CTI derivation and the target reduction.
--   * Places recursive calls in every contextual reduction case before any
--     root-closing case is discharged.
--   * Proves all contextual, identity, impossible, and target-blame cases
--     directly.
--   * Is parameterized by CTI transport, value catch-up, and the named
--     semantic closing inductions developed in separate proof files.
--   * Exports the goal-free parameterized proof `sim-back`.

open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Product using (_,_; _×_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; refl; sym; trans) renaming (subst to subst≡)

open import Types using (Ty; TyCtx; ★; _⇒_; _[_]ᵗ)
open import TyStore using (TyStore)
open import CastTerms
import Conversion as Conv
open import Imprecision using (⇒⊑⇒)
open import Primitives using (primArgTy; primResultTy)
open import Reduction
open import proof.DGG.CastTermImprecision
open import proof.DGG.CatchupToLessPreciseDef using
  (CatchupToLessPrecise)
open import proof.DGG.SimBackDef using (SimBackᵀ)
open import proof.DGG.SimBackCastClosingDef using
  (SimBackPairedCastClosingᵀ; SimBackTargetCastClosingᵀ)
open import proof.DGG.SimBackPairedAllClosingDef using
  (SimBackPairedAllClosingᵀ)
open import proof.DGG.SimBackPairedFunClosingDef using
  (SimBackPairedFunClosingᵀ)
open import proof.DGG.SimBackPrimitiveClosingDef using
  (SimBackPrimitiveClosingᵀ)
open import proof.DGG.SimBackRebasedConversionDef using
  ( SimBackPairedRevealClosingᵀ
  ; SimBackTargetRevealRebaseClosingᵀ
  ; SimBackTargetRevealRebaseFrameᵀ
  )
open import proof.DGG.SimBackSourceLambdaDef using
  (SimBackSourceLambdaᵀ)
open import proof.DGG.TargetBlameCatchupLemma using
  (target-blame-catchup)
open import proof.DGG.TransportTermImprecisionDef using
  (TransportTermImprecisionᵀ)
open import proof.DGG.World
open import proof.DGG.SourceRebase using
  (open-source-rebase-nonempty)
open import proof.DGG.WorldEvolution using (evolution-keep)
open import proof.DGG.WorldEvolutionSequence
open import proof.Reduction
import proof.Imprecision as PI
open import proof.TypeSafety.Preservation using (apply-open)


module _
    (transport-CTI : TransportTermImprecisionᵀ)
    (catchup-to-less-precise : CatchupToLessPrecise)
    (sim-back-paired-fun-closing : SimBackPairedFunClosingᵀ)
    (sim-back-paired-all-closing : SimBackPairedAllClosingᵀ)
    (sim-back-paired-cast-closing : SimBackPairedCastClosingᵀ)
    (sim-back-target-cast-closing : SimBackTargetCastClosingᵀ)
    (sim-back-paired-reveal-closing : SimBackPairedRevealClosingᵀ)
    (sim-back-target-reveal-rebase-closing :
      SimBackTargetRevealRebaseClosingᵀ)
    (sim-back-primitive-closing : SimBackPrimitiveClosingᵀ)
    (sim-back-source-lambda : SimBackSourceLambdaᵀ)
    (sim-back-target-reveal-rebase-frame :
      SimBackTargetRevealRebaseFrameᵀ)
  where

  sim-back : SimBackᵀ
  sim-back no-rebase (ƛ⊑ƛ² related) (pure-step ())

  sim-back no-rebase (·⊑·² fun-rel arg-rel)
      (pure-step target-root@(β target-value)) =
    sim-back-paired-fun-closing no-rebase fun-rel arg-rel
      (ƛ _) target-value target-root
  sim-back no-rebase (·⊑·² fun-rel arg-rel)
      (pure-step target-root@(β-⇒ function-value argument-value)) =
    sim-back-paired-fun-closing no-rebase fun-rel arg-rel
      (function-value 《 fun 》) argument-value target-root
  sim-back no-rebase (·⊑·² fun-rel arg-rel)
      (pure-step target-root@(β-reveal-⇒ function-value argument-value)) =
    sim-back-paired-fun-closing no-rebase fun-rel arg-rel
      (function-value ↑ fun) argument-value target-root
  sim-back no-rebase (·⊑·² fun-rel arg-rel)
      (pure-step target-root@(β-conceal-⇒ function-value argument-value)) =
    sim-back-paired-fun-closing no-rebase fun-rel arg-rel
      (function-value ↓ fun) argument-value target-root
  sim-back no-rebase (·⊑·² fun-rel arg-rel)
      (pure-step blame-·₁)
      with target-blame-catchup fun-rel
  sim-back no-rebase (·⊑·² {L = L} {M = M} fun-rel arg-rel)
      (pure-step blame-·₁)
    | Δᴸ′ , χsᴸ , source-blame =
      inj₂
        (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
          (L · M
            —↠+[ χsᴸ ]⟨ appL-↠ source-blame ⟩
           blame · applyTerms χsᴸ M
            —→[ keep ]⟨ pure-step blame-·₁ ⟩
           blame ∎[]))

  sim-back no-rebase (·⊑·² fun-rel arg-rel)
      (pure-step (blame-·₂ target-value))
      with catchup-to-less-precise no-rebase fun-rel target-value
  sim-back no-rebase
      (·⊑·² {L = L} {M = M} fun-rel arg-rel)
      (pure-step (blame-·₂ target-value))
    | inj₁
        (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-value , γ₁ , type-rel₁ ,
          source-steps , value , evolution₁ , fun-rel₁)
      with target-blame-catchup
        (transport-CTI no-rebase evolution₁ arg-rel)
  sim-back no-rebase
      (·⊑·² {L = L} {M = M} fun-rel arg-rel)
      (pure-step (blame-·₂ target-value))
    | inj₁
        (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-value , γ₁ , type-rel₁ ,
          source-steps , value , evolution₁ , fun-rel₁)
    | Δᴸ₂ , χsᴸ₂ , argument-blame =
      inj₂
        (Δᴸ₂ , χsᴸ₁ ++χ (χsᴸ₂ ++χ (keep ∷ [])) ,
          (L · M
            —↠+[ χsᴸ₁ ]⟨ appL-↠ source-steps ⟩
           source-value · applyTerms χsᴸ₁ M
            —↠+[ χsᴸ₂ ]⟨ appR-↠ value argument-blame ⟩
           applyTerms χsᴸ₂ source-value · blame
            —→[ keep ]⟨ pure-step
              (blame-·₂ (applyTerms-preserves-Value χsᴸ₂ value)) ⟩
           blame ∎[]))
  sim-back no-rebase
      (·⊑·² {L = L} {M = M} fun-rel arg-rel)
      (pure-step (blame-·₂ target-value))
    | inj₂ (Δᴸ′ , Σᴸ′ , χsᴸ , γ′ , source-blame , evolution) =
      inj₂
        (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
          (L · M
            —↠+[ χsᴸ ]⟨ appL-↠ source-blame ⟩
           blame · applyTerms χsᴸ M
            —→[ keep ]⟨ pure-step blame-·₁ ⟩
           blame ∎[]))

  sim-back {χᴿ = χᴿ} no-rebase
      (·⊑·² {L = L} {M = M} {A = A} {A′ = A′} {B = B} {B′ = B′}
        {pA = argument-rel} fun-rel arg-rel)
      (ξ-·₁ target-step refl)
      with sim-back no-rebase fun-rel target-step
  sim-back {χᴿ = χᴿ} no-rebase
      (·⊑·² {L = L} {M = M} {A = A} {A′ = A′} {B = B} {B′ = B′}
        {pA = argument-rel} fun-rel arg-rel)
      (ξ-·₁ target-step refl)
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , function-rel , source-steps ,
          evolution , related′)
      rewrite applyTys-⇒ χsᴸ A B | applyTy-⇒ χᴿ A′ B′
      with function-rel | related′
  sim-back {χᴿ = χᴿ} no-rebase
      (·⊑·² {L = L} {M = M} {A = A} {A′ = A′} {B = B} {B′ = B′}
        {pA = argument-rel} fun-rel arg-rel)
      (ξ-·₁ target-step refl)
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , function-rel , source-steps ,
          evolution , related′)
    | ⇒⊑⇒ argument-rel′ result-rel′ | related″ =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N · applyTerms χsᴸ M , γ′ , result-rel′ ,
          appL-↠ source-steps , evolution ,
          ·⊑·² related″
            (subst≡ (λ p → γ′ ⊢² _ ⊑ _ ∶ p)
              (PI.⊑-unique (multi-⊑ᵀ evolution argument-rel)
                argument-rel′)
              (transport-CTI no-rebase evolution arg-rel)))
  sim-back {χᴿ = χᴿ} no-rebase
      (·⊑·² {L = L} {M = M} {A = A} {A′ = A′} {B = B} {B′ = B′}
        {pA = argument-rel} fun-rel arg-rel)
      (ξ-·₁ target-step refl)
    | inj₂ (Δᴸ′ , χsᴸ , source-blame) =
      inj₂
        (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
          (L · M
            —↠+[ χsᴸ ]⟨ appL-↠ source-blame ⟩
           blame · applyTerms χsᴸ M
            —→[ keep ]⟨ pure-step blame-·₁ ⟩
           blame ∎[]))

  sim-back {χᴿ = χᴿ} no-rebase
      (·⊑·² {L = L} {L′ = L′} {M = M}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        fun-rel arg-rel)
      (ξ-·₂ {M′ = N′} target-value target-step refl)
      with catchup-to-less-precise no-rebase fun-rel target-value
  sim-back {χᴿ = χᴿ} no-rebase
      (·⊑·² {L = L} {L′ = L′} {M = M}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        fun-rel arg-rel)
      (ξ-·₂ {M′ = N′} target-value target-step refl)
    | inj₁
        (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-value , γ₁ , type-rel₁ ,
          source-steps , value , evolution₁ , fun-rel₁)
      with sim-back (multi-no-open-frames evolution₁ no-rebase)
        (transport-CTI no-rebase evolution₁ arg-rel) target-step
  sim-back {χᴿ = χᴿ} no-rebase
      (·⊑·² {L = L} {L′ = L′} {M = M}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        fun-rel arg-rel)
      (ξ-·₂ {M′ = N′} target-value target-step refl)
    | inj₁
        (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-value , γ₁ , type-rel₁ ,
          source-steps , value , evolution₁ , fun-rel₁)
    | inj₁
        (Δᴸ₂ , Σᴸ₂ , χsᴸ₂ , argument , γ₂ , argument-rel ,
          argument-steps , evolution₂ , arg-rel₂)
      with subst≡
        (λ S →
          Σ[ q ∈ S ⊑ᵀ⟨ γ₂ ⟩
              (applyTy χᴿ A′ ⇒ applyTy χᴿ B′) ]
            γ₂ ⊢² applyTerms χsᴸ₂ source-value ⊑
              applyTerm χᴿ L′ ∶ q)
        (trans (cong (applyTys χsᴸ₂) (applyTys-⇒ χsᴸ₁ A B))
          (applyTys-⇒ χsᴸ₂ (applyTys χsᴸ₁ A)
            (applyTys χsᴸ₁ B)))
        (subst≡
          (λ T →
            Σ[ q ∈
                applyTys χsᴸ₂ (applyTys χsᴸ₁ (A ⇒ B))
                  ⊑ᵀ⟨ γ₂ ⟩ T ]
              γ₂ ⊢² applyTerms χsᴸ₂ source-value ⊑
                applyTerm χᴿ L′ ∶ q)
          (applyTy-⇒ χᴿ A′ B′)
          (multi-⊑ᵀ evolution₂ type-rel₁ ,
            transport-CTI
              (multi-no-open-frames evolution₁ no-rebase)
              evolution₂ fun-rel₁))
  sim-back {χᴿ = χᴿ} no-rebase
      (·⊑·² {L = L} {L′ = L′} {M = M}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        fun-rel arg-rel)
      (ξ-·₂ {M′ = N′} target-value target-step refl)
    | inj₁
        (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-value , γ₁ , type-rel₁ ,
          source-steps , value , evolution₁ , fun-rel₁)
    | inj₁
        (Δᴸ₂ , Σᴸ₂ , χsᴸ₂ , argument , γ₂ , argument-rel ,
          argument-steps , evolution₂ , arg-rel₂)
    | ⇒⊑⇒ argument-rel′ result-rel′ , fun-rel₂
      with subst≡
        (λ S →
          Σ[ q ∈ S ⊑ᵀ⟨ γ₂ ⟩ applyTy χᴿ B′ ]
            γ₂ ⊢² applyTerms χsᴸ₂ source-value · argument ⊑
              applyTerm χᴿ L′ · N′ ∶ q)
        (applyTys-++ χsᴸ₁ χsᴸ₂ B)
        ( result-rel′
        , ·⊑·² fun-rel₂
            (subst≡ (λ q → γ₂ ⊢² argument ⊑ N′ ∶ q)
              (PI.⊑-unique argument-rel argument-rel′) arg-rel₂)
        )
  sim-back {χᴿ = χᴿ} no-rebase
      (·⊑·² {L = L} {L′ = L′} {M = M}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        fun-rel arg-rel)
      (ξ-·₂ {M′ = N′} target-value target-step refl)
    | inj₁
        (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-value , γ₁ , type-rel₁ ,
          source-steps , value , evolution₁ , fun-rel₁)
    | inj₁
        (Δᴸ₂ , Σᴸ₂ , χsᴸ₂ , argument , γ₂ , argument-rel ,
          argument-steps , evolution₂ , arg-rel₂)
    | ⇒⊑⇒ argument-rel′ result-rel′ , fun-rel₂
    | result-rel″ , application-rel =
      inj₁
        (Δᴸ₂ , Σᴸ₂ , χsᴸ₁ ++χ χsᴸ₂ ,
          applyTerms χsᴸ₂ source-value · argument , γ₂ , result-rel″ ,
          (L · M
            —↠+[ χsᴸ₁ ]⟨ appL-↠ source-steps ⟩
           source-value · applyTerms χsᴸ₁ M
            —↠[ χsᴸ₂ ]⟨ appR-↠ value argument-steps ⟩
           applyTerms χsᴸ₂ source-value · argument ∎[]) ,
          composeMultiWorldEvolution evolution₁ evolution₂ , application-rel)
  sim-back {χᴿ = χᴿ} no-rebase
      (·⊑·² {L = L} {L′ = L′} {M = M}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        fun-rel arg-rel)
      (ξ-·₂ {M′ = N′} target-value target-step refl)
    | inj₁
        (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-value , γ₁ , type-rel₁ ,
          source-steps , value , evolution₁ , fun-rel₁)
    | inj₂ (Δᴸ₂ , χsᴸ₂ , argument-blame) =
      inj₂
        (Δᴸ₂ , χsᴸ₁ ++χ (χsᴸ₂ ++χ (keep ∷ [])) ,
          (L · M
            —↠+[ χsᴸ₁ ]⟨ appL-↠ source-steps ⟩
           source-value · applyTerms χsᴸ₁ M
            —↠+[ χsᴸ₂ ]⟨ appR-↠ value argument-blame ⟩
           applyTerms χsᴸ₂ source-value · blame
            —→[ keep ]⟨ pure-step
              (blame-·₂ (applyTerms-preserves-Value χsᴸ₂ value)) ⟩
           blame ∎[]))
  sim-back {χᴿ = χᴿ} no-rebase
      (·⊑·² {L = L} {L′ = L′} {M = M}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        fun-rel arg-rel)
      (ξ-·₂ {M′ = N′} target-value target-step refl)
    | inj₂ (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , γ₁ , source-blame , evolution₁) =
      inj₂
        (Δᴸ₁ , χsᴸ₁ ++χ (keep ∷ []) ,
          (L · M
            —↠+[ χsᴸ₁ ]⟨ appL-↠ source-blame ⟩
           blame · applyTerms χsᴸ₁ M
            —→[ keep ]⟨ pure-step blame-·₁ ⟩
           blame ∎[]))

  sim-back no-rebase (Λ⊑Λ² source-value target-value related q)
      (pure-step ())

  sim-back no-rebase
      (Λ⊑² nonvar occurs source-value target⊢ related q)
      target-step =
    sim-back-source-lambda no-rebase nonvar occurs source-value target⊢
      related q target-step

  sim-back no-rebase (•⊑•² all-rel related type-rel result-rel)
      root@(pure-step (β-∀ target-value instantiated)) =
    sim-back-paired-all-closing no-rebase related type-rel result-rel
      (target-value 《 all 》) root
  sim-back no-rebase (•⊑•² all-rel related type-rel result-rel)
      (pure-step blame-•)
      with target-blame-catchup related
  sim-back no-rebase (•⊑•² all-rel related type-rel result-rel)
      (pure-step blame-•)
    | Δᴸ′ , χsᴸ , source-blame =
      inj₂
        (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
          typeApp-blame-↠ source-blame)
  sim-back no-rebase (•⊑•² all-rel related type-rel result-rel)
      root@(β-Λ target-value) =
    sim-back-paired-all-closing no-rebase related type-rel result-rel
      (Λ target-value) root
  sim-back no-rebase (•⊑•² all-rel related type-rel result-rel)
      root@(β-gen target-value not-star safe) =
    sim-back-paired-all-closing no-rebase related type-rel result-rel
      (target-value 《 genᵥ not-star safe 》) root
  sim-back no-rebase (•⊑•² all-rel related type-rel result-rel)
      root@(β-reveal-∀ target-value) =
    sim-back-paired-all-closing no-rebase related type-rel result-rel
      (target-value ↑ all) root
  sim-back no-rebase (•⊑•² all-rel related type-rel result-rel)
      root@(β-conceal-∀ target-value) =
    sim-back-paired-all-closing no-rebase related type-rel result-rel
      (target-value ↓ all) root
  sim-back {χᴿ = χᴿ} no-rebase
      (•⊑•² {M = M} {C = C} {C′ = C′} {A = A} {A′ = A′}
        all-rel related type-rel result-rel)
      (ξ-• {M′ = N′} target-step refl refl)
      with sim-back no-rebase related target-step
  sim-back {χᴿ = χᴿ} no-rebase
      (•⊑•² {M = M} {C = C} {C′ = C′} {A = A} {A′ = A′}
        all-rel related type-rel result-rel)
      (ξ-• {M′ = N′} target-step refl refl)
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , all-rel′ , source-steps ,
          evolution , related′)
      rewrite applyTys-∀ χsᴸ C | applyTy-∀ χᴿ C′
      with all-rel′ | related′
  sim-back {χᴿ = χᴿ} no-rebase
      (•⊑•² {M = M} {C = C} {C′ = C′} {A = A} {A′ = A′}
        all-rel related type-rel result-rel)
      (ξ-• {M′ = N′} target-step refl refl)
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , all-rel′ , source-steps ,
          evolution , related′)
    | all-rel″ | related″
      with subst≡
        (λ S →
          Σ[ result ∈ S ⊑ᵀ⟨ γ′ ⟩ applyTy χᴿ (C′ [ A′ ]ᵗ) ]
            γ′ ⊢² N ⦂∀ applyBodies χsᴸ C [ applyTys χsᴸ A ] ⊑
              N′ ⦂∀ applyBody χᴿ C′ [ applyTy χᴿ A′ ] ∶ result)
        (sym (applyTys-open χsᴸ C A))
        (subst≡
          (λ T →
            Σ[ result ∈
                (applyBodies χsᴸ C [ applyTys χsᴸ A ]ᵗ)
                  ⊑ᵀ⟨ γ′ ⟩ T ]
              γ′ ⊢² N ⦂∀ applyBodies χsᴸ C [ applyTys χsᴸ A ] ⊑
                N′ ⦂∀ applyBody χᴿ C′ [ applyTy χᴿ A′ ] ∶ result)
          (sym (apply-open χᴿ C′ A′))
          ( subst≡
              (λ T →
                (applyBodies χsᴸ C [ applyTys χsᴸ A ]ᵗ)
                  ⊑ᵀ⟨ γ′ ⟩ T)
              (apply-open χᴿ C′ A′)
              (subst≡
                (λ S → S ⊑ᵀ⟨ γ′ ⟩ applyTy χᴿ (C′ [ A′ ]ᵗ))
                (applyTys-open χsᴸ C A)
                (multi-⊑ᵀ evolution result-rel))
          , •⊑•² all-rel″ related″ (multi-⊑ᵀ evolution type-rel)
              (subst≡
                (λ T →
                  (applyBodies χsᴸ C [ applyTys χsᴸ A ]ᵗ)
                    ⊑ᵀ⟨ γ′ ⟩ T)
                (apply-open χᴿ C′ A′)
                (subst≡
                  (λ S → S ⊑ᵀ⟨ γ′ ⟩ applyTy χᴿ (C′ [ A′ ]ᵗ))
                  (applyTys-open χsᴸ C A)
                  (multi-⊑ᵀ evolution result-rel)))
          ))
  sim-back {χᴿ = χᴿ} no-rebase
      (•⊑•² {M = M} {C = C} {C′ = C′} {A = A} {A′ = A′}
        all-rel related type-rel result-rel)
      (ξ-• {M′ = N′} target-step refl refl)
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , all-rel′ , source-steps ,
          evolution , related′)
    | all-rel″ | related″
    | result-rel′ , whole-rel =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ ,
          N ⦂∀ applyBodies χsᴸ C [ applyTys χsᴸ A ] , γ′ ,
          result-rel′ , typeApp-↠ source-steps , evolution , whole-rel)
  sim-back {χᴿ = χᴿ} no-rebase
      (•⊑•² {M = M} {C = C} {C′ = C′} {A = A} {A′ = A′}
        all-rel related type-rel result-rel)
      (ξ-• {M′ = N′} target-step refl refl)
    | inj₂ (Δᴸ′ , χsᴸ , source-blame) =
      inj₂ (Δᴸ′ , χsᴸ ++χ (keep ∷ []) , typeApp-blame-↠ source-blame)

  sim-back {χᴿ = χᴿ} no-rebase
      (•⊑² {M = M} {C = C} {A = A}
        all-rel related type-rel result-rel)
      target-step
      with sim-back no-rebase related target-step
  sim-back {χᴿ = χᴿ} no-rebase
      (•⊑² {M = M} {C = C} {A = A}
        all-rel related type-rel result-rel)
      target-step
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , all-rel′ , source-steps ,
          evolution , related′)
      rewrite applyTys-∀ χsᴸ C
      with all-rel′ | related′
  sim-back {χᴿ = χᴿ} no-rebase
      (•⊑² {M = M} {C = C} {A = A}
        all-rel related type-rel result-rel)
      target-step
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , all-rel′ , source-steps ,
          evolution , related′)
    | all-rel″ | related″
      with subst≡
        (λ S →
          Σ[ result ∈ S ⊑ᵀ⟨ γ′ ⟩ _ ]
            γ′ ⊢² N ⦂∀ applyBodies χsᴸ C [ applyTys χsᴸ A ] ⊑ _
              ∶ result)
        (sym (applyTys-open χsᴸ C A))
        ( subst≡
            (λ S → S ⊑ᵀ⟨ γ′ ⟩ _)
            (applyTys-open χsᴸ C A)
            (multi-⊑ᵀ evolution result-rel)
        , •⊑² all-rel″ related″
            (subst≡ (λ T → applyTys χsᴸ A ⊑ᵀ⟨ γ′ ⟩ T)
              (applyTys-★ (χᴿ ∷ [])) (multi-⊑ᵀ evolution type-rel))
            (subst≡ (λ S → S ⊑ᵀ⟨ γ′ ⟩ _)
              (applyTys-open χsᴸ C A)
              (multi-⊑ᵀ evolution result-rel))
        )
  sim-back {χᴿ = χᴿ} no-rebase
      (•⊑² {M = M} {C = C} {A = A}
        all-rel related type-rel result-rel)
      target-step
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , all-rel′ , source-steps ,
          evolution , related′)
    | all-rel″ | related″
    | result-rel′ , whole-rel =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ ,
          N ⦂∀ applyBodies χsᴸ C [ applyTys χsᴸ A ] , γ′ ,
          result-rel′ , typeApp-↠ source-steps , evolution , whole-rel)
  sim-back {χᴿ = χᴿ} no-rebase
      (•⊑² {M = M} {C = C} {A = A}
        all-rel related type-rel result-rel)
      target-step
    | inj₂ (Δᴸ′ , χsᴸ , source-blame) =
      inj₂ (Δᴸ′ , χsᴸ ++χ (keep ∷ []) , typeApp-blame-↠ source-blame)

  sim-back no-rebase (κ⊑κ² constant type-rel) (pure-step ())

  sim-back no-rebase
      (cast⊑cast² source-cast target-cast related type-rel)
      root@(pure-step (β-id target-value)) =
    sim-back-paired-cast-closing no-rebase source-cast target-cast related
      type-rel target-value root
  sim-back no-rebase
      (cast⊑cast² source-cast target-cast related type-rel)
      root@(pure-step (ground target-value unequal)) =
    sim-back-paired-cast-closing no-rebase source-cast target-cast related
      type-rel target-value root
  sim-back no-rebase
      (cast⊑cast² source-cast target-cast related type-rel)
      root@(pure-step (expand target-value unequal)) =
    sim-back-paired-cast-closing no-rebase source-cast target-cast related
      type-rel target-value root
  sim-back no-rebase
      (cast⊑cast² source-cast target-cast related type-rel)
      root@(pure-step (tag-untag target-value)) =
    sim-back-paired-cast-closing no-rebase source-cast target-cast related
      type-rel (target-value 《 inj 》) root
  sim-back no-rebase
      (cast⊑cast² source-cast target-cast related type-rel)
      root@(pure-step (tag-untag-bad target-value unequal)) =
    sim-back-paired-cast-closing no-rebase source-cast target-cast related
      type-rel (target-value 《 inj 》) root
  sim-back no-rebase
      (cast⊑cast² source-cast target-cast related type-rel)
      root@(pure-step (blame-bot-intro target-value)) =
    sim-back-paired-cast-closing no-rebase source-cast target-cast related
      type-rel target-value root
  sim-back no-rebase
      (cast⊑cast² source-cast target-cast related type-rel)
      (pure-step blame-⟨⟩)
      with target-blame-catchup related
  sim-back no-rebase
      (cast⊑cast² source-cast target-cast related type-rel)
      (pure-step blame-⟨⟩)
    | Δᴸ′ , χsᴸ , source-blame =
      inj₂
        (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
          cast-blame-↠ source-cast source-blame)
  sim-back no-rebase
      (cast⊑cast² source-cast target-cast related type-rel)
      root@(β-inst target-value not-star) =
    sim-back-paired-cast-closing no-rebase source-cast target-cast related
      type-rel target-value root
  sim-back {χᴿ = χᴿ} no-rebase
      (cast⊑cast² {M = M} source-cast target-cast related type-rel)
      (ξ-⟨⟩ target-step refl)
      with sim-back no-rebase related target-step
  sim-back {χᴿ = χᴿ} no-rebase
      (cast⊑cast² {M = M} source-cast target-cast related type-rel)
      (ξ-⟨⟩ target-step refl)
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , result-rel , source-steps ,
          evolution , related′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N ⟨ applyConsistencies χsᴸ source-cast ⟩ ,
          γ′ , multi-⊑ᵀ evolution type-rel ,
          cast-↠ source-cast source-steps , evolution ,
          cast⊑cast² (applyConsistencies χsᴸ source-cast)
            (applyConsistency χᴿ target-cast) related′
            (multi-⊑ᵀ evolution type-rel))
  sim-back {χᴿ = χᴿ} no-rebase
      (cast⊑cast² {M = M} source-cast target-cast related type-rel)
      (ξ-⟨⟩ target-step refl)
    | inj₂ (Δᴸ′ , χsᴸ , source-blame) =
      inj₂
        (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
          (M ⟨ source-cast ⟩
            —↠+[ χsᴸ ]⟨ cast-↠ source-cast source-blame ⟩
           blame ⟨ applyConsistencies χsᴸ source-cast ⟩
            —→[ keep ]⟨ pure-step blame-⟨⟩ ⟩
           blame ∎[]))

  sim-back no-rebase (⊑cast² target-cast related type-rel)
      root@(pure-step (β-id target-value)) =
    sim-back-target-cast-closing no-rebase target-cast related type-rel
      target-value root
  sim-back no-rebase (⊑cast² target-cast related type-rel)
      root@(pure-step (ground target-value unequal)) =
    sim-back-target-cast-closing no-rebase target-cast related type-rel
      target-value root
  sim-back no-rebase (⊑cast² target-cast related type-rel)
      root@(pure-step (expand target-value unequal)) =
    sim-back-target-cast-closing no-rebase target-cast related type-rel
      target-value root
  sim-back no-rebase (⊑cast² target-cast related type-rel)
      root@(pure-step (tag-untag target-value)) =
    sim-back-target-cast-closing no-rebase target-cast related type-rel
      (target-value 《 inj 》) root
  sim-back no-rebase (⊑cast² target-cast related type-rel)
      root@(pure-step (tag-untag-bad target-value unequal)) =
    sim-back-target-cast-closing no-rebase target-cast related type-rel
      (target-value 《 inj 》) root
  sim-back no-rebase (⊑cast² target-cast related type-rel)
      root@(pure-step (blame-bot-intro target-value)) =
    sim-back-target-cast-closing no-rebase target-cast related type-rel
      target-value root
  sim-back no-rebase (⊑cast² target-cast related type-rel)
      (pure-step blame-⟨⟩) =
    inj₂ (target-blame-catchup related)
  sim-back no-rebase (⊑cast² target-cast related type-rel)
      root@(β-inst target-value not-star) =
    sim-back-target-cast-closing no-rebase target-cast related type-rel
      target-value root
  sim-back {χᴿ = χᴿ} no-rebase
      (⊑cast² target-cast related type-rel)
      (ξ-⟨⟩ target-step refl)
      with sim-back no-rebase related target-step
  sim-back {χᴿ = χᴿ} no-rebase
      (⊑cast² target-cast related type-rel)
      (ξ-⟨⟩ target-step refl)
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , result-rel , source-steps ,
          evolution , related′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , multi-⊑ᵀ evolution type-rel ,
          source-steps , evolution ,
          ⊑cast² (applyConsistency χᴿ target-cast) related′
            (multi-⊑ᵀ evolution type-rel))
  sim-back {χᴿ = χᴿ} no-rebase
      (⊑cast² target-cast related type-rel)
      (ξ-⟨⟩ target-step refl)
    | inj₂ source-blame = inj₂ source-blame

  sim-back no-rebase
      (⊑reveal-identity {M = M} conversion position related type-rel)
      (pure-step (id-reveal target-value)) =
    inj₁
      (_ , _ , [] , M , _ , type-rel , (M ∎[]) ,
        evolutions-step-right refl evolution-keep evolutions-refl ,
        subst≡ (λ q → _ ⊢² M ⊑ _ ∶ q)
          (PI.⊑-unique _ type-rel) related)
  sim-back no-rebase
      (⊑reveal-identity (Conv.⊢↑-unseal member) () related type-rel)
      (pure-step (conceal-reveal target-value))
  sim-back no-rebase
      (⊑reveal-identity conversion position related type-rel)
      (pure-step blame-reveal) =
    inj₂ (target-blame-catchup related)
  sim-back no-rebase
      (⊑reveal-identity {c′ = c} conversion position related type-rel)
      (ξ-reveal {χ = keep} {M′ = N′} target-step refl)
      with sim-back no-rebase related target-step
  sim-back no-rebase
      (⊑reveal-identity {c′ = c} conversion position related type-rel)
      (ξ-reveal {χ = keep} {M′ = N′} target-step refl)
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , result-rel , source-steps ,
          evolution , related′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , multi-⊑ᵀ evolution type-rel ,
          source-steps , evolution ,
          subst≡ (λ P → γ′ ⊢² N ⊑ P ∶ multi-⊑ᵀ evolution type-rel)
            (sym (renamedReveal-term N′ c))
            (⊑reveal-identity (multi-target-reveal evolution conversion)
              (trans (multi-target-reveal-position evolution conversion)
                position)
              related′ (multi-⊑ᵀ evolution type-rel)))
  sim-back no-rebase
      (⊑reveal-identity {c′ = c} conversion position related type-rel)
      (ξ-reveal {χ = keep} {M′ = N′} target-step refl)
    | inj₂ source-blame = inj₂ source-blame
  sim-back no-rebase
      (⊑reveal-identity {c′ = c} conversion position related type-rel)
      (ξ-reveal {χ = bind R} target-step refl)
      with sim-back no-rebase related target-step
  sim-back no-rebase
      (⊑reveal-identity {c′ = c} conversion position related type-rel)
      (ξ-reveal {χ = bind R} target-step refl)
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , result-rel , source-steps ,
          evolution , related′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , multi-⊑ᵀ evolution type-rel ,
          source-steps , evolution ,
          ⊑reveal-identity (multi-target-reveal evolution conversion)
            (trans (multi-target-reveal-position evolution conversion)
              position)
            related′ (multi-⊑ᵀ evolution type-rel))
  sim-back no-rebase
      (⊑reveal-identity {c′ = c} conversion position related type-rel)
      (ξ-reveal {χ = bind R} target-step refl)
    | inj₂ source-blame = inj₂ source-blame

  sim-back no-rebase
      (⊑conceal-identity {M = M} conversion position related type-rel)
      (pure-step (id-conceal target-value)) =
    inj₁
      (_ , _ , [] , M , _ , type-rel , (M ∎[]) ,
        evolutions-step-right refl evolution-keep evolutions-refl ,
        subst≡ (λ q → _ ⊢² M ⊑ _ ∶ q)
          (PI.⊑-unique _ type-rel) related)
  sim-back no-rebase
      (⊑conceal-identity conversion position related type-rel)
      (pure-step blame-conceal) =
    inj₂ (target-blame-catchup related)
  sim-back no-rebase
      (⊑conceal-identity {c′ = c} conversion position related type-rel)
      (ξ-conceal {χ = keep} {M′ = N′} target-step refl)
      with sim-back no-rebase related target-step
  sim-back no-rebase
      (⊑conceal-identity {c′ = c} conversion position related type-rel)
      (ξ-conceal {χ = keep} {M′ = N′} target-step refl)
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , result-rel , source-steps ,
          evolution , related′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , multi-⊑ᵀ evolution type-rel ,
          source-steps , evolution ,
          subst≡ (λ P → γ′ ⊢² N ⊑ P ∶ multi-⊑ᵀ evolution type-rel)
            (sym (renamedConceal-term N′ c))
            (⊑conceal-identity (multi-target-conceal evolution conversion)
              (trans (multi-target-conceal-position evolution conversion)
                position)
              related′ (multi-⊑ᵀ evolution type-rel)))
  sim-back no-rebase
      (⊑conceal-identity {c′ = c} conversion position related type-rel)
      (ξ-conceal {χ = keep} {M′ = N′} target-step refl)
    | inj₂ source-blame = inj₂ source-blame
  sim-back no-rebase
      (⊑conceal-identity {c′ = c} conversion position related type-rel)
      (ξ-conceal {χ = bind R} target-step refl)
      with sim-back no-rebase related target-step
  sim-back no-rebase
      (⊑conceal-identity {c′ = c} conversion position related type-rel)
      (ξ-conceal {χ = bind R} target-step refl)
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , result-rel , source-steps ,
          evolution , related′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , multi-⊑ᵀ evolution type-rel ,
          source-steps , evolution ,
          ⊑conceal-identity (multi-target-conceal evolution conversion)
            (trans (multi-target-conceal-position evolution conversion)
              position)
            related′ (multi-⊑ᵀ evolution type-rel))
  sim-back no-rebase
      (⊑conceal-identity {c′ = c} conversion position related type-rel)
      (ξ-conceal {χ = bind R} target-step refl)
    | inj₂ source-blame = inj₂ source-blame

  sim-back no-rebase (cast⊑² {M = M} source-cast related type-rel)
      target-step
      with sim-back no-rebase related target-step
  sim-back no-rebase (cast⊑² {M = M} source-cast related type-rel)
      target-step
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , result-rel , source-steps ,
          evolution , related′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N ⟨ applyConsistencies χsᴸ source-cast ⟩ ,
          γ′ , multi-⊑ᵀ evolution type-rel ,
          cast-↠ source-cast source-steps , evolution ,
          cast⊑² (applyConsistencies χsᴸ source-cast) related′
            (multi-⊑ᵀ evolution type-rel))
  sim-back no-rebase (cast⊑² {M = M} source-cast related type-rel)
      target-step
    | inj₂ (Δᴸ′ , χsᴸ , source-blame) =
      inj₂
        (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
          (M ⟨ source-cast ⟩
            —↠+[ χsᴸ ]⟨ cast-↠ source-cast source-blame ⟩
           blame ⟨ applyConsistencies χsᴸ source-cast ⟩
            —→[ keep ]⟨ pure-step blame-⟨⟩ ⟩
           blame ∎[]))

  sim-back no-rebase
      (reveal⊑-identity {M = M} {c = c}
        conversion position related type-rel)
      target-step
      with sim-back no-rebase related target-step
  sim-back no-rebase
      (reveal⊑-identity {M = M} {c = c}
        conversion position related type-rel)
      target-step
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , result-rel , source-steps ,
          evolution , related′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N ↑ applyReveals χsᴸ c , γ′ ,
          multi-⊑ᵀ evolution type-rel , reveal-↠ c source-steps , evolution ,
          reveal⊑-identity (multi-source-reveal evolution conversion)
            (trans (multi-source-reveal-position evolution conversion)
              position)
            related′ (multi-⊑ᵀ evolution type-rel))
  sim-back no-rebase
      (reveal⊑-identity {M = M} {c = c}
        conversion position related type-rel)
      target-step
    | inj₂ (Δᴸ′ , χsᴸ , source-blame) =
      inj₂ (Δᴸ′ , χsᴸ ++χ (keep ∷ []) , reveal-blame-↠ c source-blame)

  sim-back {χᴿ = χᴿ} no-rebase
      (reveal⊑-only² {M = M} {Rᴸ = Rᴸ} {c = c}
        conversion position mark free represented related type-rel)
      target-step
      with sim-back no-rebase related target-step
  sim-back {χᴿ = χᴿ} no-rebase
      (reveal⊑-only² {M = M} {Rᴸ = Rᴸ} {c = c}
        conversion position mark free represented related type-rel)
      target-step
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , result-rel , source-steps ,
          evolution , related′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N ↑ applyReveals χsᴸ c , γ′ ,
          multi-⊑ᵀ evolution type-rel , reveal-↠ c source-steps , evolution ,
          reveal⊑-only² (multi-source-reveal evolution conversion)
            (λ absent → position
              (trans (sym (multi-source-reveal-position evolution conversion))
                absent))
            (multi-source-mark evolution mark)
            (multi-source-disaligned evolution free)
            (subst≡ (λ T → applyTys χsᴸ Rᴸ ⊑ᵀ⟨ γ′ ⟩ T)
              (applyTys-★ (χᴿ ∷ [])) (multi-⊑ᵀ evolution represented))
            related′ (multi-⊑ᵀ evolution type-rel))
  sim-back {χᴿ = χᴿ} no-rebase
      (reveal⊑-only² {M = M} {Rᴸ = Rᴸ} {c = c}
        conversion position mark free represented related type-rel)
      target-step
    | inj₂ (Δᴸ′ , χsᴸ , source-blame) =
      inj₂ (Δᴸ′ , χsᴸ ++χ (keep ∷ []) , reveal-blame-↠ c source-blame)

  sim-back no-rebase
      (conceal⊑-identity {M = M} {c = c}
        conversion position related type-rel)
      target-step
      with sim-back no-rebase related target-step
  sim-back no-rebase
      (conceal⊑-identity {M = M} {c = c}
        conversion position related type-rel)
      target-step
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , result-rel , source-steps ,
          evolution , related′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N ↓ applyConceals χsᴸ c , γ′ ,
          multi-⊑ᵀ evolution type-rel , conceal-↠ c source-steps , evolution ,
          conceal⊑-identity (multi-source-conceal evolution conversion)
            (trans (multi-source-conceal-position evolution conversion)
              position)
            related′ (multi-⊑ᵀ evolution type-rel))
  sim-back no-rebase
      (conceal⊑-identity {M = M} {c = c}
        conversion position related type-rel)
      target-step
    | inj₂ (Δᴸ′ , χsᴸ , source-blame) =
      inj₂ (Δᴸ′ , χsᴸ ++χ (keep ∷ []) , conceal-blame-↠ c source-blame)

  sim-back {χᴿ = χᴿ} no-rebase
      (conceal⊑-only² {M = M} {Rᴸ = Rᴸ} {c = c}
        conversion position mark free represented related type-rel)
      target-step
      with sim-back no-rebase related target-step
  sim-back {χᴿ = χᴿ} no-rebase
      (conceal⊑-only² {M = M} {Rᴸ = Rᴸ} {c = c}
        conversion position mark free represented related type-rel)
      target-step
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , result-rel , source-steps ,
          evolution , related′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N ↓ applyConceals χsᴸ c , γ′ ,
          multi-⊑ᵀ evolution type-rel , conceal-↠ c source-steps , evolution ,
          conceal⊑-only² (multi-source-conceal evolution conversion)
            (λ absent → position
              (trans (sym (multi-source-conceal-position evolution conversion))
                absent))
            (multi-source-mark evolution mark)
            (multi-source-disaligned evolution free)
            (subst≡ (λ T → applyTys χsᴸ Rᴸ ⊑ᵀ⟨ γ′ ⟩ T)
              (applyTys-★ (χᴿ ∷ [])) (multi-⊑ᵀ evolution represented))
            related′ (multi-⊑ᵀ evolution type-rel))
  sim-back {χᴿ = χᴿ} no-rebase
      (conceal⊑-only² {M = M} {Rᴸ = Rᴸ} {c = c}
        conversion position mark free represented related type-rel)
      target-step
    | inj₂ (Δᴸ′ , χsᴸ , source-blame) =
      inj₂ (Δᴸ′ , χsᴸ ++χ (keep ∷ []) , conceal-blame-↠ c source-blame)

  sim-back no-rebase
      (reveal⊑reveal² {M = M} {c = c} source-conversion
        (Conv.⊢↑-id-var member X≠Y) positions aligned represented related
        type-rel)
      (pure-step (id-reveal target-value)) =
    inj₁
      (_ , _ , [] , M ↑ c , _ , type-rel , (M ↑ c ∎[]) ,
        evolutions-step-right refl evolution-keep evolutions-refl ,
        reveal⊑-identity source-conversion positions related type-rel)
  sim-back no-rebase
      (reveal⊑reveal² {M = M} {c = c} source-conversion
        (Conv.⊢↑-id-base member) positions aligned represented related
        type-rel)
      (pure-step (id-reveal target-value)) =
    inj₁
      (_ , _ , [] , M ↑ c , _ , type-rel , (M ↑ c ∎[]) ,
        evolutions-step-right refl evolution-keep evolutions-refl ,
        reveal⊑-identity source-conversion positions related type-rel)
  sim-back no-rebase
      (reveal⊑reveal² {M = M} {c = c} source-conversion
        (Conv.⊢↑-id-star member) positions aligned represented related
        type-rel)
      (pure-step (id-reveal target-value)) =
    inj₁
      (_ , _ , [] , M ↑ c , _ , type-rel , (M ↑ c ∎[]) ,
        evolutions-step-right refl evolution-keep evolutions-refl ,
        reveal⊑-identity source-conversion positions related type-rel)
  sim-back no-rebase
      (reveal⊑reveal² source-conversion target-conversion positions
        aligned represented related type-rel)
      (pure-step target-root@(conceal-reveal target-value)) =
    sim-back-paired-reveal-closing no-rebase source-conversion
      target-conversion positions aligned represented related type-rel
      target-root
  sim-back no-rebase
      (reveal⊑reveal² source-conversion target-conversion positions
        aligned represented related type-rel)
      (pure-step blame-reveal)
      with target-blame-catchup related
  sim-back no-rebase
      (reveal⊑reveal² {c = c} source-conversion target-conversion positions
        aligned represented related type-rel)
      (pure-step blame-reveal)
    | Δᴸ′ , χsᴸ , source-blame =
      inj₂
        (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
          reveal-blame-↠ c source-blame)
  sim-back no-rebase
      (reveal⊑reveal² {M = M} {c = c} {c′ = c′}
        source-conversion target-conversion positions
        aligned represented related type-rel)
      (ξ-reveal {χ = keep} {M′ = N′} target-step refl)
      with sim-back no-rebase related target-step
  sim-back no-rebase
      (reveal⊑reveal² {M = M} {c = c} {c′ = c′}
        source-conversion target-conversion positions
        aligned represented related type-rel)
      (ξ-reveal {χ = keep} {M′ = N′} target-step refl)
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , result-rel , source-steps ,
          evolution , related′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N ↑ applyReveals χsᴸ c , γ′ ,
          multi-⊑ᵀ evolution type-rel , reveal-↠ c source-steps , evolution ,
          subst≡
            (λ P → γ′ ⊢² N ↑ applyReveals χsᴸ c ⊑ P
              ∶ multi-⊑ᵀ evolution type-rel)
            (sym (renamedReveal-term N′ c′))
            (reveal⊑reveal²
              (multi-source-reveal evolution source-conversion)
              (multi-target-reveal evolution target-conversion)
              (trans (multi-source-reveal-position evolution source-conversion)
                (trans positions
                  (sym (multi-target-reveal-position evolution
                    target-conversion))))
              (multi-aligned evolution aligned)
              (multi-⊑ᵀ evolution represented)
              related′ (multi-⊑ᵀ evolution type-rel)))
  sim-back no-rebase
      (reveal⊑reveal² {M = M} {c = c} {c′ = c′}
        source-conversion target-conversion positions
        aligned represented related type-rel)
      (ξ-reveal {χ = keep} {M′ = N′} target-step refl)
    | inj₂ (Δᴸ′ , χsᴸ , source-blame) =
      inj₂ (Δᴸ′ , χsᴸ ++χ (keep ∷ []) , reveal-blame-↠ c source-blame)
  sim-back no-rebase
      (reveal⊑reveal² {M = M} {c = c} {c′ = c′}
        source-conversion target-conversion positions
        aligned represented related type-rel)
      (ξ-reveal {χ = bind R} target-step refl)
      with sim-back no-rebase related target-step
  sim-back no-rebase
      (reveal⊑reveal² {M = M} {c = c} {c′ = c′}
        source-conversion target-conversion positions
        aligned represented related type-rel)
      (ξ-reveal {χ = bind R} target-step refl)
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , result-rel , source-steps ,
          evolution , related′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N ↑ applyReveals χsᴸ c , γ′ ,
          multi-⊑ᵀ evolution type-rel , reveal-↠ c source-steps , evolution ,
          reveal⊑reveal²
            (multi-source-reveal evolution source-conversion)
            (multi-target-reveal evolution target-conversion)
            (trans (multi-source-reveal-position evolution source-conversion)
              (trans positions
                (sym (multi-target-reveal-position evolution
                  target-conversion))))
            (multi-aligned evolution aligned)
            (multi-⊑ᵀ evolution represented)
            related′ (multi-⊑ᵀ evolution type-rel))
  sim-back no-rebase
      (reveal⊑reveal² {M = M} {c = c} {c′ = c′}
        source-conversion target-conversion positions
        aligned represented related type-rel)
      (ξ-reveal {χ = bind R} target-step refl)
    | inj₂ (Δᴸ′ , χsᴸ , source-blame) =
      inj₂ (Δᴸ′ , χsᴸ ++χ (keep ∷ []) , reveal-blame-↠ c source-blame)

  sim-back no-rebase
      (conceal⊑conceal² {M = M} {c = c} source-conversion
        (Conv.⊢↓-id-var member X≠Y) positions aligned represented related
        type-rel)
      (pure-step (id-conceal target-value)) =
    inj₁
      (_ , _ , [] , M ↓ c , _ , type-rel , (M ↓ c ∎[]) ,
        evolutions-step-right refl evolution-keep evolutions-refl ,
        conceal⊑-identity source-conversion positions related type-rel)
  sim-back no-rebase
      (conceal⊑conceal² {M = M} {c = c} source-conversion
        (Conv.⊢↓-id-base member) positions aligned represented related
        type-rel)
      (pure-step (id-conceal target-value)) =
    inj₁
      (_ , _ , [] , M ↓ c , _ , type-rel , (M ↓ c ∎[]) ,
        evolutions-step-right refl evolution-keep evolutions-refl ,
        conceal⊑-identity source-conversion positions related type-rel)
  sim-back no-rebase
      (conceal⊑conceal² {M = M} {c = c} source-conversion
        (Conv.⊢↓-id-star member) positions aligned represented related
        type-rel)
      (pure-step (id-conceal target-value)) =
    inj₁
      (_ , _ , [] , M ↓ c , _ , type-rel , (M ↓ c ∎[]) ,
        evolutions-step-right refl evolution-keep evolutions-refl ,
        conceal⊑-identity source-conversion positions related type-rel)
  sim-back no-rebase
      (conceal⊑conceal² source-conversion target-conversion positions
        aligned represented related type-rel)
      (pure-step blame-conceal)
      with target-blame-catchup related
  sim-back no-rebase
      (conceal⊑conceal² {c = c} source-conversion target-conversion positions
        aligned represented related type-rel)
      (pure-step blame-conceal)
    | Δᴸ′ , χsᴸ , source-blame =
      inj₂
        (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
          conceal-blame-↠ c source-blame)
  sim-back no-rebase
      (conceal⊑conceal² {M = M} {c = c} {c′ = c′}
        source-conversion target-conversion positions
        aligned represented related type-rel)
      (ξ-conceal {χ = keep} {M′ = N′} target-step refl)
      with sim-back no-rebase related target-step
  sim-back no-rebase
      (conceal⊑conceal² {M = M} {c = c} {c′ = c′}
        source-conversion target-conversion positions
        aligned represented related type-rel)
      (ξ-conceal {χ = keep} {M′ = N′} target-step refl)
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , result-rel , source-steps ,
          evolution , related′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N ↓ applyConceals χsᴸ c , γ′ ,
          multi-⊑ᵀ evolution type-rel , conceal-↠ c source-steps , evolution ,
          subst≡
            (λ P → γ′ ⊢² N ↓ applyConceals χsᴸ c ⊑ P
              ∶ multi-⊑ᵀ evolution type-rel)
            (sym (renamedConceal-term N′ c′))
            (conceal⊑conceal²
              (multi-source-conceal evolution source-conversion)
              (multi-target-conceal evolution target-conversion)
              (trans
                (multi-source-conceal-position evolution source-conversion)
                (trans positions
                  (sym (multi-target-conceal-position evolution
                    target-conversion))))
              (multi-aligned evolution aligned)
              (multi-⊑ᵀ evolution represented)
              related′ (multi-⊑ᵀ evolution type-rel)))
  sim-back no-rebase
      (conceal⊑conceal² {M = M} {c = c} {c′ = c′}
        source-conversion target-conversion positions
        aligned represented related type-rel)
      (ξ-conceal {χ = keep} {M′ = N′} target-step refl)
    | inj₂ (Δᴸ′ , χsᴸ , source-blame) =
      inj₂ (Δᴸ′ , χsᴸ ++χ (keep ∷ []) , conceal-blame-↠ c source-blame)
  sim-back no-rebase
      (conceal⊑conceal² {M = M} {c = c} {c′ = c′}
        source-conversion target-conversion positions
        aligned represented related type-rel)
      (ξ-conceal {χ = bind R} target-step refl)
      with sim-back no-rebase related target-step
  sim-back no-rebase
      (conceal⊑conceal² {M = M} {c = c} {c′ = c′}
        source-conversion target-conversion positions
        aligned represented related type-rel)
      (ξ-conceal {χ = bind R} target-step refl)
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , result-rel , source-steps ,
          evolution , related′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N ↓ applyConceals χsᴸ c , γ′ ,
          multi-⊑ᵀ evolution type-rel , conceal-↠ c source-steps , evolution ,
          conceal⊑conceal²
            (multi-source-conceal evolution source-conversion)
            (multi-target-conceal evolution target-conversion)
            (trans (multi-source-conceal-position evolution source-conversion)
              (trans positions
                (sym (multi-target-conceal-position evolution
                  target-conversion))))
            (multi-aligned evolution aligned)
            (multi-⊑ᵀ evolution represented)
            related′ (multi-⊑ᵀ evolution type-rel))
  sim-back no-rebase
      (conceal⊑conceal² {M = M} {c = c} {c′ = c′}
        source-conversion target-conversion positions
        aligned represented related type-rel)
      (ξ-conceal {χ = bind R} target-step refl)
    | inj₂ (Δᴸ′ , χsᴸ , source-blame) =
      inj₂ (Δᴸ′ , χsᴸ ++χ (keep ∷ []) , conceal-blame-↠ c source-blame)

  sim-back no-rebase
      (⊑reveal-rebase² conversion@(Conv.⊢↑-id-var member X≠Y) rebase
        related type-rel)
      (pure-step target-root@(id-reveal target-value)) =
    sim-back-target-reveal-rebase-closing no-rebase conversion rebase
      related type-rel target-root

  sim-back no-rebase
      (⊑reveal-rebase² conversion@(Conv.⊢↑-id-base member) rebase
        related type-rel)
      (pure-step target-root@(id-reveal target-value)) =
    sim-back-target-reveal-rebase-closing no-rebase conversion rebase
      related type-rel target-root

  sim-back no-rebase
      (⊑reveal-rebase² conversion@(Conv.⊢↑-id-star member) rebase
        related type-rel)
      (pure-step target-root@(id-reveal target-value)) =
    sim-back-target-reveal-rebase-closing no-rebase conversion rebase
      related type-rel target-root

  sim-back no-rebase
      (⊑reveal-rebase² conversion rebase related type-rel)
      (pure-step target-root@(conceal-reveal target-value)) =
    sim-back-target-reveal-rebase-closing no-rebase conversion rebase
      related type-rel target-root

  sim-back no-rebase
      (⊑reveal-rebase² conversion rebase related type-rel)
      (pure-step blame-reveal) =
    inj₂ (target-blame-catchup related)

  sim-back no-rebase
      (⊑reveal-rebase² conversion rebase related type-rel)
      (ξ-reveal target-step refl) =
    sim-back-target-reveal-rebase-frame no-rebase conversion rebase
      related type-rel target-step

  sim-back no-rebase
      (⊑conceal-rebase² conversion rebase related type-rel)
      target-step =
    ⊥-elim (open-source-rebase-nonempty rebase no-rebase)

  sim-back no-rebase (blame⊑² target⊢ type-rel) target-step =
    inj₂ (_ , [] , (blame ∎[]))

  sim-back no-rebase (⊕⊑⊕² op left-rel right-rel type-rel)
      (pure-step (δ-⊕ result)) =
    sim-back-primitive-closing no-rebase left-rel right-rel type-rel result
  sim-back no-rebase (⊕⊑⊕² op left-rel right-rel type-rel)
      (pure-step blame-⊕₁)
      with target-blame-catchup left-rel
  sim-back no-rebase
      (⊕⊑⊕² op {L = L} {M = M} left-rel right-rel type-rel)
      (pure-step blame-⊕₁)
    | Δᴸ′ , χsᴸ , source-blame =
      inj₂
        (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
          (L ⊕[ op ] M
            —↠+[ χsᴸ ]⟨ primL-↠ source-blame ⟩
           blame ⊕[ op ] applyTerms χsᴸ M
            —→[ keep ]⟨ pure-step blame-⊕₁ ⟩
           blame ∎[]))

  sim-back no-rebase (⊕⊑⊕² op left-rel right-rel type-rel)
      (pure-step (blame-⊕₂ target-value))
      with catchup-to-less-precise no-rebase left-rel target-value
  sim-back no-rebase
      (⊕⊑⊕² op {L = L} {M = M} left-rel right-rel type-rel)
      (pure-step (blame-⊕₂ target-value))
    | inj₁
        (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-value , γ₁ , type-rel₁ ,
          source-steps , value , evolution₁ , left-rel₁)
      with target-blame-catchup
        (transport-CTI no-rebase evolution₁ right-rel)
  sim-back no-rebase
      (⊕⊑⊕² op {L = L} {M = M} left-rel right-rel type-rel)
      (pure-step (blame-⊕₂ target-value))
    | inj₁
        (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-value , γ₁ , type-rel₁ ,
          source-steps , value , evolution₁ , left-rel₁)
    | Δᴸ₂ , χsᴸ₂ , argument-blame =
      inj₂
        (Δᴸ₂ , χsᴸ₁ ++χ (χsᴸ₂ ++χ (keep ∷ [])) ,
          (L ⊕[ op ] M
            —↠+[ χsᴸ₁ ]⟨ primL-↠ source-steps ⟩
           source-value ⊕[ op ] applyTerms χsᴸ₁ M
            —↠+[ χsᴸ₂ ]⟨ primR-↠ value argument-blame ⟩
           applyTerms χsᴸ₂ source-value ⊕[ op ] blame
            —→[ keep ]⟨ pure-step
              (blame-⊕₂ (applyTerms-preserves-Value χsᴸ₂ value)) ⟩
           blame ∎[]))
  sim-back no-rebase
      (⊕⊑⊕² op {L = L} {M = M} left-rel right-rel type-rel)
      (pure-step (blame-⊕₂ target-value))
    | inj₂ (Δᴸ′ , Σᴸ′ , χsᴸ , γ′ , source-blame , evolution) =
      inj₂
        (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
          (L ⊕[ op ] M
            —↠+[ χsᴸ ]⟨ primL-↠ source-blame ⟩
           blame ⊕[ op ] applyTerms χsᴸ M
            —→[ keep ]⟨ pure-step blame-⊕₁ ⟩
           blame ∎[]))

  sim-back {χᴿ = χᴿ} no-rebase
      (⊕⊑⊕² op {L = L} {M = M} {M′ = M′}
        left-rel right-rel type-rel)
      (ξ-⊕₁ {L′ = N′} target-step refl)
      with sim-back no-rebase left-rel target-step
  sim-back {χᴿ = χᴿ} no-rebase
      (⊕⊑⊕² op {L = L} {M = M} {M′ = M′}
        left-rel right-rel type-rel)
      (ξ-⊕₁ {L′ = N′} target-step refl)
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , left-type , source-steps ,
          evolution , left-rel′)
      with subst≡
        (λ S →
          Σ[ p ∈ S ⊑ᵀ⟨ γ′ ⟩ primArgTy op ]
            γ′ ⊢² N ⊑ N′ ∶ p)
        (applyTys-primArgTy χsᴸ op)
        (subst≡
          (λ T →
            Σ[ p ∈ applyTys χsᴸ (primArgTy op) ⊑ᵀ⟨ γ′ ⟩ T ]
              γ′ ⊢² N ⊑ N′ ∶ p)
          (applyTys-primArgTy (χᴿ ∷ []) op)
          (left-type , left-rel′))
      | subst≡
        (λ S →
          Σ[ p ∈ S ⊑ᵀ⟨ γ′ ⟩ primArgTy op ]
            γ′ ⊢² applyTerms χsᴸ M ⊑ applyTerm χᴿ M′ ∶ p)
        (applyTys-primArgTy χsᴸ op)
        (subst≡
          (λ T →
            Σ[ p ∈ applyTys χsᴸ (primArgTy op) ⊑ᵀ⟨ γ′ ⟩ T ]
              γ′ ⊢² applyTerms χsᴸ M ⊑ applyTerm χᴿ M′ ∶ p)
          (applyTys-primArgTy (χᴿ ∷ []) op)
          (multi-⊑ᵀ evolution _ ,
            transport-CTI no-rebase evolution right-rel))
      | subst≡
        (λ S → S ⊑ᵀ⟨ γ′ ⟩ primResultTy op)
        (applyTys-primResultTy χsᴸ op)
        (subst≡
          (λ T → applyTys χsᴸ (primResultTy op) ⊑ᵀ⟨ γ′ ⟩ T)
          (applyTys-primResultTy (χᴿ ∷ []) op)
          (multi-⊑ᵀ evolution type-rel))
  sim-back {χᴿ = χᴿ} no-rebase
      (⊕⊑⊕² op {L = L} {M = M} {M′ = M′}
        left-rel right-rel type-rel)
      (ξ-⊕₁ {L′ = N′} target-step refl)
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , left-type , source-steps ,
          evolution , left-rel′)
    | left-type′ , left-rel″ | right-type′ , right-rel′ | result-rel′
      with subst≡
        (λ S →
          Σ[ p ∈ S ⊑ᵀ⟨ γ′ ⟩ applyTy χᴿ (primResultTy op) ]
            γ′ ⊢² N ⊕[ op ] applyTerms χsᴸ M ⊑
              N′ ⊕[ op ] applyTerm χᴿ M′ ∶ p)
        (sym (applyTys-primResultTy χsᴸ op))
        (subst≡
          (λ T →
            Σ[ p ∈ primResultTy op ⊑ᵀ⟨ γ′ ⟩ T ]
              γ′ ⊢² N ⊕[ op ] applyTerms χsᴸ M ⊑
                N′ ⊕[ op ] applyTerm χᴿ M′ ∶ p)
          (sym (applyTys-primResultTy (χᴿ ∷ []) op))
          (result-rel′ , ⊕⊑⊕² op left-rel″ right-rel′ result-rel′))
  sim-back {χᴿ = χᴿ} no-rebase
      (⊕⊑⊕² op {L = L} {M = M} {M′ = M′}
        left-rel right-rel type-rel)
      (ξ-⊕₁ {L′ = N′} target-step refl)
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N , γ′ , left-type , source-steps ,
          evolution , left-rel′)
    | left-type′ , left-rel″ | right-type′ , right-rel′ | result-rel′
    | final-rel , whole-rel =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , N ⊕[ op ] applyTerms χsᴸ M , γ′ ,
          final-rel , primL-↠ source-steps , evolution , whole-rel)
  sim-back {χᴿ = χᴿ} no-rebase
      (⊕⊑⊕² op {L = L} {M = M} {M′ = M′}
        left-rel right-rel type-rel)
      (ξ-⊕₁ {L′ = N′} target-step refl)
    | inj₂ (Δᴸ′ , χsᴸ , source-blame) =
      inj₂
        (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
          (L ⊕[ op ] M
            —↠+[ χsᴸ ]⟨ primL-↠ source-blame ⟩
           blame ⊕[ op ] applyTerms χsᴸ M
            —→[ keep ]⟨ pure-step blame-⊕₁ ⟩
           blame ∎[]))

  sim-back {χᴿ = χᴿ} no-rebase
      (⊕⊑⊕² op {L = L} {L′ = L′} {M = M}
        left-rel right-rel type-rel)
      (ξ-⊕₂ {M′ = N′} target-value target-step refl)
      with catchup-to-less-precise no-rebase left-rel target-value
  sim-back {χᴿ = χᴿ} no-rebase
      (⊕⊑⊕² op {L = L} {L′ = L′} {M = M}
        left-rel right-rel type-rel)
      (ξ-⊕₂ {M′ = N′} target-value target-step refl)
    | inj₁
        (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-value , γ₁ , type-rel₁ ,
          source-steps , value , evolution₁ , left-rel₁)
      with sim-back (multi-no-open-frames evolution₁ no-rebase)
        (transport-CTI no-rebase evolution₁ right-rel) target-step
  sim-back {χᴿ = χᴿ} no-rebase
      (⊕⊑⊕² op {L = L} {L′ = L′} {M = M}
        left-rel right-rel type-rel)
      (ξ-⊕₂ {M′ = N′} target-value target-step refl)
    | inj₁
        (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-value , γ₁ , type-rel₁ ,
          source-steps , value , evolution₁ , left-rel₁)
    | inj₁
        (Δᴸ₂ , Σᴸ₂ , χsᴸ₂ , argument , γ₂ , argument-type ,
          argument-steps , evolution₂ , right-rel₂)
      with subst≡
        (λ S →
          Σ[ p ∈ S ⊑ᵀ⟨ γ₂ ⟩ primArgTy op ]
            γ₂ ⊢² applyTerms χsᴸ₂ source-value ⊑
              applyTerm χᴿ L′ ∶ p)
        (trans (cong (applyTys χsᴸ₂)
          (applyTys-primArgTy χsᴸ₁ op))
          (applyTys-primArgTy χsᴸ₂ op))
        (subst≡
          (λ T →
            Σ[ p ∈
                applyTys χsᴸ₂ (applyTys χsᴸ₁ (primArgTy op))
                  ⊑ᵀ⟨ γ₂ ⟩ T ]
              γ₂ ⊢² applyTerms χsᴸ₂ source-value ⊑
                applyTerm χᴿ L′ ∶ p)
          (applyTys-primArgTy (χᴿ ∷ []) op)
          (multi-⊑ᵀ evolution₂ type-rel₁ ,
            transport-CTI
              (multi-no-open-frames evolution₁ no-rebase)
              evolution₂ left-rel₁))
      | subst≡
        (λ S →
          Σ[ p ∈ S ⊑ᵀ⟨ γ₂ ⟩ primArgTy op ]
            γ₂ ⊢² argument ⊑ N′ ∶ p)
        (trans (cong (applyTys χsᴸ₂)
          (applyTys-primArgTy χsᴸ₁ op))
          (applyTys-primArgTy χsᴸ₂ op))
        (subst≡
          (λ T →
            Σ[ p ∈
                applyTys χsᴸ₂ (applyTys χsᴸ₁ (primArgTy op))
                  ⊑ᵀ⟨ γ₂ ⟩ T ]
              γ₂ ⊢² argument ⊑ N′ ∶ p)
          (applyTys-primArgTy (χᴿ ∷ []) op)
          (argument-type , right-rel₂))
      | subst≡
        (λ S → S ⊑ᵀ⟨ γ₂ ⟩ primResultTy op)
        (applyTys-primResultTy (χsᴸ₁ ++χ χsᴸ₂) op)
        (subst≡
          (λ T →
            applyTys (χsᴸ₁ ++χ χsᴸ₂) (primResultTy op)
              ⊑ᵀ⟨ γ₂ ⟩ T)
          (applyTys-primResultTy (χᴿ ∷ []) op)
          (multi-⊑ᵀ (composeMultiWorldEvolution evolution₁ evolution₂)
            type-rel))
  sim-back {χᴿ = χᴿ} no-rebase
      (⊕⊑⊕² op {L = L} {L′ = L′} {M = M}
        left-rel right-rel type-rel)
      (ξ-⊕₂ {M′ = N′} target-value target-step refl)
    | inj₁
        (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-value , γ₁ , type-rel₁ ,
          source-steps , value , evolution₁ , left-rel₁)
    | inj₁
        (Δᴸ₂ , Σᴸ₂ , χsᴸ₂ , argument , γ₂ , argument-type ,
          argument-steps , evolution₂ , right-rel₂)
    | left-type′ , left-rel₂ | right-type′ , right-rel′ | result-rel′
      with subst≡
        (λ S →
          Σ[ p ∈ S ⊑ᵀ⟨ γ₂ ⟩ applyTy χᴿ (primResultTy op) ]
            γ₂ ⊢² applyTerms χsᴸ₂ source-value ⊕[ op ] argument ⊑
              applyTerm χᴿ L′ ⊕[ op ] N′ ∶ p)
        (sym (applyTys-primResultTy (χsᴸ₁ ++χ χsᴸ₂) op))
        (subst≡
          (λ T →
            Σ[ p ∈ primResultTy op ⊑ᵀ⟨ γ₂ ⟩ T ]
              γ₂ ⊢² applyTerms χsᴸ₂ source-value ⊕[ op ] argument ⊑
                applyTerm χᴿ L′ ⊕[ op ] N′ ∶ p)
          (sym (applyTys-primResultTy (χᴿ ∷ []) op))
          (result-rel′ , ⊕⊑⊕² op left-rel₂ right-rel′ result-rel′))
  sim-back {χᴿ = χᴿ} no-rebase
      (⊕⊑⊕² op {L = L} {L′ = L′} {M = M}
        left-rel right-rel type-rel)
      (ξ-⊕₂ {M′ = N′} target-value target-step refl)
    | inj₁
        (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-value , γ₁ , type-rel₁ ,
          source-steps , value , evolution₁ , left-rel₁)
    | inj₁
        (Δᴸ₂ , Σᴸ₂ , χsᴸ₂ , argument , γ₂ , argument-type ,
          argument-steps , evolution₂ , right-rel₂)
    | left-type′ , left-rel₂ | right-type′ , right-rel′ | result-rel′
    | final-rel , whole-rel =
      inj₁
        (Δᴸ₂ , Σᴸ₂ , χsᴸ₁ ++χ χsᴸ₂ ,
          applyTerms χsᴸ₂ source-value ⊕[ op ] argument , γ₂ , final-rel ,
          (L ⊕[ op ] M
            —↠+[ χsᴸ₁ ]⟨ primL-↠ source-steps ⟩
           source-value ⊕[ op ] applyTerms χsᴸ₁ M
            —↠[ χsᴸ₂ ]⟨ primR-↠ value argument-steps ⟩
           applyTerms χsᴸ₂ source-value ⊕[ op ] argument ∎[]) ,
          composeMultiWorldEvolution evolution₁ evolution₂ , whole-rel)
  sim-back {χᴿ = χᴿ} no-rebase
      (⊕⊑⊕² op {L = L} {L′ = L′} {M = M}
        left-rel right-rel type-rel)
      (ξ-⊕₂ {M′ = N′} target-value target-step refl)
    | inj₁
        (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-value , γ₁ , type-rel₁ ,
          source-steps , value , evolution₁ , left-rel₁)
    | inj₂ (Δᴸ₂ , χsᴸ₂ , argument-blame) =
      inj₂
        (Δᴸ₂ , χsᴸ₁ ++χ (χsᴸ₂ ++χ (keep ∷ [])) ,
          (L ⊕[ op ] M
            —↠+[ χsᴸ₁ ]⟨ primL-↠ source-steps ⟩
           source-value ⊕[ op ] applyTerms χsᴸ₁ M
            —↠+[ χsᴸ₂ ]⟨ primR-↠ value argument-blame ⟩
           applyTerms χsᴸ₂ source-value ⊕[ op ] blame
            —→[ keep ]⟨ pure-step
              (blame-⊕₂ (applyTerms-preserves-Value χsᴸ₂ value)) ⟩
           blame ∎[]))
  sim-back {χᴿ = χᴿ} no-rebase
      (⊕⊑⊕² op {L = L} {L′ = L′} {M = M}
        left-rel right-rel type-rel)
      (ξ-⊕₂ {M′ = N′} target-value target-step refl)
    | inj₂ (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , γ₁ , source-blame , evolution₁) =
      inj₂
        (Δᴸ₁ , χsᴸ₁ ++χ (keep ∷ []) ,
          (L ⊕[ op ] M
            —↠+[ χsᴸ₁ ]⟨ primL-↠ source-blame ⟩
           blame ⊕[ op ] applyTerms χsᴸ₁ M
            —→[ keep ]⟨ pure-step blame-⊕₁ ⟩
           blame ∎[]))
