module proof.DGG.SimBackProof where

-- File Charter:
--   * Develops the direct one-step backward simulation proof by cases on
--     cast-term imprecision and target reduction.
--   * Keeps unfinished cases as explicit interaction metas while this file is
--     listed in Makefile's IN_PROGRESS_PROOFS.
--   * Exposes no classifier, residual-family assumption, wrapper theorem, or
--     partial substitute for SimBackᵀ.
--   * The completed proof is `sim-back`; once every meta is closed, this file
--     moves from IN_PROGRESS_PROOFS into the strict All.agda gate.

open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; cong; trans)
  renaming (subst to subst≡)
open import Data.Product using (_,_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
import Data.List as List

open import Types using (★; _⇒_; _[_]ᵗ)
open import Primitives using (primArgTy; primResultTy)
open import CastTerms using
  (blame; _·_; _⦂∀_[_]; _⊕[_]_; _⟨_⟩)
open import proof.DGG.CastTermImprecision
open import proof.DGG.CtxImp using
  (_⊑ᵂ⟨_⟩_; liftᴸ-[]; smart-lift-[]; same-[])
open import Imprecision using (⇒⊑⇒)
open import Reduction using
  ( pure-step
  ; StoreChange
  ; []
  ; _∷_
  ; _∎[]
  ; _—↠[_]⟨_⟩_
  ; _—→[_]⟨_⟩_
  ; keep
  ; bind
  ; applyConsistency
  ; applyConsistencies
  ; applyBody
  ; applyTerm
  ; applyTy
  ; applyTys
  ; applyTerms
  ; blame-·₁
  ; blame-•
  ; blame-⊕₁
  ; blame-⟨⟩
  ; β-Λ
  ; β-inst
  ; β-gen
  ; β-reveal-∀
  ; β-conceal-∀
  ; ξ-·₁
  ; ξ-·₂
  ; ξ-•
  ; ξ-⟨⟩
  ; ξ-reveal
  ; ξ-conceal
  ; ξ-⊕₁
  ; ξ-⊕₂
  )
open import proof.DGG.CatchupToLessPreciseDef using
  (CatchupToLessPrecise)
open import proof.DGG.Parked.ParkedWorldLemma using
  (parked-world-closed)
open import proof.DGG.Parked.ParkedEvolveCompositionProof using
  (compose-parked-evolve)
open import proof.DGG.SimBackDef using (SimBackᵀ)
open import proof.DGG.SimBackRebasedConversionDef using
  ( SimBackSourceRevealRebaseᵀ
  ; SimBackPairedRevealFrameᵀ
  ; SimBackPairedConcealFrameᵀ
  )
open import proof.DGG.SimBackSourceLambdaDef using
  (SimBackSourceLambdaᵀ; SimBackSmartSourceLambdaᵀ)
open import proof.DGG.TransportTermImprecisionDef using
  (TransportTermImprecisionᴾᵀ)
open import proof.DGG.Parked.ParkedWorldLemma using (transport⊑ᴾ)
import proof.Imprecision as PI
open import proof.Reduction using
  ( _++χ_
  ; appL-↠
  ; appR-↠
  ; applyBodies
  ; applyTerms-preserves-Value
  ; applyTy-⇒
  ; applyTy-∀
  ; applyTys-⇒
  ; applyTys-∀
  ; applyTys-open
  ; applyTys-++
  ; applyTys-primArgTy
  ; applyTys-primResultTy
  ; cast-↠
  ; primL-↠
  ; primR-↠
  ; typeApp-↠
  ; _—↠+[_]⟨_⟩_
  )
open import proof.TypeSafety.Preservation using (apply-open)


applyTy-★ : ∀ {Δ Δ′} (χ : StoreChange Δ Δ′)
  → applyTy χ ★ ≡ ★
applyTy-★ keep = refl
applyTy-★ (bind A) = refl


module _
    (tr : TransportTermImprecisionᴾᵀ)
    (catchup : CatchupToLessPrecise)
    (sim-back-source-lambda : SimBackSourceLambdaᵀ)
    (sim-back-smart-source-lambda : SimBackSmartSourceLambdaᵀ)
    (sim-back-source-reveal-rebase : SimBackSourceRevealRebaseᵀ)
    (sim-back-paired-reveal-frame : SimBackPairedRevealFrameᵀ)
    (sim-back-paired-conceal-frame : SimBackPairedConcealFrameᵀ)
  where

  sim-back : SimBackᵀ
  sim-back parked (x⊑x² x) (pure-step ())

  sim-back parked (ƛ⊑ƛ² rel) (pure-step ())

  sim-back parked (·⊑·² {L = L} {M = M} fun-rel arg-rel)
      (pure-step (Reduction.β value)) = {! !}
  sim-back parked (·⊑·² fun-rel arg-rel)
      (pure-step (Reduction.β-⇒ value value′)) = {! !}
  sim-back parked (·⊑·² fun-rel arg-rel)
      (pure-step (Reduction.β-reveal-⇒ value value′)) = {! !}
  sim-back parked (·⊑·² fun-rel arg-rel)
      (pure-step (Reduction.β-conceal-⇒ value value′)) = {! !}
  sim-back parked (·⊑·² fun-rel arg-rel)
      (pure-step blame-·₁) = {! !}
  sim-back parked (·⊑·² fun-rel arg-rel)
      (pure-step (Reduction.blame-·₂ value)) = {! !}
  sim-back parked
      (·⊑·² {L = L} {M = M} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        fun-rel arg-rel)
      (ξ-·₁ {χ = χ} {L′ = N′} fun-step refl)
      with sim-back parked fun-rel fun-step
  sim-back parked
      (·⊑·² {L = L} {M = M} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        fun-rel arg-rel)
      (ξ-·₁ {χ = χ} {L′ = N′} fun-step refl)
      | inj₂ (Δᴸ′ , χsᴸ , L↠blame) =
    inj₂
      (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
       (L · M
         —↠+[ χsᴸ ]⟨ appL-↠ L↠blame ⟩
       blame · applyTerms χsᴸ M
         —→[ keep ]⟨ pure-step blame-·₁ ⟩
       blame ∎[]))
  sim-back parked
      (·⊑·² {M = M} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        fun-rel arg-rel)
      (ξ-·₁ {χ = χ} {L′ = N′} fun-step refl)
      | inj₁ (Δᴸ′ , χsᴸ , N , Δ′ , W′ , q ,
        L↠N , evolution , N⊑N′)
      with subst≡
        (λ S →
          Σ[ r ∈ S ⊑ᵂ⟨ W′ ⟩ applyTy χ (A′ ⇒ B′) ]
            W′ ∣ List.[] ⊢² N ⊑ N′ ∶ r)
        (applyTys-⇒ χsᴸ A B)
        (q , N⊑N′)
  sim-back parked
      (·⊑·² {M = M} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        fun-rel arg-rel)
      (ξ-·₁ {χ = χ} {L′ = N′} fun-step refl)
      | inj₁ (Δᴸ′ , χsᴸ , N , Δ′ , W′ , q ,
        L↠N , evolution , N⊑N′)
      | q′ , N⊑N′′
      with subst≡
        (λ T →
          Σ[ r ∈
              (applyTys χsᴸ A ⇒ applyTys χsᴸ B)
                ⊑ᵂ⟨ W′ ⟩ T ]
            W′ ∣ List.[] ⊢² N ⊑ N′ ∶ r)
        (applyTy-⇒ χ A′ B′)
        (q′ , N⊑N′′)
  sim-back parked
      (·⊑·² {M = M} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        fun-rel arg-rel)
      (ξ-·₁ {χ = χ} {L′ = N′} fun-step refl)
      | inj₁ (Δᴸ′ , χsᴸ , N , Δ′ , W′ , q ,
        L↠N , evolution , N⊑N′)
      | q′ , N⊑N′′
      | (⇒⊑⇒ qA qB) , N⊑N′⁺ =
    inj₁
      (Δᴸ′ , χsᴸ , N · applyTerms χsᴸ M , Δ′ , W′ , qB ,
       appL-↠ L↠N ,
       evolution ,
       ·⊑·² N⊑N′⁺
         (subst≡ (λ r → W′ ∣ List.[] ⊢² _ ⊑ _ ∶ r)
           (PI.⊑-unique _ qA) (tr evolution arg-rel)))

  sim-back parked (·⊑·² {L = L} {M = M} fun-rel arg-rel)
      (ξ-·₂ value arg-step refl)
      with catchup parked fun-rel value
  sim-back parked
      (·⊑·² {L = L} {M = M} fun-rel arg-rel)
      (ξ-·₂ value arg-step refl)
      | inj₂ (Δᴸ′ , χsᴸ , Δ′ , W′ , L↠blame , evolution) =
    inj₂
      (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
       (L · M
         —↠+[ χsᴸ ]⟨ appL-↠ L↠blame ⟩
       blame · applyTerms χsᴸ M
         —→[ keep ]⟨ pure-step blame-·₁ ⟩
       blame ∎[]))
  sim-back parked (·⊑·² {L = L} {M = M} fun-rel arg-rel)
      (ξ-·₂ value arg-step refl)
      | inj₁
        (Δᴸ₁ , χsᴸ₁ , V , Δ₁ , W₁ , qFun , L↠V , vV , evolution₁ ,
          fun-rel′)
        with sim-back (parked-world-closed parked evolution₁)
          (tr evolution₁ arg-rel) arg-step
  sim-back parked (·⊑·² {L = L} {M = M} fun-rel arg-rel)
      (ξ-·₂ value arg-step refl)
      | inj₁
        (Δᴸ₁ , χsᴸ₁ , V , Δ₁ , W₁ , qFun , L↠V , vV , evolution₁ ,
          fun-rel′)
      | inj₂ (Δᴸ₂ , χsᴸ₂ , M₁↠blame) =
    inj₂
      (Δᴸ₂ , χsᴸ₁ ++χ (χsᴸ₂ ++χ (keep ∷ [])) ,
       (L · M
         —↠+[ χsᴸ₁ ]⟨ appL-↠ L↠V ⟩
       V · applyTerms χsᴸ₁ M
         —↠+[ χsᴸ₂ ]⟨ appR-↠ vV M₁↠blame ⟩
       applyTerms χsᴸ₂ V · blame
         —→[ keep ]⟨ pure-step
           (Reduction.blame-·₂ (applyTerms-preserves-Value χsᴸ₂ vV)) ⟩
       blame ∎[]))
  sim-back parked
      (·⊑·² {L = L} {L′ = L′} {M = M} {M′ = M₀′}
        {A = A} {A′ = A′} {B = B} {B′ = B′} fun-rel arg-rel)
      (ξ-·₂ {χ = χ} {M′ = N′} value arg-step refl)
      | inj₁
        (Δᴸ₁ , χsᴸ₁ , V , Δ₁ , W₁ , qFun , L↠V , vV , evolution₁ ,
          fun-rel′)
      | inj₁ (Δᴸ₂ , χsᴸ₂ , N , Δ₂ , W₂ , qArg , M₁↠N , evolution₂ ,
          arg-rel′)
      with subst≡
        (λ S →
          Σ[ q ∈ S ⊑ᵂ⟨ W₂ ⟩ applyTy χ (A′ ⇒ B′) ]
            W₂ ∣ List.[] ⊢²
              applyTerms χsᴸ₂ V ⊑ applyTerm χ L′ ∶ q)
        (trans (cong (applyTys χsᴸ₂) (applyTys-⇒ χsᴸ₁ A B))
          (applyTys-⇒ χsᴸ₂ (applyTys χsᴸ₁ A) (applyTys χsᴸ₁ B)))
        (transport⊑ᴾ evolution₂ qFun , tr evolution₂ fun-rel′)
  sim-back parked
      (·⊑·² {L = L} {L′ = L′} {M = M} {M′ = M₀′}
        {A = A} {A′ = A′} {B = B} {B′ = B′} fun-rel arg-rel)
      (ξ-·₂ {χ = χ} {M′ = N′} value arg-step refl)
      | inj₁
        (Δᴸ₁ , χsᴸ₁ , V , Δ₁ , W₁ , qFun , L↠V , vV , evolution₁ ,
          fun-rel′)
      | inj₁ (Δᴸ₂ , χsᴸ₂ , N , Δ₂ , W₂ , qArg , M₁↠N , evolution₂ ,
          arg-rel′)
      | qFun′ , fun-rel″
      with subst≡
        (λ T →
          Σ[ q ∈
              (applyTys χsᴸ₂ (applyTys χsᴸ₁ A) ⇒
               applyTys χsᴸ₂ (applyTys χsᴸ₁ B)) ⊑ᵂ⟨ W₂ ⟩ T ]
            W₂ ∣ List.[] ⊢²
              applyTerms χsᴸ₂ V ⊑ applyTerm χ L′ ∶ q)
        (applyTy-⇒ χ A′ B′)
        (qFun′ , fun-rel″)
  sim-back parked
      (·⊑·² {L = L} {L′ = L′} {M = M} {M′ = M₀′}
        {A = A} {A′ = A′} {B = B} {B′ = B′} fun-rel arg-rel)
      (ξ-·₂ {χ = χ} {M′ = N′} value arg-step refl)
      | inj₁
        (Δᴸ₁ , χsᴸ₁ , V , Δ₁ , W₁ , qFun , L↠V , vV , evolution₁ ,
          fun-rel′)
      | inj₁ (Δᴸ₂ , χsᴸ₂ , N , Δ₂ , W₂ , qArg , M₁↠N , evolution₂ ,
          arg-rel′)
      | qFun′ , fun-rel″
      | (⇒⊑⇒ qA qB) , fun-rel⁺
      with subst≡
        (λ S →
          Σ[ q ∈ S ⊑ᵂ⟨ W₂ ⟩ applyTy χ B′ ]
            W₂ ∣ List.[] ⊢²
              applyTerms χsᴸ₂ V · N ⊑ applyTerm χ L′ · N′ ∶ q)
        (applyTys-++ χsᴸ₁ χsᴸ₂ B)
        (qB , ·⊑·² fun-rel⁺
          (subst≡ (λ q → W₂ ∣ List.[] ⊢² N ⊑ N′ ∶ q)
            (PI.⊑-unique qArg qA) arg-rel′))
  sim-back parked
      (·⊑·² {L = L} {L′ = L′} {M = M} {M′ = M₀′}
        {A = A} {A′ = A′} {B = B} {B′ = B′} fun-rel arg-rel)
      (ξ-·₂ {χ = χ} {M′ = N′} value arg-step refl)
      | inj₁
        (Δᴸ₁ , χsᴸ₁ , V , Δ₁ , W₁ , qFun , L↠V , vV , evolution₁ ,
          fun-rel′)
      | inj₁ (Δᴸ₂ , χsᴸ₂ , N , Δ₂ , W₂ , qArg , M₁↠N , evolution₂ ,
          arg-rel′)
      | qFun′ , fun-rel″
      | (⇒⊑⇒ qA qB) , fun-rel⁺
      | qResult , whole-rel =
    inj₁
      (Δᴸ₂ , χsᴸ₁ ++χ χsᴸ₂ , applyTerms χsᴸ₂ V · N , Δ₂ , W₂ ,
       qResult ,
       (L · M
         —↠+[ χsᴸ₁ ]⟨ appL-↠ L↠V ⟩
       V · applyTerms χsᴸ₁ M
         —↠[ χsᴸ₂ ]⟨ appR-↠ vV M₁↠N ⟩
       applyTerms χsᴸ₂ V · N ∎[]) ,
       compose-parked-evolve evolution₁ evolution₂ ,
       whole-rel)

  sim-back parked (Λ⊑Λ² lift vV vV′ rel q) (pure-step ())

  sim-back parked
      (Λ⊑² nonvar occurs liftᴸ-[] vV target-typing rel q) step
    = sim-back-source-lambda parked nonvar occurs vV target-typing rel q step

  sim-back parked
      (Λ⊑²-smart-comma nonvar occurs lift-world smart-lift-[] vV
        target-typing rel q)
      step =
    sim-back-smart-source-lambda parked nonvar occurs lift-world vV
      target-typing rel q step

  sim-back parked (•⊑•² all-rel rel type-rel result-rel)
      (pure-step (Reduction.β-∀ value equality)) = {! !}

  sim-back parked (•⊑•² all-rel rel type-rel result-rel)
      (pure-step blame-•) = {! !}

  sim-back parked (•⊑•² all-rel rel type-rel result-rel)
      (β-Λ value) = {! !}
  sim-back parked (•⊑•² all-rel rel type-rel result-rel)
      (β-gen value not-star safe) = {! !}
  sim-back parked (•⊑•² all-rel rel type-rel result-rel)
      (β-reveal-∀ value) = {! !}
  sim-back parked (•⊑•² all-rel rel type-rel result-rel)
      (β-conceal-∀ value) = {! !}
  sim-back parked
      (•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        all-rel rel type-rel result-rel)
      (ξ-• {χ = χ} {M′ = N′} body-step refl refl)
      with sim-back parked rel body-step
  sim-back parked
      (•⊑•² {M = M} {C = C} {C′ = C′} {A = A} {A′ = A′}
        all-rel rel type-rel result-rel)
      (ξ-• {χ = χ} {M′ = N′} body-step refl refl)
      | inj₂ (Δᴸ′ , χsᴸ , M↠blame) =
    inj₂
      (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
       (M ⦂∀ C [ A ]
         —↠+[ χsᴸ ]⟨ typeApp-↠ M↠blame ⟩
       blame ⦂∀ applyBodies χsᴸ C [ applyTys χsᴸ A ]
         —→[ keep ]⟨ pure-step blame-• ⟩
       blame ∎[]))
  sim-back parked
      (•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        all-rel rel type-rel result-rel)
      (ξ-• {χ = χ} {M′ = N′} body-step refl refl)
      | inj₁ (Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evolution , N⊑N′)
      rewrite applyTys-∀ χsᴸ C
            | applyTy-∀ χ C′
      with p | N⊑N′
  sim-back parked
      (•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        all-rel rel type-rel result-rel)
      (ξ-• {χ = χ} {M′ = N′} body-step refl refl)
      | inj₁ (Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evolution , N⊑N′)
      | all-rel⁺ | N⊑N′⁺
      with subst≡
        (λ S →
          Σ[ s ∈ S ⊑ᵂ⟨ W′ ⟩ applyTy χ (C′ [ A′ ]ᵗ) ]
            W′ ∣ List.[] ⊢²
              N ⦂∀ applyBodies χsᴸ C [ applyTys χsᴸ A ] ⊑
              N′ ⦂∀ applyBody χ C′ [ applyTy χ A′ ]
              ∶ s)
        (sym (applyTys-open χsᴸ C A))
        (subst≡
          (λ T →
            Σ[ s ∈
                (applyBodies χsᴸ C [ applyTys χsᴸ A ]ᵗ)
                  ⊑ᵂ⟨ W′ ⟩ T ]
              W′ ∣ List.[] ⊢²
                N ⦂∀ applyBodies χsᴸ C [ applyTys χsᴸ A ] ⊑
                N′ ⦂∀ applyBody χ C′ [ applyTy χ A′ ]
                ∶ s)
          (sym (apply-open χ C′ A′))
          ( subst≡
              (λ T →
                (applyBodies χsᴸ C [ applyTys χsᴸ A ]ᵗ)
                  ⊑ᵂ⟨ W′ ⟩ T)
              (apply-open χ C′ A′)
              (subst≡
                (λ S → S ⊑ᵂ⟨ W′ ⟩ applyTy χ (C′ [ A′ ]ᵗ))
                (applyTys-open χsᴸ C A)
                (transport⊑ᴾ evolution result-rel))
          , •⊑•² all-rel⁺ N⊑N′⁺
              (transport⊑ᴾ evolution type-rel)
              (subst≡
                (λ T →
                  (applyBodies χsᴸ C [ applyTys χsᴸ A ]ᵗ)
                    ⊑ᵂ⟨ W′ ⟩ T)
                (apply-open χ C′ A′)
                (subst≡
                  (λ S → S ⊑ᵂ⟨ W′ ⟩ applyTy χ (C′ [ A′ ]ᵗ))
                  (applyTys-open χsᴸ C A)
                  (transport⊑ᴾ evolution result-rel)))
          ))
  sim-back parked
      (•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        all-rel rel type-rel result-rel)
      (ξ-• {χ = χ} {M′ = N′} body-step refl refl)
      | inj₁ (Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evolution , N⊑N′)
      | all-rel⁺ | N⊑N′⁺
      | result-rel⁺ , whole-rel =
    inj₁
      (Δᴸ′ , χsᴸ ,
       N ⦂∀ applyBodies χsᴸ C [ applyTys χsᴸ A ] ,
       Δ′ , W′ , result-rel⁺ ,
       typeApp-↠ M↠N ,
       evolution ,
       whole-rel)

  sim-back {χᴿ = χ} parked
      (•⊑² {C = C} {A = A} all-rel rel type-rel result-rel) step
      with sim-back parked rel step
  sim-back {χᴿ = χ} parked
      (•⊑² {M = M} {C = C} {A = A}
        all-rel rel type-rel result-rel) step
      | inj₂ (Δᴸ′ , χsᴸ , M↠blame) =
    inj₂
      (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
       (M ⦂∀ C [ A ]
         —↠+[ χsᴸ ]⟨ typeApp-↠ M↠blame ⟩
       blame ⦂∀ applyBodies χsᴸ C [ applyTys χsᴸ A ]
         —→[ keep ]⟨ pure-step blame-• ⟩
       blame ∎[]))
  sim-back {χᴿ = χ} parked
      (•⊑² {C = C} {A = A} all-rel rel type-rel result-rel) step
      | inj₁ (Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evolution , N⊑N′)
      rewrite applyTys-∀ χsᴸ C
      with p | N⊑N′
  sim-back {χᴿ = χ} parked
      (•⊑² {C = C} {A = A} all-rel rel type-rel result-rel) step
      | inj₁ (Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evolution , N⊑N′)
      | all-rel⁺ | N⊑N′⁺
      with subst≡
        (λ S →
          Σ[ s ∈ S ⊑ᵂ⟨ W′ ⟩ _ ]
            W′ ∣ List.[] ⊢²
              N ⦂∀ applyBodies χsᴸ C [ applyTys χsᴸ A ]
              ⊑ _ ∶ s)
        (sym (applyTys-open χsᴸ C A))
        ( subst≡
            (λ S → S ⊑ᵂ⟨ W′ ⟩ _)
            (applyTys-open χsᴸ C A)
            (transport⊑ᴾ evolution result-rel)
        , •⊑² all-rel⁺ N⊑N′⁺
            (subst≡
              (λ T → applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ T)
              (applyTy-★ χ)
              (transport⊑ᴾ evolution type-rel))
            (subst≡
              (λ S → S ⊑ᵂ⟨ W′ ⟩ _)
              (applyTys-open χsᴸ C A)
              (transport⊑ᴾ evolution result-rel))
        )
  sim-back {χᴿ = χ} parked
      (•⊑² {C = C} {A = A} all-rel rel type-rel result-rel) step
      | inj₁ (Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evolution , N⊑N′)
      | all-rel⁺ | N⊑N′⁺
      | result-rel⁺ , whole-rel =
    inj₁
      (Δᴸ′ , χsᴸ ,
       N ⦂∀ applyBodies χsᴸ C [ applyTys χsᴸ A ] ,
       Δ′ , W′ , result-rel⁺ ,
       typeApp-↠ M↠N ,
       evolution ,
       whole-rel)

  sim-back parked (κ⊑κ² constant type-rel) (pure-step ())

  sim-back parked
      (cast⊑cast² source-cast target-cast rel type-rel)
      (pure-step (Reduction.β-id value)) = {! !}

  sim-back parked
      (cast⊑cast² source-cast target-cast rel type-rel)
      (pure-step (Reduction.ground value unequal)) = {! !}

  sim-back parked
      (cast⊑cast² source-cast target-cast rel type-rel)
      (pure-step (Reduction.expand value unequal)) = {! !}

  sim-back parked
      (cast⊑cast² source-cast target-cast rel type-rel)
      (pure-step (Reduction.tag-untag value)) = {! !}

  sim-back parked
      (cast⊑cast² source-cast target-cast rel type-rel)
      (pure-step (Reduction.tag-untag-bad value unequal)) = {! !}

  sim-back parked
      (cast⊑cast² source-cast target-cast rel type-rel)
      (pure-step (Reduction.blame-bot-intro value)) = {! !}

  sim-back parked
      (cast⊑cast² source-cast target-cast rel type-rel)
      (pure-step blame-⟨⟩) = {! !}

  sim-back parked
      (cast⊑cast² source-cast target-cast rel type-rel)
      (β-inst value not-star) = {! !}

  sim-back parked
      (cast⊑cast² source-cast target-cast rel type-rel)
      (ξ-⟨⟩ body-step refl)
      with sim-back parked rel body-step
  sim-back parked
      (cast⊑cast² {M = M} source-cast target-cast rel type-rel)
      (ξ-⟨⟩ body-step refl)
      | inj₂ (Δᴸ′ , χsᴸ , M↠blame) =
    inj₂
      (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
       (M ⟨ source-cast ⟩
         —↠+[ χsᴸ ]⟨ cast-↠ source-cast M↠blame ⟩
       blame ⟨ applyConsistencies χsᴸ source-cast ⟩
         —→[ keep ]⟨ pure-step blame-⟨⟩ ⟩
       blame ∎[]))
  sim-back parked
      (cast⊑cast² source-cast target-cast rel type-rel)
      (ξ-⟨⟩ {χ = χ} body-step refl)
      | inj₁ (Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evolution , N⊑N′) =
    inj₁
      (Δᴸ′ , χsᴸ , N ⟨ applyConsistencies χsᴸ source-cast ⟩ ,
       Δ′ , W′ , transport⊑ᴾ evolution type-rel ,
       cast-↠ source-cast M↠N ,
       evolution ,
       cast⊑cast² (applyConsistencies χsᴸ source-cast)
         (applyConsistency χ target-cast) N⊑N′
         (transport⊑ᴾ evolution type-rel))

  sim-back parked (⊑cast² target-cast rel type-rel)
      (pure-step (Reduction.β-id value)) = {! !}

  sim-back parked (⊑cast² target-cast rel type-rel)
      (pure-step (Reduction.ground value unequal)) = {! !}

  sim-back parked (⊑cast² target-cast rel type-rel)
      (pure-step (Reduction.expand value unequal)) = {! !}

  sim-back parked (⊑cast² target-cast rel type-rel)
      (pure-step (Reduction.tag-untag value)) = {! !}

  sim-back parked (⊑cast² target-cast rel type-rel)
      (pure-step (Reduction.tag-untag-bad value unequal)) = {! !}

  sim-back parked (⊑cast² target-cast rel type-rel)
      (pure-step (Reduction.blame-bot-intro value)) = {! !}

  sim-back parked (⊑cast² target-cast rel type-rel)
      (pure-step blame-⟨⟩) = {! !}

  sim-back parked (⊑cast² target-cast rel type-rel)
      (β-inst value not-star) = {! !}

  sim-back parked (⊑cast² target-cast rel type-rel)
      (ξ-⟨⟩ body-step refl)
      with sim-back parked rel body-step
  sim-back parked (⊑cast² target-cast rel type-rel)
      (ξ-⟨⟩ body-step refl)
      | inj₂ source-blame = inj₂ source-blame
  sim-back parked (⊑cast² target-cast rel type-rel)
      (ξ-⟨⟩ {χ = χ} body-step refl)
      | inj₁ (Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evolution , N⊑N′) =
    inj₁
      (Δᴸ′ , χsᴸ , N , Δ′ , W′ ,
       transport⊑ᴾ evolution type-rel ,
       M↠N ,
       evolution ,
       ⊑cast² (applyConsistency χ target-cast)
         N⊑N′ (transport⊑ᴾ evolution type-rel))

  sim-back parked (⊑reveal² conversion position rel type-rel)
      (pure-step (Reduction.id-reveal value)) = {! !}

  sim-back parked (⊑reveal² conversion position rel type-rel)
      (pure-step (Reduction.conceal-reveal value)) = {! !}

  sim-back parked (⊑reveal² conversion position rel type-rel)
      (pure-step Reduction.blame-reveal) = {! !}

  sim-back parked (⊑reveal² conversion position rel type-rel)
      (ξ-reveal body-step refl)
      with sim-back parked rel body-step
  ... | induction = {! !}

  sim-back parked (⊑conceal² conversion position rel type-rel)
      (pure-step (Reduction.id-conceal value)) = {! !}

  sim-back parked (⊑conceal² conversion position rel type-rel)
      (pure-step Reduction.blame-conceal) = {! !}

  sim-back parked (⊑conceal² conversion position rel type-rel)
      (ξ-conceal body-step refl)
      with sim-back parked rel body-step
  ... | induction = {! !}

  sim-back parked
      (cast⊑² {M = M} source-cast rel type-rel) step
      with sim-back parked rel step
  sim-back parked
      (cast⊑² {M = M} source-cast rel type-rel) step
      | inj₂ (Δᴸ′ , χsᴸ , M↠blame) =
    inj₂
      (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
       (M ⟨ source-cast ⟩
         —↠+[ χsᴸ ]⟨ cast-↠ source-cast M↠blame ⟩
       blame ⟨ applyConsistencies χsᴸ source-cast ⟩
         —→[ keep ]⟨ pure-step blame-⟨⟩ ⟩
       blame ∎[]))
  sim-back parked
      (cast⊑² source-cast rel type-rel) step
      | inj₁ (Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evolution , N⊑N′) =
    inj₁
      (Δᴸ′ , χsᴸ , N ⟨ applyConsistencies χsᴸ source-cast ⟩ ,
       Δ′ , W′ , transport⊑ᴾ evolution type-rel ,
       cast-↠ source-cast M↠N ,
       evolution ,
       cast⊑² (applyConsistencies χsᴸ source-cast)
         N⊑N′ (transport⊑ᴾ evolution type-rel))

  sim-back parked
      (reveal⊑-neutral² conversion position rel type-rel) step
      with sim-back parked rel step
  ... | induction = {! !}
  sim-back parked
      (reveal⊑-only² conversion position mark unoccupied represented rel
        type-rel)
      step
      with sim-back parked rel step
  ... | induction = {! !}
  sim-back parked
      (reveal⊑² conversion position target-member represented mono rebase
        same-[] rel type-rel)
      step =
    sim-back-source-reveal-rebase parked conversion position target-member
      represented mono rebase rel type-rel step

  sim-back parked
      (conceal⊑-neutral² conversion position rel type-rel) step
      with sim-back parked rel step
  ... | induction = {! !}
  sim-back parked
      (conceal⊑² conversion position mark unoccupied represented rel type-rel)
      step
      with sim-back parked rel step
  ... | induction = {! !}
  sim-back parked
      (reveal⊑reveal² source-conversion target-conversion positions position
        represented mono rebase same-[] rel type-rel)
      (pure-step (Reduction.id-reveal value)) = {! !}

  sim-back parked
      (reveal⊑reveal² source-conversion target-conversion positions position
        represented mono rebase same-[] rel type-rel)
      (pure-step (Reduction.conceal-reveal value)) = {! !}

  sim-back parked
      (reveal⊑reveal² source-conversion target-conversion positions position
        represented mono rebase same-[] rel type-rel)
      (pure-step Reduction.blame-reveal) = {! !}

  sim-back parked
      (reveal⊑reveal² source-conversion target-conversion positions position
        represented mono rebase same-[] rel type-rel)
      (ξ-reveal body-step refl)
    = sim-back-paired-reveal-frame parked source-conversion target-conversion
        positions position represented mono rebase rel type-rel body-step

  sim-back parked
      (conceal⊑conceal² source-conversion target-conversion positions position
        represented mono rebase same-[] rel type-rel)
      (pure-step (Reduction.id-conceal value)) = {! !}

  sim-back parked
      (conceal⊑conceal² source-conversion target-conversion positions position
        represented mono rebase same-[] rel type-rel)
      (pure-step Reduction.blame-conceal) = {! !}

  sim-back parked
      (conceal⊑conceal² source-conversion target-conversion positions position
        represented mono rebase same-[] rel type-rel)
      (ξ-conceal body-step refl)
    = sim-back-paired-conceal-frame parked source-conversion
        target-conversion positions position represented mono rebase rel
        type-rel body-step

  sim-back {Δᴸ = Δᴸ} parked
      (blame⊑² target-typing type-rel) step =
    inj₂ (Δᴸ , [] , (blame ∎[]))

  sim-back parked
      (⊕⊑⊕² op {L = L} {M = M} left-rel right-rel type-rel)
      (pure-step (Reduction.δ-⊕ delta)) = {! !}

  sim-back parked (⊕⊑⊕² op left-rel right-rel type-rel)
      (pure-step blame-⊕₁) = {! !}

  sim-back parked (⊕⊑⊕² op left-rel right-rel type-rel)
      (pure-step (Reduction.blame-⊕₂ value)) = {! !}

  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} left-rel right-rel type-rel)
      (ξ-⊕₁ {χ = χ} {L′ = N′} left-step refl)
      with sim-back parked left-rel left-step
  sim-back parked
      (⊕⊑⊕² op {L = L} {M = M} {M′ = M′}
        left-rel right-rel type-rel)
      (ξ-⊕₁ {χ = χ} {L′ = N′} left-step refl)
      | inj₂ (Δᴸ′ , χsᴸ , L↠blame) =
    inj₂
      (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
       (L ⊕[ op ] M
         —↠+[ χsᴸ ]⟨ primL-↠ L↠blame ⟩
       blame ⊕[ op ] applyTerms χsᴸ M
         —→[ keep ]⟨ pure-step blame-⊕₁ ⟩
       blame ∎[]))
  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} left-rel right-rel type-rel)
      (ξ-⊕₁ {χ = χ} {L′ = N′} left-step refl)
      | inj₁ (Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        L↠N , evolution , N⊑N′)
      with subst≡
        (λ S →
          Σ[ s ∈ S ⊑ᵂ⟨ W′ ⟩ applyTy χ (primArgTy op) ]
            W′ ∣ List.[] ⊢² N ⊑ N′ ∶ s)
        (applyTys-primArgTy χsᴸ op)
        (p , N⊑N′)
  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} left-rel right-rel type-rel)
      (ξ-⊕₁ {χ = χ} {L′ = N′} left-step refl)
      | inj₁ (Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        L↠N , evolution , N⊑N′)
      | p′ , N⊑N′′
      with subst≡
        (λ T →
          Σ[ s ∈ primArgTy op ⊑ᵂ⟨ W′ ⟩ T ]
            W′ ∣ List.[] ⊢² N ⊑ N′ ∶ s)
        (applyTys-primArgTy (χ ∷ []) op)
        (p′ , N⊑N′′)
  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} left-rel right-rel type-rel)
      (ξ-⊕₁ {χ = χ} {L′ = N′} left-step refl)
      | inj₁ (Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        L↠N , evolution , N⊑N′)
      | p′ , N⊑N′′
      | left-type-rel , N⊑N′⁺
      with subst≡
        (λ S →
          Σ[ s ∈ S ⊑ᵂ⟨ W′ ⟩ primArgTy op ]
            W′ ∣ List.[] ⊢²
              applyTerms χsᴸ M ⊑ applyTerm χ M′ ∶ s)
        (applyTys-primArgTy χsᴸ op)
        (subst≡
          (λ T →
            Σ[ s ∈ applyTys χsᴸ (primArgTy op) ⊑ᵂ⟨ W′ ⟩ T ]
              W′ ∣ List.[] ⊢²
                applyTerms χsᴸ M ⊑ applyTerm χ M′ ∶ s)
          (applyTys-primArgTy (χ ∷ []) op)
          (transport⊑ᴾ evolution _ , tr evolution right-rel))
  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} left-rel right-rel type-rel)
      (ξ-⊕₁ {χ = χ} {L′ = N′} left-step refl)
      | inj₁ (Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        L↠N , evolution , N⊑N′)
      | p′ , N⊑N′′
      | left-type-rel , N⊑N′⁺
      | right-type-rel , M⊑M′⁺
      with subst≡
        (λ S → S ⊑ᵂ⟨ W′ ⟩ primResultTy op)
        (applyTys-primResultTy χsᴸ op)
        (subst≡
          (λ T → applyTys χsᴸ (primResultTy op) ⊑ᵂ⟨ W′ ⟩ T)
          (applyTys-primResultTy (χ ∷ []) op)
          (transport⊑ᴾ evolution type-rel))
  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} left-rel right-rel type-rel)
      (ξ-⊕₁ {χ = χ} {L′ = N′} left-step refl)
      | inj₁ (Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        L↠N , evolution , N⊑N′)
      | p′ , N⊑N′′
      | left-type-rel , N⊑N′⁺
      | right-type-rel , M⊑M′⁺
      | result-type-rel
      with subst≡
        (λ S →
          Σ[ s ∈ S ⊑ᵂ⟨ W′ ⟩ applyTy χ (primResultTy op) ]
            W′ ∣ List.[] ⊢²
              N ⊕[ op ] applyTerms χsᴸ M ⊑
              N′ ⊕[ op ] applyTerm χ M′ ∶ s)
        (sym (applyTys-primResultTy χsᴸ op))
        (subst≡
          (λ T →
            Σ[ s ∈ primResultTy op ⊑ᵂ⟨ W′ ⟩ T ]
              W′ ∣ List.[] ⊢²
                N ⊕[ op ] applyTerms χsᴸ M ⊑
                N′ ⊕[ op ] applyTerm χ M′ ∶ s)
          (sym (applyTys-primResultTy (χ ∷ []) op))
          (result-type-rel ,
           ⊕⊑⊕² op N⊑N′⁺ M⊑M′⁺ result-type-rel))
  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} left-rel right-rel type-rel)
      (ξ-⊕₁ {χ = χ} {L′ = N′} left-step refl)
      | inj₁ (Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        L↠N , evolution , N⊑N′)
      | p′ , N⊑N′′
      | left-type-rel , N⊑N′⁺
      | right-type-rel , M⊑M′⁺
      | result-type-rel
      | result-type-rel′ , whole-rel =
    inj₁
      (Δᴸ′ , χsᴸ , N ⊕[ op ] applyTerms χsᴸ M ,
       Δ′ , W′ , result-type-rel′ ,
       primL-↠ L↠N ,
       evolution ,
       whole-rel)

  sim-back parked
      (⊕⊑⊕² op {L = L} {M = M} left-rel right-rel type-rel)
      (ξ-⊕₂ value right-step refl)
      with catchup parked left-rel value
  sim-back parked
      (⊕⊑⊕² op {L = L} {M = M} left-rel right-rel type-rel)
      (ξ-⊕₂ value right-step refl)
      | inj₂ (Δᴸ′ , χsᴸ , Δ′ , W′ , L↠blame , evolution) =
    inj₂
      (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
       (L ⊕[ op ] M
         —↠+[ χsᴸ ]⟨ primL-↠ L↠blame ⟩
       blame ⊕[ op ] applyTerms χsᴸ M
         —→[ keep ]⟨ pure-step blame-⊕₁ ⟩
       blame ∎[]))
  sim-back parked
      (⊕⊑⊕² op {L = L} {M = M} left-rel right-rel type-rel)
      (ξ-⊕₂ value right-step refl)
      | inj₁
        (Δᴸ₁ , χsᴸ₁ , V , Δ₁ , W₁ , qLeft , L↠V , vV , evolution₁ ,
          left-rel′)
        with sim-back (parked-world-closed parked evolution₁)
          (tr evolution₁ right-rel) right-step
  sim-back parked
      (⊕⊑⊕² op {L = L} {M = M} left-rel right-rel type-rel)
      (ξ-⊕₂ value right-step refl)
      | inj₁
        (Δᴸ₁ , χsᴸ₁ , V , Δ₁ , W₁ , qLeft , L↠V , vV , evolution₁ ,
          left-rel′)
      | inj₂ (Δᴸ₂ , χsᴸ₂ , M₁↠blame) =
    inj₂
      (Δᴸ₂ , χsᴸ₁ ++χ (χsᴸ₂ ++χ (keep ∷ [])) ,
       (L ⊕[ op ] M
         —↠+[ χsᴸ₁ ]⟨ primL-↠ L↠V ⟩
       V ⊕[ op ] applyTerms χsᴸ₁ M
         —↠+[ χsᴸ₂ ]⟨ primR-↠ vV M₁↠blame ⟩
       applyTerms χsᴸ₂ V ⊕[ op ] blame
         —→[ keep ]⟨ pure-step
           (Reduction.blame-⊕₂ (applyTerms-preserves-Value χsᴸ₂ vV)) ⟩
       blame ∎[]))
  sim-back parked
      (⊕⊑⊕² op {L = L} {M = M} left-rel right-rel type-rel)
      (ξ-⊕₂ value right-step refl)
      | inj₁
        (Δᴸ₁ , χsᴸ₁ , V , Δ₁ , W₁ , qLeft , L↠V , vV , evolution₁ ,
          left-rel′)
      | inj₁ (Δᴸ₂ , χsᴸ₂ , N , Δ₂ , W₂ , qRight , M₁↠N , evolution₂ ,
          right-rel′) = {! !}
