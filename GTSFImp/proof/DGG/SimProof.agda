{-# OPTIONS --safe #-}

module proof.DGG.SimProof where

-- File Charter:
--   * Develops forward one-step simulation by induction on the canonical CTI
--     derivation and the source reduction.
--   * Places recursive calls in every contextual reduction case before any
--     root-closing case is discharged.
--   * Is parameterized by the separate CTI-transport induction and the
--     catch-up and root-closing inductions used by the corresponding cases.
--   * Exports a complete direct proof with no unresolved interaction goals.

open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Product using (_,_; _×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; cong; refl; subst; sym; trans)

open import CastTerms using
  ( Term; Value; ⟨_,_,_⟩; _·_; _⦂∀_[_]; _⟨_⟩; _↑_; _↓_; ƛ_; Λ_
  ; _《_》; fun; all; inj; seal; genᵥ
  )
open import CastTerms using (_⊕[_]_)
open import Consistency using (Env∼; _⊢_∼_)
open import Imprecision using (⇒⊑⇒)
open import Primitives using (primArgTy; primResultTy)
open import TyStore using (TyStore)
open import Types using (Ty; TyCtx; _⇒_; _[_]ᵗ)
open import Reduction
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.CatchupToMorePreciseDef using
  (CatchupToMorePrecise)
open import proof.DGG.CastTermImprecisionTyping using (target-typing)
open import proof.DGG.ConversionPivotAlignment using
  (generator-absent; generator-here)
open import proof.DGG.SimDef using (Simᵀ)
open import proof.DGG.SimPairedAllClosingDef using
  (SimPairedAllClosingᵀ)
open import proof.DGG.SimPairedCastValuesDef using
  (SimPairedCastValuesᵀ)
open import proof.DGG.SimPairedFunClosingDef using
  (SimPairedFunClosingᵀ)
open import proof.DGG.SimPairedRevealClosingDef using
  (SimPairedRevealClosingᵀ)
open import proof.DGG.SimPrimitiveClosingDef using
  (SimPrimitiveClosingᵀ)
open import proof.DGG.SimSourceAllClosingDef using
  (SimSourceAllClosingᵀ)
open import proof.DGG.SimSourceCastValuesDef using
  (SimSourceCastValuesᵀ)
open import proof.DGG.SimSourceRevealClosingDef using
  (SimSourceRevealClosingᵀ)
open import proof.DGG.SimTargetRevealRebaseClosingDef using
  (SimTargetRevealRebaseClosingᵀ)
open import proof.DGG.TransportTermImprecisionDef using
  (TransportTermImprecisionᵀ)
open import proof.DGG.WorldEvolutionSequence using
  ( multi-no-source-rebase
  ; multi-⊑ᵀ
  ; append-left-keep
  ; composeMultiWorldEvolution
  ; evolutions-refl
  ; MultiWorldEvolution
  ; multi-aligned
  ; multi-source-disaligned
  ; multi-source-mark
  ; multi-source-conceal
  ; multi-source-conceal-position
  ; multi-source-reveal
  ; multi-source-reveal-position
  ; multi-target-conceal
  ; multi-target-conceal-position
  ; multi-target-reveal
  ; multi-target-reveal-position
  )
open import proof.DGG.World using
  (_⊑ᶜ_; _⊑ᵀ⟨_⟩_; sourceRebaseCountᶜ)
open import proof.Reduction using
  ( applyConceals
  ; applyBodies
  ; applyReveals
  ; applyTy-⇒
  ; applyTy-∀
  ; applyTys-⇒
  ; applyTys-open
  ; applyTys-★
  ; applyTys-∀
  ; applyTys-++
  ; applyTys-primArgTy
  ; applyTys-primResultTy
  ; appL-↠
  ; appR-↠
  ; cast-↠
  ; conceal-↠
  ; renamedConceal-term
  ; renamedReveal-term
  ; primL-↠
  ; primR-↠
  ; reveal-↠
  ; typeApp-↠
  ; _++χ_
  ; _—↠+[_]⟨_⟩_
  )
import proof.Imprecision as PI
open import proof.TypeSafety.Preservation using (apply-open)


generator-here≢absent : generator-here ≢ generator-absent
generator-here≢absent ()


module _
    (transport-CTI : TransportTermImprecisionᵀ)
    (catchup-to-more-precise : CatchupToMorePrecise)
    (sim-paired-fun-closing : SimPairedFunClosingᵀ)
    (sim-paired-all-closing : SimPairedAllClosingᵀ)
    (sim-source-all-closing : SimSourceAllClosingᵀ)
    (sim-paired-cast-values : SimPairedCastValuesᵀ)
    (sim-source-cast-values : SimSourceCastValuesᵀ)
    (sim-source-reveal-closing : SimSourceRevealClosingᵀ)
    (sim-paired-reveal-closing : SimPairedRevealClosingᵀ)
    (sim-primitive-closing : SimPrimitiveClosingᵀ)
    (sim-target-reveal-rebase-closing :
      SimTargetRevealRebaseClosingᵀ)
  where

  sim-paired-cast-root : ∀ {Δᴸ Δᴿ Δᴸ′ : TyCtx}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
      {χᴸ : StoreChange Δᴸ Δᴸ′}
      {V : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
      {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
      {ν : Env∼ Δᴸ} {ν′ : Env∼ Δᴿ}
      {c : ν ⊢ A ∼ B} {c′ : ν′ ⊢ A′ ∼ B′}
      {p : A ⊑ᵀ⟨ γ ⟩ A′}
    → sourceRebaseCountᶜ γ ≡ 0
    → γ CTI.⊢² V ⊑ M′ ∶ p
    → (q : B ⊑ᵀ⟨ γ ⟩ B′)
    → Value V
    → V ⟨ c ⟩ —→[ χᴸ ] N
    → Σ[ Δᴿ′ ∈ TyCtx ]
      Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
      Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
      Σ[ r ∈ applyTy χᴸ B ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B′ ]
        (M′ ⟨ c′ ⟩ —↠[ χsᴿ ] N′)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} (χᴸ ∷ []) χsᴿ
        × (γ′ CTI.⊢² N ⊑ N′ ∶ r)
  sim-paired-cast-root no-rebase prem q source-value source-step
      with catchup-to-more-precise no-rebase prem source-value
  sim-paired-cast-root {B = B} {B′ = B′} {c′ = c′}
      no-rebase prem q source-value source-step
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , V′ , γ₁ , p₁ , target-steps₁ ,
      target-value , evol₁ , rel₁
      with sim-paired-cast-values
        (multi-no-source-rebase evol₁ no-rebase) rel₁
        (multi-⊑ᵀ evol₁ q) source-value target-value source-step
  sim-paired-cast-root {B = B} {B′ = B′} {c′ = c′}
      no-rebase prem q source-value source-step
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , V′ , γ₁ , p₁ , target-steps₁ ,
      target-value , evol₁ , rel₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , N′ , γ₂ , r , target-steps₂ , evol₂ , rel₂
      with subst
        (λ T → Σ[ s ∈ _ ⊑ᵀ⟨ γ₂ ⟩ T ] γ₂ CTI.⊢² _ ⊑ N′ ∶ s)
        (applyTys-++ χsᴿ₁ χsᴿ₂ B′) (r , rel₂)
  sim-paired-cast-root {M′ = M′} {c′ = c′}
      no-rebase prem q source-value source-step
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , V′ , γ₁ , p₁ , target-steps₁ ,
      target-value , evol₁ , rel₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , N′ , γ₂ , r , target-steps₂ , evol₂ , rel₂
    | r′ , rel′ =
      Δᴿ₂ , Σᴿ₂ , χsᴿ₁ ++χ χsᴿ₂ , N′ , γ₂ , r′ ,
      (M′ ⟨ c′ ⟩
         —↠+[ χsᴿ₁ ]⟨ cast-↠ c′ target-steps₁ ⟩
       V′ ⟨ applyConsistencies χsᴿ₁ c′ ⟩
         —↠[ χsᴿ₂ ]⟨ target-steps₂ ⟩
       N′ ∎[]) ,
      composeMultiWorldEvolution evol₁ evol₂ , rel′

  sim-source-cast-root : ∀ {Δᴸ Δᴿ Δᴸ′ : TyCtx}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
      {χᴸ : StoreChange Δᴸ Δᴸ′}
      {V : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
      {A B : Ty Δᴸ} {C : Ty Δᴿ}
      {ν : Env∼ Δᴸ} {c : ν ⊢ A ∼ B}
      {p : A ⊑ᵀ⟨ γ ⟩ C}
    → sourceRebaseCountᶜ γ ≡ 0
    → γ CTI.⊢² V ⊑ M′ ∶ p
    → (q : B ⊑ᵀ⟨ γ ⟩ C)
    → Value V
    → V ⟨ c ⟩ —→[ χᴸ ] N
    → Σ[ Δᴿ′ ∈ TyCtx ]
      Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
      Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
      Σ[ r ∈ applyTy χᴸ B ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ C ]
        (M′ —↠[ χsᴿ ] N′)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} (χᴸ ∷ []) χsᴿ
        × (γ′ CTI.⊢² N ⊑ N′ ∶ r)
  sim-source-cast-root {M′ = M′}
      no-rebase prem q source-value source-step
      with catchup-to-more-precise no-rebase prem source-value
  sim-source-cast-root {C = C}
      no-rebase prem q source-value source-step
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , V′ , γ₁ , p₁ , target-steps ,
      target-value , evol₁ , rel₁
      with sim-source-cast-values
        (multi-no-source-rebase evol₁ no-rebase) rel₁
        (multi-⊑ᵀ evol₁ q) source-value target-value source-step
  sim-source-cast-root {C = C}
      no-rebase prem q source-value source-step
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , V′ , γ₁ , p₁ , target-steps ,
      target-value , evol₁ , rel₁
    | γ₂ , r , evol₂ , rel₂
      with subst
        (λ T → Σ[ s ∈ _ ⊑ᵀ⟨ γ₂ ⟩ T ] γ₂ CTI.⊢² _ ⊑ V′ ∶ s)
        (applyTys-++ χsᴿ₁ [] C) (r , rel₂)
  sim-source-cast-root {M′ = M′}
      no-rebase prem q source-value source-step
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , V′ , γ₁ , p₁ , target-steps ,
      target-value , evol₁ , rel₁
    | γ₂ , r , evol₂ , rel₂
    | r′ , rel′ =
      Δᴿ₁ , Σᴿ₁ , χsᴿ₁ ++χ [] , V′ , γ₂ , r′ ,
      (M′
         —↠+[ χsᴿ₁ ]⟨ target-steps ⟩
       V′ ∎[]) ,
      composeMultiWorldEvolution evol₁ evol₂ , rel′

  sim : Simᵀ
  sim no-rebase (CTI.x⊑x² source∋ target∋) (pure-step ())

  sim no-rebase (CTI.ƛ⊑ƛ² prem) (pure-step ())

  sim no-rebase (CTI.·⊑·² fun-rel arg-rel)
      root@(pure-step (β {N = N} argument-value)) =
    sim-paired-fun-closing no-rebase fun-rel arg-rel
      (ƛ N) argument-value root

  sim no-rebase (CTI.·⊑·² fun-rel arg-rel)
      root@(pure-step (β-⇒ source-value argument-value)) =
    sim-paired-fun-closing no-rebase fun-rel arg-rel
      (source-value 《 fun 》) argument-value root

  sim no-rebase (CTI.·⊑·² fun-rel arg-rel)
      root@(pure-step (β-reveal-⇒ source-value argument-value)) =
    sim-paired-fun-closing no-rebase fun-rel arg-rel
      (source-value ↑ fun) argument-value root

  sim no-rebase (CTI.·⊑·² fun-rel arg-rel)
      root@(pure-step (β-conceal-⇒ source-value argument-value)) =
    sim-paired-fun-closing no-rebase fun-rel arg-rel
      (source-value ↓ fun) argument-value root

  sim no-rebase
      (CTI.·⊑·² {L′ = L′} {M′ = M′} {pB = pB}
        fun-rel arg-rel)
      (pure-step blame-·₁) =
    _ , _ , [] , _ , _ , pB ,
    (L′ · M′ ∎[]) , append-left-keep evolutions-refl ,
    CTI.blame⊑² (target-typing (CTI.·⊑·² fun-rel arg-rel)) pB

  sim no-rebase
      (CTI.·⊑·² {L′ = L′} {M′ = M′} {pB = pB}
        fun-rel arg-rel)
      (pure-step (blame-·₂ source-value)) =
    _ , _ , [] , _ , _ , pB ,
    (L′ · M′ ∎[]) , append-left-keep evolutions-refl ,
    CTI.blame⊑² (target-typing (CTI.·⊑·² fun-rel arg-rel)) pB

  sim no-rebase
      (CTI.·⊑·² {A = A} {A′ = A′} {B = B} {B′ = B′}
        {pA = pA} fun-rel arg-rel)
      (ξ-·₁ {χ = χ} fun-step refl)
      with sim no-rebase fun-rel fun-step
  sim no-rebase
      (CTI.·⊑·² {A = A} {A′ = A′} {B = B} {B′ = B′}
        {pA = pA} fun-rel arg-rel)
      (ξ-·₁ {χ = χ} fun-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , fun′ , γ′ , p , target-steps , evol , rel
      with subst
        (λ T →
          Σ[ r ∈ (applyTy χ A ⇒ applyTy χ B) ⊑ᵀ⟨ γ′ ⟩ T ]
            (γ′ CTI.⊢² _ ⊑ fun′ ∶ r))
        (applyTys-⇒ χsᴿ A′ B′)
        (subst
          (λ S →
            Σ[ r ∈ S ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ (A′ ⇒ B′) ]
              (γ′ CTI.⊢² _ ⊑ fun′ ∶ r))
          (applyTy-⇒ χ A B) (p , rel))
  sim no-rebase
      (CTI.·⊑·² {A = A} {A′ = A′} {B = B} {B′ = B′}
        {pA = pA} fun-rel arg-rel)
      (ξ-·₁ {χ = χ} fun-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , fun′ , γ′ , p , target-steps , evol , rel
    | (⇒⊑⇒ qA qB) , rel′ =
      Δᴿ′ , Σᴿ′ , χsᴿ , fun′ · applyTerms χsᴿ _ , γ′ , qB ,
      appL-↠ target-steps , evol ,
      CTI.·⊑·² rel′
        (subst (λ r → γ′ CTI.⊢² _ ⊑ _ ∶ r)
          (PI.⊑-unique (multi-⊑ᵀ evol pA) qA)
          (transport-CTI evol arg-rel))

  sim no-rebase
      (CTI.·⊑·² {L = L} {L′ = L′} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′} fun-rel arg-rel)
      (ξ-·₂ {χ = χ} fun-value arg-step refl)
      with catchup-to-more-precise no-rebase fun-rel fun-value
  sim no-rebase
      (CTI.·⊑·² {L = L} {L′ = L′} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′} fun-rel arg-rel)
      (ξ-·₂ {χ = χ} fun-value arg-step refl)
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , fun′ , γ₁ , q₁ , fun-steps ,
      target-value , evol₁ , fun-rel′
      with sim (multi-no-source-rebase evol₁ no-rebase)
        (transport-CTI evol₁ arg-rel) arg-step
  sim no-rebase
      (CTI.·⊑·² {L = L} {L′ = L′} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′} fun-rel arg-rel)
      (ξ-·₂ {χ = χ} fun-value arg-step refl)
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , fun′ , γ₁ , q₁ , fun-steps ,
      target-value , evol₁ , fun-rel′
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , arg′ , γ₂ , q₂ , arg-steps , evol₂ ,
      arg-rel′
      with subst
        (λ T →
          Σ[ r ∈ (applyTy χ A ⇒ applyTy χ B) ⊑ᵀ⟨ γ₂ ⟩ T ]
            (γ₂ CTI.⊢² applyTerm χ L ⊑ applyTerms χsᴿ₂ fun′ ∶ r))
        (trans
          (cong (applyTys χsᴿ₂) (applyTys-⇒ χsᴿ₁ A′ B′))
          (applyTys-⇒ χsᴿ₂
            (applyTys χsᴿ₁ A′) (applyTys χsᴿ₁ B′)))
        (subst
          (λ S →
            Σ[ r ∈ S ⊑ᵀ⟨ γ₂ ⟩
                applyTys χsᴿ₂ (applyTys χsᴿ₁ (A′ ⇒ B′)) ]
              (γ₂ CTI.⊢² applyTerm χ L ⊑
                applyTerms χsᴿ₂ fun′ ∶ r))
          (applyTy-⇒ χ A B)
          (multi-⊑ᵀ evol₂ q₁ , transport-CTI evol₂ fun-rel′))
  sim no-rebase
      (CTI.·⊑·² {L = L} {L′ = L′} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′} fun-rel arg-rel)
      (ξ-·₂ {χ = χ} fun-value arg-step refl)
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , fun′ , γ₁ , q₁ , fun-steps ,
      target-value , evol₁ , fun-rel′
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , arg′ , γ₂ , q₂ , arg-steps , evol₂ ,
      arg-rel′
    | (⇒⊑⇒ qA qB) , fun-rel″
      with subst
        (λ T →
          Σ[ r ∈ applyTy χ B ⊑ᵀ⟨ γ₂ ⟩ T ]
            (γ₂ CTI.⊢² applyTerm χ L · _ ⊑
              applyTerms χsᴿ₂ fun′ · arg′ ∶ r))
        (applyTys-++ χsᴿ₁ χsᴿ₂ B′)
        (qB , CTI.·⊑·² fun-rel″
          (subst (λ r → γ₂ CTI.⊢² _ ⊑ arg′ ∶ r)
            (PI.⊑-unique q₂ qA) arg-rel′))
  sim no-rebase
      (CTI.·⊑·² {L = L} {L′ = L′} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′} fun-rel arg-rel)
      (ξ-·₂ {χ = χ} fun-value arg-step refl)
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , fun′ , γ₁ , q₁ , fun-steps ,
      target-value , evol₁ , fun-rel′
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , arg′ , γ₂ , q₂ , arg-steps , evol₂ ,
      arg-rel′
    | (⇒⊑⇒ qA qB) , fun-rel″
    | qB′ , app-rel =
      Δᴿ₂ , Σᴿ₂ , χsᴿ₁ ++χ χsᴿ₂ ,
      applyTerms χsᴿ₂ fun′ · arg′ , γ₂ , qB′ ,
      (L′ · M′
         —↠+[ χsᴿ₁ ]⟨ appL-↠ fun-steps ⟩
       fun′ · applyTerms χsᴿ₁ M′
         —↠[ χsᴿ₂ ]⟨ appR-↠ target-value arg-steps ⟩
       applyTerms χsᴿ₂ fun′ · arg′ ∎[]) ,
      composeMultiWorldEvolution evol₁ evol₂ , app-rel

  sim no-rebase (CTI.Λ⊑Λ² source-value target-value prem q)
    (pure-step ())

  sim no-rebase (CTI.Λ⊑² nonvar occurs source-value target⊢ prem q)
    (pure-step ())

  sim no-rebase (CTI.•⊑•² p∀ prem q r)
      root@(pure-step (β-∀ source-value instantiated)) =
    sim-paired-all-closing no-rebase prem q r
      (source-value 《 all 》) root

  sim no-rebase
      (CTI.•⊑•² {M′ = M′} {C′ = C′} {A′ = A′}
        p∀ prem q r)
      (pure-step blame-•) =
    _ , _ , [] , _ , _ , r ,
    ((M′ ⦂∀ C′ [ A′ ]) ∎[]) , append-left-keep evolutions-refl ,
    CTI.blame⊑² (target-typing
      (CTI.•⊑•² p∀ prem q r)) r

  sim no-rebase (CTI.•⊑•² p∀ prem q r)
      root@(β-Λ source-value) =
    sim-paired-all-closing no-rebase prem q r
      (Λ source-value) root

  sim no-rebase (CTI.•⊑•² p∀ prem q r)
      root@(β-gen source-value A≠★ safe) =
    sim-paired-all-closing no-rebase prem q r
      (source-value 《 genᵥ A≠★ safe 》) root

  sim no-rebase (CTI.•⊑•² p∀ prem q r)
      root@(β-reveal-∀ source-value) =
    sim-paired-all-closing no-rebase prem q r
      (source-value ↑ all) root

  sim no-rebase (CTI.•⊑•² p∀ prem q r)
      root@(β-conceal-∀ source-value) =
    sim-paired-all-closing no-rebase prem q r
      (source-value ↓ all) root

  sim no-rebase
      (CTI.•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ prem q r)
      (ξ-• {χ = χ} source-step refl refl)
      with sim no-rebase prem source-step
  sim no-rebase
      (CTI.•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ prem q r)
      (ξ-• {χ = χ} source-step refl refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , p , target-steps , evol , rel
      rewrite applyTy-∀ χ C | applyTys-∀ χsᴿ C′
      with p | rel
  sim no-rebase
      (CTI.•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ prem q r)
      (ξ-• {χ = χ} source-step refl refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , p , target-steps , evol , rel
      | p∀′ | rel′
      with subst
        (λ S →
          Σ[ s ∈ S ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ (C′ [ A′ ]ᵗ) ]
            (γ′ CTI.⊢²
              _ ⦂∀ applyBody χ C [ applyTy χ A ] ⊑
              N′ ⦂∀ applyBodies χsᴿ C′ [ applyTys χsᴿ A′ ] ∶ s))
        (sym (apply-open χ C A))
        (subst
          (λ T →
            Σ[ s ∈
              ((applyBody χ C) [ applyTy χ A ]ᵗ) ⊑ᵀ⟨ γ′ ⟩ T ]
              (γ′ CTI.⊢²
                _ ⦂∀ applyBody χ C [ applyTy χ A ] ⊑
                N′ ⦂∀ applyBodies χsᴿ C′ [ applyTys χsᴿ A′ ] ∶ s))
          (sym (applyTys-open χsᴿ C′ A′))
          ( subst
              (λ T →
                ((applyBody χ C) [ applyTy χ A ]ᵗ) ⊑ᵀ⟨ γ′ ⟩ T)
              (applyTys-open χsᴿ C′ A′)
              (subst
                (λ S → S ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ (C′ [ A′ ]ᵗ))
                (apply-open χ C A) (multi-⊑ᵀ evol r))
          , CTI.•⊑•² p∀′ rel′ (multi-⊑ᵀ evol q)
              (subst
                (λ T →
                  ((applyBody χ C) [ applyTy χ A ]ᵗ) ⊑ᵀ⟨ γ′ ⟩ T)
                (applyTys-open χsᴿ C′ A′)
                (subst
                  (λ S → S ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ (C′ [ A′ ]ᵗ))
                  (apply-open χ C A) (multi-⊑ᵀ evol r)))
          ))
  sim no-rebase
      (CTI.•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ prem q r)
      (ξ-• {χ = χ} source-step refl refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , p , target-steps , evol , rel
      | p∀′ | rel′
      | r′ , type-app-rel =
      Δᴿ′ , Σᴿ′ , χsᴿ ,
      N′ ⦂∀ applyBodies χsᴿ C′ [ applyTys χsᴿ A′ ] ,
      γ′ , r′ , typeApp-↠ target-steps , evol , type-app-rel

  sim no-rebase (CTI.•⊑² p∀ prem q r)
      root@(pure-step (β-∀ source-value instantiated)) =
    sim-source-all-closing no-rebase prem q r
      (source-value 《 all 》) root

  sim no-rebase (CTI.•⊑² {M′ = M′} p∀ prem q r)
      (pure-step blame-•) =
    _ , _ , [] , M′ , _ , r ,
    (M′ ∎[]) , append-left-keep evolutions-refl ,
    CTI.blame⊑² (target-typing (CTI.•⊑² p∀ prem q r)) r

  sim no-rebase (CTI.•⊑² p∀ prem q r)
      root@(β-Λ source-value) =
    sim-source-all-closing no-rebase prem q r
      (Λ source-value) root

  sim no-rebase (CTI.•⊑² p∀ prem q r)
      root@(β-gen source-value A≠★ safe) =
    sim-source-all-closing no-rebase prem q r
      (source-value 《 genᵥ A≠★ safe 》) root

  sim no-rebase (CTI.•⊑² p∀ prem q r)
      root@(β-reveal-∀ source-value) =
    sim-source-all-closing no-rebase prem q r
      (source-value ↑ all) root

  sim no-rebase (CTI.•⊑² p∀ prem q r)
      root@(β-conceal-∀ source-value) =
    sim-source-all-closing no-rebase prem q r
      (source-value ↓ all) root

  sim no-rebase (CTI.•⊑² {C = C} {A = A} {B = B} p∀ prem q r)
      (ξ-• {χ = χ} source-step refl refl)
      with sim no-rebase prem source-step
  sim no-rebase (CTI.•⊑² {C = C} {A = A} {B = B} p∀ prem q r)
      (ξ-• {χ = χ} source-step refl refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , p , target-steps , evol , rel
      rewrite applyTy-∀ χ C
      with p | rel
  sim no-rebase (CTI.•⊑² {C = C} {A = A} {B = B} p∀ prem q r)
      (ξ-• {χ = χ} source-step refl refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , p , target-steps , evol , rel
      | p∀′ | rel′
      with subst
        (λ S →
          Σ[ s ∈ S ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B ]
            (γ′ CTI.⊢²
              _ ⦂∀ applyBody χ C [ applyTy χ A ] ⊑ N′ ∶ s))
        (sym (apply-open χ C A))
        ( subst
            (λ S → S ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B)
            (apply-open χ C A) (multi-⊑ᵀ evol r)
        , CTI.•⊑² p∀′ rel′
            (subst
              (λ T → applyTy χ A ⊑ᵀ⟨ γ′ ⟩ T)
              (applyTys-★ χsᴿ) (multi-⊑ᵀ evol q))
            (subst
              (λ S → S ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B)
              (apply-open χ C A) (multi-⊑ᵀ evol r))
        )
  sim no-rebase (CTI.•⊑² {C = C} {A = A} {B = B} p∀ prem q r)
      (ξ-• {χ = χ} source-step refl refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , p , target-steps , evol , rel
      | p∀′ | rel′
      | r′ , whole-rel =
      Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , r′ ,
      target-steps , evol , whole-rel

  sim no-rebase (CTI.κ⊑κ² constant p) (pure-step ())

  sim no-rebase (CTI.cast⊑cast² c c′ prem q)
      root@(pure-step (β-id source-value)) =
    sim-paired-cast-root no-rebase prem q source-value root

  sim no-rebase (CTI.cast⊑cast² c c′ prem q)
      root@(pure-step (ground source-value unequal)) =
    sim-paired-cast-root no-rebase prem q source-value root

  sim no-rebase (CTI.cast⊑cast² c c′ prem q)
      root@(pure-step (expand source-value unequal)) =
    sim-paired-cast-root no-rebase prem q source-value root

  sim no-rebase (CTI.cast⊑cast² c c′ prem q)
      root@(pure-step (tag-untag source-value)) =
    sim-paired-cast-root no-rebase prem q
      (source-value 《 inj 》) root

  sim no-rebase
      (CTI.cast⊑cast² {M′ = M′} c c′ prem q)
      (pure-step (tag-untag-bad source-value unequal)) =
    _ , _ , [] , _ , _ , q ,
    (M′ ⟨ c′ ⟩ ∎[]) , append-left-keep evolutions-refl ,
    CTI.blame⊑² (target-typing
      (CTI.cast⊑cast² c c′ prem q)) q

  sim no-rebase
      (CTI.cast⊑cast² {M′ = M′} c c′ prem q)
      (pure-step (blame-bot-intro source-value)) =
    _ , _ , [] , _ , _ , q ,
    (M′ ⟨ c′ ⟩ ∎[]) , append-left-keep evolutions-refl ,
    CTI.blame⊑² (target-typing
      (CTI.cast⊑cast² c c′ prem q)) q

  sim no-rebase
      (CTI.cast⊑cast² {M′ = M′} c c′ prem q)
      (pure-step blame-⟨⟩) =
    _ , _ , [] , _ , _ , q ,
    (M′ ⟨ c′ ⟩ ∎[]) , append-left-keep evolutions-refl ,
    CTI.blame⊑² (target-typing
      (CTI.cast⊑cast² c c′ prem q)) q

  sim no-rebase (CTI.cast⊑cast² c c′ prem q)
      root@(β-inst source-value B≠★) =
    sim-paired-cast-root no-rebase prem q source-value root

  sim no-rebase (CTI.cast⊑cast² c c′ prem q)
      (ξ-⟨⟩ {χ = χ} source-step refl)
      with sim no-rebase prem source-step
  sim no-rebase (CTI.cast⊑cast² c c′ prem q)
      (ξ-⟨⟩ {χ = χ} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , r , target-steps , evol , rel =
      Δᴿ′ , Σᴿ′ , χsᴿ ,
      N′ ⟨ applyConsistencies χsᴿ c′ ⟩ , γ′ , multi-⊑ᵀ evol q ,
      cast-↠ c′ target-steps , evol ,
      CTI.cast⊑cast² (applyConsistency χ c)
        (applyConsistencies χsᴿ c′) rel (multi-⊑ᵀ evol q)

  sim no-rebase (CTI.⊑cast² c′ prem q) source-step
      with sim no-rebase prem source-step
  sim no-rebase (CTI.⊑cast² c′ prem q) source-step
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , r , target-steps , evol , rel =
      Δᴿ′ , Σᴿ′ , χsᴿ ,
      N′ ⟨ applyConsistencies χsᴿ c′ ⟩ , γ′ , multi-⊑ᵀ evol q ,
      cast-↠ c′ target-steps , evol ,
      CTI.⊑cast² (applyConsistencies χsᴿ c′) rel (multi-⊑ᵀ evol q)

  sim no-rebase
      (CTI.⊑reveal-identity {c′ = c′} c′⊢ absent prem q)
      source-step
      with sim no-rebase prem source-step
  sim no-rebase
      (CTI.⊑reveal-identity {c′ = c′} c′⊢ absent prem q)
      source-step
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , r , target-steps , evol , rel =
      Δᴿ′ , Σᴿ′ , χsᴿ , N′ ↑ applyReveals χsᴿ c′ ,
      γ′ , multi-⊑ᵀ evol q , reveal-↠ c′ target-steps , evol ,
      CTI.⊑reveal-identity (multi-target-reveal evol c′⊢)
        (trans (multi-target-reveal-position evol c′⊢) absent)
        rel (multi-⊑ᵀ evol q)

  sim no-rebase
      (CTI.⊑conceal-identity {c′ = c′} c′⊢ absent prem q)
      source-step
      with sim no-rebase prem source-step
  sim no-rebase
      (CTI.⊑conceal-identity {c′ = c′} c′⊢ absent prem q)
      source-step
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , r , target-steps , evol , rel =
      Δᴿ′ , Σᴿ′ , χsᴿ , N′ ↓ applyConceals χsᴿ c′ ,
      γ′ , multi-⊑ᵀ evol q , conceal-↠ c′ target-steps , evol ,
      CTI.⊑conceal-identity (multi-target-conceal evol c′⊢)
        (trans (multi-target-conceal-position evol c′⊢) absent)
        rel (multi-⊑ᵀ evol q)

  sim no-rebase (CTI.cast⊑² c prem q)
      root@(pure-step (β-id source-value)) =
    sim-source-cast-root no-rebase prem q source-value root

  sim no-rebase (CTI.cast⊑² c prem q)
      root@(pure-step (ground source-value unequal)) =
    sim-source-cast-root no-rebase prem q source-value root

  sim no-rebase (CTI.cast⊑² c prem q)
      root@(pure-step (expand source-value unequal)) =
    sim-source-cast-root no-rebase prem q source-value root

  sim no-rebase (CTI.cast⊑² c prem q)
      root@(pure-step (tag-untag source-value)) =
    sim-source-cast-root no-rebase prem q
      (source-value 《 inj 》) root

  sim no-rebase (CTI.cast⊑² {M′ = M′} c prem q)
      (pure-step (tag-untag-bad source-value unequal)) =
    _ , _ , [] , M′ , _ , q ,
    (M′ ∎[]) , append-left-keep evolutions-refl ,
    CTI.blame⊑² (target-typing (CTI.cast⊑² c prem q)) q

  sim no-rebase (CTI.cast⊑² {M′ = M′} c prem q)
      (pure-step (blame-bot-intro source-value)) =
    _ , _ , [] , M′ , _ , q ,
    (M′ ∎[]) , append-left-keep evolutions-refl ,
    CTI.blame⊑² (target-typing (CTI.cast⊑² c prem q)) q

  sim no-rebase (CTI.cast⊑² {M′ = M′} c prem q)
      (pure-step blame-⟨⟩) =
    _ , _ , [] , M′ , _ , q ,
    (M′ ∎[]) , append-left-keep evolutions-refl ,
    CTI.blame⊑² (target-typing (CTI.cast⊑² c prem q)) q

  sim no-rebase (CTI.cast⊑² c prem q)
      root@(β-inst source-value B≠★) =
    sim-source-cast-root no-rebase prem q source-value root

  sim no-rebase (CTI.cast⊑² c prem q)
      (ξ-⟨⟩ {χ = χ} source-step refl)
      with sim no-rebase prem source-step
  sim no-rebase (CTI.cast⊑² c prem q)
      (ξ-⟨⟩ {χ = χ} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , r , target-steps , evol , rel =
      Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , multi-⊑ᵀ evol q ,
      target-steps , evol ,
      CTI.cast⊑² (applyConsistency χ c) rel (multi-⊑ᵀ evol q)

  sim no-rebase
      (CTI.reveal⊑-identity {M′ = M′} {p = p}
        c⊢ absent prem q)
      (pure-step (id-reveal source-value)) =
    _ , _ , [] , M′ , _ , q ,
    (M′ ∎[]) , append-left-keep evolutions-refl ,
    subst (λ r → _ CTI.⊢² _ ⊑ M′ ∶ r) (PI.⊑-unique p q) prem

  sim no-rebase
      (CTI.reveal⊑-identity
        (Conv.⊢↑-unseal member) absent prem q)
      (pure-step (conceal-reveal source-value)) =
    ⊥-elim (generator-here≢absent absent)

  sim no-rebase
      (CTI.reveal⊑-identity {M′ = M′} c⊢ absent prem q)
      (pure-step blame-reveal) =
    _ , _ , [] , M′ , _ , q ,
    (M′ ∎[]) , append-left-keep evolutions-refl ,
    CTI.blame⊑² (target-typing
      (CTI.reveal⊑-identity c⊢ absent prem q)) q

  sim no-rebase (CTI.reveal⊑-identity {c = c} c⊢ absent prem q)
      (ξ-reveal {χ = keep} source-step refl)
      with sim no-rebase prem source-step
  sim no-rebase (CTI.reveal⊑-identity {c = c} c⊢ absent prem q)
      (ξ-reveal {χ = keep} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , r , target-steps , evol , rel =
      Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , multi-⊑ᵀ evol q ,
      target-steps , evol ,
      subst
        (λ K → γ′ CTI.⊢² K ⊑ N′ ∶ multi-⊑ᵀ evol q)
        (sym (renamedReveal-term _ c))
        (CTI.reveal⊑-identity (multi-source-reveal evol c⊢)
          (trans (multi-source-reveal-position evol c⊢) absent)
          rel (multi-⊑ᵀ evol q))

  sim no-rebase (CTI.reveal⊑-identity {c = c} c⊢ absent prem q)
      (ξ-reveal {χ = bind A} source-step refl)
      with sim no-rebase prem source-step
  sim no-rebase (CTI.reveal⊑-identity {c = c} c⊢ absent prem q)
      (ξ-reveal {χ = bind A} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , r , target-steps , evol , rel =
      Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , multi-⊑ᵀ evol q ,
      target-steps , evol ,
      CTI.reveal⊑-identity (multi-source-reveal evol c⊢)
        (trans (multi-source-reveal-position evol c⊢) absent)
        rel (multi-⊑ᵀ evol q)

  sim no-rebase
      (CTI.reveal⊑-only²
        (Conv.⊢↑-id-var member X≠Y) present mark free represented prem q)
      (pure-step (id-reveal source-value)) =
    ⊥-elim (present refl)

  sim no-rebase
      (CTI.reveal⊑-only²
        (Conv.⊢↑-id-base member) present mark free represented prem q)
      (pure-step (id-reveal source-value)) =
    ⊥-elim (present refl)

  sim no-rebase
      (CTI.reveal⊑-only²
        (Conv.⊢↑-id-star member) present mark free represented prem q)
      (pure-step (id-reveal source-value)) =
    ⊥-elim (present refl)

  sim no-rebase
      (CTI.reveal⊑-only² c⊢ present mark free represented prem q)
      root@(pure-step (conceal-reveal source-value)) =
    sim-source-reveal-closing no-rebase c⊢ present mark free
      represented prem q (source-value ↓ seal) root

  sim no-rebase
      (CTI.reveal⊑-only² {M′ = M′}
        c⊢ present mark free represented prem q)
      (pure-step blame-reveal) =
    _ , _ , [] , M′ , _ , q ,
    (M′ ∎[]) , append-left-keep evolutions-refl ,
    CTI.blame⊑² (target-typing
      (CTI.reveal⊑-only²
        c⊢ present mark free represented prem q)) q

  sim no-rebase
      (CTI.reveal⊑-only² {c = c}
        c⊢ present mark free represented prem q)
      (ξ-reveal {χ = keep} source-step refl)
      with sim no-rebase prem source-step
  sim no-rebase
      (CTI.reveal⊑-only² {c = c}
        c⊢ present mark free represented prem q)
      (ξ-reveal {χ = keep} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , r , target-steps , evol , rel =
      Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , multi-⊑ᵀ evol q ,
      target-steps , evol ,
      subst
        (λ K → γ′ CTI.⊢² K ⊑ N′ ∶ multi-⊑ᵀ evol q)
        (sym (renamedReveal-term _ c))
        (CTI.reveal⊑-only²
          (multi-source-reveal evol c⊢)
          (λ absent → present
            (trans (sym (multi-source-reveal-position evol c⊢))
              absent))
          (multi-source-mark evol mark)
          (multi-source-disaligned evol free)
          (subst (λ T → _ ⊑ᵀ⟨ γ′ ⟩ T)
            (applyTys-★ χsᴿ) (multi-⊑ᵀ evol represented))
          rel
          (multi-⊑ᵀ evol q))

  sim no-rebase
      (CTI.reveal⊑-only² {c = c}
        c⊢ present mark free represented prem q)
      (ξ-reveal {χ = bind A} source-step refl)
      with sim no-rebase prem source-step
  sim no-rebase
      (CTI.reveal⊑-only² {c = c}
        c⊢ present mark free represented prem q)
      (ξ-reveal {χ = bind A} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , r , target-steps , evol , rel =
      Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , multi-⊑ᵀ evol q ,
      target-steps , evol ,
      CTI.reveal⊑-only²
        (multi-source-reveal evol c⊢)
        (λ absent → present
          (trans (sym (multi-source-reveal-position evol c⊢))
            absent))
        (multi-source-mark evol mark)
        (multi-source-disaligned evol free)
        (subst (λ T → _ ⊑ᵀ⟨ γ′ ⟩ T)
          (applyTys-★ χsᴿ) (multi-⊑ᵀ evol represented))
        rel
        (multi-⊑ᵀ evol q)

  sim no-rebase
      (CTI.conceal⊑-identity {M′ = M′} {p = p}
        c⊢ absent prem q)
      (pure-step (id-conceal source-value)) =
    _ , _ , [] , M′ , _ , q ,
    (M′ ∎[]) , append-left-keep evolutions-refl ,
    subst (λ r → _ CTI.⊢² _ ⊑ M′ ∶ r) (PI.⊑-unique p q) prem

  sim no-rebase
      (CTI.conceal⊑-identity {M′ = M′} c⊢ absent prem q)
      (pure-step blame-conceal) =
    _ , _ , [] , M′ , _ , q ,
    (M′ ∎[]) , append-left-keep evolutions-refl ,
    CTI.blame⊑² (target-typing
      (CTI.conceal⊑-identity c⊢ absent prem q)) q

  sim no-rebase (CTI.conceal⊑-identity {c = c} c⊢ absent prem q)
      (ξ-conceal {χ = keep} source-step refl)
      with sim no-rebase prem source-step
  sim no-rebase (CTI.conceal⊑-identity {c = c} c⊢ absent prem q)
      (ξ-conceal {χ = keep} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , r , target-steps , evol , rel =
      Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , multi-⊑ᵀ evol q ,
      target-steps , evol ,
      subst
        (λ K → γ′ CTI.⊢² K ⊑ N′ ∶ multi-⊑ᵀ evol q)
        (sym (renamedConceal-term _ c))
        (CTI.conceal⊑-identity (multi-source-conceal evol c⊢)
          (trans (multi-source-conceal-position evol c⊢) absent)
          rel (multi-⊑ᵀ evol q))

  sim no-rebase (CTI.conceal⊑-identity {c = c} c⊢ absent prem q)
      (ξ-conceal {χ = bind A} source-step refl)
      with sim no-rebase prem source-step
  sim no-rebase (CTI.conceal⊑-identity {c = c} c⊢ absent prem q)
      (ξ-conceal {χ = bind A} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , r , target-steps , evol , rel =
      Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , multi-⊑ᵀ evol q ,
      target-steps , evol ,
      CTI.conceal⊑-identity (multi-source-conceal evol c⊢)
        (trans (multi-source-conceal-position evol c⊢) absent)
        rel (multi-⊑ᵀ evol q)

  sim no-rebase
      (CTI.conceal⊑-only²
        (Conv.⊢↓-id-var member X≠Y) present mark free represented prem q)
      (pure-step (id-conceal source-value)) =
    ⊥-elim (present refl)

  sim no-rebase
      (CTI.conceal⊑-only²
        (Conv.⊢↓-id-base member) present mark free represented prem q)
      (pure-step (id-conceal source-value)) =
    ⊥-elim (present refl)

  sim no-rebase
      (CTI.conceal⊑-only²
        (Conv.⊢↓-id-star member) present mark free represented prem q)
      (pure-step (id-conceal source-value)) =
    ⊥-elim (present refl)

  sim no-rebase
      (CTI.conceal⊑-only² {M′ = M′}
        c⊢ present mark free represented prem q)
      (pure-step blame-conceal) =
    _ , _ , [] , M′ , _ , q ,
    (M′ ∎[]) , append-left-keep evolutions-refl ,
    CTI.blame⊑² (target-typing
      (CTI.conceal⊑-only²
        c⊢ present mark free represented prem q)) q

  sim no-rebase
      (CTI.conceal⊑-only² {c = c}
        c⊢ present mark free represented prem q)
      (ξ-conceal {χ = keep} source-step refl)
      with sim no-rebase prem source-step
  sim no-rebase
      (CTI.conceal⊑-only² {c = c}
        c⊢ present mark free represented prem q)
      (ξ-conceal {χ = keep} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , r , target-steps , evol , rel =
      Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , multi-⊑ᵀ evol q ,
      target-steps , evol ,
      subst
        (λ K → γ′ CTI.⊢² K ⊑ N′ ∶ multi-⊑ᵀ evol q)
        (sym (renamedConceal-term _ c))
        (CTI.conceal⊑-only²
          (multi-source-conceal evol c⊢)
          (λ absent → present
            (trans (sym (multi-source-conceal-position evol c⊢))
              absent))
          (multi-source-mark evol mark)
          (multi-source-disaligned evol free)
          (subst (λ T → _ ⊑ᵀ⟨ γ′ ⟩ T)
            (applyTys-★ χsᴿ) (multi-⊑ᵀ evol represented))
          rel
          (multi-⊑ᵀ evol q))

  sim no-rebase
      (CTI.conceal⊑-only² {c = c}
        c⊢ present mark free represented prem q)
      (ξ-conceal {χ = bind A} source-step refl)
      with sim no-rebase prem source-step
  sim no-rebase
      (CTI.conceal⊑-only² {c = c}
        c⊢ present mark free represented prem q)
      (ξ-conceal {χ = bind A} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , r , target-steps , evol , rel =
      Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , multi-⊑ᵀ evol q ,
      target-steps , evol ,
      CTI.conceal⊑-only²
        (multi-source-conceal evol c⊢)
        (λ absent → present
          (trans (sym (multi-source-conceal-position evol c⊢))
            absent))
        (multi-source-mark evol mark)
        (multi-source-disaligned evol free)
        (subst (λ T → _ ⊑ᵀ⟨ γ′ ⟩ T)
          (applyTys-★ χsᴿ) (multi-⊑ᵀ evol represented))
        rel
        (multi-⊑ᵀ evol q)

  sim no-rebase
      (CTI.reveal⊑reveal² {M′ = M′} {c′ = c′}
        (Conv.⊢↑-id-var member X≠Y) c′⊢ positions
        aligned represented prem q)
      (pure-step (id-reveal source-value)) =
    _ , _ , [] , M′ ↑ c′ , _ , q ,
    (M′ ↑ c′ ∎[]) , append-left-keep evolutions-refl ,
    CTI.⊑reveal-identity c′⊢ (sym positions) prem q

  sim no-rebase
      (CTI.reveal⊑reveal² {M′ = M′} {c′ = c′}
        (Conv.⊢↑-id-base member) c′⊢ positions
        aligned represented prem q)
      (pure-step (id-reveal source-value)) =
    _ , _ , [] , M′ ↑ c′ , _ , q ,
    (M′ ↑ c′ ∎[]) , append-left-keep evolutions-refl ,
    CTI.⊑reveal-identity c′⊢ (sym positions) prem q

  sim no-rebase
      (CTI.reveal⊑reveal² {M′ = M′} {c′ = c′}
        (Conv.⊢↑-id-star member) c′⊢ positions
        aligned represented prem q)
      (pure-step (id-reveal source-value)) =
    _ , _ , [] , M′ ↑ c′ , _ , q ,
    (M′ ↑ c′ ∎[]) , append-left-keep evolutions-refl ,
    CTI.⊑reveal-identity c′⊢ (sym positions) prem q

  sim no-rebase
      (CTI.reveal⊑reveal² c⊢ c′⊢ positions aligned represented prem q)
      root@(pure-step (conceal-reveal source-value)) =
    sim-paired-reveal-closing no-rebase c⊢ c′⊢ positions aligned
      represented prem q (source-value ↓ seal) root

  sim no-rebase
      (CTI.reveal⊑reveal² {M′ = M′} {c′ = c′}
        c⊢ c′⊢ positions aligned represented prem q)
      (pure-step blame-reveal) =
    _ , _ , [] , _ , _ , q ,
    (M′ ↑ c′ ∎[]) , append-left-keep evolutions-refl ,
    CTI.blame⊑² (target-typing
      (CTI.reveal⊑reveal²
        c⊢ c′⊢ positions aligned represented prem q)) q

  sim no-rebase
      (CTI.reveal⊑reveal² {c = c} {c′ = c′}
        c⊢ c′⊢ positions aligned represented prem q)
      (ξ-reveal {χ = keep} source-step refl)
      with sim no-rebase prem source-step
  sim no-rebase
      (CTI.reveal⊑reveal² {c = c} {c′ = c′}
        c⊢ c′⊢ positions aligned represented prem q)
      (ξ-reveal {χ = keep} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , r , target-steps , evol , rel =
      Δᴿ′ , Σᴿ′ , χsᴿ , N′ ↑ applyReveals χsᴿ c′ , γ′ ,
      multi-⊑ᵀ evol q , reveal-↠ c′ target-steps , evol ,
      subst
        (λ K → γ′ CTI.⊢² K ⊑ N′ ↑ applyReveals χsᴿ c′ ∶
          multi-⊑ᵀ evol q)
        (sym (renamedReveal-term _ c))
        (CTI.reveal⊑reveal²
          (multi-source-reveal evol c⊢)
          (multi-target-reveal evol c′⊢)
          (trans (multi-source-reveal-position evol c⊢)
            (trans positions
              (sym (multi-target-reveal-position evol c′⊢))))
          (multi-aligned evol aligned)
          (multi-⊑ᵀ evol represented)
          rel
          (multi-⊑ᵀ evol q))

  sim no-rebase
      (CTI.reveal⊑reveal² {c = c} {c′ = c′}
        c⊢ c′⊢ positions aligned represented prem q)
      (ξ-reveal {χ = bind A} source-step refl)
      with sim no-rebase prem source-step
  sim no-rebase
      (CTI.reveal⊑reveal² {c = c} {c′ = c′}
        c⊢ c′⊢ positions aligned represented prem q)
      (ξ-reveal {χ = bind A} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , r , target-steps , evol , rel =
      Δᴿ′ , Σᴿ′ , χsᴿ , N′ ↑ applyReveals χsᴿ c′ , γ′ ,
      multi-⊑ᵀ evol q , reveal-↠ c′ target-steps , evol ,
      CTI.reveal⊑reveal²
        (multi-source-reveal evol c⊢)
        (multi-target-reveal evol c′⊢)
        (trans (multi-source-reveal-position evol c⊢)
          (trans positions
            (sym (multi-target-reveal-position evol c′⊢))))
        (multi-aligned evol aligned)
        (multi-⊑ᵀ evol represented)
        rel
        (multi-⊑ᵀ evol q)

  sim no-rebase
      (CTI.conceal⊑conceal² {M′ = M′} {c′ = c′}
        (Conv.⊢↓-id-var member X≠Y) c′⊢ positions
        aligned represented prem q)
      (pure-step (id-conceal source-value)) =
    _ , _ , [] , M′ ↓ c′ , _ , q ,
    (M′ ↓ c′ ∎[]) , append-left-keep evolutions-refl ,
    CTI.⊑conceal-identity c′⊢ (sym positions) prem q

  sim no-rebase
      (CTI.conceal⊑conceal² {M′ = M′} {c′ = c′}
        (Conv.⊢↓-id-base member) c′⊢ positions
        aligned represented prem q)
      (pure-step (id-conceal source-value)) =
    _ , _ , [] , M′ ↓ c′ , _ , q ,
    (M′ ↓ c′ ∎[]) , append-left-keep evolutions-refl ,
    CTI.⊑conceal-identity c′⊢ (sym positions) prem q

  sim no-rebase
      (CTI.conceal⊑conceal² {M′ = M′} {c′ = c′}
        (Conv.⊢↓-id-star member) c′⊢ positions
        aligned represented prem q)
      (pure-step (id-conceal source-value)) =
    _ , _ , [] , M′ ↓ c′ , _ , q ,
    (M′ ↓ c′ ∎[]) , append-left-keep evolutions-refl ,
    CTI.⊑conceal-identity c′⊢ (sym positions) prem q

  sim no-rebase
      (CTI.conceal⊑conceal² {M′ = M′} {c′ = c′}
        c⊢ c′⊢ positions aligned represented prem q)
      (pure-step blame-conceal) =
    _ , _ , [] , _ , _ , q ,
    (M′ ↓ c′ ∎[]) , append-left-keep evolutions-refl ,
    CTI.blame⊑² (target-typing
      (CTI.conceal⊑conceal²
        c⊢ c′⊢ positions aligned represented prem q)) q

  sim no-rebase
      (CTI.conceal⊑conceal² {c = c} {c′ = c′}
        c⊢ c′⊢ positions aligned represented prem q)
      (ξ-conceal {χ = keep} source-step refl)
      with sim no-rebase prem source-step
  sim no-rebase
      (CTI.conceal⊑conceal² {c = c} {c′ = c′}
        c⊢ c′⊢ positions aligned represented prem q)
      (ξ-conceal {χ = keep} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , r , target-steps , evol , rel =
      Δᴿ′ , Σᴿ′ , χsᴿ , N′ ↓ applyConceals χsᴿ c′ , γ′ ,
      multi-⊑ᵀ evol q , conceal-↠ c′ target-steps , evol ,
      subst
        (λ K → γ′ CTI.⊢² K ⊑ N′ ↓ applyConceals χsᴿ c′ ∶
          multi-⊑ᵀ evol q)
        (sym (renamedConceal-term _ c))
        (CTI.conceal⊑conceal²
          (multi-source-conceal evol c⊢)
          (multi-target-conceal evol c′⊢)
          (trans (multi-source-conceal-position evol c⊢)
            (trans positions
              (sym (multi-target-conceal-position evol c′⊢))))
          (multi-aligned evol aligned)
          (multi-⊑ᵀ evol represented)
          rel
          (multi-⊑ᵀ evol q))

  sim no-rebase
      (CTI.conceal⊑conceal² {c = c} {c′ = c′}
        c⊢ c′⊢ positions aligned represented prem q)
      (ξ-conceal {χ = bind A} source-step refl)
      with sim no-rebase prem source-step
  sim no-rebase
      (CTI.conceal⊑conceal² {c = c} {c′ = c′}
        c⊢ c′⊢ positions aligned represented prem q)
      (ξ-conceal {χ = bind A} source-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , N′ , γ′ , r , target-steps , evol , rel =
      Δᴿ′ , Σᴿ′ , χsᴿ , N′ ↓ applyConceals χsᴿ c′ , γ′ ,
      multi-⊑ᵀ evol q , conceal-↠ c′ target-steps , evol ,
      CTI.conceal⊑conceal²
        (multi-source-conceal evol c⊢)
        (multi-target-conceal evol c′⊢)
        (trans (multi-source-conceal-position evol c⊢)
          (trans positions
            (sym (multi-target-conceal-position evol c′⊢))))
        (multi-aligned evol aligned)
        (multi-⊑ᵀ evol represented)
        rel
        (multi-⊑ᵀ evol q)

  sim no-rebase
      (CTI.⊑reveal-rebase² c′⊢ present ok represented prem q)
      source-step =
    sim-target-reveal-rebase-closing no-rebase c′⊢ present ok
      represented prem q source-step

  sim ()
      (CTI.⊑conceal-rebase² c′⊢ present ok represented prem q)
      source-step

  sim no-rebase (CTI.blame⊑² target⊢ p) (pure-step ())

  sim no-rebase (CTI.⊕⊑⊕² op left-rel right-rel r)
      (pure-step (δ-⊕ primitive-step)) =
    sim-primitive-closing no-rebase left-rel right-rel r primitive-step

  sim no-rebase
      (CTI.⊕⊑⊕² op {L′ = L′} {M′ = M′}
        left-rel right-rel r)
      (pure-step blame-⊕₁) =
    _ , _ , [] , _ , _ , r ,
    (L′ ⊕[ op ] M′ ∎[]) , append-left-keep evolutions-refl ,
    CTI.blame⊑² (target-typing
      (CTI.⊕⊑⊕² op left-rel right-rel r)) r

  sim no-rebase
      (CTI.⊕⊑⊕² op {L′ = L′} {M′ = M′}
        left-rel right-rel r)
      (pure-step (blame-⊕₂ source-value)) =
    _ , _ , [] , _ , _ , r ,
    (L′ ⊕[ op ] M′ ∎[]) , append-left-keep evolutions-refl ,
    CTI.blame⊑² (target-typing
      (CTI.⊕⊑⊕² op left-rel right-rel r)) r

  sim no-rebase
      (CTI.⊕⊑⊕² op {L′ = target-left} {M = M} {M′ = M′}
        left-rel right-rel r)
      (ξ-⊕₁ {χ = χ} {L′ = N} left-step refl)
      with sim no-rebase left-rel left-step
  sim no-rebase
      (CTI.⊕⊑⊕² op {L′ = target-left} {M = M} {M′ = M′}
        left-rel right-rel r)
      (ξ-⊕₁ {χ = χ} {L′ = N} left-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , left′ , γ′ , q , target-steps , evol , rel
      with subst
        (λ S →
          Σ[ s ∈ S ⊑ᵀ⟨ γ′ ⟩ primArgTy op ]
            (γ′ CTI.⊢² N ⊑ left′ ∶ s))
        (applyTys-primArgTy (χ ∷ []) op)
        (subst
          (λ T →
            Σ[ s ∈ applyTy χ (primArgTy op) ⊑ᵀ⟨ γ′ ⟩ T ]
              (γ′ CTI.⊢² N ⊑ left′ ∶ s))
          (applyTys-primArgTy χsᴿ op) (q , rel))
        | subst
        (λ S →
          Σ[ s ∈ S ⊑ᵀ⟨ γ′ ⟩ primArgTy op ]
            (γ′ CTI.⊢² applyTerm χ M ⊑ applyTerms χsᴿ M′ ∶ s))
        (applyTys-primArgTy (χ ∷ []) op)
        (subst
          (λ T →
            Σ[ s ∈ applyTy χ (primArgTy op) ⊑ᵀ⟨ γ′ ⟩ T ]
              (γ′ CTI.⊢² applyTerm χ M ⊑ applyTerms χsᴿ M′ ∶ s))
          (applyTys-primArgTy χsᴿ op)
          (multi-⊑ᵀ evol _ , transport-CTI evol right-rel))
  sim no-rebase
      (CTI.⊕⊑⊕² op {L′ = target-left} {M = M} {M′ = M′}
        left-rel right-rel r)
      (ξ-⊕₁ {χ = χ} {L′ = N} left-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , left′ , γ′ , q , target-steps , evol , rel
    | q′ , rel′ | q″ , right-rel′
      with multi-⊑ᵀ evol r
  sim no-rebase
      (CTI.⊕⊑⊕² op {L′ = target-left} {M = M} {M′ = M′}
        left-rel right-rel r)
      (ξ-⊕₁ {χ = χ} {L′ = N} left-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , left′ , γ′ , q , target-steps , evol , rel
    | q′ , rel′ | q″ , right-rel′
    | r′
      with subst
        (λ S → S ⊑ᵀ⟨ γ′ ⟩ primResultTy op)
        (applyTys-primResultTy (χ ∷ []) op)
        (subst
          (λ T → applyTy χ (primResultTy op) ⊑ᵀ⟨ γ′ ⟩ T)
          (applyTys-primResultTy χsᴿ op) r′)
  sim no-rebase
      (CTI.⊕⊑⊕² op {L′ = target-left} {M = M} {M′ = M′}
        left-rel right-rel r)
      (ξ-⊕₁ {χ = χ} {L′ = N} left-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , left′ , γ′ , q , target-steps , evol , rel
    | q′ , rel′ | q″ , right-rel′
    | r′ | r⁺
      with subst
        (λ S →
          Σ[ s ∈ S ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ (primResultTy op) ]
            (γ′ CTI.⊢² N ⊕[ op ] applyTerm χ M ⊑
              left′ ⊕[ op ] applyTerms χsᴿ M′ ∶ s))
        (sym (applyTys-primResultTy (χ ∷ []) op))
        (subst
          (λ T →
            Σ[ s ∈ primResultTy op ⊑ᵀ⟨ γ′ ⟩ T ]
              (γ′ CTI.⊢² N ⊕[ op ] applyTerm χ M ⊑
                left′ ⊕[ op ] applyTerms χsᴿ M′ ∶ s))
          (sym (applyTys-primResultTy χsᴿ op))
          (r⁺ , CTI.⊕⊑⊕² op rel′ right-rel′ r⁺))
  sim no-rebase
      (CTI.⊕⊑⊕² op {L′ = target-left} {M = M} {M′ = M′}
        left-rel right-rel r)
      (ξ-⊕₁ {χ = χ} {L′ = N} left-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , left′ , γ′ , q , target-steps , evol , rel
    | q′ , rel′ | q″ , right-rel′
    | r′ | r⁺
    | r″ , whole-rel =
      Δᴿ′ , Σᴿ′ , χsᴿ , left′ ⊕[ op ] applyTerms χsᴿ M′ ,
      γ′ , r″ , primL-↠ target-steps , evol , whole-rel

  sim no-rebase
      (CTI.⊕⊑⊕² op {L = L} {L′ = L′} {M′ = M′}
        left-rel right-rel r)
      (ξ-⊕₂ {χ = χ} left-value right-step refl)
      with catchup-to-more-precise no-rebase left-rel left-value
  sim no-rebase
      (CTI.⊕⊑⊕² op {L = L} {L′ = L′} {M′ = M′}
        left-rel right-rel r)
      (ξ-⊕₂ {χ = χ} left-value right-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , left′ , γ′ , q , target-steps ,
      target-value , evol₁ , left-rel′
      with sim (multi-no-source-rebase evol₁ no-rebase)
        (transport-CTI evol₁ right-rel) right-step
  sim no-rebase
      (CTI.⊕⊑⊕² op {L = L} {L′ = L′} {M′ = M′}
        left-rel right-rel r)
      (ξ-⊕₂ {χ = χ} left-value right-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , left′ , γ′ , q , target-steps ,
      target-value , evol₁ , left-rel′
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , right′ , γ₂ , q₂ , right-steps , evol₂ ,
      right-rel′
      with subst
        (λ S →
          Σ[ s ∈ S ⊑ᵀ⟨ γ₂ ⟩ primArgTy op ]
            (γ₂ CTI.⊢² applyTerm χ L ⊑
              applyTerms χsᴿ₂ left′ ∶ s))
        (applyTys-primArgTy (χ ∷ []) op)
        (subst
          (λ T →
            Σ[ s ∈ applyTy χ (primArgTy op) ⊑ᵀ⟨ γ₂ ⟩ T ]
              (γ₂ CTI.⊢² applyTerm χ L ⊑
                applyTerms χsᴿ₂ left′ ∶ s))
          (trans (applyTys-++ χsᴿ χsᴿ₂ (primArgTy op))
            (applyTys-primArgTy (χsᴿ ++χ χsᴿ₂) op))
          (multi-⊑ᵀ evol₂ q , transport-CTI evol₂ left-rel′))
        | subst
        (λ S →
          Σ[ s ∈ S ⊑ᵀ⟨ γ₂ ⟩ primArgTy op ]
            (γ₂ CTI.⊢² _ ⊑ right′ ∶ s))
        (applyTys-primArgTy (χ ∷ []) op)
        (subst
          (λ T →
            Σ[ s ∈ applyTy χ (primArgTy op) ⊑ᵀ⟨ γ₂ ⟩ T ]
              (γ₂ CTI.⊢² _ ⊑ right′ ∶ s))
          (trans (applyTys-++ χsᴿ χsᴿ₂ (primArgTy op))
            (applyTys-primArgTy (χsᴿ ++χ χsᴿ₂) op))
          (q₂ , right-rel′))
  sim no-rebase
      (CTI.⊕⊑⊕² op {L = L} {L′ = L′} {M′ = M′}
        left-rel right-rel r)
      (ξ-⊕₂ {χ = χ} left-value right-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , left′ , γ′ , q , target-steps ,
      target-value , evol₁ , left-rel′
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , right′ , γ₂ , q₂ , right-steps , evol₂ ,
      right-rel′
    | qL , left-rel″ | qR , right-rel″
      with subst
        (λ S → S ⊑ᵀ⟨ γ₂ ⟩ primResultTy op)
        (applyTys-primResultTy (χ ∷ []) op)
        (subst
          (λ T → applyTy χ (primResultTy op) ⊑ᵀ⟨ γ₂ ⟩ T)
          (trans (applyTys-++ χsᴿ χsᴿ₂ (primResultTy op))
            (applyTys-primResultTy (χsᴿ ++χ χsᴿ₂) op))
          (multi-⊑ᵀ evol₂ (multi-⊑ᵀ evol₁ r)))
  sim no-rebase
      (CTI.⊕⊑⊕² op {L = L} {L′ = L′} {M′ = M′}
        left-rel right-rel r)
      (ξ-⊕₂ {χ = χ} left-value right-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , left′ , γ′ , q , target-steps ,
      target-value , evol₁ , left-rel′
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , right′ , γ₂ , q₂ , right-steps , evol₂ ,
      right-rel′
    | qL , left-rel″ | qR , right-rel″
    | r₂
      with subst
        (λ S →
          Σ[ s ∈ S ⊑ᵀ⟨ γ₂ ⟩
              applyTys (χsᴿ ++χ χsᴿ₂) (primResultTy op) ]
            (γ₂ CTI.⊢² applyTerm χ L ⊕[ op ] _ ⊑
              applyTerms χsᴿ₂ left′ ⊕[ op ] right′ ∶ s))
        (sym (applyTys-primResultTy (χ ∷ []) op))
        (subst
          (λ T →
            Σ[ s ∈ primResultTy op ⊑ᵀ⟨ γ₂ ⟩ T ]
              (γ₂ CTI.⊢² applyTerm χ L ⊕[ op ] _ ⊑
                applyTerms χsᴿ₂ left′ ⊕[ op ] right′ ∶ s))
          (sym (applyTys-primResultTy (χsᴿ ++χ χsᴿ₂) op))
          (r₂ , CTI.⊕⊑⊕² op left-rel″ right-rel″ r₂))
  sim no-rebase
      (CTI.⊕⊑⊕² op {L = L} {L′ = L′} {M′ = M′}
        left-rel right-rel r)
      (ξ-⊕₂ {χ = χ} left-value right-step refl)
    | Δᴿ′ , Σᴿ′ , χsᴿ , left′ , γ′ , q , target-steps ,
      target-value , evol₁ , left-rel′
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , right′ , γ₂ , q₂ , right-steps , evol₂ ,
      right-rel′
    | qL , left-rel″ | qR , right-rel″
    | r₂
    | r′ , whole-rel =
      Δᴿ₂ , Σᴿ₂ , χsᴿ ++χ χsᴿ₂ ,
      applyTerms χsᴿ₂ left′ ⊕[ op ] right′ , γ₂ , r′ ,
      (L′ ⊕[ op ] M′
         —↠+[ χsᴿ ]⟨ primL-↠ target-steps ⟩
       left′ ⊕[ op ] applyTerms χsᴿ M′
         —↠[ χsᴿ₂ ]⟨ primR-↠ target-value right-steps ⟩
       applyTerms χsᴿ₂ left′ ⊕[ op ] right′ ∎[]) ,
      composeMultiWorldEvolution evol₁ evol₂ , whole-rel
