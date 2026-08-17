module proof.DGG.SimBackProof where

-- File Charter:
--   * Gives a parameterized top-down case skeleton for SimBackᵀ.
--   * Proves structural backward simulation cases whose target step occurs in
--     an immediate premise under ordinary application, cast, or primitive
--     frames.
--   * Leaves value-closing, target-boundary, and other blocked case families
--     behind an explicit residual simulation parameter documented in notes.

open import Data.Product using (_×_; _,_; Σ-syntax)
import Data.List as List
open import Relation.Binary.PropositionalEquality using
  (refl; sym)
  renaming (subst to subst≡)

open import Types using (TyCtx; _⇒_)
open import Primitives using (primArgTy; primResultTy)
open import CastTerms
open import Reduction
open import Imprecision using (⇒⊑⇒)
open import proof.Reduction using
  ( applyTy-⇒
  ; applyTys-⇒
  ; applyTys-primArgTy
  ; applyTys-primResultTy
  ; appL-↠
  ; cast-↠
  ; primL-↠
  )
import proof.Imprecision as PI
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2
open import proof.DGG.Parked.ParkedWorldLemma using (transport⊑ᴾ)
open import proof.DGG.SimBackDef using (SimBackᵀ)
open import proof.DGG.TransportTermImprecisionDef
  using (TransportTermImprecisionᴾᵀ)


module _
    (sim-back-residual : SimBackᵀ)
    (tr : TransportTermImprecisionᴾᵀ)
  where

  ------------------------------------------------------------------------
  -- Direct backward simulation skeleton
  ------------------------------------------------------------------------

  sim-back : SimBackᵀ

  ------------------------------------------------------------------------
  -- Irreducible target forms
  ------------------------------------------------------------------------

  sim-back parked
      (x⊑x² x) (pure-step ())
  sim-back parked
      (ƛ⊑ƛ² rel) (pure-step ())
  sim-back parked
      (Λ⊑Λ² lift vV vV′ rel q) (pure-step ())
  sim-back parked
      (κ⊑κ² κ p) (pure-step ())

  ------------------------------------------------------------------------
  -- Application squares: target operator step
  ------------------------------------------------------------------------

  sim-back parked
      (·⊑·² {M = M} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        L⊑L′ M⊑M′)
      (ξ-·₁ {χ = χ} {L′ = N′} L′→N′ refl)
      with sim-back parked L⊑L′ L′→N′
  sim-back parked
      (·⊑·² {M = M} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        L⊑L′ M⊑M′)
      (ξ-·₁ {χ = χ} {L′ = N′} L′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , q ,
        L↠N , evol , N⊑N′
      with subst≡
        (λ S →
          Σ[ r ∈ S ⊑ᵂ⟨ W′ ⟩ applyTy χ (A′ ⇒ B′) ]
            W′ ∣ List.[] ⊢² N ⊑ N′ ∶ r)
        (applyTys-⇒ χsᴸ A B)
        (q , N⊑N′)
  sim-back parked
      (·⊑·² {M = M} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        L⊑L′ M⊑M′)
      (ξ-·₁ {χ = χ} {L′ = N′} L′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , q ,
        L↠N , evol , N⊑N′
      | q′ , N⊑N′′
      with subst≡
        (λ T →
          Σ[ r ∈
              (applyTys χsᴸ A ⇒ applyTys χsᴸ B) ⊑ᵂ⟨ W′ ⟩ T ]
            W′ ∣ List.[] ⊢² N ⊑ N′ ∶ r)
        (applyTy-⇒ χ A′ B′)
        (q′ , N⊑N′′)
  sim-back parked
      (·⊑·² {M = M} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        L⊑L′ M⊑M′)
      (ξ-·₁ {χ = χ} {L′ = N′} L′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , q ,
        L↠N , evol , N⊑N′
      | q′ , N⊑N′′
      | (⇒⊑⇒ qA qB) , N⊑N′⁺ =
    Δᴸ′ , χsᴸ , N · applyTerms χsᴸ M , Δ′ , W′ , qB ,
    appL-↠ L↠N ,
    evol ,
    ·⊑·² N⊑N′⁺
      (subst≡ (λ r → W′ ∣ List.[] ⊢² _ ⊑ _ ∶ r)
        (PI.⊑-unique _ qA) (tr evol M⊑M′))

  ------------------------------------------------------------------------
  -- Cast squares: target body step
  ------------------------------------------------------------------------

  sim-back parked
      (cast⊑cast² c c′ M⊑M′ q)
      (ξ-⟨⟩ {χ = χ} M′→N′ refl)
      with sim-back parked M⊑M′ M′→N′
  sim-back parked
      (cast⊑cast² c c′ M⊑M′ q)
      (ξ-⟨⟩ {χ = χ} M′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evol , N⊑N′ =
    Δᴸ′ , χsᴸ , N ⟨ applyConsistencies χsᴸ c ⟩ ,
    Δ′ , W′ , transport⊑ᴾ evol q ,
    cast-↠ c M↠N ,
    evol ,
    cast⊑cast² (applyConsistencies χsᴸ c)
      (applyConsistency χ c′) N⊑N′ (transport⊑ᴾ evol q)

  sim-back parked
      (⊑cast² c′ M⊑M′ q)
      (ξ-⟨⟩ {χ = χ} M′→N′ refl)
      with sim-back parked M⊑M′ M′→N′
  sim-back parked
      (⊑cast² c′ M⊑M′ q)
      (ξ-⟨⟩ {χ = χ} M′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evol , N⊑N′ =
    Δᴸ′ , χsᴸ , N , Δ′ , W′ , transport⊑ᴾ evol q ,
    M↠N ,
    evol ,
    ⊑cast² (applyConsistency χ c′) N⊑N′ (transport⊑ᴾ evol q)

  sim-back parked
      (cast⊑² c M⊑M′ q) M′→N′
      with sim-back parked M⊑M′ M′→N′
  sim-back parked
      (cast⊑² c M⊑M′ q) M′→N′
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evol , N⊑N′ =
    Δᴸ′ , χsᴸ , N ⟨ applyConsistencies χsᴸ c ⟩ ,
    Δ′ , W′ , transport⊑ᴾ evol q ,
    cast-↠ c M↠N ,
    evol ,
    cast⊑² (applyConsistencies χsᴸ c)
      N⊑N′ (transport⊑ᴾ evol q)

  ------------------------------------------------------------------------
  -- Primitive-operation squares: target left operand step
  ------------------------------------------------------------------------

  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₁ {χ = χ} {L′ = N′} L′→N′ refl)
      with sim-back parked L⊑L′ L′→N′
  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₁ {χ = χ} {L′ = N′} L′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        L↠N , evol , N⊑N′
      with subst≡
        (λ S →
          Σ[ s ∈ S ⊑ᵂ⟨ W′ ⟩ applyTy χ (primArgTy op) ]
            W′ ∣ List.[] ⊢² N ⊑ N′ ∶ s)
        (applyTys-primArgTy χsᴸ op)
        (p , N⊑N′)
  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₁ {χ = χ} {L′ = N′} L′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        L↠N , evol , N⊑N′
      | p′ , N⊑N′′
      with subst≡
        (λ T →
          Σ[ s ∈ primArgTy op ⊑ᵂ⟨ W′ ⟩ T ]
            W′ ∣ List.[] ⊢² N ⊑ N′ ∶ s)
        (applyTys-primArgTy (χ ∷ []) op)
        (p′ , N⊑N′′)
  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₁ {χ = χ} {L′ = N′} L′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        L↠N , evol , N⊑N′
      | p′ , N⊑N′′
      | qL , N⊑N′⁺
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
          (transport⊑ᴾ evol _ , tr evol M⊑M′))
  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₁ {χ = χ} {L′ = N′} L′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        L↠N , evol , N⊑N′
      | p′ , N⊑N′′
      | qL , N⊑N′⁺
      | qM , M⊑M′⁺
      with subst≡
        (λ S → S ⊑ᵂ⟨ W′ ⟩ primResultTy op)
        (applyTys-primResultTy χsᴸ op)
        (subst≡
          (λ T → applyTys χsᴸ (primResultTy op) ⊑ᵂ⟨ W′ ⟩ T)
          (applyTys-primResultTy (χ ∷ []) op)
          (transport⊑ᴾ evol r))
  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₁ {χ = χ} {L′ = N′} L′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        L↠N , evol , N⊑N′
      | p′ , N⊑N′′
      | qL , N⊑N′⁺
      | qM , M⊑M′⁺
      | r′
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
          (r′ , ⊕⊑⊕² op N⊑N′⁺ M⊑M′⁺ r′))
  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₁ {χ = χ} {L′ = N′} L′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        L↠N , evol , N⊑N′
      | p′ , N⊑N′′
      | qL , N⊑N′⁺
      | qM , M⊑M′⁺
      | r′
      | r″ , whole-rel =
    Δᴸ′ , χsᴸ , N ⊕[ op ] applyTerms χsᴸ M ,
    Δ′ , W′ , r″ ,
    primL-↠ L↠N ,
    evol ,
    whole-rel

  ------------------------------------------------------------------------
  -- Residual case families
  ------------------------------------------------------------------------

  sim-back parked rel step = sim-back-residual parked rel step
