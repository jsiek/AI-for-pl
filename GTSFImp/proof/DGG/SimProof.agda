module proof.DGG.SimProof where

-- File Charter:
--   * Gives the direct term-imprecision/reduction case skeleton for Simᵀ.
--   * Holds fixed helper interfaces as module parameters across recursion.
--   * Recurses only on immediate term-imprecision premises; any other case
--     analysis or induction belongs in separately compiled helper lemmas.
--   * Performs target catch-up before invoking value-level cast, reveal,
--     conceal, and primitive-operation closing capabilities.
--   * Contains the complete direct proof, delegating non-structural closing
--     arguments to the parameterized simulation capabilities.

open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Empty using (⊥-elim)
import Data.List as List
open import Relation.Binary.PropositionalEquality using
  (refl; cong; sym; trans)
  renaming (subst to subst≡)

open import Types using (Ty; TyCtx; _⇒_; _[_]ᵗ)
open import Consistency using (Env∼; _⊢_∼_)
import Conversion
open import Primitives using (primArgTy; primResultTy)
open import CastTerms
open import Reduction
open import Imprecision using (⇒⊑⇒)
open import proof.Reduction using
  ( applyBodies
  ; applyTy-⇒
  ; applyTy-∀
  ; applyTys-⇒
  ; applyTys-∀
  ; applyTys-★
  ; applyTys-primArgTy
  ; applyTys-primResultTy
  ; applyTys-open
  ; appL-↠
  ; appR-↠
  ; applyTerms-preserves-Value
  ; cast-↠
  ; primL-↠
  ; primR-↠
  ; typeApp-↠
  )
open import proof.TypeSafety.Preservation using (apply-open)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.Imprecision as PI
open import proof.DGG.ConvImp using
  (conv↑-generator∈; conv↓-generator∈)
open CTX
open CTI2
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve; evolve-refl; evolve-keepᴸ)
open import proof.DGG.Parked.ParkedWorldLemma using
  (parked-world-closed; transport⊑ᴾ)
open import proof.DGG.Parked.ParkedEvolveCompositionProof using
  (compose-parked-evolve)
open import proof.Reduction using
  (_++χ_; applyTys-++; composeReduction)
open import proof.DGG.SimDef using (Simᵀ)
open import proof.DGG.SimPairedAllClosingDef
  using (SimPairedAllClosingᵀ)
open import proof.DGG.SimPairedCastValuesDef
  using (SimPairedCastValuesᵀ)
open import proof.DGG.SimPairedFunClosingDef
  using (SimPairedFunClosingᵀ)
open import proof.DGG.SimPrimitiveValuesDef
  using (SimPrimitiveValuesᵀ)
open import proof.DGG.SimSourceAllClosingDef
  using (SimSourceAllClosingᵀ)
open import proof.DGG.SimSourceCastValuesDef
  using (SimSourceCastValuesᵀ)
open import proof.DGG.SimConversionFramesDef
  using (SimConversionFramesᵀ)
open import proof.DGG.SimSourceRevealValuesDef
  using (SimSourceRevealValuesᵀ)
open import proof.DGG.SimPairedRevealValuesDef
  using (SimPairedRevealValuesᵀ)
open import proof.DGG.SimSourceConcealValuesDef
  using (SimSourceConcealValuesᵀ)
open import proof.DGG.SimPairedConcealValuesDef
  using (SimPairedConcealValuesᵀ)
open import proof.DGG.TransportTermImprecisionDef
  using (TransportTermImprecisionᴾᵀ)
open import proof.DGG.CatchupToMorePreciseDef
  using
    ( CatchupToMorePrecise
    ; boundary-refl
    ; boundary-source-reveal
    ; boundary-source-conceal
    ; toTagRebaseAtᴸ
    )

------------------------------------------------------------------------
-- Direct simulation skeleton
------------------------------------------------------------------------

module _
    (sim-paired-fun-closing : SimPairedFunClosingᵀ)
    (sim-paired-all-closing : SimPairedAllClosingᵀ)
    (sim-paired-cast-values : SimPairedCastValuesᵀ)
    (sim-primitive-values : SimPrimitiveValuesᵀ)
    (sim-source-all-closing : SimSourceAllClosingᵀ)
    (sim-source-cast-values : SimSourceCastValuesᵀ)
    (sim-conversion-frames : SimConversionFramesᵀ)
    (sim-source-reveal-values : SimSourceRevealValuesᵀ)
    (sim-paired-reveal-values : SimPairedRevealValuesᵀ)
    (sim-source-conceal-values : SimSourceConcealValuesᵀ)
    (sim-paired-conceal-values : SimPairedConcealValuesᵀ)
    (tr : TransportTermImprecisionᴾᵀ)
    (catchup : CatchupToMorePrecise)
  where

  open SimConversionFramesᵀ sim-conversion-frames

  ------------------------------------------------------------------------
  -- Paired cast-root assembly
  ------------------------------------------------------------------------

  sim-paired-cast-root :
    ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W : World Δᴸ Δᴿ Δ}
      {χᴸ : StoreChange Δᴸ Δᴸ′}
      {V : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
      {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
      {μ : Env∼ Δᴸ} {μ′ : Env∼ Δᴿ}
      {c : μ ⊢ A ∼ B} {c′ : μ′ ⊢ A′ ∼ B′}
      {p : A ⊑ᵂ⟨ W ⟩ A′}
    → ParkedWorld W
    → W ∣ List.[] ⊢² V ⊑ M′ ∶ p
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
    → Value V
    → V ⟨ c ⟩ —→[ χᴸ ] N
    → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
      Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
      Σ[ r ∈ applyTy χᴸ B ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B′ ]
        (M′ ⟨ c′ ⟩ —↠[ χsᴿ ] N′) ×
        ParkedEvolve (χᴸ ∷ Reduction.[]) χsᴿ W W′ ×
        (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ r)
  sim-paired-cast-root parked V⊑M′ q vV Vc→N
      with catchup parked boundary-refl V⊑M′ vV
  sim-paired-cast-root
      {χᴸ = χᴸ} {N = N} {B = B} {B′ = B′} {c′ = c′}
      parked V⊑M′ q vV Vc→N
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , p₁ , _ ,
        M′↠V′ , vV′ , evol₁ , _ , _ , V⊑V′
      with sim-paired-cast-values
        {c′ = applyConsistencies χsᴿ₁ c′}
        (parked-world-closed parked evol₁)
        V⊑V′ (transport⊑ᴾ evol₁ q) vV vV′ Vc→N
  sim-paired-cast-root
      {χᴸ = χᴸ} {N = N} {B = B} {B′ = B′} {c′ = c′}
      parked V⊑M′ q vV Vc→N
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , p₁ , _ ,
        M′↠V′ , vV′ , evol₁ , _ , _ , V⊑V′
      | Δᴿ₂ , χsᴿ₂ , N′ , Δ₂ , W₂ , r ,
        V′c′↠N′ , evol₂ , N⊑N′
      with subst≡
        (λ T →
          Σ[ s ∈ applyTy χᴸ B ⊑ᵂ⟨ W₂ ⟩ T ]
            W₂ ∣ List.[] ⊢² N ⊑ N′ ∶ s)
        (applyTys-++ χsᴿ₁ χsᴿ₂ B′)
        (r , N⊑N′)
  sim-paired-cast-root
      {χᴸ = χᴸ} {N = N} {B = B} {c′ = c′}
      parked V⊑M′ q vV Vc→N
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , p₁ , _ ,
        M′↠V′ , vV′ , evol₁ , _ , _ , V⊑V′
      | Δᴿ₂ , χsᴿ₂ , N′ , Δ₂ , W₂ , r ,
        V′c′↠N′ , evol₂ , N⊑N′
      | r′ , N⊑N′′ =
    Δᴿ₂ , χsᴿ₁ ++χ χsᴿ₂ , N′ , Δ₂ , W₂ , r′ ,
    composeReduction (cast-↠ c′ M′↠V′) V′c′↠N′ ,
    compose-parked-evolve evol₁ evol₂ ,
    N⊑N′′

  ------------------------------------------------------------------------
  -- Source-only cast-root assembly
  ------------------------------------------------------------------------

  sim-source-cast-root :
    ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W : World Δᴸ Δᴿ Δ}
      {χᴸ : StoreChange Δᴸ Δᴸ′}
      {V : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
      {A B : Ty Δᴸ} {C : Ty Δᴿ}
      {μ : Env∼ Δᴸ} {c : μ ⊢ A ∼ B}
      {p : A ⊑ᵂ⟨ W ⟩ C}
    → ParkedWorld W
    → W ∣ List.[] ⊢² V ⊑ M′ ∶ p
    → (q : B ⊑ᵂ⟨ W ⟩ C)
    → Value V
    → V ⟨ c ⟩ —→[ χᴸ ] N
    → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
      Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
      Σ[ r ∈ applyTy χᴸ B ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ C ]
        (M′ —↠[ χsᴿ ] N′) ×
        ParkedEvolve (χᴸ ∷ Reduction.[]) χsᴿ W W′ ×
        (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ r)
  sim-source-cast-root parked V⊑M′ q vV Vc→N
      with catchup parked boundary-refl V⊑M′ vV
  sim-source-cast-root
      {χᴸ = χᴸ} {N = N} {B = B} {C = C}
      parked V⊑M′ q vV Vc→N
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , p₁ , _ ,
        M′↠V′ , vV′ , evol₁ , _ , _ , V⊑V′
      with sim-source-cast-values
        (parked-world-closed parked evol₁)
        V⊑V′ (transport⊑ᴾ evol₁ q) vV vV′ Vc→N
  sim-source-cast-root
      {χᴸ = χᴸ} {N = N} {B = B} {C = C}
      parked V⊑M′ q vV Vc→N
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , p₁ , _ ,
        M′↠V′ , vV′ , evol₁ , _ , _ , V⊑V′
      | Δ₂ , W₂ , r , evol₂ , N⊑V′
      with subst≡
        (λ T →
          Σ[ s ∈ applyTy χᴸ B ⊑ᵂ⟨ W₂ ⟩ T ]
            W₂ ∣ List.[] ⊢² N ⊑ V′ ∶ s)
        (applyTys-++ χsᴿ₁ Reduction.[] C)
        (r , N⊑V′)
  sim-source-cast-root
      {χᴸ = χᴸ} {N = N} {B = B}
      parked V⊑M′ q vV Vc→N
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , p₁ , _ ,
        M′↠V′ , vV′ , evol₁ , _ , _ , V⊑V′
      | Δ₂ , W₂ , r , evol₂ , N⊑V′
      | r′ , N⊑V′′ =
    Δᴿ₁ , χsᴿ₁ ++χ Reduction.[] , V′ , Δ₂ , W₂ , r′ ,
    composeReduction M′↠V′ (V′ ∎[]) ,
    compose-parked-evolve evol₁ evol₂ ,
    N⊑V′′

  sim : Simᵀ

  ------------------------------------------------------------------------
  -- Irreducible source forms
  ------------------------------------------------------------------------

  sim parked
      (x⊑x² x) (pure-step ())
  sim parked
      (ƛ⊑ƛ² rel) (pure-step ())
  sim parked
      (Λ⊑Λ² lift vV vV′ rel q) (pure-step ())
  sim parked
      (Λ⊑² Anv z∈A lift vV M′⊢ rel q) (pure-step ())
  sim parked
      (Λ⊑²-smart-comma Anv z∈A smart lift vV M′⊢ rel q)
      (pure-step ())
  sim parked
      (κ⊑κ² κ p) (pure-step ())
  sim parked
      (blame⊑² M′⊢ p) (pure-step ())

  ------------------------------------------------------------------------
  -- Application squares
  ------------------------------------------------------------------------

  sim parked
      (·⊑·² L⊑L′ V⊑M′) (pure-step (β vV)) =
    sim-paired-fun-closing parked L⊑L′ V⊑M′
      (ƛ _) vV (pure-step (β vV))

  sim parked
      (·⊑·² L⊑L′ M⊑M′) (pure-step (β-⇒ vV vM)) =
    sim-paired-fun-closing parked L⊑L′ M⊑M′
      (vV 《 fun 》) vM (pure-step (β-⇒ vV vM))

  sim parked
      (·⊑·² L⊑L′ M⊑M′) (pure-step (β-reveal-⇒ vV vM)) =
    sim-paired-fun-closing parked L⊑L′ M⊑M′
      (vV ↑ fun) vM (pure-step (β-reveal-⇒ vV vM))

  sim parked
      (·⊑·² L⊑L′ M⊑M′) (pure-step (β-conceal-⇒ vV vM)) =
    sim-paired-fun-closing parked L⊑L′ M⊑M′
      (vV ↓ fun) vM (pure-step (β-conceal-⇒ vV vM))

  sim
      {Δᴿ = Δᴿ} {W = W} {p = p} parked
      rel@(·⊑·² L⊑L′ M⊑M′) (pure-step blame-·₁) =
    Δᴿ , [] , _ , _ , W , p ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) p

  sim
      {Δᴿ = Δᴿ} {W = W} {p = p} parked
      rel@(·⊑·² L⊑L′ M⊑M′) (pure-step (blame-·₂ vL)) =
    Δᴿ , [] , _ , _ , W , p ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) p

  sim parked
      (·⊑·² {M′ = M′} {A = A} {A′ = A′} {B = B} {B′ = B′}
        L⊑L′ M⊑M′)
      (ξ-·₁ {χ = χ} {L′ = N} L→N refl)
      with sim parked L⊑L′ L→N
  sim parked
      (·⊑·² {M′ = M′} {A = A} {A′ = A′} {B = B} {B′ = B′}
        L⊑L′ M⊑M′)
      (ξ-·₁ {χ = χ} {L′ = N} L→N refl)
      | Δᴿ′ , χsᴿ , L₁′ , Δ′ , W′ , q ,
        L′↠L₁′ , evol , L₁⊑L₁′
        with subst≡
          (λ T →
            Σ[ r ∈ (applyTy χ A ⇒ applyTy χ B) ⊑ᵂ⟨ W′ ⟩ T ]
              W′ ∣ List.[] ⊢² N ⊑ L₁′ ∶ r)
          (applyTys-⇒ χsᴿ A′ B′)
          (subst≡
            (λ S →
              Σ[ r ∈ S ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ (A′ ⇒ B′) ]
                W′ ∣ List.[] ⊢² N ⊑ L₁′ ∶ r)
            (applyTy-⇒ χ A B) (q , L₁⊑L₁′))
  sim parked
      (·⊑·² {M′ = M′} {A = A} {A′ = A′} {B = B} {B′ = B′}
        L⊑L′ M⊑M′)
      (ξ-·₁ {χ = χ} {L′ = N} L→N refl)
      | Δᴿ′ , χsᴿ , L₁′ , Δ′ , W′ , q ,
        L′↠L₁′ , evol , L₁⊑L₁′
      | (⇒⊑⇒ qA qB) , L₁⊑L₁′⁺ =
    Δᴿ′ , χsᴿ , L₁′ · applyTerms χsᴿ M′ , Δ′ , W′ , qB ,
    appL-↠ L′↠L₁′ ,
    evol ,
    ·⊑·² L₁⊑L₁′⁺
      (subst≡ (λ r → W′ ∣ List.[] ⊢² _ ⊑ _ ∶ r)
        (PI.⊑-unique _ qA) (tr evol M⊑M′))

  sim parked
      (·⊑·² {L = L} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        L⊑L′ M⊑M′)
      (ξ-·₂ {χ = χ} {M′ = N} vL M→N refl)
      with catchup parked boundary-refl L⊑L′ vL
  sim parked
      (·⊑·² {L = L} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        L⊑L′ M⊑M′)
      (ξ-·₂ {χ = χ} {M′ = N} vL M→N refl)
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , q₁ , _ ,
        L′↠V′ , vV′ , evol₁ , _ , _ , L⊑V′
      with sim (parked-world-closed parked evol₁)
        (tr evol₁ M⊑M′) M→N
  sim parked
      (·⊑·² {L = L} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        L⊑L′ M⊑M′)
      (ξ-·₂ {χ = χ} {M′ = N} vL M→N refl)
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , q₁ , _ ,
        L′↠V′ , vV′ , evol₁ , _ , _ , L⊑V′
      | Δᴿ₂ , χsᴿ₂ , N′ , Δ₂ , W₂ , qN ,
        M₁′↠N′ , evol₂ , N⊑N′
      with subst≡
        (λ T →
          Σ[ r ∈ (applyTy χ A ⇒ applyTy χ B) ⊑ᵂ⟨ W₂ ⟩ T ]
            W₂ ∣ List.[] ⊢²
              applyTerm χ L ⊑ applyTerms χsᴿ₂ V′ ∶ r)
        (trans
          (cong (applyTys χsᴿ₂) (applyTys-⇒ χsᴿ₁ A′ B′))
          (applyTys-⇒ χsᴿ₂
            (applyTys χsᴿ₁ A′) (applyTys χsᴿ₁ B′)))
        (subst≡
          (λ S →
            Σ[ r ∈ S ⊑ᵂ⟨ W₂ ⟩
                applyTys χsᴿ₂ (applyTys χsᴿ₁ (A′ ⇒ B′)) ]
              W₂ ∣ List.[] ⊢²
                applyTerm χ L ⊑ applyTerms χsᴿ₂ V′ ∶ r)
          (applyTy-⇒ χ A B)
          (transport⊑ᴾ evol₂ q₁ , tr evol₂ L⊑V′))
  sim parked
      (·⊑·² {L = L} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        L⊑L′ M⊑M′)
      (ξ-·₂ {χ = χ} {M′ = N} vL M→N refl)
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , q₁ , _ ,
        L′↠V′ , vV′ , evol₁ , _ , _ , L⊑V′
      | Δᴿ₂ , χsᴿ₂ , N′ , Δ₂ , W₂ , qN ,
        M₁′↠N′ , evol₂ , N⊑N′
      | (⇒⊑⇒ qA qB) , L₂⊑V₂′
      with subst≡
        (λ T →
          Σ[ r ∈ applyTy χ B ⊑ᵂ⟨ W₂ ⟩ T ]
            W₂ ∣ List.[] ⊢²
              (applyTerm χ L · N) ⊑
              (applyTerms χsᴿ₂ V′ · N′) ∶ r)
        (applyTys-++ χsᴿ₁ χsᴿ₂ B′)
        (qB ,
          ·⊑·² L₂⊑V₂′
            (subst≡
              (λ r → W₂ ∣ List.[] ⊢² N ⊑ N′ ∶ r)
              (PI.⊑-unique qN qA) N⊑N′))
  sim parked
      (·⊑·² {L = L} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        L⊑L′ M⊑M′)
      (ξ-·₂ {χ = χ} {M′ = N} vL M→N refl)
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , q₁ , _ ,
        L′↠V′ , vV′ , evol₁ , _ , _ , L⊑V′
      | Δᴿ₂ , χsᴿ₂ , N′ , Δ₂ , W₂ , qN ,
        M₁′↠N′ , evol₂ , N⊑N′
      | (⇒⊑⇒ qA qB) , L₂⊑V₂′
      | qB′ , app-rel =
    Δᴿ₂ , χsᴿ₁ ++χ χsᴿ₂ ,
    applyTerms χsᴿ₂ V′ · N′ ,
    Δ₂ , W₂ , qB′ ,
    composeReduction
      (appL-↠ L′↠V′)
      (appR-↠ vV′ M₁′↠N′) ,
    compose-parked-evolve evol₁ evol₂ ,
    app-rel

  ------------------------------------------------------------------------
  -- Type-application squares
  ------------------------------------------------------------------------

  sim parked
      (•⊑•² p∀ M⊑M′ q r) (pure-step (β-∀ vM eq)) =
    sim-paired-all-closing parked M⊑M′ q r
      (vM 《 all 》) (pure-step (β-∀ vM eq))
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(•⊑•² p∀ M⊑M′ q r) (pure-step blame-•) =
    Δᴿ , [] , _ , _ , W , r ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) r
  sim parked
      (•⊑•² p∀ M⊑M′ q r) (β-Λ vM) =
    sim-paired-all-closing parked M⊑M′ q r
      (Λ vM) (β-Λ vM)
  sim parked
      (•⊑•² p∀ M⊑M′ q r) (β-gen vM A≠★ safe) =
    sim-paired-all-closing parked M⊑M′ q r
      (vM 《 genᵥ A≠★ safe 》) (β-gen vM A≠★ safe)
  sim parked
      (•⊑•² p∀ M⊑M′ q r) (β-reveal-∀ vM) =
    sim-paired-all-closing parked M⊑M′ q r
      (vM ↑ all) (β-reveal-∀ vM)
  sim parked
      (•⊑•² p∀ M⊑M′ q r) (β-conceal-∀ vM) =
    sim-paired-all-closing parked M⊑M′ q r
      (vM ↓ all) (β-conceal-∀ vM)
  sim parked
      (•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ M⊑M′ q r)
      (ξ-• {χ = χ} {M′ = N} M→N refl refl)
      with sim parked M⊑M′ M→N
  sim parked
      (•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ M⊑M′ q r)
      (ξ-• {χ = χ} {M′ = N} M→N refl refl)
      | Δᴿ′ , χsᴿ , N′ , Δ′ , W′ , p ,
        M′↠N′ , evol , N⊑N′
      rewrite applyTy-∀ χ C
            | applyTys-∀ χsᴿ C′
      with p | N⊑N′
  sim parked
      (•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ M⊑M′ q r)
      (ξ-• {χ = χ} {M′ = N} M→N refl refl)
      | Δᴿ′ , χsᴿ , N′ , Δ′ , W′ , p ,
        M′↠N′ , evol , N⊑N′
      | p∀⁺ | N⊑N′⁺
      with subst≡
        (λ S →
          Σ[ s ∈ S ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ (C′ [ A′ ]ᵗ) ]
            W′ ∣ List.[] ⊢²
              N ⦂∀ applyBody χ C [ applyTy χ A ] ⊑
              N′ ⦂∀ applyBodies χsᴿ C′ [ applyTys χsᴿ A′ ]
              ∶ s)
        (sym (apply-open χ C A))
        (subst≡
          (λ T →
            Σ[ s ∈
                ((applyBody χ C) [ applyTy χ A ]ᵗ) ⊑ᵂ⟨ W′ ⟩ T ]
              W′ ∣ List.[] ⊢²
                N ⦂∀ applyBody χ C [ applyTy χ A ] ⊑
                N′ ⦂∀ applyBodies χsᴿ C′ [ applyTys χsᴿ A′ ]
                ∶ s)
          (sym (applyTys-open χsᴿ C′ A′))
          ( subst≡
              (λ T →
                ((applyBody χ C) [ applyTy χ A ]ᵗ) ⊑ᵂ⟨ W′ ⟩ T)
              (applyTys-open χsᴿ C′ A′)
              (subst≡
                (λ S →
                  S ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ (C′ [ A′ ]ᵗ))
                (apply-open χ C A) (transport⊑ᴾ evol r))
          , •⊑•² p∀⁺ N⊑N′⁺
              (transport⊑ᴾ evol q)
              (subst≡
                (λ T →
                  ((applyBody χ C) [ applyTy χ A ]ᵗ) ⊑ᵂ⟨ W′ ⟩ T)
                (applyTys-open χsᴿ C′ A′)
                (subst≡
                  (λ S →
                    S ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ (C′ [ A′ ]ᵗ))
                  (apply-open χ C A) (transport⊑ᴾ evol r)))
          ))
  sim parked
      (•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ M⊑M′ q r)
      (ξ-• {χ = χ} {M′ = N} M→N refl refl)
      | Δᴿ′ , χsᴿ , N′ , Δ′ , W′ , p ,
        M′↠N′ , evol , N⊑N′
      | p∀⁺ | N⊑N′⁺
      | r⁺ , whole-rel =
    Δᴿ′ , χsᴿ ,
    N′ ⦂∀ applyBodies χsᴿ C′ [ applyTys χsᴿ A′ ] ,
    Δ′ , W′ , r⁺ ,
    typeApp-↠ M′↠N′ ,
    evol ,
    whole-rel

  sim parked
      (•⊑² p∀ M⊑M′ q r) (pure-step (β-∀ vM eq)) =
    sim-source-all-closing parked M⊑M′ q r
      (vM 《 all 》) (pure-step (β-∀ vM eq))
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(•⊑² p∀ M⊑M′ q r) (pure-step blame-•) =
    Δᴿ , [] , _ , _ , W , r ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) r
  sim parked
      (•⊑² p∀ M⊑M′ q r) (β-Λ vM) =
    sim-source-all-closing parked M⊑M′ q r (Λ vM) (β-Λ vM)
  sim parked
      (•⊑² p∀ M⊑M′ q r) (β-gen vM A≠★ safe) =
    sim-source-all-closing parked M⊑M′ q r
      (vM 《 genᵥ A≠★ safe 》) (β-gen vM A≠★ safe)
  sim parked
      (•⊑² p∀ M⊑M′ q r) (β-reveal-∀ vM) =
    sim-source-all-closing parked M⊑M′ q r
      (vM ↑ all) (β-reveal-∀ vM)
  sim parked
      (•⊑² p∀ M⊑M′ q r) (β-conceal-∀ vM) =
    sim-source-all-closing parked M⊑M′ q r
      (vM ↓ all) (β-conceal-∀ vM)
  sim parked
      (•⊑² {C = C} {A = A} {B = B} p∀ M⊑M′ q r)
      (ξ-• {χ = χ} {M′ = N} M→N refl refl)
      with sim parked M⊑M′ M→N
  sim parked
      (•⊑² {C = C} {A = A} {B = B} p∀ M⊑M′ q r)
      (ξ-• {χ = χ} {M′ = N} M→N refl refl)
      | Δᴿ′ , χsᴿ , N′ , Δ′ , W′ , p ,
        M′↠N′ , evol , N⊑N′
      rewrite applyTy-∀ χ C
      with p | N⊑N′
  sim parked
      (•⊑² {C = C} {A = A} {B = B} p∀ M⊑M′ q r)
      (ξ-• {χ = χ} {M′ = N} M→N refl refl)
      | Δᴿ′ , χsᴿ , N′ , Δ′ , W′ , p ,
        M′↠N′ , evol , N⊑N′
      | p∀⁺ | N⊑N′⁺
      with subst≡
        (λ S →
          Σ[ s ∈ S ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B ]
            W′ ∣ List.[] ⊢²
              N ⦂∀ applyBody χ C [ applyTy χ A ] ⊑ N′ ∶ s)
        (sym (apply-open χ C A))
        ( subst≡
            (λ S → S ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B)
            (apply-open χ C A) (transport⊑ᴾ evol r)
        , •⊑² p∀⁺ N⊑N′⁺
            (subst≡
              (λ T → applyTy χ A ⊑ᵂ⟨ W′ ⟩ T)
              (applyTys-★ χsᴿ) (transport⊑ᴾ evol q))
            (subst≡
              (λ S → S ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B)
              (apply-open χ C A) (transport⊑ᴾ evol r))
        )
  sim parked
      (•⊑² {C = C} {A = A} {B = B} p∀ M⊑M′ q r)
      (ξ-• {χ = χ} {M′ = N} M→N refl refl)
      | Δᴿ′ , χsᴿ , N′ , Δ′ , W′ , p ,
        M′↠N′ , evol , N⊑N′
      | p∀⁺ | N⊑N′⁺
      | r⁺ , whole-rel =
    Δᴿ′ , χsᴿ , N′ , Δ′ , W′ , r⁺ ,
    M′↠N′ ,
    evol ,
    whole-rel

  ------------------------------------------------------------------------
  -- Cast squares
  ------------------------------------------------------------------------

  sim parked
      (cast⊑cast² c c′ M⊑M′ q)
      root@(pure-step (β-id vM)) =
    sim-paired-cast-root {c = c} {c′ = c′}
      parked M⊑M′ q vM root
  sim parked
      (cast⊑cast² c c′ M⊑M′ q)
      root@(pure-step (ground vM A≠G)) =
    sim-paired-cast-root {c = c} {c′ = c′}
      parked M⊑M′ q vM root
  sim parked
      (cast⊑cast² c c′ M⊑M′ q)
      root@(pure-step (expand vM G≠B)) =
    sim-paired-cast-root {c = c} {c′ = c′}
      parked M⊑M′ q vM root
  sim parked
      (cast⊑cast² c c′ M⊑M′ q)
      root@(pure-step (tag-untag vM)) =
    sim-paired-cast-root {c = c} {c′ = c′}
      parked M⊑M′ q (vM 《 inj 》) root
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(cast⊑cast² c c′ M⊑M′ q)
      (pure-step (tag-untag-bad vM G≠H)) =
    Δᴿ , [] , _ , _ , W , q ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) q
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(cast⊑cast² c c′ M⊑M′ q) (pure-step (blame-bot-intro vM)) =
    Δᴿ , [] , _ , _ , W , q ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) q
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(cast⊑cast² c c′ M⊑M′ q) (pure-step blame-⟨⟩) =
    Δᴿ , [] , _ , _ , W , q ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) q
  sim parked
      (cast⊑cast² c c′ M⊑M′ q)
      root@(β-inst vM B≠★) =
    sim-paired-cast-root {c = c} {c′ = c′}
      parked M⊑M′ q vM root
  sim parked
      (cast⊑cast² c c′ M⊑M′ q)
      (ξ-⟨⟩ {χ = χ} M→N refl)
      with sim parked M⊑M′ M→N
  sim parked
      (cast⊑cast² c c′ M⊑M′ q)
      (ξ-⟨⟩ {χ = χ} M→N refl)
      | Δᴿ′ , χsᴿ , N′ , Δ′ , W′ , p ,
        M′↠N′ , evol , N⊑N′ =
    Δᴿ′ , χsᴿ , N′ ⟨ applyConsistencies χsᴿ c′ ⟩ ,
    Δ′ , W′ , transport⊑ᴾ evol q ,
    cast-↠ c′ M′↠N′ ,
    evol ,
    cast⊑cast² (applyConsistency χ c)
      (applyConsistencies χsᴿ c′) N⊑N′ (transport⊑ᴾ evol q)

  sim parked
      (cast⊑² c M⊑M′ q)
      root@(pure-step (β-id vM)) =
    sim-source-cast-root {c = c}
      parked M⊑M′ q vM root
  sim parked
      (cast⊑² c M⊑M′ q)
      root@(pure-step (ground vM A≠G)) =
    sim-source-cast-root {c = c}
      parked M⊑M′ q vM root
  sim parked
      (cast⊑² c M⊑M′ q)
      root@(pure-step (expand vM G≠B)) =
    sim-source-cast-root {c = c}
      parked M⊑M′ q vM root
  sim parked
      (cast⊑² c M⊑M′ q)
      root@(pure-step (tag-untag vM)) =
    sim-source-cast-root {c = c}
      parked M⊑M′ q (vM 《 inj 》) root
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(cast⊑² c M⊑M′ q) (pure-step (tag-untag-bad vM G≠H)) =
    Δᴿ , [] , _ , _ , W , q ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) q
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(cast⊑² c M⊑M′ q) (pure-step (blame-bot-intro vM)) =
    Δᴿ , [] , _ , _ , W , q ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) q
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(cast⊑² c M⊑M′ q) (pure-step blame-⟨⟩) =
    Δᴿ , [] , _ , _ , W , q ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) q
  sim parked
      (cast⊑² c M⊑M′ q)
      root@(β-inst vM B≠★) =
    sim-source-cast-root {c = c}
      parked M⊑M′ q vM root
  sim parked
      (cast⊑² c M⊑M′ q) (ξ-⟨⟩ {χ = χ} M→N refl)
      with sim parked M⊑M′ M→N
  sim parked
      (cast⊑² c M⊑M′ q) (ξ-⟨⟩ {χ = χ} M→N refl)
      | Δᴿ′ , χsᴿ , N′ , Δ′ , W′ , p ,
        M′↠N′ , evol , N⊑N′ =
    Δᴿ′ , χsᴿ , N′ , Δ′ , W′ , transport⊑ᴾ evol q ,
    M′↠N′ ,
    evol ,
    cast⊑² (applyConsistency χ c) N⊑N′ (transport⊑ᴾ evol q)

  ------------------------------------------------------------------------
  -- Target-only wrappers: recurse on the source step
  ------------------------------------------------------------------------

  sim parked
      (⊑cast² c′ M⊑M′ q) M→N
      with sim parked M⊑M′ M→N
  sim parked
      (⊑cast² c′ M⊑M′ q) M→N
      | Δᴿ′ , χsᴿ , N′ , Δ′ , W′ , p ,
        M′↠N′ , evol , N⊑N′ =
    Δᴿ′ , χsᴿ , N′ ⟨ applyConsistencies χsᴿ c′ ⟩ ,
    Δ′ , W′ , transport⊑ᴾ evol q ,
    cast-↠ c′ M′↠N′ ,
    evol ,
    ⊑cast² (applyConsistencies χsᴿ c′)
      N⊑N′ (transport⊑ᴾ evol q)

  sim parked
      rel@(⊑reveal² c′⊢ position≡absent M⊑M′ q) M→N =
    target-reveal-frame parked rel M→N

  sim parked
      rel@(⊑conceal² c′⊢ position≡absent M⊑M′ q) M→N =
    target-conceal-frame parked rel M→N

  ------------------------------------------------------------------------
  -- Reveal and conceal squares
  ------------------------------------------------------------------------

  sim parked
      rel@(reveal⊑-neutral² c⊢@(Conversion.⊢↑-id-var _ _)
        refl M⊑M′ q)
      step@(pure-step (id-reveal vM))
      with catchup parked
        (boundary-source-reveal impEnvMono-refl tag-rebase-idᴸ)
        M⊑M′ vM
  sim parked
      rel@(reveal⊑-neutral² c⊢@(Conversion.⊢↑-id-var _ _)
        refl M⊑M′ q)
      step@(pure-step (id-reveal vM))
      | caught =
    sim-source-reveal-values parked impEnvMono-refl c⊢ rebase-idᴸ
      M⊑M′ q rel vM step caught
  sim parked
      rel@(reveal⊑-neutral² c⊢@(Conversion.⊢↑-id-base _)
        refl M⊑M′ q)
      step@(pure-step (id-reveal vM))
      with catchup parked
        (boundary-source-reveal impEnvMono-refl tag-rebase-idᴸ)
        M⊑M′ vM
  sim parked
      rel@(reveal⊑-neutral² c⊢@(Conversion.⊢↑-id-base _)
        refl M⊑M′ q)
      step@(pure-step (id-reveal vM))
      | caught =
    sim-source-reveal-values parked impEnvMono-refl c⊢ rebase-idᴸ
      M⊑M′ q rel vM step caught
  sim parked
      rel@(reveal⊑-neutral² c⊢@(Conversion.⊢↑-id-star _)
        refl M⊑M′ q)
      step@(pure-step (id-reveal vM))
      with catchup parked
        (boundary-source-reveal impEnvMono-refl tag-rebase-idᴸ)
        M⊑M′ vM
  sim parked
      rel@(reveal⊑-neutral² c⊢@(Conversion.⊢↑-id-star _)
        refl M⊑M′ q)
      step@(pure-step (id-reveal vM))
      | caught =
    sim-source-reveal-values parked impEnvMono-refl c⊢ rebase-idᴸ
      M⊑M′ q rel vM step caught
  sim parked
      (reveal⊑-only² (Conversion.⊢↑-id-var member X≠Y)
        position≢absent mark disaligned represented M⊑M′ q)
      (pure-step (id-reveal vM)) =
    ⊥-elim (position≢absent refl)
  sim parked
      (reveal⊑-only² (Conversion.⊢↑-id-base member)
        position≢absent mark disaligned represented M⊑M′ q)
      (pure-step (id-reveal vM)) =
    ⊥-elim (position≢absent refl)
  sim parked
      (reveal⊑-only² (Conversion.⊢↑-id-star member)
        position≢absent mark disaligned represented M⊑M′ q)
      (pure-step (id-reveal vM)) =
    ⊥-elim (position≢absent refl)
  sim parked
      (reveal⊑² (Conversion.⊢↑-id-var member X≠Y)
        position≢absent target∋ represented mono rebase same M⊑M′ q)
      (pure-step (id-reveal vM)) =
    ⊥-elim (position≢absent refl)
  sim parked
      (reveal⊑² (Conversion.⊢↑-id-base member)
        position≢absent target∋ represented mono rebase same M⊑M′ q)
      (pure-step (id-reveal vM)) =
    ⊥-elim (position≢absent refl)
  sim parked
      (reveal⊑² (Conversion.⊢↑-id-star member)
        position≢absent target∋ represented mono rebase same M⊑M′ q)
      (pure-step (id-reveal vM)) =
    ⊥-elim (position≢absent refl)
  sim parked
      rel@(reveal⊑-only² c⊢@(Conversion.⊢↑-unseal _)
        position≢absent mark disaligned
        represented M⊑M′ q)
      step@(pure-step (conceal-reveal vM))
      with catchup parked
        (boundary-source-reveal impEnvMono-refl
          (tag-rebase-onlyᴸ (conv↑-generator∈ c⊢)
            mark disaligned represented))
        M⊑M′ (vM ↓ seal)
  sim parked
      rel@(reveal⊑-only² c⊢@(Conversion.⊢↑-unseal _)
        position≢absent mark disaligned
        represented M⊑M′ q)
      step@(pure-step (conceal-reveal vM))
      | caught =
    sim-source-reveal-values parked impEnvMono-refl c⊢
      (rebase-onlyᴸ (conv↑-generator∈ c⊢) mark disaligned represented)
      M⊑M′ q rel (vM ↓ seal) step caught
  sim parked
      rel@(reveal⊑² c⊢@(Conversion.⊢↑-unseal _)
        position≢absent target∋ represented mono
        rebase same-[] M⊑M′ q)
      step@(pure-step (conceal-reveal vM))
      with catchup parked
        (boundary-source-reveal mono (tag-rebase-varᴸ rebase))
        M⊑M′ (vM ↓ seal)
  sim parked
      rel@(reveal⊑² c⊢@(Conversion.⊢↑-unseal _)
        position≢absent target∋ represented mono
        rebase same-[] M⊑M′ q)
      step@(pure-step (conceal-reveal vM))
      | caught =
    sim-source-reveal-values parked mono c⊢ (rebase-varᴸ rebase)
      M⊑M′ q rel (vM ↓ seal) step caught
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(reveal⊑-neutral² c⊢ position≡absent M⊑M′ q)
      (pure-step blame-reveal) =
    Δᴿ , [] , _ , _ , W , q ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) q
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(reveal⊑-only² c⊢ position≢absent mark disaligned
        represented M⊑M′ q)
      (pure-step blame-reveal) =
    Δᴿ , [] , _ , _ , W , q ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) q
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(reveal⊑² c⊢ position≢absent target∋ represented mono
        rebase same M⊑M′ q)
      (pure-step blame-reveal) =
    Δᴿ , [] , _ , _ , W , q ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) q
  sim parked
      rel@(reveal⊑-neutral² c⊢ position≡absent M⊑M′ q)
      step@(ξ-reveal M→N refl) =
    source-reveal-frame parked rel step
  sim parked
      rel@(reveal⊑-only² c⊢ position≢absent mark disaligned represented
        M⊑M′ q)
      step@(ξ-reveal M→N refl) =
    source-reveal-frame parked rel step
  sim parked
      rel@(reveal⊑² c⊢ position≢absent target∋ represented mono
        rebase same M⊑M′ q)
      step@(ξ-reveal M→N refl) =
    source-reveal-frame parked rel step

  sim parked
      rel@(conceal⊑-neutral² c⊢@(Conversion.⊢↓-id-var _ _)
        refl M⊑M′ q)
      step@(pure-step (id-conceal vM))
      with catchup parked
        (boundary-source-conceal impEnvMono-refl tag-rebase-idᴸ)
        M⊑M′ vM
  sim parked
      rel@(conceal⊑-neutral² c⊢@(Conversion.⊢↓-id-var _ _)
        refl M⊑M′ q)
      step@(pure-step (id-conceal vM))
      | caught =
    sim-source-conceal-values parked impEnvMono-refl c⊢
      tag-rebase-idᴸ M⊑M′ q vM step caught
  sim parked
      rel@(conceal⊑-neutral² c⊢@(Conversion.⊢↓-id-base _)
        refl M⊑M′ q)
      step@(pure-step (id-conceal vM))
      with catchup parked
        (boundary-source-conceal impEnvMono-refl tag-rebase-idᴸ)
        M⊑M′ vM
  sim parked
      rel@(conceal⊑-neutral² c⊢@(Conversion.⊢↓-id-base _)
        refl M⊑M′ q)
      step@(pure-step (id-conceal vM))
      | caught =
    sim-source-conceal-values parked impEnvMono-refl c⊢
      tag-rebase-idᴸ M⊑M′ q vM step caught
  sim parked
      rel@(conceal⊑-neutral² c⊢@(Conversion.⊢↓-id-star _)
        refl M⊑M′ q)
      step@(pure-step (id-conceal vM))
      with catchup parked
        (boundary-source-conceal impEnvMono-refl tag-rebase-idᴸ)
        M⊑M′ vM
  sim parked
      rel@(conceal⊑-neutral² c⊢@(Conversion.⊢↓-id-star _)
        refl M⊑M′ q)
      step@(pure-step (id-conceal vM))
      | caught =
    sim-source-conceal-values parked impEnvMono-refl c⊢
      tag-rebase-idᴸ M⊑M′ q vM step caught
  sim parked
      (conceal⊑² (Conversion.⊢↓-id-var member X≠Y)
        position≢absent mark disaligned represented M⊑M′ q)
      (pure-step (id-conceal vM)) =
    ⊥-elim (position≢absent refl)
  sim parked
      (conceal⊑² (Conversion.⊢↓-id-base member)
        position≢absent mark disaligned represented M⊑M′ q)
      (pure-step (id-conceal vM)) =
    ⊥-elim (position≢absent refl)
  sim parked
      (conceal⊑² (Conversion.⊢↓-id-star member)
        position≢absent mark disaligned represented M⊑M′ q)
      (pure-step (id-conceal vM)) =
    ⊥-elim (position≢absent refl)
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(conceal⊑-neutral² c⊢ position≡absent M⊑M′ q)
      (pure-step blame-conceal) =
    Δᴿ , [] , _ , _ , W , q ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) q
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(conceal⊑² c⊢ position≢absent mark disaligned represented
        M⊑M′ q)
      (pure-step blame-conceal) =
    Δᴿ , [] , _ , _ , W , q ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) q
  sim parked
      rel@(conceal⊑-neutral² c⊢ position≡absent M⊑M′ q)
      step@(ξ-conceal M→N refl) =
    source-conceal-frame parked rel step
  sim parked
      rel@(conceal⊑² c⊢ position≢absent mark disaligned represented
        M⊑M′ q)
      step@(ξ-conceal M→N refl) =
    source-conceal-frame parked rel step

  sim parked
      (reveal⊑reveal² (Conversion.⊢↑-id-var member X≠Y) c′⊢
        positions position≢absent
        represented mono rebase same-[] M⊑M′ q)
      step@(pure-step (id-reveal vM))
    = ⊥-elim (position≢absent refl)
  sim parked
      (reveal⊑reveal² (Conversion.⊢↑-id-base member) c′⊢
        positions position≢absent represented mono rebase same-[]
        M⊑M′ q)
      step@(pure-step (id-reveal vM)) =
    ⊥-elim (position≢absent refl)
  sim parked
      (reveal⊑reveal² (Conversion.⊢↑-id-star member) c′⊢
        positions position≢absent represented mono rebase same-[]
        M⊑M′ q)
      step@(pure-step (id-reveal vM)) =
    ⊥-elim (position≢absent refl)
  sim parked
      rel@(reveal⊑reveal² c⊢@(Conversion.⊢↑-unseal _) c′⊢
        positions position≢absent
        represented mono rebase same-[] M⊑M′ q)
      step@(pure-step (conceal-reveal vM))
      with catchup parked
        (boundary-source-reveal mono (tag-rebase-varᴸ rebase))
        M⊑M′ (vM ↓ seal)
  sim parked
      rel@(reveal⊑reveal² c⊢@(Conversion.⊢↑-unseal _) c′⊢
        positions position≢absent
        represented mono rebase same-[] M⊑M′ q)
      step@(pure-step (conceal-reveal vM))
      | caught =
    sim-paired-reveal-values parked c⊢ c′⊢ positions position≢absent
      represented mono rebase
      M⊑M′ q (vM ↓ seal) step caught
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(reveal⊑reveal² c⊢ c′⊢ positions position≢absent
        represented mono rebase same M⊑M′ q)
      (pure-step blame-reveal) =
    Δᴿ , [] , _ , _ , W , q ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) q
  sim parked
      rel@(reveal⊑reveal² c⊢ c′⊢ positions position≢absent
        represented mono rebase same M⊑M′ q)
      step@(ξ-reveal M→N refl) =
    source-reveal-frame parked rel step

  sim parked
      (conceal⊑conceal² (Conversion.⊢↓-id-var member X≠Y) c′⊢
        positions position≢absent represented mono rebase same M⊑M′ q)
      (pure-step (id-conceal vM)) =
    ⊥-elim (position≢absent refl)
  sim parked
      (conceal⊑conceal² (Conversion.⊢↓-id-base member) c′⊢
        positions position≢absent represented mono rebase same M⊑M′ q)
      (pure-step (id-conceal vM)) =
    ⊥-elim (position≢absent refl)
  sim parked
      (conceal⊑conceal² (Conversion.⊢↓-id-star member) c′⊢
        positions position≢absent represented mono rebase same M⊑M′ q)
      (pure-step (id-conceal vM)) =
    ⊥-elim (position≢absent refl)
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(conceal⊑conceal² c⊢ c′⊢ positions position≢absent
        represented mono rebase same M⊑M′ q)
      (pure-step blame-conceal) =
    Δᴿ , [] , _ , _ , W , q ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) q
  sim parked
      rel@(conceal⊑conceal² c⊢ c′⊢ positions position≢absent
        represented mono rebase same M⊑M′ q)
      step@(ξ-conceal M→N refl) =
    source-conceal-frame parked rel step

  ------------------------------------------------------------------------
  -- Primitive-operation squares
  ------------------------------------------------------------------------

  sim parked
      (⊕⊑⊕² op L⊑L′ M⊑M′ r)
      (pure-step
        (δ-⊕ {κ = κ} {κ′ = κ′} {κ″ = κ″} δ))
      with catchup parked boundary-refl L⊑L′ ($ κ)
  sim parked
      (⊕⊑⊕² op L⊑L′ M⊑M′ r)
      (pure-step
        (δ-⊕ {κ = κ} {κ′ = κ′} {κ″ = κ″} δ))
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , p₁ , _ ,
        L′↠V′ , vV′ , evol₁ , _ , _ , L⊑V′
      with catchup (parked-world-closed parked evol₁)
        boundary-refl (tr evol₁ M⊑M′) ($ κ′)
  sim parked
      (⊕⊑⊕² op L⊑L′ M⊑M′ r)
      (pure-step
        (δ-⊕ {κ = κ} {κ′ = κ′} {κ″ = κ″} δ))
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , p₁ , _ ,
        L′↠V′ , vV′ , evol₁ , _ , _ , L⊑V′
      | Δᴿ₂ , χsᴿ₂ , U′ , Δ₂ , W₂ , _ , _ ,
        boundary-refl , q₂ , _ ,
        M₁′↠U′ , vU′ , evol₂ , _ , _ , M⊑U′
      with subst≡
        (λ T →
          Σ[ s ∈ primArgTy op ⊑ᵂ⟨ W₂ ⟩ T ]
            W₂ ∣ List.[] ⊢²
              $ κ ⊑ applyTerms χsᴿ₂ V′ ∶ s)
        (trans (applyTys-++ χsᴿ₁ χsᴿ₂ (primArgTy op))
          (applyTys-primArgTy (χsᴿ₁ ++χ χsᴿ₂) op))
        (transport⊑ᴾ evol₂ p₁ , tr evol₂ L⊑V′)
         | subst≡
        (λ T →
          Σ[ s ∈ primArgTy op ⊑ᵂ⟨ W₂ ⟩ T ]
            W₂ ∣ List.[] ⊢² $ κ′ ⊑ U′ ∶ s)
        (trans (applyTys-++ χsᴿ₁ χsᴿ₂ (primArgTy op))
          (applyTys-primArgTy (χsᴿ₁ ++χ χsᴿ₂) op))
        (q₂ , M⊑U′)
  sim parked
      (⊕⊑⊕² op L⊑L′ M⊑M′ r)
      (pure-step
        (δ-⊕ {κ = κ} {κ′ = κ′} {κ″ = κ″} δ))
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , p₁ , _ ,
        L′↠V′ , vV′ , evol₁ , _ , _ , L⊑V′
      | Δᴿ₂ , χsᴿ₂ , U′ , Δ₂ , W₂ , _ , _ ,
        boundary-refl , q₂ , _ ,
        M₁′↠U′ , vU′ , evol₂ , _ , _ , M⊑U′
      | p₂ , L⊑V₂′ | q₂′ , M⊑U′′
      with subst≡
        (λ T → primResultTy op ⊑ᵂ⟨ W₂ ⟩ T)
        (trans (applyTys-++ χsᴿ₁ χsᴿ₂ (primResultTy op))
          (applyTys-primResultTy (χsᴿ₁ ++χ χsᴿ₂) op))
        (transport⊑ᴾ evol₂ (transport⊑ᴾ evol₁ r))
  sim parked
      (⊕⊑⊕² op L⊑L′ M⊑M′ r)
      (pure-step
        (δ-⊕ {κ = κ} {κ′ = κ′} {κ″ = κ″} δ))
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , p₁ , _ ,
        L′↠V′ , vV′ , evol₁ , _ , _ , L⊑V′
      | Δᴿ₂ , χsᴿ₂ , U′ , Δ₂ , W₂ , _ , _ ,
        boundary-refl , q₂ , _ ,
        M₁′↠U′ , vU′ , evol₂ , _ , _ , M⊑U′
      | p₂ , L⊑V₂′ | q₂′ , M⊑U′′
      | r₂
      with sim-primitive-values
        (parked-world-closed (parked-world-closed parked evol₁) evol₂)
        L⊑V₂′ M⊑U′′ r₂
        (applyTerms-preserves-Value χsᴿ₂ vV′) vU′ δ
  sim parked
      (⊕⊑⊕² op L⊑L′ M⊑M′ r)
      (pure-step
        (δ-⊕ {κ = κ} {κ′ = κ′} {κ″ = κ″} δ))
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , p₁ , _ ,
        L′↠V′ , vV′ , evol₁ , _ , _ , L⊑V′
      | Δᴿ₂ , χsᴿ₂ , U′ , Δ₂ , W₂ , _ , _ ,
        boundary-refl , q₂ , _ ,
        M₁′↠U′ , vU′ , evol₂ , _ , _ , M⊑U′
      | p₂ , L⊑V₂′ | q₂′ , M⊑U′′
      | r₂
      | Δᴿ₃ , χsᴿ₃ , N′ , Δ₃ , W₃ , s ,
        VU′↠N′ , evol₃ , result-rel
      with subst≡
        (λ T →
          Σ[ s′ ∈ primResultTy op ⊑ᵂ⟨ W₃ ⟩ T ]
            W₃ ∣ List.[] ⊢² $ κ″ ⊑ N′ ∶ s′)
        (sym (applyTys-primResultTy
          (χsᴿ₁ ++χ (χsᴿ₂ ++χ χsᴿ₃)) op))
        (subst≡
          (λ T →
            Σ[ s′ ∈ primResultTy op ⊑ᵂ⟨ W₃ ⟩ T ]
              W₃ ∣ List.[] ⊢² $ κ″ ⊑ N′ ∶ s′)
          (applyTys-primResultTy χsᴿ₃ op)
          (s , result-rel))
  sim parked
      (⊕⊑⊕² op L⊑L′ M⊑M′ r)
      (pure-step
        (δ-⊕ {κ = κ} {κ′ = κ′} {κ″ = κ″} δ))
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , p₁ , _ ,
        L′↠V′ , vV′ , evol₁ , _ , _ , L⊑V′
      | Δᴿ₂ , χsᴿ₂ , U′ , Δ₂ , W₂ , _ , _ ,
        boundary-refl , q₂ , _ ,
        M₁′↠U′ , vU′ , evol₂ , _ , _ , M⊑U′
      | p₂ , L⊑V₂′ | q₂′ , M⊑U′′
      | r₂
      | Δᴿ₃ , χsᴿ₃ , N′ , Δ₃ , W₃ , s ,
        VU′↠N′ , evol₃ , result-rel
      | s′ , result-rel′ =
    Δᴿ₃ , χsᴿ₁ ++χ (χsᴿ₂ ++χ χsᴿ₃) ,
    N′ , Δ₃ , W₃ , s′ ,
    composeReduction (primL-↠ L′↠V′)
      (composeReduction (primR-↠ vV′ M₁′↠U′) VU′↠N′) ,
    compose-parked-evolve evol₁
      (compose-parked-evolve evol₂ evol₃) ,
    result-rel′
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(⊕⊑⊕² op L⊑L′ M⊑M′ r) (pure-step blame-⊕₁) =
    Δᴿ , [] , _ , _ , W , r ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) r
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(⊕⊑⊕² op L⊑L′ M⊑M′ r) (pure-step (blame-⊕₂ vL)) =
    Δᴿ , [] , _ , _ , W , r ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) r
  sim parked
      (⊕⊑⊕² op {M = M} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₁ {χ = χ} {L′ = N} L→N refl)
      with sim parked L⊑L′ L→N
  sim parked
      (⊕⊑⊕² op {M = M} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₁ {χ = χ} {L′ = N} L→N refl)
      | Δᴿ′ , χsᴿ , N′ , Δ′ , W′ , q ,
        L′↠N′ , evol , N⊑N′
      with subst≡
        (λ S →
          Σ[ s ∈ S ⊑ᵂ⟨ W′ ⟩ primArgTy op ]
            W′ ∣ List.[] ⊢² N ⊑ N′ ∶ s)
        (applyTys-primArgTy (χ ∷ Reduction.[]) op)
        (subst≡
          (λ T →
            Σ[ s ∈ applyTy χ (primArgTy op) ⊑ᵂ⟨ W′ ⟩ T ]
              W′ ∣ List.[] ⊢² N ⊑ N′ ∶ s)
          (applyTys-primArgTy χsᴿ op) (q , N⊑N′))
         | subst≡
        (λ S →
          Σ[ s ∈ S ⊑ᵂ⟨ W′ ⟩ primArgTy op ]
            W′ ∣ List.[] ⊢²
              applyTerm χ M ⊑ applyTerms χsᴿ M′ ∶ s)
        (applyTys-primArgTy (χ ∷ Reduction.[]) op)
        (subst≡
          (λ T →
            Σ[ s ∈ applyTy χ (primArgTy op) ⊑ᵂ⟨ W′ ⟩ T ]
              W′ ∣ List.[] ⊢²
                applyTerm χ M ⊑ applyTerms χsᴿ M′ ∶ s)
          (applyTys-primArgTy χsᴿ op)
          (transport⊑ᴾ evol _ , tr evol M⊑M′))
  sim parked
      (⊕⊑⊕² op {M = M} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₁ {χ = χ} {L′ = N} L→N refl)
      | Δᴿ′ , χsᴿ , N′ , Δ′ , W′ , q ,
        L′↠N′ , evol , N⊑N′
      | q′ , N⊑N′′ | q″ , M⁺⊑M′⁺
      with transport⊑ᴾ evol r
  sim parked
      (⊕⊑⊕² op {M = M} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₁ {χ = χ} {L′ = N} L→N refl)
      | Δᴿ′ , χsᴿ , N′ , Δ′ , W′ , q ,
        L′↠N′ , evol , N⊑N′
      | q′ , N⊑N′′ | q″ , M⁺⊑M′⁺
      | r′
      with subst≡
        (λ S → S ⊑ᵂ⟨ W′ ⟩ primResultTy op)
        (applyTys-primResultTy (χ ∷ Reduction.[]) op)
        (subst≡
          (λ T → applyTy χ (primResultTy op) ⊑ᵂ⟨ W′ ⟩ T)
          (applyTys-primResultTy χsᴿ op) r′)
  sim parked
      (⊕⊑⊕² op {M = M} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₁ {χ = χ} {L′ = N} L→N refl)
      | Δᴿ′ , χsᴿ , N′ , Δ′ , W′ , q ,
        L′↠N′ , evol , N⊑N′
      | q′ , N⊑N′′ | q″ , M⁺⊑M′⁺
      | r′ | r⁺
      with subst≡
        (λ S →
            Σ[ s ∈ S ⊑ᵂ⟨ W′ ⟩
              applyTys χsᴿ (primResultTy op) ]
            W′ ∣ List.[] ⊢²
              N ⊕[ op ] applyTerm χ M ⊑
              N′ ⊕[ op ] applyTerms χsᴿ M′ ∶ s)
        (sym (applyTys-primResultTy (χ ∷ Reduction.[]) op))
        (subst≡
          (λ T →
            Σ[ s ∈ primResultTy op ⊑ᵂ⟨ W′ ⟩ T ]
              W′ ∣ List.[] ⊢²
                N ⊕[ op ] applyTerm χ M ⊑
                N′ ⊕[ op ] applyTerms χsᴿ M′ ∶ s)
          (sym (applyTys-primResultTy χsᴿ op))
          (r⁺ , ⊕⊑⊕² op N⊑N′′ M⁺⊑M′⁺ r⁺))
  sim parked
      (⊕⊑⊕² op {M = M} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₁ {χ = χ} {L′ = N} L→N refl)
      | Δᴿ′ , χsᴿ , N′ , Δ′ , W′ , q ,
        L′↠N′ , evol , N⊑N′
      | q′ , N⊑N′′ | q″ , M⁺⊑M′⁺
      | r′ | r⁺
      | r″ , whole-rel =
    Δᴿ′ , χsᴿ , N′ ⊕[ op ] applyTerms χsᴿ M′ ,
    Δ′ , W′ , r″ ,
    primL-↠ L′↠N′ ,
    evol ,
    whole-rel
  sim parked
      (⊕⊑⊕² op {L = L} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₂ {χ = χ} {M′ = N} vL M→N refl)
      with catchup parked boundary-refl L⊑L′ vL
  sim parked
      (⊕⊑⊕² op {L = L} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₂ {χ = χ} {M′ = N} vL M→N refl)
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , q₁ , _ ,
        L′↠V′ , vV′ , evol₁ , _ , _ , L⊑V′
      with sim (parked-world-closed parked evol₁)
        (tr evol₁ M⊑M′) M→N
  sim parked
      (⊕⊑⊕² op {L = L} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₂ {χ = χ} {M′ = N} vL M→N refl)
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , q₁ , _ ,
        L′↠V′ , vV′ , evol₁ , _ , _ , L⊑V′
      | Δᴿ₂ , χsᴿ₂ , N′ , Δ₂ , W₂ , q₂ ,
        M₁′↠N′ , evol₂ , N⊑N′
      with subst≡
        (λ S →
          Σ[ s ∈ S ⊑ᵂ⟨ W₂ ⟩ primArgTy op ]
            W₂ ∣ List.[] ⊢² N ⊑ N′ ∶ s)
        (applyTys-primArgTy (χ ∷ Reduction.[]) op)
        (subst≡
          (λ T →
            Σ[ s ∈ applyTy χ (primArgTy op) ⊑ᵂ⟨ W₂ ⟩ T ]
              W₂ ∣ List.[] ⊢² N ⊑ N′ ∶ s)
          (trans (applyTys-++ χsᴿ₁ χsᴿ₂ (primArgTy op))
            (applyTys-primArgTy (χsᴿ₁ ++χ χsᴿ₂) op))
          (q₂ , N⊑N′))
         | subst≡
        (λ S →
          Σ[ s ∈ S ⊑ᵂ⟨ W₂ ⟩ primArgTy op ]
            W₂ ∣ List.[] ⊢²
              applyTerm χ L ⊑ applyTerms χsᴿ₂ V′ ∶ s)
        (applyTys-primArgTy (χ ∷ Reduction.[]) op)
        (subst≡
          (λ T →
            Σ[ s ∈ applyTy χ (primArgTy op) ⊑ᵂ⟨ W₂ ⟩ T ]
              W₂ ∣ List.[] ⊢²
                applyTerm χ L ⊑ applyTerms χsᴿ₂ V′ ∶ s)
          (trans (applyTys-++ χsᴿ₁ χsᴿ₂ (primArgTy op))
            (applyTys-primArgTy (χsᴿ₁ ++χ χsᴿ₂) op))
          (transport⊑ᴾ evol₂ q₁ , tr evol₂ L⊑V′))
  sim parked
      (⊕⊑⊕² op {L = L} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₂ {χ = χ} {M′ = N} vL M→N refl)
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , q₁ , _ ,
        L′↠V′ , vV′ , evol₁ , _ , _ , L⊑V′
      | Δᴿ₂ , χsᴿ₂ , N′ , Δ₂ , W₂ , q₂ ,
        M₁′↠N′ , evol₂ , N⊑N′
      | qN , N⊑N′′ | qL , L⁺⊑V′⁺
      with subst≡
        (λ S → S ⊑ᵂ⟨ W₂ ⟩ primResultTy op)
        (applyTys-primResultTy (χ ∷ Reduction.[]) op)
        (subst≡
          (λ T → applyTy χ (primResultTy op) ⊑ᵂ⟨ W₂ ⟩ T)
          (trans (applyTys-++ χsᴿ₁ χsᴿ₂ (primResultTy op))
            (applyTys-primResultTy (χsᴿ₁ ++χ χsᴿ₂) op))
          (transport⊑ᴾ evol₂ (transport⊑ᴾ evol₁ r)))
  sim parked
      (⊕⊑⊕² op {L = L} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₂ {χ = χ} {M′ = N} vL M→N refl)
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , q₁ , _ ,
        L′↠V′ , vV′ , evol₁ , _ , _ , L⊑V′
      | Δᴿ₂ , χsᴿ₂ , N′ , Δ₂ , W₂ , q₂ ,
        M₁′↠N′ , evol₂ , N⊑N′
      | qN , N⊑N′′ | qL , L⁺⊑V′⁺
      | r₂
      with subst≡
        (λ S →
          Σ[ s ∈ S ⊑ᵂ⟨ W₂ ⟩
              applyTys (χsᴿ₁ ++χ χsᴿ₂) (primResultTy op) ]
            W₂ ∣ List.[] ⊢²
              applyTerm χ L ⊕[ op ] N ⊑
              applyTerms χsᴿ₂ V′ ⊕[ op ] N′ ∶ s)
        (sym (applyTys-primResultTy (χ ∷ Reduction.[]) op))
        (subst≡
          (λ T →
            Σ[ s ∈ primResultTy op ⊑ᵂ⟨ W₂ ⟩ T ]
              W₂ ∣ List.[] ⊢²
                applyTerm χ L ⊕[ op ] N ⊑
                applyTerms χsᴿ₂ V′ ⊕[ op ] N′ ∶ s)
          (sym
            (applyTys-primResultTy (χsᴿ₁ ++χ χsᴿ₂) op))
          (r₂ , ⊕⊑⊕² op L⁺⊑V′⁺ N⊑N′′ r₂))
  sim parked
      (⊕⊑⊕² op {L = L} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₂ {χ = χ} {M′ = N} vL M→N refl)
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , q₁ , _ ,
        L′↠V′ , vV′ , evol₁ , _ , _ , L⊑V′
      | Δᴿ₂ , χsᴿ₂ , N′ , Δ₂ , W₂ , q₂ ,
        M₁′↠N′ , evol₂ , N⊑N′
      | qN , N⊑N′′ | qL , L⁺⊑V′⁺
      | r₂
      | r′ , whole-rel =
    Δᴿ₂ , χsᴿ₁ ++χ χsᴿ₂ ,
    applyTerms χsᴿ₂ V′ ⊕[ op ] N′ ,
    Δ₂ , W₂ , r′ ,
    composeReduction
      (primL-↠ L′↠V′)
      (primR-↠ vV′ M₁′↠N′) ,
    compose-parked-evolve evol₁ evol₂ ,
    whole-rel
