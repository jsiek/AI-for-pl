module proof.DGG.SimProof where

-- File Charter:
--   * Gives the direct term-imprecision/reduction case skeleton for Simᵀ.
--   * Holds fixed helper interfaces as module parameters across recursion.
--   * Recurses only on immediate term-imprecision premises; any other case
--     analysis or induction belongs in separately compiled helper lemmas.
--   * Is currently a partial proof: square-shaped cases are left as holes
--     until their helper interfaces and transports are fixed.

open import Data.Product using (_×_; _,_; Σ-syntax)
import Data.List as List
open import Relation.Binary.PropositionalEquality using
  (refl; cong; sym; trans)
  renaming (subst to subst≡)

open import Types using (Ty; TyCtx; _⇒_; _[_]ᵗ)
open import Consistency using (Env∼; _⊢_∼_)
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
  ; applyTys-open
  ; appL-↠
  ; appR-↠
  ; cast-↠
  ; typeApp-↠
  )
open import proof.TypeSafety.Preservation using (apply-open)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.Imprecision as PI
open CTI2
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve; evolve-refl; evolve-keepᴸ)
open import proof.DGG.Parked.ParkedWorldLemma using
  (parked-world-closed; transport⊑ᴾ)
open import proof.DGG.Parked.ParkedEvolveCompositionProof using
  (compose-parked-evolve)
open import proof.DGG.Catchup.ValueCatchupRightDef using (_++χ_)
open import proof.DGG.Catchup.ColumnSupportProof using
  (applyTys-++; composeReduction)
open import proof.DGG.SimDef using (Simᵀ)
open import proof.DGG.SimPairedAllClosingDef
  using (SimPairedAllClosingᵀ)
open import proof.DGG.SimPairedCastValuesDef
  using (SimPairedCastValuesᵀ)
open import proof.DGG.SimPairedFunClosingDef
  using (SimPairedFunClosingᵀ)
open import proof.DGG.SimSourceAllClosingDef
  using (SimSourceAllClosingᵀ)
open import proof.DGG.SimSourceCastValuesDef
  using (SimSourceCastValuesᵀ)
open import proof.DGG.TransportTermImprecisionDef
  using (TransportTermImprecisionᴾᵀ)
open import proof.DGG.SimSourceRevealDef using (SimSourceRevealᵀ)
open import proof.DGG.SimTargetRevealDef using (SimTargetRevealᵀ)
open import proof.DGG.SimSourceConcealDef using (SimSourceConcealᵀ)
open import proof.DGG.SimTargetConcealDef using (SimTargetConcealᵀ)
open import proof.DGG.CatchupToMorePreciseDef
  using
    ( CatchupToMorePrecise
    ; boundary-refl
    )

------------------------------------------------------------------------
-- Direct simulation skeleton
------------------------------------------------------------------------

module _
    (sim-paired-fun-closing : SimPairedFunClosingᵀ)
    (sim-paired-all-closing : SimPairedAllClosingᵀ)
    (sim-paired-cast-values : SimPairedCastValuesᵀ)
    (sim-source-all-closing : SimSourceAllClosingᵀ)
    (sim-source-cast-values : SimSourceCastValuesᵀ)
    (tr : TransportTermImprecisionᴾᵀ)
    (src↑ : SimSourceRevealᵀ)
    (tgt↑ : SimTargetRevealᵀ)
    (src↓ : SimSourceConcealᵀ)
    (tgt↓ : SimTargetConcealᵀ)
    (catchup : CatchupToMorePrecise)
  where

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
        M′↠V′ , vV′ , evol₁ , _ , V⊑V′
      with sim-paired-cast-values
        {c′ = applyConsistencies χsᴿ₁ c′}
        (parked-world-closed parked evol₁)
        V⊑V′ (transport⊑ᴾ evol₁ q) vV vV′ Vc→N
  sim-paired-cast-root
      {χᴸ = χᴸ} {N = N} {B = B} {B′ = B′} {c′ = c′}
      parked V⊑M′ q vV Vc→N
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , p₁ , _ ,
        M′↠V′ , vV′ , evol₁ , _ , V⊑V′
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
        M′↠V′ , vV′ , evol₁ , _ , V⊑V′
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
        M′↠V′ , vV′ , evol₁ , _ , V⊑V′
      with sim-source-cast-values
        (parked-world-closed parked evol₁)
        V⊑V′ (transport⊑ᴾ evol₁ q) vV vV′ Vc→N
  sim-source-cast-root
      {χᴸ = χᴸ} {N = N} {B = B} {C = C}
      parked V⊑M′ q vV Vc→N
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , p₁ , _ ,
        M′↠V′ , vV′ , evol₁ , _ , V⊑V′
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
        M′↠V′ , vV′ , evol₁ , _ , V⊑V′
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
        L′↠V′ , vV′ , evol₁ , _ , L⊑V′
      with sim (parked-world-closed parked evol₁)
        (tr evol₁ M⊑M′) M→N
  sim parked
      (·⊑·² {L = L} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        L⊑L′ M⊑M′)
      (ξ-·₂ {χ = χ} {M′ = N} vL M→N refl)
      | Δᴿ₁ , χsᴿ₁ , V′ , Δ₁ , W₁ , _ , _ ,
        boundary-refl , q₁ , _ ,
        L′↠V′ , vV′ , evol₁ , _ , L⊑V′
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
        L′↠V′ , vV′ , evol₁ , _ , L⊑V′
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
        L′↠V′ , vV′ , evol₁ , _ , L⊑V′
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
      rel@(⊑reveal² mono rebase same c′⊢ M⊑M′ q) M→N =
    tgt↑ parked rel M→N

  sim parked
      rel@(⊑conceal² mono rebase same c′⊢ M⊑M′ q) M→N =
    tgt↓ parked rel M→N

  ------------------------------------------------------------------------
  -- Reveal and conceal squares
  ------------------------------------------------------------------------

  sim parked
      rel@(reveal⊑² mono rebase same-[] c⊢ M⊑M′ q)
      step@(pure-step (id-reveal vM)) =
    src↑ parked rel step
  sim parked
      rel@(reveal⊑² mono rebase same-[] c⊢ M⊑M′ q)
      step@(pure-step (conceal-reveal vM)) =
    src↑ parked rel step
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(reveal⊑² mono rebase same c⊢ M⊑M′ q)
      (pure-step blame-reveal) =
    Δᴿ , [] , _ , _ , W , q ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) q
  sim parked
      rel@(reveal⊑² mono rebase same c⊢ M⊑M′ q)
      step@(ξ-reveal M→N refl) =
    src↑ parked rel step

  sim parked
      rel@(conceal⊑² partner mono rebase same-[] c⊢ M⊑M′ q)
      step@(pure-step (id-conceal vM)) =
    src↓ parked rel step
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(conceal⊑² partner mono rebase same c⊢ M⊑M′ q)
      (pure-step blame-conceal) =
    Δᴿ , [] , _ , _ , W , q ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) q
  sim parked
      rel@(conceal⊑² partner mono rebase same c⊢ M⊑M′ q)
      step@(ξ-conceal M→N refl) =
    src↓ parked rel step

  sim parked
      rel@(reveal⊑reveal² mono rebase same-[] c⊢ c′⊢ M⊑M′ q)
      step@(pure-step (id-reveal vM)) =
    src↑ parked rel step
  sim parked
      rel@(reveal⊑reveal² mono rebase same-[] c⊢ c′⊢ M⊑M′ q)
      step@(pure-step (conceal-reveal vM)) =
    src↑ parked rel step
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(reveal⊑reveal² mono rebase same c⊢ c′⊢ M⊑M′ q)
      (pure-step blame-reveal) =
    Δᴿ , [] , _ , _ , W , q ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) q
  sim parked
      rel@(reveal⊑reveal² mono rebase same c⊢ c′⊢ M⊑M′ q)
      step@(ξ-reveal M→N refl) =
    src↑ parked rel step

  sim parked
      rel@(conceal⊑conceal² partner mono rebase same-[] c⊢ c′⊢
        M⊑M′ q) step@(pure-step (id-conceal vM)) =
    src↓ parked rel step
  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(conceal⊑conceal² partner mono rebase same c⊢ c′⊢ M⊑M′ q)
      (pure-step blame-conceal) =
    Δᴿ , [] , _ , _ , W , q ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) q
  sim parked
      rel@(conceal⊑conceal² partner mono rebase same c⊢ c′⊢
        M⊑M′ q) step@(ξ-conceal M→N refl) =
    src↓ parked rel step

  sim
      {Δᴿ = Δᴿ} {W = W} parked
      rel@(packaged-seal-star² partner mono rebase same c⊢ c′⊢
        M⊑M′ sealed q)
      (pure-step blame-conceal) =
    Δᴿ , [] , _ , _ , W , q ,
    (_ ∎[]) ,
    evolve-keepᴸ evolve-refl ,
    blame⊑² (CTI2T.target-typing² rel) q
  sim parked
      rel@(packaged-seal-star² partner mono rebase same c⊢ c′⊢
        M⊑M′ sealed q) step@(ξ-conceal M→N refl) =
    src↓ parked rel step

  ------------------------------------------------------------------------
  -- Primitive-operation squares
  ------------------------------------------------------------------------

  sim parked
      (⊕⊑⊕² op L⊑L′ M⊑M′ r) (pure-step (δ-⊕ δ)) =
    {!!}
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
      (⊕⊑⊕² op L⊑L′ M⊑M′ r) (ξ-⊕₁ L→N refl)
      with sim parked L⊑L′ L→N
  sim parked
      (⊕⊑⊕² op L⊑L′ M⊑M′ r) (ξ-⊕₁ L→N refl)
      | result =
    {!!}
  sim parked
      (⊕⊑⊕² op L⊑L′ M⊑M′ r) (ξ-⊕₂ vL M→N refl)
      with catchup parked boundary-refl L⊑L′ vL
  sim parked
      (⊕⊑⊕² op L⊑L′ M⊑M′ r) (ξ-⊕₂ vL M→N refl)
      | caught-up =
    {!!}
