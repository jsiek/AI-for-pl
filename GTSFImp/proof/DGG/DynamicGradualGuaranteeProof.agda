module proof.DGG.DynamicGradualGuaranteeProof where

-- File Charter:
--   * Proves the closed GTSFImp dynamic gradual guarantee from the
--     multi-step simulation and terminal catch-up interfaces.
--   * Uses completed compilation, parked-world, reduction-composition, and
--     type-safety proofs directly.
--   * Contains no induction; operational inductions remain confined to the
--     parameterized simulation, catch-up, and irreducibility lemmas.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Product using (_×_; _,_; proj₂; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Types using (Ty; TyCtx)
open import TyStore using (store-empty)
open import Imprecision using (idᵐ; _⊢_⊑_)
open import GradualTerms using (GTerm)
open import GradualTermImprecision
  using
    ( _∣_⊢ᴳ_⊑_⦂_⊑_∶_
    ; gradual-term-imprecision-source-typing
    )
open import Compile using (compile)
open import CastTerms using
  (Term; Value; blame; ⟨_,_,_⟩; _⊢_⦂_)
open import Reduction using
  ( StoreChanges
  ; applyTys
  ; _—↠[_]_
  )
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CompilePreservesImprecision2 as CompileMonotone
open import proof.DGG.DynamicGradualGuaranteeDef
  using
    ( Convergesᶜ
    ; Divergesᶜ
    ; DivergeOrBlameᶜ
    ; GradualDGG
    ; compiled-left
    ; compiled-right
    )
open import proof.DGG.SimDef using (Sim*ᵀ)
open import proof.DGG.SimBackDef using (SimBack*ᵀ)
open import proof.DGG.CatchupDef using (CatchupToLessPrecise)
open import proof.DGG.CatchupToMorePreciseDef
  using (CatchupToMorePrecise)
open import proof.DGG.TargetBlameCatchupDef
  using (TargetBlameCatchupᵀ)
open import proof.Reduction.ValueIrreducibleDef
  using (ValueTraceRefl; value-trace-refl; ValueIrreducible*ᵀ)
open import proof.Reduction.BlameIrreducibleDef
  using (BlameTraceRefl; blame-trace-refl; BlameIrreducible*ᵀ)
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; parked-initial)
open import proof.DGG.Parked.ParkedWorldLemma
  using (parked-world-closed)
open import proof.DGG.Catchup.ValueCatchupRightDef using (_++χ_)
open import proof.DGG.Catchup.ColumnSupportProof
  using (applyTys-++; composeReduction)
open import proof.TypeSafety.Progress using
  (Progress; done; step; crash; progress)
open import proof.TypeSafety.Preservation using (multi-preservation)
open CTI2 using (World; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Equality transport for terminal related terms
------------------------------------------------------------------------

transport-related-source : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
  → A ≡ A′
  → (Σ[ p ∈ A ⊑ᵂ⟨ W ⟩ B ] (W ∣ [] ⊢² M ⊑ M′ ∶ p))
  → Σ[ q ∈ A′ ⊑ᵂ⟨ W ⟩ B ] (W ∣ [] ⊢² M ⊑ M′ ∶ q)
transport-related-source refl related = related


transport-related-target : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
  → B ≡ B′
  → (Σ[ p ∈ A ⊑ᵂ⟨ W ⟩ B ] (W ∣ [] ⊢² M ⊑ M′ ∶ p))
  → Σ[ q ∈ A ⊑ᵂ⟨ W ⟩ B′ ] (W ∣ [] ⊢² M ⊑ M′ ∶ q)
transport-related-target refl related = related

------------------------------------------------------------------------
-- Dynamic gradual guarantee
------------------------------------------------------------------------

dynamic-gradual-guarantee :
    Sim*ᵀ
  → SimBack*ᵀ
  → CatchupToLessPrecise
  → CatchupToMorePrecise
  → TargetBlameCatchupᵀ
  → ValueIrreducible*ᵀ
  → BlameIrreducible*ᵀ
  → GradualDGG
dynamic-gradual-guarantee sim* sim-back* catchup catchup-to-more-precise
    target-blame-catchup value-irreducible* blame-irreducible*
    {A = A} {B = B} {p = p} M⊑M′ =
  source-value , source-diverges , target-value , target-diverges
  where
  initial-parked : ParkedWorld
      (CompileMonotone.initialWorld idᵐ store-empty)
  initial-parked = parked-initial

  initial-related :
    CompileMonotone.initialWorld idᵐ store-empty ∣ [] ⊢²
      compiled-left M⊑M′ ⊑ compiled-right M⊑M′
        ∶ CompileMonotone.initial-⊑ {Σ = store-empty} p
  initial-related =
    CompileMonotone.compile-preserves-imprecision² M⊑M′

  source-value : ∀ {Δᴸ} (V : Term Δᴸ)
      (χsᴸ : StoreChanges 0 Δᴸ)
    → compiled-left M⊑M′ —↠[ χsᴸ ] V
    → Value V
    → ∃[ Δᴿ ] (Σ[ χsᴿ ∈ StoreChanges 0 Δᴿ ]
      (∃[ V′ ] (∃[ Δ ] (Σ[ W ∈ World Δᴸ Δᴿ Δ ]
        (Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W ⟩ applyTys χsᴿ B ]
          ((compiled-right M⊑M′ —↠[ χsᴿ ] V′) ×
           Value V′ ×
           (W ∣ [] ⊢² V ⊑ V′ ∶ q)))))))
  source-value {Δᴸ} V χsᴸ M↠V vV
      with sim* initial-parked initial-related M↠V
  source-value {Δᴸ} V χsᴸ M↠V vV
      | Δᴿ₁ , χsᴿ₁ , N′ , Δ₁ , W₁ , q₁ , M′↠N′ ,
        evol₁ , V⊑N′
      with catchup-to-more-precise
        (parked-world-closed initial-parked evol₁) V⊑N′ vV
  source-value {Δᴸ} V χsᴸ M↠V vV
      | Δᴿ₁ , χsᴿ₁ , N′ , Δ₁ , W₁ , q₁ , M′↠N′ ,
        evol₁ , V⊑N′
      | Δᴿ₂ , ψsᴿ , V′ , Δ₂ , W₂ , q₂ , N′↠V′ , vV′ ,
        evol₂ , V⊑V′
      with transport-related-target
        (applyTys-++ χsᴿ₁ ψsᴿ _) (q₂ , V⊑V′)
  source-value {Δᴸ} V χsᴸ M↠V vV
      | Δᴿ₁ , χsᴿ₁ , N′ , Δ₁ , W₁ , q₁ , M′↠N′ ,
        evol₁ , V⊑N′
      | Δᴿ₂ , ψsᴿ , V′ , Δ₂ , W₂ , q₂ , N′↠V′ , vV′ ,
        evol₂ , V⊑V′
      | q , V⊑V′′ =
    Δᴿ₂ , (χsᴿ₁ ++χ ψsᴿ) , V′ , Δ₂ , W₂ , q ,
    composeReduction M′↠N′ N′↠V′ , vV′ , V⊑V′′

  target-value : ∀ {Δᴿ} (V′ : Term Δᴿ)
      (χsᴿ : StoreChanges 0 Δᴿ)
    → compiled-right M⊑M′ —↠[ χsᴿ ] V′
    → Value V′
    → (∃[ Δᴸ ] (Σ[ χsᴸ ∈ StoreChanges 0 Δᴸ ]
        (∃[ V ] (∃[ Δ ] (Σ[ W ∈ World Δᴸ Δᴿ Δ ]
          (Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W ⟩ applyTys χsᴿ B ]
            ((compiled-left M⊑M′ —↠[ χsᴸ ] V) ×
             Value V ×
             (W ∣ [] ⊢² V ⊑ V′ ∶ q))))))))
      ⊎ (∃[ Δᴸ ] (Σ[ χsᴸ ∈ StoreChanges 0 Δᴸ ]
          (compiled-left M⊑M′ —↠[ χsᴸ ] blame)))
  target-value {Δᴿ} V′ χsᴿ M′↠V′ vV′
      with sim-back* initial-parked initial-related M′↠V′
  target-value {Δᴿ} V′ χsᴿ M′↠V′ vV′
      | Δᴸ₁ , χsᴸ₁ , N , Δᴿ₂ , ψsᴿ , N₂′ , Δ₁ , W₁ ,
        q₁ , M↠N , V′↠N₂′ , evol₁ , N⊑N₂′
      with value-irreducible* vV′ V′↠N₂′
  target-value {Δᴿ} V′ χsᴿ M′↠V′ vV′
      | Δᴸ₁ , χsᴸ₁ , N , .Δᴿ , .Reduction.[] , .V′ , Δ₁ ,
        W₁ , q₁ , M↠N , V′↠N₂′ , evol₁ , N⊑N₂′
      | value-trace-refl
      with catchup
        (parked-world-closed initial-parked evol₁) N⊑N₂′ vV′
  target-value {Δᴿ} V′ χsᴿ M′↠V′ vV′
      | Δᴸ₁ , χsᴸ₁ , N , .Δᴿ , .Reduction.[] , .V′ , Δ₁ ,
        W₁ , q₁ , M↠N , V′↠N₂′ , evol₁ , N⊑N₂′
      | value-trace-refl
      | inj₁ (Δᴸ₂ , ψsᴸ , V , Δ₂ , W₂ , q₂ , N↠V , vV ,
          evol₂ , V⊑V′)
      with transport-related-source
        (applyTys-++ χsᴸ₁ ψsᴸ _) (q₂ , V⊑V′)
  target-value {Δᴿ} V′ χsᴿ M′↠V′ vV′
      | Δᴸ₁ , χsᴸ₁ , N , .Δᴿ , .Reduction.[] , .V′ , Δ₁ ,
        W₁ , q₁ , M↠N , V′↠N₂′ , evol₁ , N⊑N₂′
      | value-trace-refl
      | inj₁ (Δᴸ₂ , ψsᴸ , V , Δ₂ , W₂ , q₂ , N↠V , vV ,
          evol₂ , V⊑V′)
      | q , V⊑V′′ =
    inj₁
      (Δᴸ₂ , (χsᴸ₁ ++χ ψsᴸ) , V , Δ₂ , W₂ , q ,
       composeReduction M↠N N↠V , vV , V⊑V′′)
  target-value {Δᴿ} V′ χsᴿ M′↠V′ vV′
      | Δᴸ₁ , χsᴸ₁ , N , .Δᴿ , .Reduction.[] , .V′ , Δ₁ ,
        W₁ , q₁ , M↠N , V′↠N₂′ , evol₁ , N⊑N₂′
      | value-trace-refl
      | inj₂ (Δᴸ₂ , ψsᴸ , Δ₂ , W₂ , N↠blame , evol₂) =
    inj₂
      (Δᴸ₂ , (χsᴸ₁ ++χ ψsᴸ) ,
       composeReduction M↠N N↠blame)

  target-blame : ∀ {Δᴿ} (χsᴿ : StoreChanges 0 Δᴿ)
    → compiled-right M⊑M′ —↠[ χsᴿ ] blame
    → ∃[ Δᴸ ] (Σ[ χsᴸ ∈ StoreChanges 0 Δᴸ ]
        (compiled-left M⊑M′ —↠[ χsᴸ ] blame))
  target-blame {Δᴿ} χsᴿ M′↠blame
      with sim-back* initial-parked initial-related M′↠blame
  target-blame {Δᴿ} χsᴿ M′↠blame
      | Δᴸ₁ , χsᴸ₁ , N , Δᴿ₂ , ψsᴿ , N₂′ , Δ₁ , W₁ ,
        q₁ , M↠N , blame↠N₂′ , evol₁ , N⊑N₂′
      with blame-irreducible* blame↠N₂′
  target-blame {Δᴿ} χsᴿ M′↠blame
      | Δᴸ₁ , χsᴸ₁ , N , .Δᴿ , .Reduction.[] , .blame , Δ₁ ,
        W₁ , q₁ , M↠N , blame↠N₂′ , evol₁ , N⊑N₂′
      | blame-trace-refl
      with target-blame-catchup
        (parked-world-closed initial-parked evol₁) N⊑N₂′
  target-blame {Δᴿ} χsᴿ M′↠blame
      | Δᴸ₁ , χsᴸ₁ , N , .Δᴿ , .Reduction.[] , .blame , Δ₁ ,
        W₁ , q₁ , M↠N , blame↠N₂′ , evol₁ , N⊑N₂′
      | blame-trace-refl
      | Δᴸ₂ , ψsᴸ , Δ₂ , W₂ , N↠blame , evol₂ =
    Δᴸ₂ , (χsᴸ₁ ++χ ψsᴸ) , composeReduction M↠N N↠blame

  right-converges⇒left-converges :
    Convergesᶜ (compiled-right M⊑M′)
    → Convergesᶜ (compiled-left M⊑M′)
  right-converges⇒left-converges
      (Δᴿ , V′ , χsᴿ , M′↠V′ , inj₁ vV′)
      with target-value V′ χsᴿ M′↠V′ vV′
  right-converges⇒left-converges
      (Δᴿ , V′ , χsᴿ , M′↠V′ , inj₁ vV′)
      | inj₁ (Δᴸ , χsᴸ , V , Δ , W , q , M↠V , vV , V⊑V′) =
    Δᴸ , V , χsᴸ , M↠V , inj₁ vV
  right-converges⇒left-converges
      (Δᴿ , V′ , χsᴿ , M′↠V′ , inj₁ vV′)
      | inj₂ (Δᴸ , χsᴸ , M↠blame) =
    Δᴸ , blame , χsᴸ , M↠blame , inj₂ refl
  right-converges⇒left-converges
      (Δᴿ , .blame , χsᴿ , M′↠blame , inj₂ refl)
      with target-blame χsᴿ M′↠blame
  right-converges⇒left-converges
      (Δᴿ , .blame , χsᴿ , M′↠blame , inj₂ refl)
      | Δᴸ , χsᴸ , M↠blame =
    Δᴸ , blame , χsᴸ , M↠blame , inj₂ refl

  source-diverges : Divergesᶜ (compiled-left M⊑M′)
    → Divergesᶜ (compiled-right M⊑M′)
  source-diverges M⇑ M′⇓ =
    M⇑ (right-converges⇒left-converges M′⇓)

  source-typing : ⟨ 0 , store-empty , [] ⟩ ⊢
      compiled-left M⊑M′ ⦂ A
  source-typing =
    proj₂
      (compile {Σ = store-empty}
        (gradual-term-imprecision-source-typing M⊑M′))

  target-diverges : Divergesᶜ (compiled-right M⊑M′)
    → DivergeOrBlameᶜ (compiled-left M⊑M′)
  target-diverges M′⇑ N {χsᴸ} M↠N
      with progress (multi-preservation source-typing M↠N)
  target-diverges M′⇑ N {χsᴸ} M↠N | crash N≡blame =
    inj₁ N≡blame
  target-diverges M′⇑ N {χsᴸ} M↠N
      | step {Δ′ = Δᴸ′} {χ = χ} {N = N′} N→N′ =
    inj₂ (Δᴸ′ , χ , N′ , N→N′)
  target-diverges M′⇑ N {χsᴸ} M↠N | done vN
      with source-value N χsᴸ M↠N vN
  target-diverges M′⇑ N {χsᴸ} M↠N | done vN
      | Δᴿ , χsᴿ , V′ , Δ , W , q , M′↠V′ , vV′ , N⊑V′ =
    ⊥-elim (M′⇑ (Δᴿ , V′ , χsᴿ , M′↠V′ , inj₁ vV′))
