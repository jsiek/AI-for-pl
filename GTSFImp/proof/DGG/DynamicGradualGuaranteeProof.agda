{-# OPTIONS --safe #-}

module proof.DGG.DynamicGradualGuaranteeProof where

-- File Charter:
--   * Proves the closed GTSFImp dynamic gradual guarantee from the
--     multi-step simulation and terminal catch-up interfaces.
--   * Uses completed compilation, canonical multi-world evolution, reduction
--     composition, and irreducibility and type-safety proofs directly.
--   * Contains no induction; operational inductions remain confined to the
--     parameterized simulation and catch-up lemmas.
--   * Collects the shared simulation and catch-up interfaces once in an
--     enclosing module; only the generic theorem takes target-blame catch-up.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Product using (_×_; _,_; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore; store-empty)
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
  ; applyStores
  ; applyTys
  ; _—↠[_]_
  ; _—↠[_]⟨_⟩_
  ; _∎[]
  )
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
import proof.DGG.CompilePreservesImprecision as CompileMonotone
open import proof.DGG.DynamicGradualGuaranteeDef
  using
    ( Convergesᶜ
    ; Divergesᶜ
    ; DivergeOrBlameᶜ
    ; GradualDGG
    ; compiled-left
    ; compiled-right
    )
open import proof.DGG.MultiSimDef using (Sim*ᵀ)
open import proof.DGG.MultiSimBackDef using (SimBack*ᵀ)
open import proof.DGG.CatchupToLessPreciseDef
  using (CatchupToLessPrecise)
open import proof.DGG.CatchupToMorePreciseDef
  using (CatchupToMorePrecise)
open import proof.DGG.TargetBlameCatchupDef
  using (TargetBlameCatchupᵀ)
open import proof.DGG.TargetBlameCatchupLemma
  using (target-blame-catchup)
open import proof.Reduction.ValueIrreducibleDef
  using (ValueTraceRefl; value-trace-refl)
open import proof.Reduction.ValueIrreducibleProof
  using (value-irreducible*)
open import proof.Reduction.BlameIrreducibleDef
  using (BlameTraceRefl; blame-trace-refl)
open import proof.Reduction.BlameIrreducibleProof
  using (blame-irreducible*)
open import proof.Reduction using
  (_++χ_; applyStores-++; applyTys-++; _—↠+[_]⟨_⟩_)
open import proof.TypeSafety.Progress using
  (Progress; done; step; crash; progress)
open import proof.TypeSafety.Preservation using (multi-preservation)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using
  ( composeMultiWorldEvolution
  ; multi-no-open-frames
  ; multi-source-store
  ; multi-target-store
  )

------------------------------------------------------------------------
-- Equality transport for terminal related terms
------------------------------------------------------------------------

transport-related-source : ∀ {Γᴸ Γᴿ : CastTerms.Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (CastTerms.Δᵉ Γᴸ)} {M′ : Term (CastTerms.Δᵉ Γᴿ)}
    {A A′ : Ty (CastTerms.Δᵉ Γᴸ)} {B : Ty (CastTerms.Δᵉ Γᴿ)}
  → A ≡ A′
  → (Σ[ p ∈ A ⊑ᵀ⟨ γ ⟩ B ] (γ ⊢² M ⊑ M′ ∶ p))
  → Σ[ q ∈ A′ ⊑ᵀ⟨ γ ⟩ B ] (γ ⊢² M ⊑ M′ ∶ q)
transport-related-source refl related = related


transport-related-target : ∀ {Γᴸ Γᴿ : CastTerms.Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (CastTerms.Δᵉ Γᴸ)} {M′ : Term (CastTerms.Δᵉ Γᴿ)}
    {A : Ty (CastTerms.Δᵉ Γᴸ)}
    {B B′ : Ty (CastTerms.Δᵉ Γᴿ)}
  → B ≡ B′
  → (Σ[ p ∈ A ⊑ᵀ⟨ γ ⟩ B ] (γ ⊢² M ⊑ M′ ∶ p))
  → Σ[ q ∈ A ⊑ᵀ⟨ γ ⟩ B′ ] (γ ⊢² M ⊑ M′ ∶ q)
transport-related-target refl related = related


transport-related-stores : ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ Σᴸ′ : TyStore Δᴸ}
    {Σᴿ Σᴿ′ : TyStore Δᴿ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → Σᴸ ≡ Σᴸ′
  → Σᴿ ≡ Σᴿ′
  → (Σ[ γ ∈ ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩ ]
      Σ[ p ∈ A ⊑ᵀ⟨ γ ⟩ B ] (γ ⊢² M ⊑ M′ ∶ p))
  → Σ[ γ′ ∈ ⟨ Δᴸ , Σᴸ′ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ′ , [] ⟩ ]
      Σ[ q ∈ A ⊑ᵀ⟨ γ′ ⟩ B ] (γ′ ⊢² M ⊑ M′ ∶ q)
transport-related-stores refl refl related = related

------------------------------------------------------------------------
-- Dynamic gradual guarantee
------------------------------------------------------------------------

module _
    (sim* : Sim*ᵀ)
    (sim-back* : SimBack*ᵀ)
    (catchup : CatchupToLessPrecise)
    (catchup-to-more-precise : CatchupToMorePrecise)
  where

  dynamic-gradual-guarantee-with-target-blame : TargetBlameCatchupᵀ
    → GradualDGG
  dynamic-gradual-guarantee-with-target-blame
      target-blame-catchup {A = A} {B = B} {p = p} M⊑M′ =
    source-value , source-diverges , target-value , target-diverges
    where
    initial-related :
      CompileMonotone.initialContextWorld
        {μ = idᵐ {Δ = 0}} [] ⊢²
        compiled-left M⊑M′ ⊑ compiled-right M⊑M′
          ∶ CompileMonotone.initialContext-⊑
            {μ = idᵐ {Δ = 0}} [] p
    initial-related =
      CompileMonotone.compile-preserves-imprecision M⊑M′

    initial-no-open-frames :
      openFramesᶜ
        (CompileMonotone.initialContextWorld
          {μ = idᵐ {Δ = 0}} []) ≡ []
    initial-no-open-frames =
      CompileMonotone.initialContext-no-open-frames
        {μ = idᵐ {Δ = 0}} []

    source-value : ∀ {Δᴸ} (V : Term Δᴸ)
        (χsᴸ : StoreChanges 0 Δᴸ)
      → compiled-left M⊑M′ —↠[ χsᴸ ] V
      → Value V
      → ∃[ Δᴿ ] (Σ[ χsᴿ ∈ StoreChanges 0 Δᴿ ]
        (∃[ V′ ]
          (Σ[ γ ∈
            ⟨ Δᴸ , applyStores χsᴸ store-empty , [] ⟩ ⊑ᶜ
            ⟨ Δᴿ , applyStores χsᴿ store-empty , [] ⟩ ]
          (Σ[ q ∈ applyTys χsᴸ A ⊑ᵀ⟨ γ ⟩ applyTys χsᴿ B ]
            ((compiled-right M⊑M′ —↠[ χsᴿ ] V′) ×
             Value V′ ×
             (γ ⊢² V ⊑ V′ ∶ q))))))
    source-value {Δᴸ} V χsᴸ M↠V vV
        with sim* initial-no-open-frames initial-related M↠V
    source-value {Δᴸ} V χsᴸ M↠V vV
        | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , N′ , γ₁ , q₁ , M′↠N′ ,
          evol₁ , V⊑N′
        with catchup-to-more-precise
          (multi-no-open-frames evol₁ initial-no-open-frames)
          V⊑N′ vV
    source-value {Δᴸ} V χsᴸ M↠V vV
        | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , N′ , γ₁ , q₁ , M′↠N′ ,
          evol₁ , V⊑N′
        | Δᴿ₂ , Σᴿ₂ , ψsᴿ , V′ , γ₂ , q₂ , N′↠V′ ,
          vV′ , evol₂ , V⊑V′
        with transport-related-target
          (applyTys-++ χsᴿ₁ ψsᴿ _) (q₂ , V⊑V′)
    source-value {Δᴸ} V χsᴸ M↠V vV
        | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , N′ , γ₁ , q₁ , M′↠N′ ,
          evol₁ , V⊑N′
        | Δᴿ₂ , Σᴿ₂ , ψsᴿ , V′ , γ₂ , q₂ , N′↠V′ ,
          vV′ , evol₂ , V⊑V′
        | q , V⊑V′′
        with transport-related-stores refl
          (multi-target-store
            (composeMultiWorldEvolution evol₁ evol₂))
          (γ₂ , q , V⊑V′′)
    source-value {Δᴸ} V χsᴸ M↠V vV
        | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , N′ , γ₁ , q₁ , M′↠N′ ,
          evol₁ , V⊑N′
        | Δᴿ₂ , Σᴿ₂ , ψsᴿ , V′ , γ₂ , q₂ , N′↠V′ ,
          vV′ , evol₂ , V⊑V′
        | q , V⊑V′′
        | γ , q′ , final-related =
      Δᴿ₂ , (χsᴿ₁ ++χ ψsᴿ) , V′ , γ , q′ ,
        (compiled-right M⊑M′
        —↠+[ χsᴿ₁ ]⟨ M′↠N′ ⟩
          N′
        —↠[ ψsᴿ ]⟨ N′↠V′ ⟩
          V′ ∎[]) ,
        vV′ , final-related

    target-value : ∀ {Δᴿ} (V′ : Term Δᴿ)
        (χsᴿ : StoreChanges 0 Δᴿ)
      → compiled-right M⊑M′ —↠[ χsᴿ ] V′
      → Value V′
      → (∃[ Δᴸ ] (Σ[ χsᴸ ∈ StoreChanges 0 Δᴸ ]
          (∃[ V ]
            (Σ[ γ ∈
              ⟨ Δᴸ , applyStores χsᴸ store-empty , [] ⟩ ⊑ᶜ
              ⟨ Δᴿ , applyStores χsᴿ store-empty , [] ⟩ ]
            (Σ[ q ∈ applyTys χsᴸ A ⊑ᵀ⟨ γ ⟩ applyTys χsᴿ B ]
              ((compiled-left M⊑M′ —↠[ χsᴸ ] V) ×
               Value V ×
               (γ ⊢² V ⊑ V′ ∶ q))))))
        ⊎ (∃[ Δᴸ ] (Σ[ χsᴸ ∈ StoreChanges 0 Δᴸ ]
            (compiled-left M⊑M′ —↠[ χsᴸ ] blame))))
    target-value {Δᴿ} V′ χsᴿ M′↠V′ vV′
        with sim-back* initial-no-open-frames initial-related M′↠V′
    target-value {Δᴿ} V′ χsᴿ M′↠V′ vV′
        | inj₂ source-blame = inj₂ source-blame
    target-value {Δᴿ} V′ χsᴿ M′↠V′ vV′
        | inj₁ (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , N , Δᴿ₂ , Σᴿ₂ , ψsᴿ ,
          N₂′ , γ₁ , q₁ , M↠N , V′↠N₂′ , evol₁ , N⊑N₂′)
        with value-irreducible* vV′ V′↠N₂′
    target-value {Δᴿ} V′ χsᴿ M′↠V′ vV′
        | inj₁ (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , N , .Δᴿ , Σᴿ₂ ,
          .Reduction.[] , .V′ , γ₁ , q₁ , M↠N , V′↠N₂′ , evol₁ ,
          N⊑N₂′)
        | value-trace-refl
        with catchup
          (multi-no-open-frames evol₁ initial-no-open-frames)
          N⊑N₂′ vV′
    target-value {Δᴿ} V′ χsᴿ M′↠V′ vV′
        | inj₁ (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , N , .Δᴿ , Σᴿ₂ ,
          .Reduction.[] , .V′ , γ₁ , q₁ , M↠N , V′↠N₂′ , evol₁ ,
          N⊑N₂′)
        | value-trace-refl
        | inj₁ (Δᴸ₂ , Σᴸ₂ , ψsᴸ , V , γ₂ , q₂ , N↠V , vV ,
            evol₂ , V⊑V′)
        with transport-related-source
          (applyTys-++ χsᴸ₁ ψsᴸ _) (q₂ , V⊑V′)
    target-value {Δᴿ} V′ χsᴿ M′↠V′ vV′
        | inj₁ (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , N , .Δᴿ , Σᴿ₂ ,
          .Reduction.[] , .V′ , γ₁ , q₁ , M↠N , V′↠N₂′ , evol₁ ,
          N⊑N₂′)
        | value-trace-refl
        | inj₁ (Δᴸ₂ , Σᴸ₂ , ψsᴸ , V , γ₂ , q₂ , N↠V , vV ,
            evol₂ , V⊑V′)
        | q , V⊑V′′
        with transport-related-stores
          (multi-source-store
            (composeMultiWorldEvolution evol₁ evol₂))
          (trans (multi-target-store evol₁)
            (sym (applyStores-++ χsᴿ Reduction.[] store-empty)))
          (γ₂ , q , V⊑V′′)
    target-value {Δᴿ} V′ χsᴿ M′↠V′ vV′
        | inj₁ (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , N , .Δᴿ , Σᴿ₂ ,
          .Reduction.[] , .V′ , γ₁ , q₁ , M↠N , V′↠N₂′ , evol₁ ,
          N⊑N₂′)
        | value-trace-refl
        | inj₁ (Δᴸ₂ , Σᴸ₂ , ψsᴸ , V , γ₂ , q₂ , N↠V , vV ,
            evol₂ , V⊑V′)
        | q , V⊑V′′
        | γ , q′ , final-related =
      inj₁
        (Δᴸ₂ , (χsᴸ₁ ++χ ψsᴸ) , V , γ , q′ ,
          (compiled-left M⊑M′
          —↠+[ χsᴸ₁ ]⟨ M↠N ⟩
            N
          —↠[ ψsᴸ ]⟨ N↠V ⟩
            V ∎[]) ,
          vV , final-related)
    target-value {Δᴿ} V′ χsᴿ M′↠V′ vV′
        | inj₁ (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , N , .Δᴿ , Σᴿ₂ ,
          .Reduction.[] , .V′ , γ₁ , q₁ , M↠N , V′↠N₂′ , evol₁ ,
          N⊑N₂′)
        | value-trace-refl
        | inj₂ (Δᴸ₂ , Σᴸ₂ , ψsᴸ , γ₂ , N↠blame , evol₂) =
      inj₂
        (Δᴸ₂ , (χsᴸ₁ ++χ ψsᴸ) ,
          (compiled-left M⊑M′
          —↠+[ χsᴸ₁ ]⟨ M↠N ⟩
            N
          —↠[ ψsᴸ ]⟨ N↠blame ⟩
            blame ∎[]))

    target-blame : ∀ {Δᴿ} (χsᴿ : StoreChanges 0 Δᴿ)
      → compiled-right M⊑M′ —↠[ χsᴿ ] blame
      → ∃[ Δᴸ ] (Σ[ χsᴸ ∈ StoreChanges 0 Δᴸ ]
          (compiled-left M⊑M′ —↠[ χsᴸ ] blame))
    target-blame {Δᴿ} χsᴿ M′↠blame
        with sim-back* initial-no-open-frames initial-related M′↠blame
    target-blame {Δᴿ} χsᴿ M′↠blame
        | inj₂ source-blame = source-blame
    target-blame {Δᴿ} χsᴿ M′↠blame
        | inj₁ (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , N , Δᴿ₂ , Σᴿ₂ , ψsᴿ ,
          N₂′ , γ₁ , q₁ , M↠N , blame↠N₂′ , evol₁ , N⊑N₂′)
        with blame-irreducible* blame↠N₂′
    target-blame {Δᴿ} χsᴿ M′↠blame
        | inj₁ (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , N , .Δᴿ , Σᴿ₂ ,
          .Reduction.[] , .blame , γ₁ , q₁ , M↠N , blame↠N₂′ , evol₁ ,
          N⊑N₂′)
        | blame-trace-refl
        with target-blame-catchup N⊑N₂′
    target-blame {Δᴿ} χsᴿ M′↠blame
        | inj₁ (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , N , .Δᴿ , Σᴿ₂ ,
          .Reduction.[] , .blame , γ₁ , q₁ , M↠N , blame↠N₂′ , evol₁ ,
          N⊑N₂′)
        | blame-trace-refl
        | Δᴸ₂ , ψsᴸ , N↠blame =
      Δᴸ₂ , (χsᴸ₁ ++χ ψsᴸ) ,
        (compiled-left M⊑M′
        —↠+[ χsᴸ₁ ]⟨ M↠N ⟩
          N
        —↠[ ψsᴸ ]⟨ N↠blame ⟩
          blame ∎[])

    right-converges⇒left-converges :
      Convergesᶜ (compiled-right M⊑M′)
      → Convergesᶜ (compiled-left M⊑M′)
    right-converges⇒left-converges
        (Δᴿ , V′ , χsᴿ , M′↠V′ , inj₁ vV′)
        with target-value V′ χsᴿ M′↠V′ vV′
    right-converges⇒left-converges
        (Δᴿ , V′ , χsᴿ , M′↠V′ , inj₁ vV′)
        | inj₁ (Δᴸ , χsᴸ , V , γ , q , M↠V , vV , V⊑V′) =
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
        | Δᴿ , χsᴿ , V′ , γ , q , M′↠V′ , vV′ , N⊑V′ =
      ⊥-elim (M′⇑ (Δᴿ , V′ , χsᴿ , M′↠V′ , inj₁ vV′))


  dynamic-gradual-guarantee : GradualDGG
  dynamic-gradual-guarantee =
    dynamic-gradual-guarantee-with-target-blame
      target-blame-catchup
