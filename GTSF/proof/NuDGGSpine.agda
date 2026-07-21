module proof.NuDGGSpine where

-- File Charter:
--   * Connects the public gradual-language DGG statement to a closed Nu-term
--     operational DGG theorem.
--   * Checks that compiler monotonicity produces exactly the initial relation
--     consumed by the operational theorem.
--   * Leaves one explicit proof boundary: `ClosedNuDGG`, whose four clauses
--     are the forward and backward convergence/divergence obligations.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst)

open import Types
open import Ctx using (ctxWf-[])
open import CompileTermImprecision using
  (compile-preserves-term-imprecision)
open import DynamicGradualGuarantee using
  ( Convergesᶜ
  ; Divergesᶜ
  ; DivergeOrBlameᶜ
  ; GradualDGG
  ; compiled-left
  ; compiled-right
  )
open import GradualTermImprecision using
  ( _∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_
  ; gradual-term-imprecision-source-typing
  ; gradual-term-imprecision-target-typing
  )
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  ( StoreChanges
  ; applyStores
  ; applyTyCtxs
  ; applyTys
  ; _—→[_]_
  ; _—↠[_]_
  )
open import NuTermImprecision using
  ( CtxImp
  ; StoreImp
  ; leftCtxⁱ
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuMetaTheory using
  ( multi-preservation
  ; multi-runtime-preservation
  ; progress
  )
open import NuStore using (StoreWf)
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; Value
  ; blame
  ; _∣_∣_⊢_⦂_
  )
open import proof.NuProgress using (Progress; crash; done; step)
open import proof.NuDGGClosedWorld using (empty-store-wf)
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; nu-term-imprecision-source-typing
  )
open import Run using (compileᵀ-runtime)
open import TermTyping using (forget)

------------------------------------------------------------------------
-- Compiler boundary
------------------------------------------------------------------------

compiled-term-imprecision :
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  (M⊑M′ : [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  [] ∣ 0 ∣ 0 ∣ [] ∣ []
    ⊢ᴺ compiled-left M⊑M′ ⊑ compiled-right M⊑M′
    ⦂ A ⊑ B ∶ p
compiled-term-imprecision M⊑M′ =
  compile-preserves-term-imprecision ctxWf-[] ctxWf-[] M⊑M′

compiled-left-runtime :
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  (M⊑M′ : [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  RuntimeOK (compiled-left M⊑M′)
compiled-left-runtime M⊑M′ =
  compileᵀ-runtime ctxWf-[]
    (gradual-term-imprecision-source-typing M⊑M′)

compiled-right-runtime :
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  (M⊑M′ : [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  RuntimeOK (compiled-right M⊑M′)
compiled-right-runtime M⊑M′ =
  compileᵀ-runtime ctxWf-[]
    (gradual-term-imprecision-target-typing M⊑M′)

------------------------------------------------------------------------
-- Observation-level consequences of terminal simulation
------------------------------------------------------------------------

closed-left-store :
  leftStoreⁱ {Φ = []} {Δᴸ = 0} {Δᴿ = 0} [] ≡ []
closed-left-store = refl

closed-left-ctx :
  leftCtxⁱ {Φ = []} {Δᴸ = 0} {Δᴿ = 0} [] ≡ []
closed-left-ctx = refl

closed-nu-source-typing :
  ∀ {N N′ A B p} →
  [] ∣ 0 ∣ 0 ∣ [] ∣ [] ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p →
  0 ∣ [] ∣ [] ⊢ N ⦂ A
closed-nu-source-typing {N = N} {N′ = N′} {A = A} {B = B} N⊑N′ =
  subst (λ Σ → 0 ∣ Σ ∣ [] ⊢ N ⦂ A) closed-left-store
    (subst (λ Γ →
        0 ∣ leftStoreⁱ {Φ = []} {Δᴸ = 0} {Δᴿ = 0} []
          ∣ Γ ⊢ N ⦂ A)
      closed-left-ctx
      (forget
        (nu-term-imprecision-source-typing
          {Φ = []} {Δᴸ = 0} {Δᴿ = 0} {ρ = []} {γ = []}
          {M = N} {M′ = N′} {A = A} {B = B} N⊑N′)))

target-convergence-implies-source-convergence :
  ∀ {N N′} →
  (∀ V′ χs′ →
    N′ —↠[ χs′ ] V′ →
    Value V′ →
      (∃[ V ] (Σ[ χs ∈ StoreChanges ]
        ((N —↠[ χs ] V) × Value V)))
      ⊎ (∃[ χs ] (N —↠[ χs ] blame))) →
  (∀ χs′ →
    N′ —↠[ χs′ ] blame →
    ∃[ χs ] (N —↠[ χs ] blame)) →
  Convergesᶜ N′ →
  Convergesᶜ N
target-convergence-implies-source-convergence value-observation
    blame-observation
    (V′ , χs′ , N′↠V′ , inj₁ vV′)
    with value-observation V′ χs′ N′↠V′ vV′
target-convergence-implies-source-convergence value-observation
    blame-observation
    (V′ , χs′ , N′↠V′ , inj₁ vV′)
    | inj₁ (V , χs , N↠V , vV) =
  V , χs , N↠V , inj₁ vV
target-convergence-implies-source-convergence value-observation
    blame-observation
    (V′ , χs′ , N′↠V′ , inj₁ vV′)
    | inj₂ (χs , N↠blame) =
  blame , χs , N↠blame , inj₂ refl
target-convergence-implies-source-convergence value-observation
    blame-observation
    (V′ , χs′ , N′↠V′ , inj₂ refl)
    with blame-observation χs′ N′↠V′
target-convergence-implies-source-convergence value-observation
    blame-observation
    (V′ , χs′ , N′↠V′ , inj₂ refl)
    | χs , N↠blame =
  blame , χs , N↠blame , inj₂ refl

source-divergence-follows-from-target-observations :
  ∀ {N N′} →
  (∀ V′ χs′ →
    N′ —↠[ χs′ ] V′ →
    Value V′ →
      (∃[ V ] (Σ[ χs ∈ StoreChanges ]
        ((N —↠[ χs ] V) × Value V)))
      ⊎ (∃[ χs ] (N —↠[ χs ] blame))) →
  (∀ χs′ →
    N′ —↠[ χs′ ] blame →
    ∃[ χs ] (N —↠[ χs ] blame)) →
  Divergesᶜ N →
  Divergesᶜ N′
source-divergence-follows-from-target-observations
    value-observation blame-observation N⇑ N′⇓ =
  N⇑
    (target-convergence-implies-source-convergence
      value-observation blame-observation N′⇓)

target-divergence-implies-source-diverge-or-blame :
  ∀ {N N′ A B p} →
  RuntimeOK N →
  [] ∣ 0 ∣ 0 ∣ [] ∣ [] ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p →
  (∀ V χs →
    N —↠[ χs ] V →
    Value V →
    ∃[ V′ ] (Σ[ χs′ ∈ StoreChanges ]
      ((N′ —↠[ χs′ ] V′) × Value V′))) →
  Divergesᶜ N′ →
  DivergeOrBlameᶜ N
target-divergence-implies-source-diverge-or-blame
    {N = N} {N′ = N′} {A = A} {B = B}
    okN N⊑N′ forward N′⇑ P { χs } N↠P
    with progress
      (multi-runtime-preservation
        {Δ = 0} {Σ = []} {M = N} {A = A} {χs = χs}
        empty-store-wf okN
        (closed-nu-source-typing N⊑N′)
        N↠P)
      (multi-preservation
        {Δ = 0} {Σ = []} {M = N} {A = A} {χs = χs}
        empty-store-wf okN
        (closed-nu-source-typing N⊑N′)
        N↠P)
target-divergence-implies-source-diverge-or-blame
    {N = N} {N′ = N′} {A = A} {B = B}
    okN N⊑N′ forward N′⇑ P { χs } N↠P
    | crash P≡blame =
  inj₁ P≡blame
target-divergence-implies-source-diverge-or-blame
    {N = N} {N′ = N′} {A = A} {B = B}
    okN N⊑N′ forward N′⇑ P { χs } N↠P
    | step { χ = χ } { N = Q } P→Q =
  inj₂ (χ , Q , P→Q)
target-divergence-implies-source-diverge-or-blame
    {N = N} {N′ = N′} {A = A} {B = B}
    okN N⊑N′ forward N′⇑ P { χs } N↠P
    | done vP
    with forward P χs N↠P vP
target-divergence-implies-source-diverge-or-blame
    {N = N} {N′ = N′} {A = A} {B = B}
    okN N⊑N′ forward N′⇑ P { χs } N↠P
    | done vP | V′ , χs′ , N′↠V′ , vV′ =
  ⊥-elim (N′⇑ (V′ , χs′ , N′↠V′ , inj₁ vV′))

------------------------------------------------------------------------
-- Closed Nu operational theorem required by the public DGG
------------------------------------------------------------------------

ClosedNuDGG : Set₁
ClosedNuDGG =
  ∀ {N N′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  RuntimeOK N →
  RuntimeOK N′ →
  [] ∣ 0 ∣ 0 ∣ [] ∣ [] ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p →
    (∀ V χs →
      N —↠[ χs ] V →
      Value V →
      ∃[ V′ ] (Σ[ χs′ ∈ StoreChanges ]
      (∃[ Φ ] (Σ[ ρ ∈
          StoreImp Φ (applyTyCtxs χs 0) (applyTyCtxs χs′ 0) ]
      (Σ[ q ∈
          (Φ ∣ applyTyCtxs χs 0
            ⊢ applyTys χs A ⊑ applyTys χs′ B
            ⊣ applyTyCtxs χs′ 0) ]
        ((N′ —↠[ χs′ ] V′) ×
         Value V′ ×
         (leftStoreⁱ ρ ≡ applyStores χs []) ×
         (rightStoreⁱ ρ ≡ applyStores χs′ []) ×
         Φ ∣ applyTyCtxs χs 0 ∣ applyTyCtxs χs′ 0 ∣ ρ ∣ []
           ⊢ᴺ V ⊑ V′
           ⦂ applyTys χs A ⊑ applyTys χs′ B ∶ q))))))
    × (Divergesᶜ N → Divergesᶜ N′)
    × (∀ V′ χs′ →
      N′ —↠[ χs′ ] V′ →
      Value V′ →
        (∃[ V ] (Σ[ χs ∈ StoreChanges ]
        (∃[ Φ ] (Σ[ ρ ∈
            StoreImp Φ (applyTyCtxs χs 0) (applyTyCtxs χs′ 0) ]
        (Σ[ q ∈
            (Φ ∣ applyTyCtxs χs 0
              ⊢ applyTys χs A ⊑ applyTys χs′ B
              ⊣ applyTyCtxs χs′ 0) ]
          ((N —↠[ χs ] V) ×
           Value V ×
           (leftStoreⁱ ρ ≡ applyStores χs []) ×
           (rightStoreⁱ ρ ≡ applyStores χs′ []) ×
           Φ ∣ applyTyCtxs χs 0 ∣ applyTyCtxs χs′ 0 ∣ ρ ∣ []
             ⊢ᴺ V ⊑ V′
             ⦂ applyTys χs A ⊑ applyTys χs′ B ∶ q)))))
        ⊎ (∃[ χs ] (N —↠[ χs ] blame))))
    × (Divergesᶜ N′ → DivergeOrBlameᶜ N)


forget-forward-terminal-worlds :
  ∀ {N′ V A B χs} →
  (∃[ V′ ] (Σ[ χs′ ∈ StoreChanges ]
    (∃[ Φ ] (Σ[ ρ ∈
        StoreImp Φ (applyTyCtxs χs 0) (applyTyCtxs χs′ 0) ]
    (Σ[ q ∈
        (Φ ∣ applyTyCtxs χs 0
          ⊢ applyTys χs A ⊑ applyTys χs′ B
          ⊣ applyTyCtxs χs′ 0) ]
      ((N′ —↠[ χs′ ] V′) ×
       Value V′ ×
       (leftStoreⁱ ρ ≡ applyStores χs []) ×
       (rightStoreⁱ ρ ≡ applyStores χs′ []) ×
       Φ ∣ applyTyCtxs χs 0 ∣ applyTyCtxs χs′ 0 ∣ ρ ∣ []
         ⊢ᴺ V ⊑ V′
         ⦂ applyTys χs A ⊑ applyTys χs′ B ∶ q)))))) →
  ∃[ V′ ] (Σ[ χs′ ∈ StoreChanges ]
    ((N′ —↠[ χs′ ] V′) × Value V′))
forget-forward-terminal-worlds
    (V′ , χs′ , Φ , ρ , q , N′↠V′ , vV′ ,
      left-eq , right-eq , V⊑V′) =
  V′ , χs′ , N′↠V′ , vV′

forget-backward-terminal-worlds :
  ∀ {N V′ A B χs′} →
  (∃[ V ] (Σ[ χs ∈ StoreChanges ]
    (∃[ Φ ] (Σ[ ρ ∈
        StoreImp Φ (applyTyCtxs χs 0) (applyTyCtxs χs′ 0) ]
    (Σ[ q ∈
        (Φ ∣ applyTyCtxs χs 0
          ⊢ applyTys χs A ⊑ applyTys χs′ B
          ⊣ applyTyCtxs χs′ 0) ]
      ((N —↠[ χs ] V) ×
       Value V ×
       (leftStoreⁱ ρ ≡ applyStores χs []) ×
       (rightStoreⁱ ρ ≡ applyStores χs′ []) ×
       Φ ∣ applyTyCtxs χs 0 ∣ applyTyCtxs χs′ 0 ∣ ρ ∣ []
         ⊢ᴺ V ⊑ V′
         ⦂ applyTys χs A ⊑ applyTys χs′ B ∶ q)))))
    ⊎ (∃[ χs ] (N —↠[ χs ] blame))) →
  (∃[ V ] (Σ[ χs ∈ StoreChanges ]
    ((N —↠[ χs ] V) × Value V)))
    ⊎ (∃[ χs ] (N —↠[ χs ] blame))
forget-backward-terminal-worlds
    (inj₁ (V , χs , Φ , ρ , q , N↠V , vV ,
      left-eq , right-eq , V⊑V′)) =
  inj₁ (V , χs , N↠V , vV)
forget-backward-terminal-worlds (inj₂ N↠blame) = inj₂ N↠blame


closed-nu-terminal-simulation⇒closed-nu-dgg :
  (∀ {N N′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
    RuntimeOK N →
    RuntimeOK N′ →
    [] ∣ 0 ∣ 0 ∣ [] ∣ [] ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p →
      ( (∀ V χs →
          N —↠[ χs ] V →
          Value V →
          ∃[ V′ ] (Σ[ χs′ ∈ StoreChanges ]
          (∃[ Φ ] (Σ[ ρ ∈
              StoreImp Φ (applyTyCtxs χs 0) (applyTyCtxs χs′ 0) ]
          (Σ[ q ∈
              (Φ ∣ applyTyCtxs χs 0
                ⊢ applyTys χs A ⊑ applyTys χs′ B
                ⊣ applyTyCtxs χs′ 0) ]
            ((N′ —↠[ χs′ ] V′) ×
             Value V′ ×
             (leftStoreⁱ ρ ≡ applyStores χs []) ×
             (rightStoreⁱ ρ ≡ applyStores χs′ []) ×
             Φ ∣ applyTyCtxs χs 0 ∣ applyTyCtxs χs′ 0 ∣ ρ ∣ []
               ⊢ᴺ V ⊑ V′
               ⦂ applyTys χs A ⊑ applyTys χs′ B ∶ q))))))
      × (∀ V′ χs′ →
          N′ —↠[ χs′ ] V′ →
          Value V′ →
            (∃[ V ] (Σ[ χs ∈ StoreChanges ]
            (∃[ Φ ] (Σ[ ρ ∈
                StoreImp Φ (applyTyCtxs χs 0)
                  (applyTyCtxs χs′ 0) ]
            (Σ[ q ∈
                (Φ ∣ applyTyCtxs χs 0
                  ⊢ applyTys χs A ⊑ applyTys χs′ B
                  ⊣ applyTyCtxs χs′ 0) ]
              ((N —↠[ χs ] V) ×
               Value V ×
               (leftStoreⁱ ρ ≡ applyStores χs []) ×
               (rightStoreⁱ ρ ≡ applyStores χs′ []) ×
               Φ ∣ applyTyCtxs χs 0 ∣ applyTyCtxs χs′ 0 ∣ ρ ∣ []
                 ⊢ᴺ V ⊑ V′
                 ⦂ applyTys χs A ⊑ applyTys χs′ B ∶ q)))))
              ⊎ (∃[ χs ] (N —↠[ χs ] blame))))
      × (∀ χs′ →
          N′ —↠[ χs′ ] blame →
          ∃[ χs ] (N —↠[ χs ] blame)))) →
  ClosedNuDGG
closed-nu-terminal-simulation⇒closed-nu-dgg terminal
    {N = N} {N′ = N′} {A = A} {B = B} okN okN′ N⊑N′
    with terminal okN okN′ N⊑N′
closed-nu-terminal-simulation⇒closed-nu-dgg terminal
    {N = N} {N′ = N′} {A = A} {B = B} okN okN′ N⊑N′
    | forward , backward , target-blame =
  forward ,
  source-divergence-follows-from-target-observations
    (λ V′ χs′ N′↠V′ vV′ →
      forget-backward-terminal-worlds
        {N = N} {V′ = V′} {A = A} {B = B} {χs′ = χs′}
        (backward V′ χs′ N′↠V′ vV′))
    target-blame ,
  backward ,
  target-divergence-implies-source-diverge-or-blame
    okN N⊑N′
    (λ V χs N↠V vV →
      forget-forward-terminal-worlds
        {N′ = N′} {V = V} {A = A} {B = B} {χs = χs}
        (forward V χs N↠V vV))

------------------------------------------------------------------------
-- Public theorem reduction
------------------------------------------------------------------------

closed-nu-dgg⇒gradual-dgg :
  ClosedNuDGG →
  GradualDGG
closed-nu-dgg⇒gradual-dgg nu-dgg M⊑M′ =
  nu-dgg
    (compiled-left-runtime M⊑M′)
    (compiled-right-runtime M⊑M′)
    (compiled-term-imprecision M⊑M′)
