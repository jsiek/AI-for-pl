module proof.DGG.SimBackProof where

-- File Charter:
--   * Gives a top-down proof of SimBackᵀ modulo four narrow residual families.
--   * Proves structural, type-application, source-blame, and target-blame
--     cases, including blame catch-up through reveal/conceal boundaries.
--   * Shares the remaining root-closing, strict-right, conversion-boundary,
--     and source-lambda obligations through one parameter per proof idea.

open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Empty using (⊥)
import Data.List as List
import Data.Fin as Fin
import Data.Nat as Nat
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym)
  renaming (subst to subst≡)

open import Types using
  (Ty; TyCtx; Atom; Ground; NonStar; NonVar; _⇒_; ★; `∀; _[_]ᵗ;
   _∈ᵗ_; ⇑ᵗ; renameᵗ)
open import Consistency using
  ( Env∼
  ; flipᵐ
  ; extᵐ
  ; instᵐ
  ; genᵐ
  ; _⊢_∼_
  ; _⊢_∼★
  ; _⊢★∼_
  ; _[_]ᶜ
  )
open import Conversion using (Conv↑; Conv↓; rename↑; rename↓)
open import Primitives using (Prim; primArgTy; primResultTy; δ)
open import CastTerms
open import Reduction
open import Imprecision using (⇒⊑⇒)
open import proof.Reduction using
  ( applyTy-⇒
  ; applyTy-∀
  ; applyBodies
  ; applyTys-⇒
  ; applyTys-∀
  ; applyTys-open
  ; applyTys-primArgTy
  ; applyTys-primResultTy
  ; appL-↠
  ; cast-↠
  ; composeReduction
  ; conceal-↠
  ; primL-↠
  ; reveal-↠
  ; typeApp-↠
  ; _++χ_
  )
import proof.Imprecision as PI
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2
open import proof.DGG.Parked.ParkedWorldDef
  using
    ( ParkedWorld
    ; ParkedEvolve
    ; evolve-refl
    ; evolve-keepᴸ
    ; evolve-keepᴿ
    ; evolve-right-bind
    )
open import proof.DGG.Parked.ParkedEvolveCompositionProof
  using (compose-parked-evolve)
open import proof.DGG.Parked.ParkedWorldLemma using (transport⊑ᴾ)
open import proof.DGG.SimBackDef using (SimBackᵀ)
open import proof.DGG.CatchupToMorePreciseDef using (toTagRebaseAtᴿ)
open import proof.DGG.TargetBlameCatchupProof
  using
    ( target-blame-catchup
    ; target-blame-boundary-refl
    ; target-blame-boundary-source-reveal
    ; target-blame-boundary-source-conceal
    ; target-value-blame-exclusion
    ; target-blame-catchup-under-boundary
    )
open import proof.DGG.TransportTermImprecisionDef
  using (TransportTermImprecisionᴾᵀ)
open import proof.TypeSafety.Preservation using (apply-open; preservation)

applyTy-★ : ∀ {Δ Δ′} (χ : StoreChange Δ Δ′)
  → applyTy χ ★ ≡ ★
applyTy-★ keep = refl
applyTy-★ (bind A) = refl

finish-target-blame : ∀ {Δᴸ Δᴸ′ Δᴿ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ Δ′}
    {M : Term Δᴸ} {K : Term Δᴸ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {χsᴸ : StoreChanges Δᴸ Δᴸ′}
  → (p : A ⊑ᵂ⟨ W ⟩ B)
  → M —↠[ χsᴸ ] K
  → K —→[ keep ] blame
  → ParkedEvolve χsᴸ [] W W′
  → Σ[ q ∈
      applyTys (χsᴸ ++χ (keep ∷ [])) A ⊑ᵂ⟨ W′ ⟩ B ]
      (M —↠[ χsᴸ ++χ (keep ∷ []) ] blame) ×
      ParkedEvolve (χsᴸ ++χ (keep ∷ [])) (keep ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² blame ⊑ blame ∶ q)
finish-target-blame {K = K} p M↠K K→blame evol =
  q′ ,
  composeReduction M↠K
    (K
      —→[ keep ]⟨ K→blame ⟩
     blame ∎[]) ,
  evol′ ,
  blame⊑² ⊢blame q′
  where
  evol′ = compose-parked-evolve evol
    (evolve-keepᴸ (evolve-keepᴿ evolve-refl))
  q′ = transport⊑ᴾ evol′ p

------------------------------------------------------------------------
-- Narrow residual-family classifiers
------------------------------------------------------------------------

ApplicationRootStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
ApplicationRootStep (pure-step (β _)) = ⊤
ApplicationRootStep (pure-step (β-⇒ _ _)) = ⊤
ApplicationRootStep (pure-step (β-reveal-⇒ _ _)) = ⊤
ApplicationRootStep (pure-step (β-conceal-⇒ _ _)) = ⊤
ApplicationRootStep (pure-step (blame-·₂ _)) = ⊤
ApplicationRootStep _ = ⊥

ApplicationRightStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
ApplicationRightStep (ξ-·₂ _ _ _) = ⊤
ApplicationRightStep _ = ⊥

TypeApplicationRootStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
TypeApplicationRootStep (pure-step (β-∀ _ _)) = ⊤
TypeApplicationRootStep (β-Λ _) = ⊤
TypeApplicationRootStep (β-gen _ _ _) = ⊤
TypeApplicationRootStep (β-reveal-∀ _) = ⊤
TypeApplicationRootStep (β-conceal-∀ _) = ⊤
TypeApplicationRootStep _ = ⊥

CastRootStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
CastRootStep (pure-step (β-id _)) = ⊤
CastRootStep (pure-step (ground _ _)) = ⊤
CastRootStep (pure-step (expand _ _)) = ⊤
CastRootStep (pure-step (tag-untag _)) = ⊤
CastRootStep (pure-step (tag-untag-bad _ _)) = ⊤
CastRootStep (pure-step (blame-bot-intro _)) = ⊤
CastRootStep (β-inst _ _) = ⊤
CastRootStep _ = ⊥

RevealRootStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
RevealRootStep (pure-step (id-reveal _)) = ⊤
RevealRootStep (pure-step (conceal-reveal _)) = ⊤
RevealRootStep _ = ⊥

RevealFrameStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
RevealFrameStep (ξ-reveal _ _) = ⊤
RevealFrameStep _ = ⊥

ConcealRootStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
ConcealRootStep (pure-step (id-conceal _)) = ⊤
ConcealRootStep _ = ⊥

ConcealFrameStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
ConcealFrameStep (ξ-conceal _ _) = ⊤
ConcealFrameStep _ = ⊥

PrimitiveRootStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
PrimitiveRootStep (pure-step (δ-⊕ _)) = ⊤
PrimitiveRootStep (pure-step (blame-⊕₂ _)) = ⊤
PrimitiveRootStep _ = ⊥

PrimitiveRightStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
PrimitiveRightStep (ξ-⊕₂ _ _ _) = ⊤
PrimitiveRightStep _ = ⊥

TargetRootClosing : ∀ {Δᴸ Δᴿ Δ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → W ∣ List.[] ⊢² M ⊑ M′ ∶ p
  → M′ —→[ χᴿ ] N′
  → Set
TargetRootClosing (·⊑·² _ _) step = ApplicationRootStep step
TargetRootClosing (•⊑•² _ _ _ _) step = TypeApplicationRootStep step
TargetRootClosing (cast⊑cast² _ _ _ _) step = CastRootStep step
TargetRootClosing (⊑cast² _ _ _) step = CastRootStep step
TargetRootClosing (⊑reveal² _ _ _ _ _ _) step = RevealRootStep step
TargetRootClosing (⊑conceal² _ _ _ _ _ _) step = ConcealRootStep step
TargetRootClosing (reveal⊑reveal² _ _ _ _ _ _ _) step =
  RevealRootStep step
TargetRootClosing (conceal⊑conceal² _ _ _ _ _ _ _ _) step =
  ConcealRootStep step
TargetRootClosing (packaged-seal-star² _ _ _ _ _ _ _ _ _) step =
  ConcealRootStep step
TargetRootClosing (⊕⊑⊕² _ _ _ _) step = PrimitiveRootStep step
TargetRootClosing _ step = ⊥

StrictRightStep : ∀ {Δᴸ Δᴿ Δ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → W ∣ List.[] ⊢² M ⊑ M′ ∶ p
  → M′ —→[ χᴿ ] N′
  → Set
StrictRightStep (·⊑·² _ _) step = ApplicationRightStep step
StrictRightStep (⊕⊑⊕² _ _ _ _) step = PrimitiveRightStep step
StrictRightStep _ step = ⊥

ConversionBoundaryStep : ∀ {Δᴸ Δᴿ Δ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → W ∣ List.[] ⊢² M ⊑ M′ ∶ p
  → M′ —→[ χᴿ ] N′
  → Set
ConversionBoundaryStep (⊑reveal² _ _ _ _ _ _) step =
  RevealFrameStep step
ConversionBoundaryStep (⊑conceal² _ _ _ _ _ _) step =
  ConcealFrameStep step
ConversionBoundaryStep (reveal⊑² _ _ _ _ _ _) step = ⊤
ConversionBoundaryStep (conceal⊑²-seal-star-open _ _ _ _ _ _ _) step = ⊤
ConversionBoundaryStep (conceal⊑²-source-ok _ _ _ _ _ _ _) step = ⊤
ConversionBoundaryStep (reveal⊑reveal² _ _ _ _ _ _ _) step =
  RevealFrameStep step
ConversionBoundaryStep (conceal⊑conceal² _ _ _ _ _ _ _ _) step =
  ConcealFrameStep step
ConversionBoundaryStep (packaged-seal-star² _ _ _ _ _ _ _ _ _) step =
  ConcealFrameStep step
ConversionBoundaryStep _ step = ⊥

SourceLambdaStep : ∀ {Δᴸ Δᴿ Δ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → W ∣ List.[] ⊢² M ⊑ M′ ∶ p
  → M′ —→[ χᴿ ] N′
  → Set
SourceLambdaStep (Λ⊑² _ _ _ _ _ _ _) step = ⊤
SourceLambdaStep (Λ⊑²-smart-comma _ _ _ _ _ _ _ _) step = ⊤
SourceLambdaStep _ step = ⊥

------------------------------------------------------------------------
-- Narrow residual-family surfaces
------------------------------------------------------------------------

SimBackTargetRootᵀ : Set
SimBackTargetRootᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (rel : W ∣ List.[] ⊢² M ⊑ M′ ∶ p)
  → (step : M′ —→[ χᴿ ] N′)
  → TargetRootClosing rel step
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (M —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ q)

SimBackStrictRightᵀ : Set
SimBackStrictRightᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (rel : W ∣ List.[] ⊢² M ⊑ M′ ∶ p)
  → (step : M′ —→[ χᴿ ] N′)
  → StrictRightStep rel step
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (M —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ q)

SimBackConversionBoundaryᵀ : Set
SimBackConversionBoundaryᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (rel : W ∣ List.[] ⊢² M ⊑ M′ ∶ p)
  → (step : M′ —→[ χᴿ ] N′)
  → ConversionBoundaryStep rel step
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (M —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ q)

SimBackSourceLambdaᵀ : Set
SimBackSourceLambdaᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (rel : W ∣ List.[] ⊢² M ⊑ M′ ∶ p)
  → (step : M′ —→[ χᴿ ] N′)
  → SourceLambdaStep rel step
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (M —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ q)

module _
    (sim-back-target-root : SimBackTargetRootᵀ)
    (sim-back-strict-right : SimBackStrictRightᵀ)
    (sim-back-conversion-boundary : SimBackConversionBoundaryᵀ)
    (sim-back-source-lambda : SimBackSourceLambdaᵀ)
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

  sim-back parked rel@(·⊑·² L⊑L′ M⊑M′)
      step@(pure-step (β vV)) =
    sim-back-target-root parked rel step tt
  sim-back parked rel@(·⊑·² L⊑L′ M⊑M′)
      step@(pure-step (β-⇒ vV vW)) =
    sim-back-target-root parked rel step tt
  sim-back parked rel@(·⊑·² L⊑L′ M⊑M′)
      step@(pure-step (β-reveal-⇒ vV vW)) =
    sim-back-target-root parked rel step tt
  sim-back parked rel@(·⊑·² L⊑L′ M⊑M′)
      step@(pure-step (β-conceal-⇒ vV vW)) =
    sim-back-target-root parked rel step tt
  sim-back {p = p} parked (·⊑·² {M = M} L⊑blame M⊑M′)
      (pure-step blame-·₁)
      with target-blame-catchup parked L⊑blame
  sim-back {p = p} parked (·⊑·² {M = M} L⊑blame M⊑M′)
      (pure-step blame-·₁)
      | Δᴸ′ , χsᴸ , Δ′ , W′ , L↠blame , evol
      with finish-target-blame p
        (appL-↠ {M = M} L↠blame) (pure-step blame-·₁) evol
  sim-back {p = p} parked (·⊑·² {M = M} L⊑blame M⊑M′)
      (pure-step blame-·₁)
      | Δᴸ′ , χsᴸ , Δ′ , W′ , L↠blame , evol
      | q , LM↠blame , evol′ , endpoint =
    Δᴸ′ , χsᴸ ++χ (keep ∷ []) , blame , Δ′ , W′ , q ,
    LM↠blame ,
    evol′ ,
    endpoint
  sim-back parked rel@(·⊑·² L⊑L′ M⊑M′)
      step@(pure-step (blame-·₂ vV)) =
    sim-back-target-root parked rel step tt
  sim-back parked rel@(·⊑·² L⊑L′ M⊑M′)
      step@(ξ-·₂ vV M′→N′ refl) =
    sim-back-strict-right parked rel step tt

  sim-back parked rel@(•⊑•² p∀ M⊑M′ q r)
      step@(pure-step (β-∀ vV eq)) =
    sim-back-target-root parked rel step tt
  sim-back {p = r} parked
      (•⊑•² {C = C} {A = A} p∀ M⊑blame q r)
      (pure-step blame-•)
      with target-blame-catchup parked M⊑blame
  sim-back {p = r} parked
      (•⊑•² {C = C} {A = A} p∀ M⊑blame q r)
      (pure-step blame-•)
      | Δᴸ′ , χsᴸ , Δ′ , W′ , M↠blame , evol
      with finish-target-blame r
        (typeApp-↠ {C = C} {A = A} M↠blame)
        (pure-step blame-•) evol
  sim-back {p = r} parked
      (•⊑•² {C = C} {A = A} p∀ M⊑blame q r)
      (pure-step blame-•)
      | Δᴸ′ , χsᴸ , Δ′ , W′ , M↠blame , evol
      | r′ , whole↠blame , evol′ , endpoint =
    Δᴸ′ , χsᴸ ++χ (keep ∷ []) , blame , Δ′ , W′ , r′ ,
    whole↠blame ,
    evol′ ,
    endpoint
  sim-back parked rel@(•⊑•² p∀ M⊑M′ q r)
      step@(β-Λ vV) =
    sim-back-target-root parked rel step tt
  sim-back parked rel@(•⊑•² p∀ M⊑M′ q r)
      step@(β-gen vV A≢★ safe) =
    sim-back-target-root parked rel step tt
  sim-back parked rel@(•⊑•² p∀ M⊑M′ q r)
      step@(β-reveal-∀ vV) =
    sim-back-target-root parked rel step tt
  sim-back parked rel@(•⊑•² p∀ M⊑M′ q r)
      step@(β-conceal-∀ vV) =
    sim-back-target-root parked rel step tt
  sim-back parked
      (•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ M⊑M′ q r)
      (ξ-• {χ = χ} {M′ = N′} M′→N′ refl refl)
      with sim-back parked M⊑M′ M′→N′
  sim-back parked
      (•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ M⊑M′ q r)
      (ξ-• {χ = χ} {M′ = N′} M′→N′ refl refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evol , N⊑N′
      rewrite applyTys-∀ χsᴸ C
            | applyTy-∀ χ C′
      with p | N⊑N′
  sim-back parked
      (•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ M⊑M′ q r)
      (ξ-• {χ = χ} {M′ = N′} M′→N′ refl refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evol , N⊑N′
      | p∀⁺ | N⊑N′⁺
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
                (λ S →
                  S ⊑ᵂ⟨ W′ ⟩ applyTy χ (C′ [ A′ ]ᵗ))
                (applyTys-open χsᴸ C A)
                (transport⊑ᴾ evol r))
          , •⊑•² p∀⁺ N⊑N′⁺
              (transport⊑ᴾ evol q)
              (subst≡
                (λ T →
                  (applyBodies χsᴸ C [ applyTys χsᴸ A ]ᵗ)
                    ⊑ᵂ⟨ W′ ⟩ T)
                (apply-open χ C′ A′)
                (subst≡
                  (λ S →
                    S ⊑ᵂ⟨ W′ ⟩ applyTy χ (C′ [ A′ ]ᵗ))
                  (applyTys-open χsᴸ C A)
                  (transport⊑ᴾ evol r)))
          ))
  sim-back parked
      (•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ M⊑M′ q r)
      (ξ-• {χ = χ} {M′ = N′} M′→N′ refl refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evol , N⊑N′
      | p∀⁺ | N⊑N′⁺
      | r⁺ , whole-rel =
    Δᴸ′ , χsᴸ ,
    N ⦂∀ applyBodies χsᴸ C [ applyTys χsᴸ A ] ,
    Δ′ , W′ , r⁺ ,
    typeApp-↠ M↠N ,
    evol ,
    whole-rel

  sim-back {χᴿ = χ} parked
      (•⊑² {C = C} {A = A} p∀ M⊑M′ q r) M′→N′
      with sim-back parked M⊑M′ M′→N′
  sim-back {χᴿ = χ} parked
      (•⊑² {C = C} {A = A} p∀ M⊑M′ q r) M′→N′
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evol , N⊑N′
      rewrite applyTys-∀ χsᴸ C
      with p | N⊑N′
  sim-back {χᴿ = χ} parked
      (•⊑² {C = C} {A = A} p∀ M⊑M′ q r) M′→N′
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evol , N⊑N′
      | p∀⁺ | N⊑N′⁺
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
            (transport⊑ᴾ evol r)
        , •⊑² p∀⁺ N⊑N′⁺
            (subst≡
              (λ T → applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ T)
              (applyTy-★ χ)
              (transport⊑ᴾ evol q))
            (subst≡
              (λ S → S ⊑ᵂ⟨ W′ ⟩ _)
              (applyTys-open χsᴸ C A)
              (transport⊑ᴾ evol r))
        )
  sim-back {χᴿ = χ} parked
      (•⊑² {C = C} {A = A} p∀ M⊑M′ q r) M′→N′
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evol , N⊑N′
      | p∀⁺ | N⊑N′⁺
      | r⁺ , whole-rel =
    Δᴸ′ , χsᴸ ,
    N ⦂∀ applyBodies χsᴸ C [ applyTys χsᴸ A ] ,
    Δ′ , W′ , r⁺ ,
    typeApp-↠ M↠N ,
    evol ,
    whole-rel

  sim-back parked rel@(cast⊑cast² c c′ M⊑M′ q)
      step@(pure-step (β-id vV)) =
    sim-back-target-root parked rel step tt
  sim-back parked rel@(cast⊑cast² c c′ M⊑M′ q)
      step@(pure-step (ground vV A≢G)) =
    sim-back-target-root parked rel step tt
  sim-back parked rel@(cast⊑cast² c c′ M⊑M′ q)
      step@(pure-step (expand vV G≢B)) =
    sim-back-target-root parked rel step tt
  sim-back parked rel@(cast⊑cast² c c′ M⊑M′ q)
      step@(pure-step (tag-untag vV)) =
    sim-back-target-root parked rel step tt
  sim-back parked rel@(cast⊑cast² c c′ M⊑M′ q)
      step@(pure-step (tag-untag-bad vV G≢H)) =
    sim-back-target-root parked rel step tt
  sim-back parked rel@(cast⊑cast² c c′ M⊑M′ q)
      step@(pure-step (blame-bot-intro vV)) =
    sim-back-target-root parked rel step tt
  sim-back {p = q} parked (cast⊑cast² c c′ M⊑blame q)
      (pure-step blame-⟨⟩)
      with target-blame-catchup parked M⊑blame
  sim-back {p = q} parked (cast⊑cast² c c′ M⊑blame q)
      (pure-step blame-⟨⟩)
      | Δᴸ′ , χsᴸ , Δ′ , W′ , M↠blame , evol
      with finish-target-blame q
        (cast-↠ c M↠blame) (pure-step blame-⟨⟩) evol
  sim-back {p = q} parked (cast⊑cast² c c′ M⊑blame q)
      (pure-step blame-⟨⟩)
      | Δᴸ′ , χsᴸ , Δ′ , W′ , M↠blame , evol
      | q′ , whole↠blame , evol′ , endpoint =
    Δᴸ′ , χsᴸ ++χ (keep ∷ []) , blame , Δ′ , W′ , q′ ,
    whole↠blame ,
    evol′ ,
    endpoint
  sim-back parked rel@(cast⊑cast² c c′ M⊑M′ q)
      step@(β-inst vV B≢★) =
    sim-back-target-root parked rel step tt

  sim-back parked rel@(⊑cast² c′ M⊑M′ q)
      step@(pure-step (β-id vV)) =
    sim-back-target-root parked rel step tt
  sim-back parked rel@(⊑cast² c′ M⊑M′ q)
      step@(pure-step (ground vV A≢G)) =
    sim-back-target-root parked rel step tt
  sim-back parked rel@(⊑cast² c′ M⊑M′ q)
      step@(pure-step (expand vV G≢B)) =
    sim-back-target-root parked rel step tt
  sim-back parked rel@(⊑cast² c′ M⊑M′ q)
      step@(pure-step (tag-untag vV)) =
    sim-back-target-root parked rel step tt
  sim-back parked rel@(⊑cast² c′ M⊑M′ q)
      step@(pure-step (tag-untag-bad vV G≢H)) =
    sim-back-target-root parked rel step tt
  sim-back parked rel@(⊑cast² c′ M⊑M′ q)
      step@(pure-step (blame-bot-intro vV)) =
    sim-back-target-root parked rel step tt
  sim-back {p = q} parked (⊑cast² c′ M⊑blame q)
      (pure-step blame-⟨⟩)
      with target-blame-catchup parked M⊑blame
  sim-back {p = q} parked (⊑cast² c′ M⊑blame q)
      (pure-step blame-⟨⟩)
      | Δᴸ′ , χsᴸ , Δ′ , W′ , M↠blame , evol =
    Δᴸ′ , χsᴸ , blame , Δ′ , W′ ,
    transport⊑ᴾ (evolve-keepᴿ evol) q ,
    M↠blame ,
    evolve-keepᴿ evol ,
    blame⊑² ⊢blame (transport⊑ᴾ (evolve-keepᴿ evol) q)
  sim-back parked rel@(⊑cast² c′ M⊑M′ q)
      step@(β-inst vV B≢★) =
    sim-back-target-root parked rel step tt

  sim-back parked rel@(⊑reveal² mono rebase same c′⊢ M⊑M′ q)
      step@(pure-step (id-reveal vV)) =
    sim-back-target-root parked rel step tt
  sim-back parked rel@(⊑reveal² mono rebase same c′⊢ M⊑M′ q)
      step@(pure-step (conceal-reveal vV)) =
    sim-back-target-root parked rel step tt
  sim-back {p = q} parked
      (⊑reveal² mono rebase same-[] c′⊢ M⊑blame q)
      (pure-step blame-reveal)
      with target-blame-catchup-under-boundary
        target-value-blame-exclusion parked
        (target-blame-boundary-source-reveal
          target-blame-boundary-refl mono (toTagRebaseAtᴿ rebase))
        M⊑blame
  sim-back {p = q} parked
      (⊑reveal² mono rebase same-[] c′⊢ M⊑blame q)
      (pure-step blame-reveal)
      | Δᴸ′ , χsᴸ , Δ′ , W′ , M↠blame , evol =
    Δᴸ′ , χsᴸ , blame , Δ′ , W′ ,
    transport⊑ᴾ (evolve-keepᴿ evol) q ,
    M↠blame ,
    evolve-keepᴿ evol ,
    blame⊑² ⊢blame (transport⊑ᴾ (evolve-keepᴿ evol) q)
  sim-back parked rel@(⊑reveal² mono rebase same c′⊢ M⊑M′ q)
      step@(ξ-reveal M′→N′ refl) =
    sim-back-conversion-boundary parked rel step tt

  sim-back parked rel@(⊑conceal² mono rebase same c′⊢ M⊑M′ q)
      step@(pure-step (id-conceal vV)) =
    sim-back-target-root parked rel step tt
  sim-back {p = q} parked
      (⊑conceal² mono rebase same-[] c′⊢ M⊑blame q)
      (pure-step blame-conceal)
      with target-blame-catchup-under-boundary
        target-value-blame-exclusion parked
        (target-blame-boundary-source-conceal
          target-blame-boundary-refl mono (toTagRebaseAtᴿ rebase))
        M⊑blame
  sim-back {p = q} parked
      (⊑conceal² mono rebase same-[] c′⊢ M⊑blame q)
      (pure-step blame-conceal)
      | Δᴸ′ , χsᴸ , Δ′ , W′ , M↠blame , evol =
    Δᴸ′ , χsᴸ , blame , Δ′ , W′ ,
    transport⊑ᴾ (evolve-keepᴿ evol) q ,
    M↠blame ,
    evolve-keepᴿ evol ,
    blame⊑² ⊢blame (transport⊑ᴾ (evolve-keepᴿ evol) q)
  sim-back parked rel@(⊑conceal² mono rebase same c′⊢ M⊑M′ q)
      step@(ξ-conceal M′→N′ refl) =
    sim-back-conversion-boundary parked rel step tt

  sim-back parked rel@(reveal⊑² mono rebase same c⊢ M⊑M′ q) step =
    sim-back-conversion-boundary parked rel step tt

  sim-back parked
      rel@(conceal⊑²-seal-star-open no-target mono rebase same c⊢ M⊑M′ q)
      step =
    sim-back-conversion-boundary parked rel step tt
  sim-back parked
      rel@(conceal⊑²-source-ok ok mono rebase same c⊢ M⊑M′ q) step =
    sim-back-conversion-boundary parked rel step tt

  sim-back parked rel@(reveal⊑reveal² mono rebase same c⊢ c′⊢ M⊑M′ q)
      step@(pure-step (id-reveal vV)) =
    sim-back-target-root parked rel step tt
  sim-back parked rel@(reveal⊑reveal² mono rebase same c⊢ c′⊢ M⊑M′ q)
      step@(pure-step (conceal-reveal vV)) =
    sim-back-target-root parked rel step tt
  sim-back {p = q} parked
      (reveal⊑reveal² {c = c} mono rebase same-[]
        c⊢ c′⊢ M⊑blame q)
      (pure-step blame-reveal)
      with target-blame-catchup-under-boundary
        target-value-blame-exclusion parked
        (target-blame-boundary-source-reveal
          target-blame-boundary-refl mono (tag-rebase-varᴸ rebase))
        M⊑blame
  sim-back {p = q} parked
      (reveal⊑reveal² {c = c} mono rebase same-[]
        c⊢ c′⊢ M⊑blame q)
      (pure-step blame-reveal)
      | Δᴸ′ , χsᴸ , Δ′ , W′ , M↠blame , evol
      with finish-target-blame q
        (reveal-↠ c M↠blame) (pure-step blame-reveal) evol
  sim-back {p = q} parked
      (reveal⊑reveal² {c = c} mono rebase same-[]
        c⊢ c′⊢ M⊑blame q)
      (pure-step blame-reveal)
      | Δᴸ′ , χsᴸ , Δ′ , W′ , M↠blame , evol
      | q′ , whole↠blame , evol′ , endpoint =
    Δᴸ′ , χsᴸ ++χ (keep ∷ []) , blame , Δ′ , W′ , q′ ,
    whole↠blame ,
    evol′ ,
    endpoint
  sim-back parked rel@(reveal⊑reveal² mono rebase same c⊢ c′⊢ M⊑M′ q)
      step@(ξ-reveal M′→N′ refl) =
    sim-back-conversion-boundary parked rel step tt

  sim-back parked
      rel@(conceal⊑conceal² partner mono rebase same c⊢ c′⊢ M⊑M′ q)
      step@(pure-step (id-conceal vV)) =
    sim-back-target-root parked rel step tt
  sim-back {p = q} parked
      (conceal⊑conceal² {c = c} partner mono rebase same-[]
        c⊢ c′⊢ M⊑blame q)
      (pure-step blame-conceal)
      with target-blame-catchup-under-boundary
        target-value-blame-exclusion parked
        (target-blame-boundary-source-conceal
          target-blame-boundary-refl mono (tag-rebase-varᴸ rebase))
        M⊑blame
  sim-back {p = q} parked
      (conceal⊑conceal² {c = c} partner mono rebase same-[]
        c⊢ c′⊢ M⊑blame q)
      (pure-step blame-conceal)
      | Δᴸ′ , χsᴸ , Δ′ , W′ , M↠blame , evol
      with finish-target-blame q
        (conceal-↠ c M↠blame) (pure-step blame-conceal) evol
  sim-back {p = q} parked
      (conceal⊑conceal² {c = c} partner mono rebase same-[]
        c⊢ c′⊢ M⊑blame q)
      (pure-step blame-conceal)
      | Δᴸ′ , χsᴸ , Δ′ , W′ , M↠blame , evol
      | q′ , whole↠blame , evol′ , endpoint =
    Δᴸ′ , χsᴸ ++χ (keep ∷ []) , blame , Δ′ , W′ , q′ ,
    whole↠blame ,
    evol′ ,
    endpoint
  sim-back parked
      rel@(conceal⊑conceal² partner mono rebase same c⊢ c′⊢ M⊑M′ q)
      step@(ξ-conceal M′→N′ refl) =
    sim-back-conversion-boundary parked rel step tt

  sim-back {p = q} parked
      (packaged-seal-star² {Xᴸ = Xᴸ} partner mono rebase same-[]
        c⊢ c′⊢ M⊑blame sealed q)
      (pure-step blame-conceal)
      with target-blame-catchup-under-boundary
        target-value-blame-exclusion parked
        (target-blame-boundary-source-conceal
          target-blame-boundary-refl mono (tag-rebase-varᴸ rebase))
        M⊑blame
  sim-back {p = q} parked
      (packaged-seal-star² {Xᴸ = Xᴸ} partner mono rebase same-[]
        c⊢ c′⊢ M⊑blame sealed q)
      (pure-step blame-conceal)
      | Δᴸ′ , χsᴸ , Δ′ , W′ , M↠blame , evol
      with finish-target-blame q
        (conceal-↠ (Conversion.seal Xᴸ ★) M↠blame)
        (pure-step blame-conceal) evol
  sim-back {p = q} parked
      (packaged-seal-star² {Xᴸ = Xᴸ} partner mono rebase same-[]
        c⊢ c′⊢ M⊑blame sealed q)
      (pure-step blame-conceal)
      | Δᴸ′ , χsᴸ , Δ′ , W′ , M↠blame , evol
      | q′ , whole↠blame , evol′ , endpoint =
    Δᴸ′ , χsᴸ ++χ (keep ∷ []) , blame , Δ′ , W′ , q′ ,
    whole↠blame ,
    evol′ ,
    endpoint
  sim-back parked
      rel@(packaged-seal-star² partner mono rebase same c⊢ c′⊢
        M⊑M′ sealed q)
      step@(ξ-conceal M′→N′ refl) =
    sim-back-conversion-boundary parked rel step tt

  sim-back {Δᴸ = Δᴸ} {W = W} {p = p} {χᴿ = keep}
      parked (blame⊑² M′⊢ q) step =
    Δᴸ , [] , blame , _ , W , p ,
    (blame ∎[]) ,
    evolve-keepᴿ evolve-refl ,
    blame⊑² (preservation M′⊢ step) p
  sim-back {Δᴸ = Δᴸ} {W = W} {p = p} {χᴿ = bind B₀}
      parked (blame⊑² M′⊢ q) step =
    Δᴸ , [] , blame , _ , CTI2.rightOnlyWorld W B₀ ,
    transport⊑ᴾ
      (evolve-right-bind {W = W} {B = B₀} evolve-refl) p ,
    (blame ∎[]) ,
    evolve-right-bind {W = W} {B = B₀} evolve-refl ,
    blame⊑² (preservation M′⊢ step)
      (transport⊑ᴾ
        (evolve-right-bind {W = W} {B = B₀} evolve-refl) p)

  sim-back parked rel@(Λ⊑² Anv zero∈A liftγ vV M′⊢ V⊑M′ q)
      step =
    sim-back-source-lambda parked rel step tt
  sim-back parked
      rel@(Λ⊑²-smart-comma Anv zero∈A liftW liftγ vV M′⊢ V⊑M′ q)
      step =
    sim-back-source-lambda parked rel step tt

  sim-back parked rel@(⊕⊑⊕² op L⊑L′ M⊑M′ r)
      step@(pure-step (δ-⊕ δκ)) =
    sim-back-target-root parked rel step tt
  sim-back {p = r} parked
      (⊕⊑⊕² op {M = M} L⊑blame M⊑M′ r)
      (pure-step blame-⊕₁)
      with target-blame-catchup parked L⊑blame
  sim-back {p = r} parked
      (⊕⊑⊕² op {M = M} L⊑blame M⊑M′ r)
      (pure-step blame-⊕₁)
      | Δᴸ′ , χsᴸ , Δ′ , W′ , L↠blame , evol
      with finish-target-blame r
        (primL-↠ {M = M} {op = op} L↠blame)
        (pure-step blame-⊕₁) evol
  sim-back {p = r} parked
      (⊕⊑⊕² op {M = M} L⊑blame M⊑M′ r)
      (pure-step blame-⊕₁)
      | Δᴸ′ , χsᴸ , Δ′ , W′ , L↠blame , evol
      | r′ , whole↠blame , evol′ , endpoint =
    Δᴸ′ , χsᴸ ++χ (keep ∷ []) , blame , Δ′ , W′ , r′ ,
    whole↠blame ,
    evol′ ,
    endpoint
  sim-back parked rel@(⊕⊑⊕² op L⊑L′ M⊑M′ r)
      step@(pure-step (blame-⊕₂ vV)) =
    sim-back-target-root parked rel step tt
  sim-back parked rel@(⊕⊑⊕² op L⊑L′ M⊑M′ r)
      step@(ξ-⊕₂ vV M′→N′ refl) =
    sim-back-strict-right parked rel step tt
