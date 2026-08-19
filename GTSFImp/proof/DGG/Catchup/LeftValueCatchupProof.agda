module proof.DGG.Catchup.LeftValueCatchupProof where

-- File Charter:
--   * Provides the checked source-value catch-up driver shell.
--   * Closes terminal value/refutation/blame rows directly.
--   * Routes source-operation, target-wrapper, paired-wrapper, and route-2
--     package rows through narrow syntactically pinned residual fields.

open import Data.List using ([])
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _+_; suc; _<_)
open import Data.Nat.Properties using (m≤m+n; m≤n+m; n<1+n; ≤-<-trans)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types using (Ty; TyVar; ★; ＇_)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (Conv↑; Conv↓; seal)
import CastTerms as CT
open import CastTerms
  using (Term; Value; blame; _⟨_⟩; _↑_; _↓_)
import Reduction as R
open import Reduction using (_∎[])
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Catchup.LeftBoundaryCatchupDef
  using (LeftCatchupResult)
open import proof.DGG.Catchup.LeftValueCatchupDef
  using (LeftValueCatchupAt; SourceCastBound)
import proof.DGG.Catchup.LeftSourceOperationsDef as LSO
open import proof.Consistency using (castSize)
open import proof.DGG.CatchupToMorePreciseDef
  using (boundary-refl; same-boundary)
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; evolve-refl)
open CTX using
  (World;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


sourceCastBudget : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ q
  → ℕ
sourceCastBudget (CTI2.x⊑x² x∈) = 0
sourceCastBudget (CTI2.ƛ⊑ƛ² rel) = sourceCastBudget rel
sourceCastBudget (CTI2.·⊑·² rel₁ rel₂) =
  sourceCastBudget rel₁ + sourceCastBudget rel₂
sourceCastBudget (CTI2.Λ⊑Λ² liftγ vV vV′ rel q) =
  sourceCastBudget rel
sourceCastBudget (CTI2.Λ⊑² Anv zero∈A liftγ vV target⊢ rel q) =
  sourceCastBudget rel
sourceCastBudget
    (CTI2.Λ⊑²-smart-comma Anv zero∈A liftW liftγ vV target⊢ rel q) =
  sourceCastBudget rel
sourceCastBudget (CTI2.•⊑•² p∀ rel q r) = sourceCastBudget rel
sourceCastBudget (CTI2.•⊑² p∀ rel q r) = sourceCastBudget rel
sourceCastBudget (CTI2.κ⊑κ² κ p) = 0
sourceCastBudget (CTI2.cast⊑cast² c c′ rel q) =
  castSize c + sourceCastBudget rel
sourceCastBudget (CTI2.⊑cast² c′ rel q) = sourceCastBudget rel
sourceCastBudget (CTI2.⊑reveal² mono rb sameγ c′⊢ rel q) =
  sourceCastBudget rel
sourceCastBudget (CTI2.⊑conceal² mono rb sameγ c′⊢ rel q) =
  sourceCastBudget rel
sourceCastBudget (CTI2.cast⊑² c rel q) =
  castSize c + sourceCastBudget rel
sourceCastBudget (CTI2.reveal⊑² mono rb sameγ c⊢ rel q) =
  sourceCastBudget rel
sourceCastBudget
    (CTI2.conceal⊑²-seal-star-open no-target mono rb sameγ c⊢ rel q) =
  sourceCastBudget rel
sourceCastBudget
    (CTI2.conceal⊑²-source-ok ok mono rb sameγ c⊢ rel q) =
  sourceCastBudget rel
sourceCastBudget
    (CTI2.reveal⊑reveal² mono rb sameγ c⊢ c′⊢ rel q) =
  sourceCastBudget rel
sourceCastBudget
    (CTI2.conceal⊑conceal² partner mono rb sameγ c⊢ c′⊢ rel q) =
  sourceCastBudget rel
sourceCastBudget
    (CTI2.packaged-seal-star² partner mono rb sameγ c⊢ c′⊢
      rel pkg-rel q) =
  sourceCastBudget rel + sourceCastBudget pkg-rel
sourceCastBudget (CTI2.blame⊑² target⊢ p) = 0
sourceCastBudget (CTI2.⊕⊑⊕² op rel₁ rel₂ r) =
  sourceCastBudget rel₁ + sourceCastBudget rel₂


source-cast-bound< : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → (rel : W ∣ γ ⊢² M ⊑ M′ ∶ q)
  → sourceCastBudget rel < fuel
  → SourceCastBound fuel rel
source-cast-bound< (CTI2.x⊑x² x∈) budget< = tt
source-cast-bound< (CTI2.ƛ⊑ƛ² rel) budget< =
  source-cast-bound< rel budget<
source-cast-bound< (CTI2.·⊑·² rel₁ rel₂) budget< =
  source-cast-bound< rel₁
    (≤-<-trans (m≤m+n (sourceCastBudget rel₁) (sourceCastBudget rel₂))
      budget<) ,
  source-cast-bound< rel₂
    (≤-<-trans (m≤n+m (sourceCastBudget rel₂) (sourceCastBudget rel₁))
      budget<)
source-cast-bound< (CTI2.Λ⊑Λ² liftγ vV vV′ rel q) budget< =
  source-cast-bound< rel budget<
source-cast-bound< (CTI2.Λ⊑² Anv zero∈A liftγ vV target⊢ rel q)
    budget< =
  source-cast-bound< rel budget<
source-cast-bound< (CTI2.Λ⊑²-smart-comma Anv zero∈A liftW liftγ vV
    target⊢ rel q) budget< =
  source-cast-bound< rel budget<
source-cast-bound< (CTI2.•⊑•² p∀ rel q r) budget< =
  source-cast-bound< rel budget<
source-cast-bound< (CTI2.•⊑² p∀ rel q r) budget< =
  source-cast-bound< rel budget<
source-cast-bound< (CTI2.κ⊑κ² κ p) budget< = tt
source-cast-bound< (CTI2.cast⊑cast² c c′ rel q) budget< =
  ≤-<-trans (m≤m+n (castSize c) (sourceCastBudget rel)) budget< ,
  source-cast-bound< rel
    (≤-<-trans (m≤n+m (sourceCastBudget rel) (castSize c))
      budget<)
source-cast-bound< (CTI2.⊑cast² c′ rel q) budget< =
  source-cast-bound< rel budget<
source-cast-bound< (CTI2.⊑reveal² mono rb sameγ c′⊢ rel q) budget< =
  source-cast-bound< rel budget<
source-cast-bound< (CTI2.⊑conceal² mono rb sameγ c′⊢ rel q) budget< =
  source-cast-bound< rel budget<
source-cast-bound< (CTI2.cast⊑² c rel q) budget< =
  ≤-<-trans (m≤m+n (castSize c) (sourceCastBudget rel)) budget< ,
  source-cast-bound< rel
    (≤-<-trans (m≤n+m (sourceCastBudget rel) (castSize c))
      budget<)
source-cast-bound< (CTI2.reveal⊑² mono rb sameγ c⊢ rel q) budget< =
  source-cast-bound< rel budget<
source-cast-bound<
    (CTI2.conceal⊑²-seal-star-open no-target mono rb sameγ c⊢ rel q)
    budget< =
  source-cast-bound< rel budget<
source-cast-bound<
    (CTI2.conceal⊑²-source-ok ok mono rb sameγ c⊢ rel q) budget< =
  source-cast-bound< rel budget<
source-cast-bound<
    (CTI2.reveal⊑reveal² mono rb sameγ c⊢ c′⊢ rel q) budget< =
  source-cast-bound< rel budget<
source-cast-bound<
    (CTI2.conceal⊑conceal² partner mono rb sameγ c⊢ c′⊢ rel q) budget< =
  source-cast-bound< rel budget<
source-cast-bound<
    (CTI2.packaged-seal-star² partner mono rb sameγ c⊢ c′⊢
      rel pkg-rel q) budget< =
  source-cast-bound< rel
    (≤-<-trans (m≤m+n (sourceCastBudget rel) (sourceCastBudget pkg-rel))
      budget<) ,
  source-cast-bound< pkg-rel
    (≤-<-trans (m≤n+m (sourceCastBudget pkg-rel) (sourceCastBudget rel))
      budget<)
source-cast-bound< (CTI2.blame⊑² target⊢ p) budget< = tt
source-cast-bound< (CTI2.⊕⊑⊕² op rel₁ rel₂ r) budget< =
  source-cast-bound< rel₁
    (≤-<-trans (m≤m+n (sourceCastBudget rel₁) (sourceCastBudget rel₂))
      budget<) ,
  source-cast-bound< rel₂
    (≤-<-trans (m≤n+m (sourceCastBudget rel₂) (sourceCastBudget rel₁))
      budget<)


source-cast-bound : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → (rel : W ∣ γ ⊢² M ⊑ M′ ∶ q)
  → SourceCastBound (suc (sourceCastBudget rel)) rel
source-cast-bound rel = source-cast-bound< rel (n<1+n (sourceCastBudget rel))


left-zero-value-result : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {q : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ [] ⊢² M ⊑ V′ ∶ q
  → Value M
  → Value V′
  → LeftCatchupResult
      {W = W} {Wᵖ = W}
      {kind = same-boundary}
      {Xᴸ? = nothing} {Xᴿ? = nothing}
      {M = M} {V′ = V′} {A = A} {B = B}
left-zero-value-result {M = M} rel vM vV′ =
  inj₁ (_ , R.[] , M , _ , _ , _ , nothing , boundary-refl ,
    _ , refl , (M ∎[]) , vM , evolve-refl , evolve-refl , rel)


left-zero-blame-result : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {V′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {q : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ [] ⊢² blame ⊑ V′ ∶ q
  → Value V′
  → LeftCatchupResult
      {W = W} {Wᵖ = W}
      {kind = same-boundary}
      {Xᴸ? = nothing} {Xᴿ? = nothing}
      {M = blame} {V′ = V′} {A = A} {B = B}
left-zero-blame-result rel vV′ =
  inj₂ (_ , R.[] , _ , _ , _ , nothing , boundary-refl ,
    refl , (blame ∎[]) , evolve-refl , evolve-refl)


record LeftValueCatchupResidualsAt (fuel : ℕ) : Set₁ where
  field
    source-operations : LSO.LeftSourceOperationsAt fuel

    paired-cast-row : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {M : Term Δᴸ} {M′ : Term Δᴿ}
        {A A′ : Ty Δᴸ} {B B′ : Ty Δᴿ}
        {ν : Env∼ Δᴸ} {ν′ : Env∼ Δᴿ}
        {c : ν ⊢ A ∼ A′} {c′ : ν′ ⊢ B ∼ B′}
        {q : A′ ⊑ᵂ⟨ W ⟩ B′}
      → (rel : W ∣ [] ⊢² M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ∶ q)
      → ParkedWorld W
      → Value (M′ ⟨ c′ ⟩)
      → SourceCastBound fuel rel
      → LeftCatchupResult
          {W = W} {Wᵖ = W}
          {kind = same-boundary}
          {Xᴸ? = nothing} {Xᴿ? = nothing}
          {M = M ⟨ c ⟩} {V′ = M′ ⟨ c′ ⟩} {A = A′} {B = B′}

    target-cast-row : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {M : Term Δᴸ} {M′ : Term Δᴿ}
        {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
        {ν′ : Env∼ Δᴿ} {c′ : ν′ ⊢ B ∼ B′}
        {q : A ⊑ᵂ⟨ W ⟩ B′}
      → (rel : W ∣ [] ⊢² M ⊑ M′ ⟨ c′ ⟩ ∶ q)
      → ParkedWorld W
      → Value (M′ ⟨ c′ ⟩)
      → SourceCastBound fuel rel
      → LeftCatchupResult
          {W = W} {Wᵖ = W}
          {kind = same-boundary}
          {Xᴸ? = nothing} {Xᴿ? = nothing}
          {M = M} {V′ = M′ ⟨ c′ ⟩} {A = A} {B = B′}

    target-reveal-row : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {M : Term Δᴸ} {M′ : Term Δᴿ}
        {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
        {c′ : Conv↑ Δᴿ B B′}
        {q : A ⊑ᵂ⟨ W ⟩ B′}
      → (rel : W ∣ [] ⊢² M ⊑ M′ ↑ c′ ∶ q)
      → ParkedWorld W
      → Value (M′ ↑ c′)
      → SourceCastBound fuel rel
      → LeftCatchupResult
          {W = W} {Wᵖ = W}
          {kind = same-boundary}
          {Xᴸ? = nothing} {Xᴿ? = nothing}
          {M = M} {V′ = M′ ↑ c′} {A = A} {B = B′}

    target-conceal-row : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {M : Term Δᴸ} {M′ : Term Δᴿ}
        {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
        {c′ : Conv↓ Δᴿ B B′}
        {q : A ⊑ᵂ⟨ W ⟩ B′}
      → (rel : W ∣ [] ⊢² M ⊑ M′ ↓ c′ ∶ q)
      → ParkedWorld W
      → Value (M′ ↓ c′)
      → SourceCastBound fuel rel
      → LeftCatchupResult
          {W = W} {Wᵖ = W}
          {kind = same-boundary}
          {Xᴸ? = nothing} {Xᴿ? = nothing}
          {M = M} {V′ = M′ ↓ c′} {A = A} {B = B′}

    source-reveal-row : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {M : Term Δᴸ} {V′ : Term Δᴿ}
        {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
        {c : Conv↑ Δᴸ A A′}
        {q : A′ ⊑ᵂ⟨ W ⟩ B}
      → (rel : W ∣ [] ⊢² M ↑ c ⊑ V′ ∶ q)
      → ParkedWorld W
      → Value V′
      → SourceCastBound fuel rel
      → LeftCatchupResult
          {W = W} {Wᵖ = W}
          {kind = same-boundary}
          {Xᴸ? = nothing} {Xᴿ? = nothing}
          {M = M ↑ c} {V′ = V′} {A = A′} {B = B}

    source-conceal-row : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {M : Term Δᴸ} {V′ : Term Δᴿ}
        {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
        {c : Conv↓ Δᴸ A A′}
        {q : A′ ⊑ᵂ⟨ W ⟩ B}
      → (rel : W ∣ [] ⊢² M ↓ c ⊑ V′ ∶ q)
      → ParkedWorld W
      → Value V′
      → SourceCastBound fuel rel
      → LeftCatchupResult
          {W = W} {Wᵖ = W}
          {kind = same-boundary}
          {Xᴸ? = nothing} {Xᴿ? = nothing}
          {M = M ↓ c} {V′ = V′} {A = A′} {B = B}

    paired-reveal-row : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {M : Term Δᴸ} {M′ : Term Δᴿ}
        {A A′ : Ty Δᴸ} {B B′ : Ty Δᴿ}
        {c : Conv↑ Δᴸ A A′} {c′ : Conv↑ Δᴿ B B′}
        {q : A′ ⊑ᵂ⟨ W ⟩ B′}
      → (rel : W ∣ [] ⊢² M ↑ c ⊑ M′ ↑ c′ ∶ q)
      → ParkedWorld W
      → Value (M′ ↑ c′)
      → SourceCastBound fuel rel
      → LeftCatchupResult
          {W = W} {Wᵖ = W}
          {kind = same-boundary}
          {Xᴸ? = nothing} {Xᴿ? = nothing}
          {M = M ↑ c} {V′ = M′ ↑ c′} {A = A′} {B = B′}

    paired-conceal-row : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {M : Term Δᴸ} {M′ : Term Δᴿ}
        {A A′ : Ty Δᴸ} {B B′ : Ty Δᴿ}
        {c : Conv↓ Δᴸ A A′} {c′ : Conv↓ Δᴿ B B′}
        {q : A′ ⊑ᵂ⟨ W ⟩ B′}
      → (rel : W ∣ [] ⊢² M ↓ c ⊑ M′ ↓ c′ ∶ q)
      → ParkedWorld W
      → Value (M′ ↓ c′)
      → SourceCastBound fuel rel
      → LeftCatchupResult
          {W = W} {Wᵖ = W}
          {kind = same-boundary}
          {Xᴸ? = nothing} {Xᴿ? = nothing}
          {M = M ↓ c} {V′ = M′ ↓ c′} {A = A′} {B = B′}

    packaged-seal-star-route2-row : ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ}
        {M : Term Δᴸ} {M′ : Term Δᴿ}
        {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
        {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Xᴿ)}
      → (rel : W ∣ [] ⊢²
          M ↓ seal Xᴸ ★ ⊑ M′ ↓ seal Xᴿ ★ ∶ q)
      → ParkedWorld W
      → Value (M′ ↓ seal Xᴿ ★)
      → SourceCastBound fuel rel
      → LeftCatchupResult
          {W = W} {Wᵖ = W}
          {kind = same-boundary}
          {Xᴸ? = nothing} {Xᴿ? = nothing}
          {M = M ↓ seal Xᴸ ★} {V′ = M′ ↓ seal Xᴿ ★}
          {A = ＇ Xᴸ} {B = ＇ Xᴿ}


left-value-catchup-with-residuals : ∀ {fuel}
  → LeftValueCatchupResidualsAt fuel
  → LeftValueCatchupAt fuel
left-value-catchup-with-residuals residuals parked (CTI2.x⊑x² ()) vV′ bound
left-value-catchup-with-residuals residuals parked
    rel@(CTI2.ƛ⊑ƛ² prem) vV′ bound =
  left-zero-value-result rel (CT.ƛ _) vV′
left-value-catchup-with-residuals residuals parked
    (CTI2.·⊑·² prem₁ prem₂) () bound
left-value-catchup-with-residuals residuals parked
    rel@(CTI2.Λ⊑Λ² liftγ vV vV′ prem q) target-value bound =
  left-zero-value-result rel (CT.Λ vV) target-value
left-value-catchup-with-residuals residuals parked
    rel@(CTI2.Λ⊑² Anv zero∈A liftγ vV target⊢ prem q) vV′ bound =
  left-zero-value-result rel (CT.Λ vV) vV′
left-value-catchup-with-residuals residuals parked
    rel@(CTI2.Λ⊑²-smart-comma Anv zero∈A liftW liftγ vV
      target⊢ prem q) vV′ bound =
  left-zero-value-result rel (CT.Λ vV) vV′
left-value-catchup-with-residuals residuals parked
    (CTI2.•⊑•² p∀ prem q r) () bound
left-value-catchup-with-residuals residuals parked
    (CTI2.•⊑² p∀ prem q r) vV′ bound =
  LSO.LeftSourceOperationsAt.left-source-type-app-catchup-at
    (LeftValueCatchupResidualsAt.source-operations residuals)
    parked prem vV′ bound
left-value-catchup-with-residuals residuals parked
    rel@(CTI2.κ⊑κ² κ p) vV′ bound =
  left-zero-value-result rel (CT.$ κ) vV′
left-value-catchup-with-residuals residuals parked
    rel@(CTI2.cast⊑cast² c c′ prem q) vV′ bound =
  LeftValueCatchupResidualsAt.paired-cast-row residuals rel parked vV′ bound
left-value-catchup-with-residuals residuals parked
    rel@(CTI2.⊑cast² c′ prem q) vV′ bound =
  LeftValueCatchupResidualsAt.target-cast-row residuals rel parked vV′ bound
left-value-catchup-with-residuals residuals parked
    rel@(CTI2.⊑reveal² mono rb sameγ c′⊢ prem q) vV′ bound =
  LeftValueCatchupResidualsAt.target-reveal-row residuals rel parked vV′ bound
left-value-catchup-with-residuals residuals parked
    rel@(CTI2.⊑conceal² mono rb sameγ c′⊢ prem q) vV′ bound =
  LeftValueCatchupResidualsAt.target-conceal-row residuals rel parked vV′ bound
left-value-catchup-with-residuals residuals parked
    rel@(CTI2.cast⊑² c prem q) vV′ (c<fuel , prem-bound) =
  LSO.LeftSourceOperationsAt.left-extra-cast-at
    (LeftValueCatchupResidualsAt.source-operations residuals)
    c c<fuel parked prem vV′ prem-bound
left-value-catchup-with-residuals residuals parked
    rel@(CTI2.reveal⊑² mono rb sameγ c⊢ prem q) vV′ bound =
  LeftValueCatchupResidualsAt.source-reveal-row residuals rel parked vV′ bound
left-value-catchup-with-residuals residuals parked
    rel@(CTI2.conceal⊑²-seal-star-open no-target mono rb sameγ c⊢ prem q)
    vV′ bound =
  LeftValueCatchupResidualsAt.source-conceal-row residuals rel parked vV′ bound
left-value-catchup-with-residuals residuals parked
    rel@(CTI2.conceal⊑²-source-ok ok mono rb sameγ c⊢ prem q) vV′ bound =
  LeftValueCatchupResidualsAt.source-conceal-row residuals rel parked vV′ bound
left-value-catchup-with-residuals residuals parked
    rel@(CTI2.reveal⊑reveal² mono rb sameγ c⊢ c′⊢ prem q) vV′ bound =
  LeftValueCatchupResidualsAt.paired-reveal-row residuals rel parked vV′ bound
left-value-catchup-with-residuals residuals parked
    rel@(CTI2.conceal⊑conceal² partner mono rb sameγ c⊢ c′⊢ prem q)
    vV′ bound =
  LeftValueCatchupResidualsAt.paired-conceal-row residuals rel parked vV′ bound
left-value-catchup-with-residuals residuals parked
    rel@(CTI2.packaged-seal-star² partner mono rb sameγ c⊢ c′⊢
      prem pkg-rel q) vV′ bound =
  LeftValueCatchupResidualsAt.packaged-seal-star-route2-row
    residuals rel parked vV′ bound
left-value-catchup-with-residuals residuals parked
    rel@(CTI2.blame⊑² target⊢ p) vV′ bound =
  left-zero-blame-result rel vV′
left-value-catchup-with-residuals residuals parked
    (CTI2.⊕⊑⊕² op prem₁ prem₂ r) () bound
