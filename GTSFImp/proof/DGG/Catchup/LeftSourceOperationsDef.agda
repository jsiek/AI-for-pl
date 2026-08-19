module proof.DGG.Catchup.LeftSourceOperationsDef where

-- File Charter:
--   * States the source operational package surfaces consumed by left
--     catch-up.
--   * Packages source casts, source type application, source reveal/conceal,
--     route-2 packaged seal-star, and blame-lift workers.
--   * Records the two-sided peel interfaces as explicit parameters rather
--     than deriving one-sided peels.
--   * Contains no catch-up proof.

import Data.Fin as Fin
import Data.Nat as Nat
open import Data.List using ([])
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _<_)
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Types
  using (Ty; TyCtx; TyVar; NonVar; _∈ᵗ_; ★; ＇_; `∀; ⇑ᵗ; _[_]ᵗ)
open import Consistency using (Env∼; _⊢_∼_; instᵐ; inst_; ↑ᶜ_)
open import Conversion using (Conv↑; Conv↓; seal)
open import CastTerms using (Term; Value; blame; _⟨_⟩; _↑_; _↓_; _⦂∀_[_])
open import Reduction using (StoreChanges; _—↠[_]_)
import Reduction as R
open import proof.Consistency using (castSize)
import proof.DGG.CtxImp as CTI2
import proof.DGG.CastTermImprecision as CTIR
open import proof.DGG.Catchup.LeftBoundaryCatchupDef
  using (LeftCatchupResult)
open import proof.DGG.Catchup.LeftValueCatchupDef
  using (LeftValueCatchupAt; SourceCastBound)
open import proof.DGG.CatchupToMorePreciseDef
  using (same-boundary)
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedEvolve; ParkedWorld)
open import proof.DGG.SimConcealRevealPeel
  using (PairedConcealRevealPeelᵀ; SourceOnlyConcealRevealPeelᵀ)
open CTI2 using
  (World;
   _⊑ᵂ⟨_⟩_)
open CTIR using (_∣_⊢²_⊑_∶_)


LeftExtraCastAt : ℕ → Set
LeftExtraCastAt fuel =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
    {ν : Env∼ Δᴸ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (c : ν ⊢ A ∼ A′)
  → castSize c < fuel
  → ParkedWorld W
  → (rel : W ∣ [] ⊢² M ⊑ V′ ∶ p)
  → Value V′
  → SourceCastBound fuel rel
  → LeftCatchupResult
      {W = W} {Wᵖ = W}
      {kind = same-boundary}
      {Xᴸ? = nothing} {Xᴿ? = nothing}
      {M = M ⟨ c ⟩} {V′ = V′} {A = A′} {B = B}


LeftInstCatchupAt : ℕ → Set
LeftInstCatchupAt fuel =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {V : Term Δᴸ} {V′ : Term Δᴿ}
    {A : Ty (Nat.suc Δᴸ)} {A′ : Ty Δᴸ} {B : Ty Δᴿ}
    {ν : Env∼ Δᴸ}
    {p : `∀ A ⊑ᵂ⟨ W ⟩ B}
  → ParkedWorld W
  → W ∣ [] ⊢² V ⊑ V′ ∶ p
  → Value V
  → Value V′
  → (c : instᵐ ν ⊢ A ∼ ⇑ᵗ A′)
  → ⦃ Anv : NonVar A ⦄
  → ⦃ zero∈A : Fin.zero ∈ᵗ A ⦄
  → (A′≢★ : A′ ≢ ★)
  → castSize ((inst c) A′≢★) < fuel
  → LeftCatchupResult
      {W = W} {Wᵖ = W}
      {kind = same-boundary}
      {Xᴸ? = nothing} {Xᴿ? = nothing}
      {M = V ⟨ (inst c) A′≢★ ⟩}
      {V′ = V′} {A = A′} {B = B}


LeftSourceTypeAppCatchupAt : ℕ → Set
LeftSourceTypeAppCatchupAt fuel =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {C : Ty (Nat.suc Δᴸ)} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p∀ : `∀ C ⊑ᵂ⟨ W ⟩ B}
  → ParkedWorld W
  → (rel : W ∣ [] ⊢² M ⊑ V′ ∶ p∀)
  → Value V′
  → SourceCastBound fuel rel
  → LeftCatchupResult
      {W = W} {Wᵖ = W}
      {kind = same-boundary}
      {Xᴸ? = nothing} {Xᴿ? = nothing}
      {M = M ⦂∀ C [ A ]} {V′ = V′}
      {A = C [ A ]ᵗ} {B = B}


LeftSourceRevealCatchupAt : ℕ → Set
LeftSourceRevealCatchupAt fuel =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (c : Conv↑ Δᴸ A A′)
  → ParkedWorld W
  → (rel : W ∣ [] ⊢² M ⊑ V′ ∶ p)
  → Value V′
  → SourceCastBound fuel rel
  → LeftCatchupResult
      {W = W} {Wᵖ = W}
      {kind = same-boundary}
      {Xᴸ? = nothing} {Xᴿ? = nothing}
      {M = M ↑ c} {V′ = V′} {A = A′} {B = B}


LeftSourceConcealCatchupAt : ℕ → Set
LeftSourceConcealCatchupAt fuel =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (c : Conv↓ Δᴸ A A′)
  → ParkedWorld W
  → (rel : W ∣ [] ⊢² M ⊑ V′ ∶ p)
  → Value V′
  → SourceCastBound fuel rel
  → LeftCatchupResult
      {W = W} {Wᵖ = W}
      {kind = same-boundary}
      {Xᴸ? = nothing} {Xᴿ? = nothing}
      {M = M ↓ c} {V′ = V′} {A = A′} {B = B}


LeftPackagedSealStarRoute2At : ℕ → Set
LeftPackagedSealStarRoute2At fuel =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ} {Xᴿ?}
    {p★ : ★ ⊑ᵂ⟨ W ⟩ ★}
    {qᵖ : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ ★}
  → CTI2.MatchedConcealPartnerOK W M (seal Xᴸ ★) Xᴿ? M′
  → ParkedWorld W
  → (rel : W ∣ [] ⊢² M ⊑ M′ ∶ p★)
  → (pkg-rel : W ∣ [] ⊢² M ↓ seal Xᴸ ★ ⊑ M′ ∶ qᵖ)
  → Value (M′ ↓ seal Xᴿ ★)
  → SourceCastBound fuel rel
  → SourceCastBound fuel pkg-rel
  → LeftCatchupResult
      {W = W} {Wᵖ = W}
      {kind = same-boundary}
      {Xᴸ? = nothing} {Xᴿ? = nothing}
      {M = M ↓ seal Xᴸ ★} {V′ = M′ ↓ seal Xᴿ ★}
      {A = ＇ Xᴸ} {B = ＇ Xᴿ}


LeftBlameCastLiftAt : Set
LeftBlameCastLiftAt =
  ∀ {Δᴸ Δᴸ′ Δᴿ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ Δ′}
    {M : Term Δᴸ} {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {ν : Env∼ Δᴸ} {A A′ : Ty Δᴸ}
  → (c : ν ⊢ A ∼ A′)
  → M —↠[ χsᴸ ] blame
  → ParkedEvolve χsᴸ R.[] W W′
  → Σ[ Δᴸ″ ∈ TyCtx ] Σ[ ψsᴸ ∈ StoreChanges Δᴸ Δᴸ″ ]
    Σ[ Δ″ ∈ TyCtx ] Σ[ W″ ∈ World Δᴸ″ Δᴿ Δ″ ]
      (M ⟨ c ⟩ —↠[ ψsᴸ ] blame) ×
      ParkedEvolve ψsᴸ R.[] W W″


LeftBlameRevealLiftAt : Set
LeftBlameRevealLiftAt =
  ∀ {Δᴸ Δᴸ′ Δᴿ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ Δ′}
    {M : Term Δᴸ} {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {A A′ : Ty Δᴸ}
  → (c : Conv↑ Δᴸ A A′)
  → M —↠[ χsᴸ ] blame
  → ParkedEvolve χsᴸ R.[] W W′
  → Σ[ Δᴸ″ ∈ TyCtx ] Σ[ ψsᴸ ∈ StoreChanges Δᴸ Δᴸ″ ]
    Σ[ Δ″ ∈ TyCtx ] Σ[ W″ ∈ World Δᴸ″ Δᴿ Δ″ ]
      (M ↑ c —↠[ ψsᴸ ] blame) ×
      ParkedEvolve ψsᴸ R.[] W W″


LeftBlameConcealLiftAt : Set
LeftBlameConcealLiftAt =
  ∀ {Δᴸ Δᴸ′ Δᴿ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ Δ′}
    {M : Term Δᴸ} {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {A A′ : Ty Δᴸ}
  → (c : Conv↓ Δᴸ A A′)
  → M —↠[ χsᴸ ] blame
  → ParkedEvolve χsᴸ R.[] W W′
  → Σ[ Δᴸ″ ∈ TyCtx ] Σ[ ψsᴸ ∈ StoreChanges Δᴸ Δᴸ″ ]
    Σ[ Δ″ ∈ TyCtx ] Σ[ W″ ∈ World Δᴸ″ Δᴿ Δ″ ]
      (M ↓ c —↠[ ψsᴸ ] blame) ×
      ParkedEvolve ψsᴸ R.[] W W″


record LeftTwoSidedPeelPackage : Set where
  field
    paired-conceal-reveal-peel : PairedConcealRevealPeelᵀ
    source-only-conceal-reveal-peel : SourceOnlyConcealRevealPeelᵀ


record LeftSourceOperationsAt (fuel : ℕ) : Set₁ where
  field
    left-extra-cast-at : LeftExtraCastAt fuel
    left-inst-catchup-at : LeftInstCatchupAt fuel
    left-source-type-app-catchup-at : LeftSourceTypeAppCatchupAt fuel
    left-source-reveal-catchup-at : LeftSourceRevealCatchupAt fuel
    left-source-conceal-catchup-at : LeftSourceConcealCatchupAt fuel
    left-packaged-seal-star-route2-at : LeftPackagedSealStarRoute2At fuel
    left-blame-cast-lift-at : LeftBlameCastLiftAt
    left-blame-reveal-lift-at : LeftBlameRevealLiftAt
    left-blame-conceal-lift-at : LeftBlameConcealLiftAt
    left-two-sided-peels : LeftTwoSidedPeelPackage


record LeftFuelKnot (fuel : ℕ) : Set₁ where
  field
    left-source-operations-at : LeftSourceOperationsAt fuel
    left-value-catchup-at : LeftValueCatchupAt fuel


record LeftFuelStepSurface (fuel : ℕ) : Set₁ where
  field
    smaller-left-source-operations :
      ∀ {m} → m < fuel → LeftSourceOperationsAt m
    smaller-left-value :
      ∀ {m} → m < fuel → LeftValueCatchupAt m
