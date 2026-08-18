module proof.DGG.Catchup.FuelDischargeProof where

-- File Charter:
--   * Discharges the derivation-indexed target-cast fuel obligation for
--     `ValueCatchupRightAt`.
--   * Builds a fuel and `TargetCastBound` witness by structural recursion on
--     the live CTI2 derivation.
--   * Composes the builder with a fuel-indexed value-catch-up driver, and
--     exports the FuelKnot factory-parametric `ValueCatchupRight²` adapter.

open import Data.Nat using (ℕ; suc; _<_; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (tt)

open import Types using (Ty)
open import CastTerms using (Term; Value)
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (castSize; TargetCastBound; ValueCatchupRight²; ValueCatchupRightAt;
   FuelKnot)
open import proof.DGG.Catchup.FuelKnotProof using
  (ExtraCastFactory; ValueCatchupFactory; InstCatchupFactory;
   build-fuel-knot)


≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
≤-step z≤n = z≤n
≤-step (s≤s m≤n) = s≤s (≤-step m≤n)


target-cast-bound-mono : ∀ {fuel fuel′ Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
    {rel : W ∣ γ ⊢² M ⊑ M′ ∶ q}
  → fuel ≤ fuel′
  → TargetCastBound fuel rel
  → TargetCastBound fuel′ rel
target-cast-bound-mono {rel = CTI2.x⊑x² x∈} fuel≤fuel′ bound = tt
target-cast-bound-mono {rel = CTI2.ƛ⊑ƛ² rel} fuel≤fuel′ bound =
  target-cast-bound-mono {rel = rel} fuel≤fuel′ bound
target-cast-bound-mono {rel = CTI2.·⊑·² rel₁ rel₂}
    fuel≤fuel′ (bound₁ , bound₂) =
  target-cast-bound-mono {rel = rel₁} fuel≤fuel′ bound₁ ,
  target-cast-bound-mono {rel = rel₂} fuel≤fuel′ bound₂
target-cast-bound-mono {rel = CTI2.Λ⊑Λ² liftγ vV vV′ rel q}
    fuel≤fuel′ bound =
  target-cast-bound-mono {rel = rel} fuel≤fuel′ bound
target-cast-bound-mono {rel = CTI2.Λ⊑² Anv z∈A liftγ vV M⊢ rel q}
    fuel≤fuel′ bound =
  target-cast-bound-mono {rel = rel} fuel≤fuel′ bound
target-cast-bound-mono
    {rel = CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vV M⊢ rel q}
    fuel≤fuel′ bound =
  target-cast-bound-mono {rel = rel} fuel≤fuel′ bound
target-cast-bound-mono {rel = CTI2.•⊑•² p∀ rel q r}
    fuel≤fuel′ bound =
  target-cast-bound-mono {rel = rel} fuel≤fuel′ bound
target-cast-bound-mono {rel = CTI2.•⊑² p∀ rel q r}
    fuel≤fuel′ bound =
  target-cast-bound-mono {rel = rel} fuel≤fuel′ bound
target-cast-bound-mono {rel = CTI2.κ⊑κ² κ p} fuel≤fuel′ bound = tt
target-cast-bound-mono {rel = CTI2.cast⊑cast² c c′ rel q}
    fuel≤fuel′ (c′<fuel , bound) =
  ≤-trans c′<fuel fuel≤fuel′ ,
  target-cast-bound-mono {rel = rel} fuel≤fuel′ bound
target-cast-bound-mono {rel = CTI2.⊑cast² c′ rel q}
    fuel≤fuel′ (c′<fuel , bound) =
  ≤-trans c′<fuel fuel≤fuel′ ,
  target-cast-bound-mono {rel = rel} fuel≤fuel′ bound
target-cast-bound-mono {rel = CTI2.⊑reveal² mono rb sameγ c′⊢ rel q}
    fuel≤fuel′ bound =
  target-cast-bound-mono {rel = rel} fuel≤fuel′ bound
target-cast-bound-mono {rel = CTI2.⊑conceal² mono rb sameγ c′⊢ rel q}
    fuel≤fuel′ bound =
  target-cast-bound-mono {rel = rel} fuel≤fuel′ bound
target-cast-bound-mono {rel = CTI2.cast⊑² c rel q}
    fuel≤fuel′ bound =
  target-cast-bound-mono {rel = rel} fuel≤fuel′ bound
target-cast-bound-mono {rel = CTI2.reveal⊑² mono rb sameγ c⊢ rel q}
    fuel≤fuel′ bound =
  target-cast-bound-mono {rel = rel} fuel≤fuel′ bound
target-cast-bound-mono
    {rel = CTI2.conceal⊑² partner mono rb sameγ c⊢ rel q}
    fuel≤fuel′ bound =
  target-cast-bound-mono {rel = rel} fuel≤fuel′ bound
target-cast-bound-mono
    {rel = CTI2.reveal⊑reveal² mono rb sameγ c⊢ c′⊢ rel q}
    fuel≤fuel′ bound =
  target-cast-bound-mono {rel = rel} fuel≤fuel′ bound
target-cast-bound-mono
    {rel = CTI2.conceal⊑conceal² partner mono rb sameγ c⊢ c′⊢ rel q}
    fuel≤fuel′ bound =
  target-cast-bound-mono {rel = rel} fuel≤fuel′ bound
target-cast-bound-mono
    {rel =
      CTI2.packaged-seal-star² partner mono rb sameγ c⊢ c′⊢
        rel pkg-rel q}
    fuel≤fuel′ (bound , pkg-bound) =
  target-cast-bound-mono {rel = rel} fuel≤fuel′ bound ,
  target-cast-bound-mono {rel = pkg-rel} fuel≤fuel′ pkg-bound
target-cast-bound-mono {rel = CTI2.blame⊑² M′⊢ p} fuel≤fuel′ bound =
  tt
target-cast-bound-mono {rel = CTI2.⊕⊑⊕² op rel₁ rel₂ r}
    fuel≤fuel′ (bound₁ , bound₂) =
  target-cast-bound-mono {rel = rel₁} fuel≤fuel′ bound₁ ,
  target-cast-bound-mono {rel = rel₂} fuel≤fuel′ bound₂


⊢²-target-cast-bound : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → (rel : W ∣ γ ⊢² M ⊑ M′ ∶ q)
  → Σ[ fuel ∈ ℕ ] TargetCastBound fuel rel
⊢²-target-cast-bound (CTI2.x⊑x² x∈) = 0 , tt
⊢²-target-cast-bound (CTI2.ƛ⊑ƛ² rel) = ⊢²-target-cast-bound rel
⊢²-target-cast-bound (CTI2.·⊑·² rel₁ rel₂)
  with ⊢²-target-cast-bound rel₁ | ⊢²-target-cast-bound rel₂
⊢²-target-cast-bound (CTI2.·⊑·² rel₁ rel₂)
  | fuel₁ , bound₁ | fuel₂ , bound₂ =
  fuel₁ ⊔ fuel₂ ,
  target-cast-bound-mono {rel = rel₁} (m≤m⊔n fuel₁ fuel₂) bound₁ ,
  target-cast-bound-mono {rel = rel₂} (m≤n⊔m fuel₁ fuel₂) bound₂
⊢²-target-cast-bound (CTI2.Λ⊑Λ² liftγ vV vV′ rel q) =
  ⊢²-target-cast-bound rel
⊢²-target-cast-bound (CTI2.Λ⊑² Anv z∈A liftγ vV M⊢ rel q) =
  ⊢²-target-cast-bound rel
⊢²-target-cast-bound
    (CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vV M⊢ rel q) =
  ⊢²-target-cast-bound rel
⊢²-target-cast-bound (CTI2.•⊑•² p∀ rel q r) =
  ⊢²-target-cast-bound rel
⊢²-target-cast-bound (CTI2.•⊑² p∀ rel q r) =
  ⊢²-target-cast-bound rel
⊢²-target-cast-bound (CTI2.κ⊑κ² κ p) = 0 , tt
⊢²-target-cast-bound (CTI2.cast⊑cast² c c′ rel q)
  with ⊢²-target-cast-bound rel
⊢²-target-cast-bound (CTI2.cast⊑cast² c c′ rel q) | fuel , bound =
  suc (castSize c′ ⊔ fuel) ,
  s≤s (m≤m⊔n (castSize c′) fuel) ,
  target-cast-bound-mono {rel = rel}
    (≤-step (m≤n⊔m (castSize c′) fuel)) bound
⊢²-target-cast-bound (CTI2.⊑cast² c′ rel q)
  with ⊢²-target-cast-bound rel
⊢²-target-cast-bound (CTI2.⊑cast² c′ rel q) | fuel , bound =
  suc (castSize c′ ⊔ fuel) ,
  s≤s (m≤m⊔n (castSize c′) fuel) ,
  target-cast-bound-mono {rel = rel}
    (≤-step (m≤n⊔m (castSize c′) fuel)) bound
⊢²-target-cast-bound (CTI2.⊑reveal² mono rb sameγ c′⊢ rel q) =
  ⊢²-target-cast-bound rel
⊢²-target-cast-bound (CTI2.⊑conceal² mono rb sameγ c′⊢ rel q) =
  ⊢²-target-cast-bound rel
⊢²-target-cast-bound (CTI2.cast⊑² c rel q) = ⊢²-target-cast-bound rel
⊢²-target-cast-bound (CTI2.reveal⊑² mono rb sameγ c⊢ rel q) =
  ⊢²-target-cast-bound rel
⊢²-target-cast-bound (CTI2.conceal⊑² partner mono rb sameγ c⊢ rel q) =
  ⊢²-target-cast-bound rel
⊢²-target-cast-bound
    (CTI2.reveal⊑reveal² mono rb sameγ c⊢ c′⊢ rel q) =
  ⊢²-target-cast-bound rel
⊢²-target-cast-bound
    (CTI2.conceal⊑conceal² partner mono rb sameγ c⊢ c′⊢ rel q) =
  ⊢²-target-cast-bound rel
⊢²-target-cast-bound
    (CTI2.packaged-seal-star² partner mono rb sameγ c⊢ c′⊢
      rel pkg-rel q)
  with ⊢²-target-cast-bound rel | ⊢²-target-cast-bound pkg-rel
⊢²-target-cast-bound
    (CTI2.packaged-seal-star² partner mono rb sameγ c⊢ c′⊢
      rel pkg-rel q)
  | fuel , bound | pkg-fuel , pkg-bound =
  fuel ⊔ pkg-fuel ,
  target-cast-bound-mono {rel = rel} (m≤m⊔n fuel pkg-fuel) bound ,
  target-cast-bound-mono {rel = pkg-rel}
    (m≤n⊔m fuel pkg-fuel) pkg-bound
⊢²-target-cast-bound (CTI2.blame⊑² M′⊢ p) = 0 , tt
⊢²-target-cast-bound (CTI2.⊕⊑⊕² op rel₁ rel₂ r)
  with ⊢²-target-cast-bound rel₁ | ⊢²-target-cast-bound rel₂
⊢²-target-cast-bound (CTI2.⊕⊑⊕² op rel₁ rel₂ r)
  | fuel₁ , bound₁ | fuel₂ , bound₂ =
  fuel₁ ⊔ fuel₂ ,
  target-cast-bound-mono {rel = rel₁} (m≤m⊔n fuel₁ fuel₂) bound₁ ,
  target-cast-bound-mono {rel = rel₂} (m≤n⊔m fuel₁ fuel₂) bound₂


value-catchup-right²-from-at : (∀ fuel → ValueCatchupRightAt fuel)
  → ValueCatchupRight²
value-catchup-right²-from-at value-at vM rel
  with ⊢²-target-cast-bound rel
value-catchup-right²-from-at value-at vM rel | fuel , bound =
  value-at fuel vM rel bound


value-catchup-right²-from-fuel-knot-factories : ExtraCastFactory
  → ValueCatchupFactory
  → InstCatchupFactory
  → ValueCatchupRight²
value-catchup-right²-from-fuel-knot-factories
    extra-factory value-factory inst-factory =
  value-catchup-right²-from-at
    (λ fuel → FuelKnot.value-catchup-at
      (build-fuel-knot extra-factory value-factory inst-factory fuel))
