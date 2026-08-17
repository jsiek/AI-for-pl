module proof.DGG.Catchup.ValueCatchupRightProof where

-- File Charter:
--   * Proves the fuel-indexed M6 value catch-up worker for provenance-carrying
--     cast columns.
--   * Processes one full-provenance head cast, transports and re-heads the
--     term-independent tail, and recurses at a strict tail-size bound.
--   * Depends on the current-fuel extra-cast worker and the smaller-fuel
--     surface, plus the cast-column transport and composition support.

open import Data.Nat using (zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-<-trans; +-mono-≤; m≤m+n; n<1+n)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym)
  renaming (subst to subst≡)

open import Types
open import Consistency using
  (Env∼; _⊢_∼_; id; _↦_; ∀ᶜ_; _!; ？_; inst_; gen_;
   bot-elim; bot-intro)
open import CastTerms using (Term; Value)
open import Reduction using
  (StoreChanges; _—↠[_]_; []; ↠-refl; applyTys)

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
import proof.Imprecision as PI
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (castSize; CastColumn; []ᶜ; _▻ᶜ_; columnSize; applyColumn;
   mapColumn; _++χ_; CatchupColumn⁻; ccol⁻-[]; ccol⁻-▻;
   CatchupColumn; ccol-[]; ccol-▻; ExtraCastRightAt;
   ValueCatchupRightProvAt; FuelStepSurface)
open import proof.DGG.Catchup.ColumnSupportProof using
  (columnSize-map; composeWorldExtendᴿ; mapCtxᴿ-compose;
   composeReduction; liftReductionThroughColumn; catchup⁻-embed;
   catchup-column⁻-transport; applyTys-++)


castSize-positive : ∀ {Δ} {ν : Env∼ Δ} {A B : Ty Δ}
  → (c : ν ⊢ A ∼ B)
  → suc zero ≤ castSize c
castSize-positive (id a) = s≤s z≤n
castSize-positive (c ↦ d) = s≤s z≤n
castSize-positive (∀ᶜ c) = s≤s z≤n
castSize-positive (_! c) = s≤s z≤n
castSize-positive (？ c) = s≤s z≤n
castSize-positive (inst_ c B≢★) = s≤s z≤n
castSize-positive (gen_ c A≢★) = s≤s z≤n
castSize-positive bot-elim = s≤s z≤n
castSize-positive bot-intro = s≤s z≤n


head-size<column-fuel : ∀ {Δ} {ν : Env∼ Δ} {A B C : Ty Δ}
    {fuel} (c : ν ⊢ A ∼ B) (κ : CastColumn B C)
  → columnSize (c ▻ᶜ κ) < fuel
  → castSize c < fuel
head-size<column-fuel c κ total<fuel =
  ≤-<-trans (m≤m+n (castSize c) (columnSize κ)) total<fuel


tail-size<column-fuel : ∀ {Δ} {ν : Env∼ Δ} {A B C : Ty Δ}
    {fuel} (c : ν ⊢ A ∼ B) (κ : CastColumn B C)
  → columnSize (c ▻ᶜ κ) < fuel
  → suc (columnSize κ) < fuel
tail-size<column-fuel c κ total<fuel =
  ≤-<-trans (+-mono-≤ (castSize-positive c) ≤-refl) total<fuel


column-tail-rehead : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {A : Ty Δᴸ}
    {B B′ : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
    {κ : CastColumn B B′}
  → (N : Term Δᴿ)
  → CatchupColumn⁻ {W = W} {A = A} p κ q
  → CatchupColumn {W = W} {A = A} N p κ q
column-tail-rehead N ccol⁻-[] = ccol-[]
column-tail-rehead N (ccol⁻-▻ k ks) = ccol-▻ (catchup⁻-embed N k) ks


⊢²-retarget : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p q : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ N ∶ p
  → W ∣ γ ⊢² M ⊑ N ∶ q
⊢²-retarget {W = W} {γ = γ} {M = M} {N = N} {p = p} {q = q} d =
  subst≡ (λ r → W ∣ γ ⊢² M ⊑ N ∶ r) (PI.⊑-unique p q) d


rel-target-transportᴿ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
  → (eq : B ≡ B′)
  → (p : A ⊑ᵂ⟨ W ⟩ B)
  → W ∣ γ ⊢² M ⊑ N ∶ p
  → W ∣ γ ⊢² M ⊑ N ∶
      subst≡ (λ C → A ⊑ᵂ⟨ W ⟩ C) eq p
rel-target-transportᴿ refl p rel = rel


value-catchup-right-prov-at : ∀ {fuel}
  → ExtraCastRightAt fuel
  → FuelStepSurface fuel
  → ValueCatchupRightProvAt fuel
value-catchup-right-prov-at extra fuel-step
    {Δᴿ = Δᴿ} {Δ = Δ} {W = W} {γ = γ}
    rel vM vM′ []ᶜ column<fuel q ccol-[] =
  Δᴿ , [] , Δ , W , ECR.sameWorldExtendᴿ , _ , vM′ , ↠-refl ,
  subst≡
    (λ γ′ → W ∣ γ′ ⊢² _ ⊑ _ ∶ q)
    (sym (ECR.mapCtxᴿ-same γ))
    (⊢²-retarget rel)
value-catchup-right-prov-at extra fuel-step
    {γ = γ} {M = M} {B′ = B′}
    rel vM vM′ (c ▻ᶜ κ) column<fuel q (ccol-▻ head tail)
    with extra rel vM vM′ c
      (head-size<column-fuel c κ column<fuel) _ head
... | Δᴿ₁ , χs , Δ₁ , W₁ , ext₁ , N₁ ,
      (vN₁ , head↠N₁ , rel₁)
    with FuelStepSurface.smaller-value fuel-step
      (tail-size<column-fuel c κ column<fuel)
      rel₁ vM vN₁ (mapColumn χs κ)
      (subst≡ (λ n → n < suc (columnSize κ))
        (sym (columnSize-map χs κ)) (n<1+n (columnSize κ)))
      (ECR.transport⊑ᵂ ext₁ q)
      (column-tail-rehead N₁
        (catchup-column⁻-transport ext₁ tail))
... | Δᴿ₂ , ψs , Δ₂ , W₂ , ext₂ , N₂ ,
      (vN₂ , tail↠N₂ , rel₂) =
  Δᴿ₂ , χs ++χ ψs , Δ₂ , W₂ ,
  composeWorldExtendᴿ ext₁ ext₂ , N₂ , vN₂ ,
  composeReduction
    (liftReductionThroughColumn κ head↠N₁) tail↠N₂ ,
  subst≡
    (λ γ′ → W₂ ∣ γ′ ⊢² M ⊑ N₂ ∶
      ECR.transport⊑ᵂ (composeWorldExtendᴿ ext₁ ext₂) q)
    (mapCtxᴿ-compose ext₁ ext₂ γ)
    (⊢²-retarget
      (rel-target-transportᴿ (applyTys-++ χs ψs B′)
        (ECR.transport⊑ᵂ ext₂ (ECR.transport⊑ᵂ ext₁ q)) rel₂))
