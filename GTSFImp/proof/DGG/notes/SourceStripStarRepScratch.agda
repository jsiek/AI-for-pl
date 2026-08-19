module SourceStripStarRepScratch where

-- Scratch validation for the M3 source-strip star-representation repair.
-- Checks that the source-only `★` seal is rebuilt against the premise-side
-- target core, and only then optionally rewrapped by the source injection.

open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (sym)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (seal)
open import CastTerms using (Term; _↓_; _⟨_⟩)
open import Imprecision
import CastTerms
import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Inversion.SpineValueDef using
  (variable-obligation-aligns)

open CTX using
  (World;
   CtxImp;
   TagRebaseAtᴸ;
   _⊑ᵂ⟨_⟩_;
   sourceStoreʷ)
open CTI2 using (_∣_⊢²_⊑_∶_)

rebase-only-star-rep-no-var-target :
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → TagRebaseAtᴸ W W (just X) nothing
  → (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)
  → ⊥
rebase-only-star-rep-no-var-target {W = W} {X = X} {Y = Y}
    (CTX.tag-rebase-onlyᴸ to-star disaligned represented) q =
  disaligned Y (sym (variable-obligation-aligns {W = W} {X = X} {Y = Y} q))

plain-star-rep-premise :
  ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {p : ★ ⊑ᵂ⟨ W′ ⟩ ★}
    {q : (＇ X) ⊑ᵂ⟨ W ⟩ ★}
  → CTX.ImpEnvMono W W′
  → TagRebaseAtᴸ W′ W (just X) Xᴿ?
  → CTX.SameCtx γ γ′
  → sourceStoreʷ W ∋ X ⦂ ★
  → W′ ∣ γ′ ⊢² V ⊑ U ∶ p
  → W ∣ γ ⊢² V ↓ seal X ★ ⊑ U ∶ q
plain-star-rep-premise mono rb sc X∈ prem =
  CTI2.conceal⊑²
    (CTX.seal-partner-ok CTX.star-rep-target)
    mono rb sc (Conv.⊢↓-sealˣ X∈) prem _

injected-star-rep-premise :
  ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X) ∼ ★}
    {p : ★ ⊑ᵂ⟨ W′ ⟩ ★}
    {q : (＇ X) ⊑ᵂ⟨ W ⟩ ★}
  → CTX.ImpEnvMono W W′
  → TagRebaseAtᴸ W′ W (just X) Xᴿ?
  → CTX.SameCtx γ γ′
  → sourceStoreʷ W ∋ X ⦂ ★
  → CastTerms.Inert c
  → W′ ∣ γ′ ⊢² V ⊑ U ∶ p
  → W ∣ γ ⊢² (V ↓ seal X ★) ⟨ c ⟩ ⊑ U ∶ ★⊑★
injected-star-rep-premise {c = c} {q = q} mono rb sc X∈ inert prem =
  CTI2.cast⊑² {p = q} c
    (plain-star-rep-premise mono rb sc X∈ prem)
    ★⊑★
