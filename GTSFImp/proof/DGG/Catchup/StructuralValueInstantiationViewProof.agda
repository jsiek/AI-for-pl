module
  proof.DGG.Catchup.StructuralValueInstantiationViewProof where

-- File Charter:
--   * Inverts a related value source against a target type application.
--   * Confirms that every recursive case exposes a relation subderivation.

open import Data.Nat using (suc)
open import Data.Empty using (⊥)
open import Types using (Ty; _[_]ᵗ)
import CastTerms
open import CastTerms using (Term; Value; _⦂∀_[_])
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open CTX using
  (World;
   CtxImp;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)
open import
  proof.DGG.Catchup.StructuralValueInstantiationViewDef


value-type-app-source-view : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {L : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {C : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B [ C ]ᵗ}
  → W ∣ γ ⊢² M ⊑ L ⦂∀ B [ C ] ∶ q
  → Value M
  → ValueTypeAppSourceView M
value-type-app-source-view (CTI2.Λ⊑² Anv z∈A liftγ
    vV target⊢ prem q) (CastTerms.Λ vV′) =
  type-app-source-Λ vV
value-type-app-source-view (CTI2.Λ⊑²-smart-comma Anv z∈A
    liftW liftγ vV target⊢ prem q) (CastTerms.Λ vV′) =
  type-app-source-Λ vV
value-type-app-source-view (CTI2.cast⊑² c prem q)
    (vV′ CastTerms.《 inert 》) =
  type-app-source-cast vV′ inert
value-type-app-source-view (CTI2.reveal⊑² mono rb sc c⊢ prem q)
    (vV′ CastTerms.↑ rv) =
  type-app-source-reveal vV′ rv
value-type-app-source-view
    (CTI2.conceal⊑²-seal-star-open no-target mono rb sc c⊢ prem q)
    (vV′ CastTerms.↓ cv) =
  type-app-source-conceal vV′ cv
value-type-app-source-view
    (CTI2.conceal⊑²-source-ok ok mono rb sc c⊢ prem q)
    (vV′ CastTerms.↓ cv) =
  type-app-source-conceal vV′ cv


no-value-source-type-app : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {L : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {C : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B [ C ]ᵗ}
  → W ∣ γ ⊢² M ⊑ L ⦂∀ B [ C ] ∶ q
  → Value M
  → ⊥
no-value-source-type-app (CTI2.Λ⊑² Anv z∈A liftγ
    vV target⊢ prem q) (CastTerms.Λ vV′) =
  no-value-source-type-app prem vV
no-value-source-type-app (CTI2.Λ⊑²-smart-comma Anv z∈A
    liftW liftγ vV target⊢ prem q) (CastTerms.Λ vV′) =
  no-value-source-type-app prem vV
no-value-source-type-app (CTI2.cast⊑² c prem q)
    (vV CastTerms.《 inert 》) =
  no-value-source-type-app prem vV
no-value-source-type-app (CTI2.reveal⊑² mono rb sc c⊢ prem q)
    (vV CastTerms.↑ rv) =
  no-value-source-type-app prem vV
no-value-source-type-app
    (CTI2.conceal⊑²-seal-star-open no-target mono rb sc c⊢ prem q)
    (vV CastTerms.↓ cv) =
  no-value-source-type-app prem vV
no-value-source-type-app
    (CTI2.conceal⊑²-source-ok ok mono rb sc c⊢ prem q)
    (vV CastTerms.↓ cv) =
  no-value-source-type-app prem vV
