module proof.DGG.Catchup.StructuralTargetFrameAbsorptionDef where

-- File Charter:
--   * Defines the target-frame absorption chain for structural value
--     instantiation spines.
--   * Records neutral target-only cast, reveal, and conceal premises.
--   * Provides checked root and strict-child constructor cells used by the
--     generalized structural worker.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; TyVar; ＇_; `∀; _[_]ᵗ)
open import Consistency using (Env∼; extᵐ; _⊢_∼_; _[_]ᶜ)
open import Conversion using (Conv↑; Conv↓)
open import CastTerms using (Term; Value; _⟨_⟩; _↑_; _↓_)
open import Reduction using
  (StoreChanges; keep; bind; applyBody; _—→[_]_)
open import proof.TypeSafety.Preservation using
  (applyBody-open-zero; replace-zero-open)
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.ConversionPivotAlignment using
  (generator-absent; revealGeneratorPosition; concealGeneratorPosition)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralWorldExtendDef using
  (StructuralWorldExtendᴿ)
open import proof.DGG.Catchup.StructuralTermProvenanceDef using
  (StructuralTermProvenance)
import proof.DGG.Catchup.StructuralGeneratedFrameGeometryDef as GFG


data TargetFrameAbsorptionChain {Δᴸ Δᴿ Δ}
    (W : CTX.World Δᴸ Δᴿ Δ) (γ : CTX.CtxImp W)
    (A : Ty Δᴸ) :
    ∀ {B E : Ty Δᴿ}
    → InstantiationSpine B E
    → A CTX.⊑ᵂ⟨ W ⟩ E
    → Set₁ where

  tfa-[] : ∀ {B} {q : A CTX.⊑ᵂ⟨ W ⟩ B}
    → TargetFrameAbsorptionChain W γ A []ⁱ q

  tfa-type : ∀ {B C E}
      {eq : B ≡ C} {spine : InstantiationSpine C E}
      {q : A CTX.⊑ᵂ⟨ W ⟩ E}
    → TargetFrameAbsorptionChain W γ A spine q
    → TargetFrameAbsorptionChain W γ A
        (type-transport-frame eq ▻ⁱ spine) q

  tfa-name : ∀ {B C E X}
      {D : Ty (suc Δᴿ)} {eqB : B ≡ `∀ D}
      {eqC : C ≡ D [ ＇ X ]ᵗ}
      {spine : InstantiationSpine C E}
      {q : A CTX.⊑ᵂ⟨ W ⟩ E}
    → TargetFrameAbsorptionChain W γ A spine q
    → TargetFrameAbsorptionChain W γ A
        (name-type-app-frame D X eqB eqC ▻ⁱ spine) q

  tfa-cast : ∀ {B C E μ}
      {c : μ ⊢ B ∼ C} {spine : InstantiationSpine C E}
      {q : A CTX.⊑ᵂ⟨ W ⟩ E}
    → A CTX.⊑ᵂ⟨ W ⟩ C
    → TargetFrameAbsorptionChain W γ A spine q
    → TargetFrameAbsorptionChain W γ A (cast-frame c ▻ⁱ spine) q

  tfa-reveal : ∀ {B C E Xᴿ Rᴿ}
      {c : Conv↑ Δᴿ B C} {spine : InstantiationSpine C E}
      {q : A CTX.⊑ᵂ⟨ W ⟩ E}
    → (c⊢ : CTX.targetStoreʷ W Conv.⊢↑[ Xᴿ ⦂ Rᴿ ] c)
    → (position : revealGeneratorPosition c⊢ ≡ generator-absent)
    → (qC : A CTX.⊑ᵂ⟨ W ⟩ C)
    → (∀ {Δᴿ′ Δ′} {χs : StoreChanges Δᴿ Δᴿ′}
        {W′′ : CTX.World Δᴸ Δᴿ′ Δ′}
        {M N} {p : A CTX.⊑ᵂ⟨ W ⟩ B}
      → (plan : StructuralWorldExtendᴿ χs W W′′)
      → (rel : W CTI2.∣ γ ⊢² M ⊑ N ∶ p)
      → StructuralTermProvenance plan rel
      → StructuralTermProvenance plan
          (CTI2.⊑reveal² c⊢ position rel qC))
    → (keep-rel : ∀ {M N N₁}
        → W CTI2.∣ γ ⊢² M ⊑ N ↑ c ∶ qC
        → (N ↑ c) —→[ keep ] N₁
        → Value N₁
        → W CTI2.∣ γ ⊢² M ⊑ N₁ ∶ qC)
    → (∀ {Δᴿ′ Δ′} {χs : StoreChanges Δᴿ Δᴿ′}
        {W′′ : CTX.World Δᴸ Δᴿ′ Δ′}
        {M N N₁} {rel : W CTI2.∣ γ ⊢² M ⊑ N ↑ c ∶ qC}
        {step : (N ↑ c) —→[ keep ] N₁} {vN₁ : Value N₁}
      → (plan : StructuralWorldExtendᴿ χs W W′′)
      → StructuralTermProvenance plan rel
      → StructuralTermProvenance plan (keep-rel rel step vN₁))
    → TargetFrameAbsorptionChain W γ A (mapInstantiationSpine keep spine) q
    → TargetFrameAbsorptionChain W γ A spine q
    → TargetFrameAbsorptionChain W γ A (reveal-frame c ▻ⁱ spine) q

  tfa-conceal : ∀ {B C E Xᴿ Rᴿ}
      {c : Conv↓ Δᴿ B C} {spine : InstantiationSpine C E}
      {q : A CTX.⊑ᵂ⟨ W ⟩ E}
    → (c⊢ : CTX.targetStoreʷ W Conv.⊢↓[ Xᴿ ⦂ Rᴿ ] c)
    → (position : concealGeneratorPosition c⊢ ≡ generator-absent)
    → (qC : A CTX.⊑ᵂ⟨ W ⟩ C)
    → (∀ {Δᴿ′ Δ′} {χs : StoreChanges Δᴿ Δᴿ′}
        {W′′ : CTX.World Δᴸ Δᴿ′ Δ′}
        {M N} {p : A CTX.⊑ᵂ⟨ W ⟩ B}
      → (plan : StructuralWorldExtendᴿ χs W W′′)
      → (rel : W CTI2.∣ γ ⊢² M ⊑ N ∶ p)
      → StructuralTermProvenance plan rel
      → StructuralTermProvenance plan
          (CTI2.⊑conceal² c⊢ position rel qC))
    → (keep-rel : ∀ {M N N₁}
        → W CTI2.∣ γ ⊢² M ⊑ N ↓ c ∶ qC
        → (N ↓ c) —→[ keep ] N₁
        → Value N₁
        → W CTI2.∣ γ ⊢² M ⊑ N₁ ∶ qC)
    → (∀ {Δᴿ′ Δ′} {χs : StoreChanges Δᴿ Δᴿ′}
        {W′′ : CTX.World Δᴸ Δᴿ′ Δ′}
        {M N N₁} {rel : W CTI2.∣ γ ⊢² M ⊑ N ↓ c ∶ qC}
        {step : (N ↓ c) —→[ keep ] N₁} {vN₁ : Value N₁}
      → (plan : StructuralWorldExtendᴿ χs W W′′)
      → StructuralTermProvenance plan rel
      → StructuralTermProvenance plan (keep-rel rel step vN₁))
    → TargetFrameAbsorptionChain W γ A (mapInstantiationSpine keep spine) q
    → TargetFrameAbsorptionChain W γ A spine q
    → TargetFrameAbsorptionChain W γ A (conceal-frame c ▻ⁱ spine) q


target-frame-cast-absorption : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ} {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B C E : Ty Δᴿ} {μ : Env∼ Δᴿ}
    {c : μ ⊢ B ∼ C} {spine : InstantiationSpine C E}
    {p : A CTX.⊑ᵂ⟨ W ⟩ B}
    {q : A CTX.⊑ᵂ⟨ W ⟩ E}
  → TargetFrameAbsorptionChain W γ A (cast-frame c ▻ⁱ spine) q
  → W CTI2.∣ γ ⊢² M ⊑ V ∶ p
  → Σ[ qC ∈ A CTX.⊑ᵂ⟨ W ⟩ C ]
      W CTI2.∣ γ ⊢² M ⊑ V ⟨ c ⟩ ∶ qC
target-frame-cast-absorption (tfa-cast qC tail) rel =
  qC , CTI2.⊑cast² _ rel qC


target-frame-reveal-absorption : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ} {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B C E : Ty Δᴿ}
    {c : Conv↑ Δᴿ B C} {spine : InstantiationSpine C E}
    {p : A CTX.⊑ᵂ⟨ W ⟩ B}
    {q : A CTX.⊑ᵂ⟨ W ⟩ E}
  → TargetFrameAbsorptionChain W γ A (reveal-frame c ▻ⁱ spine) q
  → W CTI2.∣ γ ⊢² M ⊑ V ∶ p
  → Σ[ qC ∈ A CTX.⊑ᵂ⟨ W ⟩ C ]
      W CTI2.∣ γ ⊢² M ⊑ (V ↑ c) ∶ qC
target-frame-reveal-absorption
    (tfa-reveal c⊢ position qC wrap-provenance keep-rel
      keep-provenance keep-chain tail) rel =
  qC , CTI2.⊑reveal² c⊢ position rel qC


target-frame-conceal-absorption : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ} {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B C E : Ty Δᴿ}
    {c : Conv↓ Δᴿ B C} {spine : InstantiationSpine C E}
    {p : A CTX.⊑ᵂ⟨ W ⟩ B}
    {q : A CTX.⊑ᵂ⟨ W ⟩ E}
  → TargetFrameAbsorptionChain W γ A (conceal-frame c ▻ⁱ spine) q
  → W CTI2.∣ γ ⊢² M ⊑ V ∶ p
  → Σ[ qC ∈ A CTX.⊑ᵂ⟨ W ⟩ C ]
      W CTI2.∣ γ ⊢² M ⊑ (V ↓ c) ∶ qC
target-frame-conceal-absorption
    (tfa-conceal c⊢ position qC wrap-provenance keep-rel
      keep-provenance keep-chain tail) rel =
  qC , CTI2.⊑conceal² c⊢ position rel qC


allv-∀-child-frame-chain : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ} {γ : CTX.CtxImp W}
    {Aₛ : Ty Δᴸ} {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {μ : Env∼ Δᴿ}
    {d : extᵐ μ ⊢ B ∼ C}
    {spine : InstantiationSpine (C [ ＇ X ]ᵗ) E}
    {q : Aₛ CTX.⊑ᵂ⟨ W ⟩ E}
  → GFG.StructuralAllGeneratedFrameGeometry W Aₛ C X
  → TargetFrameAbsorptionChain W γ Aₛ
      (mapInstantiationSpine keep spine) q
  → TargetFrameAbsorptionChain W γ Aₛ
      (name-type-app-frame B X refl refl ▻ⁱ
        cast-frame (d [ ＇ X ]ᶜ) ▻ⁱ
        mapInstantiationSpine keep spine) q
allv-∀-child-frame-chain geom tail =
  tfa-name (tfa-cast
    (GFG.StructuralAllGeneratedFrameGeometry.qCast geom) tail)



root-value-instantiation-frame-chain : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ (suc Δᴿ) Δ} {γ : CTX.CtxImp W}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {R : Ty Δᴿ}
    {q : A CTX.⊑ᵂ⟨ W ⟩
      applyBody (bind R) B [ ＇ Fin.zero ]ᵗ}
  → TargetFrameAbsorptionChain W γ A
      (name-type-app-frame (applyBody (bind R) B)
        Fin.zero refl refl ▻ⁱ []ⁱ) q
root-value-instantiation-frame-chain = tfa-name tfa-[]
